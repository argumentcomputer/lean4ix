#!/usr/bin/env perl
use strict;
use warnings;

# Enforce the checked-in Lean4Lean sorry frontier.
#
# This is a source-token audit rather than a raw grep: comments and strings
# may discuss sorries without enlarging the trusted frontier. Every real
# Lean sorry token is attributed to its nearest top-level declaration and
# compared with the exact allowlist below. Progress = shrinking allowlist;
# any new sorry (or a moved/renamed one) fails loudly.
#
# The allowlist is the gap inventory of the fork execution plan
# (ix:plans/lean4lean-upstream-gaps.md §2), tiered:
#   S - missing specification (nothing exists to prove against)
#   P - stated but sorried, blocked only on Tier S
#   V - upstream checker verification, blocked on Tiers S/P
#   R - research-grade metatheory (open frontier, not scheduled)
# Lean4Lean/Experimental/ is excluded from the scan entirely: parked or
# abandoned proof attacks, not part of the trusted development.
#
# Usage: check_sorry_frontier.pl [repo-root]   (defaults to script's ../..)

use Cwd qw(abs_path);
use FindBin qw($RealBin);
use File::Find qw(find);
use File::Spec;

my $repo_root =
  @ARGV
  ? abs_path($ARGV[0])
  : abs_path(File::Spec->catdir($RealBin, '..', '..'));
die "not a directory: $repo_root\n" unless -d $repo_root;

my @exclude_prefixes = (
  '.lake/',
  'Lean4Lean/Experimental/',
  'nix/',
);

my %expected = (
  # Tier S - missing specification
  # (VInductDecl.WF and VEnv.addInduct are real staged definitions)
  "Lean4Lean/Verify/Typing/Expr.lean\0def TrProj"          => 1,
  # Tier P - blocked only on Tier S
  # (addInduct_WF proven for the stage-3 direct-indexed class, 2026-07-30)
  "Lean4Lean/Verify/Typing/Lemmas.lean\0TrProj.weak'"      => 1,
  "Lean4Lean/Verify/Typing/Lemmas.lean\0TrProj.weak'_inv"  => 1,
  "Lean4Lean/Verify/Typing/Lemmas.lean\0TrProj.defeqDFC"   => 1,
  "Lean4Lean/Verify/Typing/Lemmas.lean\0TrProj.wf"         => 1,
  "Lean4Lean/Verify/Typing/Lemmas.lean\0TrProj.uniq"       => 1,
  "Lean4Lean/Verify/Typing/Lemmas.lean\0TrProj.instN"      => 1,
  "Lean4Lean/Verify/Typing/Lemmas.lean\0TrProj.instL"      => 1,
  # Tier V - checker verification, blocked on Tiers S/P
  "Lean4Lean/Verify/Level.lean\0NormLevel.subsumption_eval"     => 1,
  "Lean4Lean/Verify/Level.lean\0isEquiv_wf"                    => 1,
  "Lean4Lean/Verify/Environment.lean\0addDecl.WF"              => 1,
  "Lean4Lean/Verify/TypeChecker/InferType.lean\0inferProj.WF"   => 1,
  "Lean4Lean/Verify/TypeChecker/WHNF.lean\0reduceRecursor.WF"   => 1,
  "Lean4Lean/Verify/TypeChecker/WHNF.lean\0reduceProj.WF"       => 1,
  "Lean4Lean/Verify/TypeChecker/IsDefEq.lean\0tryEtaStructCore.WF" => 1,
  "Lean4Lean/Verify/TypeChecker/IsDefEq.lean\0isDefEqUnitLike.WF"  => 1,
  # Tier R - research-grade metatheory (do not schedule; upstream-driven)
  "Lean4Lean/Theory/Typing/Injectivity.lean\0IsDefEqU.sort_inv" => 1,
  "Lean4Lean/Theory/Typing/Injectivity.lean\0IsDefEqU.forallE_inv_stratified" => 1,
  "Lean4Lean/Theory/Typing/Injectivity.lean\0IsDefEqU.sort_forallE_inv" => 1,
  "Lean4Lean/Theory/Typing/UniqueTyping.lean\0IsDefEqU.weakN_iff"   => 1,
  "Lean4Lean/Theory/Typing/ChurchRosser.lean\0NormalEq.parRed"      => 2,
);

sub mask_chunk {
  my ($chunk) = @_;
  $chunk =~ s/[^\n]/ /g;
  return $chunk;
}

sub earliest {
  my @positions = grep { $_ >= 0 } @_;
  return -1 unless @positions;
  my ($first) = sort { $a <=> $b } @positions;
  return $first;
}

sub mask_non_code {
  my ($source, $path) = @_;
  my $length = length $source;
  my $index = 0;
  my $block_depth = 0;
  my @masked;

  while ($index < $length) {
    if ($block_depth) {
      my $open = index($source, '/-', $index);
      my $close = index($source, '-/', $index);
      my $next = earliest($open, $close);
      die "$path: unterminated block comment\n" if $next < 0;
      push @masked, mask_chunk(substr($source, $index, $next + 2 - $index));
      if ($next == $open) {
        ++$block_depth;
      } else {
        --$block_depth;
      }
      $index = $next + 2;
      next;
    }

    my $line_comment = index($source, '--', $index);
    my $block_comment = index($source, '/-', $index);
    my $quote = index($source, '"', $index);
    my $next = earliest($line_comment, $block_comment, $quote);

    if ($next < 0) {
      push @masked, substr($source, $index);
      $index = $length;
      next;
    }

    push @masked, substr($source, $index, $next - $index);
    if ($next == $line_comment) {
      my $newline = index($source, "\n", $next);
      my $end = $newline < 0 ? $length : $newline;
      push @masked, mask_chunk(substr($source, $next, $end - $next));
      $index = $end;
    } elsif ($next == $block_comment) {
      push @masked, '  ';
      $block_depth = 1;
      $index = $next + 2;
    } else {
      my $closing = $next + 1;
      while (1) {
        $closing = index($source, '"', $closing);
        die "$path: unterminated string literal\n" if $closing < 0;
        my $slashes = 0;
        my $before = $closing - 1;
        while ($before > $next && substr($source, $before, 1) eq '\\') {
          ++$slashes;
          --$before;
        }
        last if $slashes % 2 == 0;
        ++$closing;
      }
      push @masked,
        mask_chunk(substr($source, $next, $closing + 1 - $next));
      $index = $closing + 1;
    }
  }

  die "$path: unterminated block comment\n" if $block_depth;
  return join '', @masked;
}

sub relative_path {
  my ($path) = @_;
  my $relative = File::Spec->abs2rel($path, $repo_root);
  $relative =~ s{\\}{/}g;
  return $relative;
}

sub find_sorries {
  my ($path) = @_;
  open my $handle, '<:encoding(UTF-8)', $path
    or die "cannot read $path: $!\n";
  local $/;
  my $source = <$handle>;
  close $handle;

  return () unless $source =~ /\bsorry\b/;
  my $code = mask_non_code($source, $path);
  my @commands;
  while (
    $code =~
      m{^[ \t]*(?:@\[[^\]]*\][ \t]+)*
        (?:(?:private|protected|noncomputable|nonrec)[ \t]+)*
        (theorem|lemma|def|opaque|abbrev|instance|inductive|structure|example)
        [ \t]+([A-Za-z_][A-Za-z0-9_'.?]*)}mgx
  ) {
    push @commands, [$-[0], $1, $2];
  }

  my @found;
  my $command_index = -1;
  while ($code =~ /\bsorry\b/g) {
    my $position = $-[0];
    while (
      $command_index + 1 < @commands
      && $commands[$command_index + 1]->[0] < $position
    ) {
      ++$command_index;
    }

    my $declaration = '<no enclosing declaration>';
    if ($command_index >= 0) {
      my ($unused, $kind, $name) = @{$commands[$command_index]};
      $declaration = $kind =~ /^(?:theorem|lemma)$/ ? $name : "$kind $name";
    }
    my $prefix = substr($source, 0, $position);
    my $line = 1 + ($prefix =~ tr/\n//);
    push @found, [relative_path($path), $declaration, $line];
  }
  return @found;
}

my @observed_with_lines;
eval {
  my @lean_files;
  find(
    {
      no_chdir => 1,
      wanted => sub {
        return unless -f $File::Find::name;
        return unless $File::Find::name =~ /\.lean\z/;
        my $relative = relative_path($File::Find::name);
        for my $prefix (@exclude_prefixes) {
          return if index($relative, $prefix) == 0;
        }
        push @lean_files, $File::Find::name;
      },
    },
    $repo_root,
  );
  for my $path (sort @lean_files) {
    push @observed_with_lines, find_sorries($path);
  }
  1;
} or do {
  my $error = $@ || 'unknown scan error';
  print STDERR "sorry-frontier audit failed to scan sources: $error";
  exit 2;
};

my %observed;
for my $entry (@observed_with_lines) {
  ++$observed{"$entry->[0]\0$entry->[1]"};
}

my $matches = 1;
for my $key (keys %expected) {
  $matches = 0 if ($observed{$key} // 0) != $expected{$key};
}
for my $key (keys %observed) {
  $matches = 0 if ($expected{$key} // 0) != $observed{$key};
}

if (!$matches) {
  print STDERR "Lean4Lean sorry frontier changed.\n";
  print STDERR "Expected:\n";
  for my $key (sort keys %expected) {
    my ($path, $declaration) = split /\0/, $key, 2;
    print STDERR "  $expected{$key} x $path :: $declaration\n";
  }
  print STDERR "Observed:\n";
  if (@observed_with_lines) {
    for my $entry (@observed_with_lines) {
      print STDERR "  $entry->[0]:$entry->[2] :: $entry->[1]\n";
    }
  } else {
    print STDERR "  <none>\n";
  }
  print STDERR
    "Update the allowlist only when the trusted frontier intentionally changes.\n";
  exit 1;
}

print "Lean4Lean sorry frontier OK (" . scalar(@observed_with_lines) . " known sorries):\n";
for my $entry (@observed_with_lines) {
  print "  $entry->[0]:$entry->[2] :: $entry->[1]\n";
}
