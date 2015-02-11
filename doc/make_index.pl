#!/usr/local/bin/perl

# Useful for making an index laTex file from *.idx file

if ( $#ARGV != 0 ) {
  print "Usage: $0 <idxfilename>\n";
  exit 0;
}
 
$idxfile=$ARGV[0];


open(IN,"<$idxfile") || die("Can not open $idxfile");

while(<IN>) {
	chomp;
	s/}//g;
	($junk, $idname, $page) = split /{/;
	$idname =~ s#^\\##;
	if ($index{$idname} eq "") {
		$index{$idname}="$page";
	}
	elsif ($index{$idname} ne "$page" && ($index{$idname} !~ / $page/)) {
		$index{$idname}.=" $page";
	}
}
close(IN);

print "\\begin{theindex}\n";
foreach $i (sort(keys %index)) {
   my $line_numbers = $index{$i};
   $line_numbers =~ s/ /, /; 

	#print "\\item $i $index{$i}\n";
	print "\\item $i $line_numbers\n";
}
print "\\end{theindex}\n";

