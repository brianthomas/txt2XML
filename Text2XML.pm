#!/usr/bin/perl -w 

# /** COPYRIGHT
#    Text2XML.pm Copyright (C) 2000 Brian Thomas,
#    ADC/GSFC-NASA, Code 631, Greenbelt MD, 20771
#  
#    This program is free software; it is licensed under the same terms
#    as Perl itself is. Please refer to the file LICENSE which is contained
#    in the distribution that this file came in.
#  
#   This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
# */

# $Id: Text2XML.pm,v 1.34 2000/04/27 14:42:54 thomas Exp thomas $

# DESCRIPTION
# ------------ 
# A generic text 2 XML parser module using DOM objects. 
#
# Reads in an XML formatted set of parsing rules
# for the document of interest and then extracts
# them as directed by that format statement. 
#
# System: XML legacy parsing 
#
# Design by Ed Shaya/Brian Thomas and Jim Blackwell 
# Code   by Brian Thomas and Ed Shaya 
#
# Contact Persons: Brian Thomas (thomas@adc.gsfc.nasa.gov)
#                  Ed Shaya (shaya@xfiles.gsfc.nasa.gov)

# Version Map
# ------------
# 6/22/99 v0.01 Our first version sees the light of day. It
#               can load text file to chunk, it can load XML
#               formatted rules file. -b.t. 
# 6/23/99 v0.02 Work on pattern matching logic started. Will
#               recursively pass the chunk.
# 6/25/99 v0.5  Alpha version. Functionality of repeat,choose
#               match rules complete. Included non-tag match
#               functionality.
# 6/29/99 v0.8  Various bugs fixed, added in remainder attribute
#               to match rules
# 6/30/99 v0.9  More bugs fixed. Added in test string capability
#               and more advanced error reporting
# 7/3/99  v0.95 Modularized
# 7/7/99  v0.96 Inserted parser events code; This allows us to
#               pass back an "object" array that contains information
#               on the chunk, match, errors for each rule as the
#               parse occured.
# 7/14/99 v0.97 Folded in bug fixes from txt2XML.pl to this version
# 7/22/99 v0.98 More bug fixes. In certain cases, after a repeat rule
#               finished and had exhausted the current chunk, any sibling
#               rules were ignored. Now, all rules will be traversed.
# 7/23/99 v0.99 Bad bug in event display stuff. Treatment of statusOfEnd
#               strings left out when "accept" was the rule case. Fixed.
#               Now we use document Entity defs to properly output/tag
#               stuff.
# 7/26/99 v1.00 Release version. Fixed minor error report that had 
#               doubly entified output.
# 7/27/99 v1.01 Bug fix. When the matching string was '0', it was thinking
#               no string had actually matched(!). Fixed to allow single '0'
#               in matches.
# 7/29/99 v1.1  Changed <toXML> rule to be <txt2XML>. Seems like semi-major
#               format change, so lets bump up version number by .1 
# 8/4/99  v1.11 Added root_tag attribute to the txt2XML tag.
# 8/5/99  v1.12 Fixed bug in match remainder error. Wasnt clearing out match_string
#               after error occured, this allowed the match_string to be re-appended
#               to the working chunk.
# 8/17/99 v1.13 Changed to make preamble comment now tagged element just inside the
#               root tag. Fixed some 'memory leaks' from not clearing/reseting
#               global arrays for events, opentags and the like. AND a big memory
#               waster of passing whole string chunks instead of just the lengths
#               in the events array. Error events no longer passed (they were redundant
#               with the error buffer anyways). 
# 8/18/99 v1.20 Added the ignore rule.  
# 8/20/99 v1.21 Bug fix for halt rule (was deleting all rules following it).
# 8/23/99 v1.22 Allow null matching switch, put txt2XML tag within root tag. 
# 8/30/99 v1.23 Bug fix for display problem. Implimented script (rules) version 
#               declaration.
# 8/31/99 v1.24 Bug fix version for null matching. Non-required rules shouldnt
# [RCS 1.16?]   open elements on null matches
# 2/18/00 v1.25 Bug fix. Remainder data wasnt being encoded as requested.
# [RCS 1.17]    Also, remainder data rules not working as advertised. Fixed.
#         v1.26 ??
# 2/28/00 v1.27 Changed code to accomodate new click-on-error interface in txt2XML
# [1.18]        Fixed minor close element indentation bug (not being used!) 
# 2/29/00 v1.28 Fixed bug in remainder="Data" nullmatching rules that had children
# [1.19]        werent being closed properly. Added configuration of runtime params
#               from attributes declared in the txt2XML rule. These values may still be over
#               ridden by txt2XML.pl command line args or gui menu selections. 
# 3/01/00  v1.29 Y2K bug fix in get_file_stat. Now year returned is 4 digit year.
# 3/01/00  v1.30 Merged version numbers between RCS and Code
# 3/06/00  v1.31 parse_document passes along the number of errors that occured
# 3/09/00  v1.32 Bug fixing: When remainder="data" and the data was "0" you would fail
#                to write the value out. Also, if the match was "0" and should have
#                been passed to child rules, it wouldnt. Finally: allow match
#                remainder to be error level 0 in the case matching_string is all
#                whitespace. 
# 3/15/00  v1.33 Small changes to parseing of text (make_DOM_from_text used instead
#                of hacky load_rules_from_text). Small changes to sanity check on 
#                rules. 
# 4/13/00  v1.34 Minor fix. lowered missing root_tag attribute to error level 2, made
#                the program open a root tag called "NO_ROOT_TAG_SPECIFIED" in this case.
# 4/27/00  v1.35 Bug fix. When match w/ children had statusOfStart==Accept the
#                highlighting of the string was incorrect. Fixed Text2XML.pm to pass
#                better information to the GUI.  



# P A C K A G E  S E T U P

package Text2XML;

# Modules we will use
use XML::DOM;

# pragmas
use strict;
use vars qw ($VERSION);
use integer; # tells perl to assume integer, rather than floating point
             # this screws up the score calculation

$VERSION = 1.35;      # the version of txt2XML this is 

# Global Runtime parameters
my $parse_nest_level = 0;  # keeps track of level of recursive calls to parser 
my $XML_VERSION = '1.0';
my $PREAMBLE_STRING = "";

# Global arrays (feh!). 
                          # This should really be an array of objects 
my @events;               # a record of how we traversed the rules
                          # and input text. Holds information on chunk too. 
my @open_tags_at_this_level = [{}];
my @choose_rule_at_this_level;
my @repeat_rule_at_this_level;

# error levels. The higher the value, the more serious the error
my $TRIVIAL_ERROR = 0; 
my $REGULAR_ERROR = 1; 
my $SERIOUS_ERROR = 2; 
my $IMPOSSIBLE_ERROR = 99;

# Global runtime control parameters
my %RUNTIME_PARAM = (
                      'include_errors_in_output' => 0,
                      'halt_count' => 0,               # numver of halt statement to stop parsing at  
                      'print_errors_to_stderr' => 0,
                      'accept_null_matches' => 0,
                      'entities_to_encode' => '"&<>' . "'",
                      'output_filehandle' => 0, 
                      'halt_on_error_level' => $IMPOSSIBLE_ERROR, # dont Halt 
                      'error_tag' => 'ERROR',
                    );

# my $INCLUDE_ERRORS_IN_OUTPUT = 0;
# my $HALT_COUNT = 0;		# number of halt statement to stop parsing at
# my $PRINT_ERRORS_TO_STDERR = 0;
#my $ACCEPT_NULL_MATCHES_AS_GOOD = 0;
# my $DEFAULT_ENTITIES_TO_ENCODE = '"&<>' . "'";
#my $ERROR_TAG ="ERROR";
#my $HALT_ON_ERROR_LEVEL = $IMPOSSIBLE_ERROR;    # Dont Halt 

# Other (internal) Global Defines

my $OUTPUT_FILEHANDLE = 0; # Either a real filehandle (eg STDOUT or an open file) or
                           # '0' which means to store parsed output in the $output_text SCALAR.

my $CURRENT_EVENT;        # reference to the current event in the events array 
my $ABSOLUTE_CHUNK_START_POSITION = 0; # text index of where we are currently 
                                       # in the input doc. 
my $output_text;          # the parsed output text. 
# my $error_buffer;         # buffer with all the accumulated error messages from parse 
my $removed_text_buffer;  # how much removed text (from errors). This is used by
                          # calculate score 
my $error_number;         # the number of errors we have encountered this parse 

# strictly internal runtime params
my $USE_EVENTS = 0; 		# 0 == dont use parser events
my $STOP_ON_HALT = 0;
my $HALT_PARSE = 0;             # a control statement that stops our parsing

my $INDENT_PER_NESTED_LEVEL = "  "; # chars to use for indentation per nested level


# default attribute values (also tells us allowed attributes) 
# for various rules

#### MATCH, IGNORE && txt2XML rules ####
my %default_match_attribute_value = ( 
                                'tag' => "",               # name of tag to be created 
                                'start' => '^', 
                                'end' => '$', 
                                'test' => 0,                # 0 or a pattern to test with. The
                                                            # tests the string after start/end are matched
                                'root_tag' => "",           # same as 'tag', but only used in txt2XML rule
                                'script_version' => "",     # should only be used by txt2XML rule,
                                                            # it identifies the rule defined version
                                                            # number for their rules
                                'statusOfStart' => 'drop',  # 'drop' or 'accept' 
                                'statusOfEnd' => 'drop',    # 'drop' or 'accept' or 'donate' 
                                                            # (ie to leave as part of working chunk) 
                                'remainder' => 'error',     # 'error' or 'data'. This is how
                                                            # we treat the chunk text.
                                'required' => 'yes'         # 'yes' or 'no' (ie do we need to 
                                                            #  to match while parsing) 
                                    );

#### CHOOSE rules ####
my %default_choose_attribute_value = ( 'required' => "no"   # "yes" or "no" 
                                    );

#### REPEAT rules ####
my %default_repeat_attribute_value = ( 'required' => "no"   # "yes" or "no"   
                                    );

#### PRINT rules ####
my %default_print_attribute_value = ( 'what' => "chunk"     # either 'rule' or 'chunk' 
                                    );

#### HALT rules ####
my %default_halt_attribute_value = ( 'when' => "now"        # either 'now' or number of times before halt
                                                            # NOT implemented currently
                                    );

my $SPECIAL_NON_WORD_MATCHING_CHAR = '\^\$';  # ^ and $ are special, dont treat as words 
                                                 # and so we wont build a pattern that uses
                                                 # the \b word boundry. See get_match_pattern()
                                                 # below for its logic.

my $ANY_CHAR_MATCH = '\s\S'; # perl has problems with more than one set of brackets in 
                             # a where one of the brakets needs a '.' AND '*' AND is within a 
                             # parenthesis match pattern. Eg. this pattern will work
                             #
                             #   $match =~ /([A-Z])(.*?)(string)/;
                             #
                             # whereas this will *not*work
                             #
                             #   $match =~ /([A-Z])([.\n]*?)(string)/;
                             #                      ^^^^^^^ 
                             # To avoid this problem then, we will kludge around needing
                             # the [.\n]* part of the match by replacing the '.' with other
                             # perl match character(s) as defined above. 

my $MEM_DEBUG = 0;  # Only if youre wacky enough to handle it
my $EXTREME_MEM_DEBUG = 0;  # Only if youre wacky enough to handle it
my $EXTREME_RULE_DEBUG = 0;  # Only if youre wacky enough to handle it
my $EXTREME_MATCH_DEBUG = 0; # Only if you love TONS of output
my $TRUNCATE_ERROR_CHUNK_MSG = 0; # lets not print more than one line of chunk that
                                  # creates the error
my $DEBUG = 0;               # Other Debugging output flag 


#
# M E T H O D S which change/retrieve runtime parameters
#

sub set_output_filehandle { $OUTPUT_FILEHANDLE = @_;}
sub set_debug_flag { $DEBUG = @_; }
sub set_mem_debug_flag { $MEM_DEBUG = @_; }

sub get_runtime_params { return %RUNTIME_PARAM; }

# O T H E R  S U B R O U T I N E S

#load the rules into a DOM 
sub load_rules_from_file {
  my ($format_file) = @_;

  my $parser = new XML::DOM::Parser;

  print "CREATING the DOM from $format_file\n" if $DEBUG;
  my $rules;

  $rules = $parser->parsefile($format_file);

  my $ok = &check_rules_for_sanity($rules);
  return ($ok ,$rules);
}

sub load_rules_from_text {
  my ($text) = @_;

  my $rules = make_DOM_from_text($text);
  my $ok = &check_rules_for_sanity($rules);
  return ($ok ,$rules);

}

sub make_DOM_from_text {
  my ($text) = @_;

  print "CREATING the DOM from text.\n" if $DEBUG;
  my $parser = new XML::DOM::Parser;
  my $doc = $parser->parse($text);
  return $doc;

}

# this is hacky, but works
sub load_rules_from_text_old {
  my ($text) = @_;

  my $tmp_file = "TMP_RULES_FILE";
  open(TMP_FILE,">$tmp_file");
  print TMP_FILE $text;
  close TMP_FILE;

  my ($load_ok,$doc) = &load_rules_from_file($tmp_file); 

  # clean up
  unlink ($tmp_file);
 
  return ($load_ok,$doc); 
}

sub check_rules_for_sanity {
  my ($rules) = @_;

  print "Examining the RULES DOM\n" if $DEBUG;
  print_DOM($rules) if $EXTREME_RULE_DEBUG && $rules;

  return &sanity_check_on_rules($rules);
}

sub reset_globals_for_document_parse {
  # clear output text, error buffer & removed text buffers 
 #  $error_buffer = " ";
  $removed_text_buffer = " ";
  $output_text = "";

  # reset the arrays  
  &reset_open_tags();
  @choose_rule_at_this_level = ();
  @repeat_rule_at_this_level = ();
  foreach my $event (0 ... $#events) { $events[$event] = 0; }

  @events = (); 
  $ABSOLUTE_CHUNK_START_POSITION = 0;
  $CURRENT_EVENT = undef;

  # set the number of encountered errors back to 0
  $error_number = 0;

  $HALT_PARSE = 0;
  $STOP_ON_HALT = -1;

  $RUNTIME_PARAM{'root_tag'} = "root";
  $RUNTIME_PARAM{'script_version'} = "-1";

}

# sloppy, should be in RUNTIME_PARAM hash
sub set_runtime_params {
  my ($include_errors_in_out_text, $halt_to_stop_on, $halt_error_level,
      $allow_null_matches,$use_events) = @_;

  $USE_EVENTS = $use_events if defined $use_events;

  # set how we will send out error messages
  # $INCLUDE_ERRORS_IN_OUTPUT = $include_errors_in_out_text;
  $RUNTIME_PARAM{'include_errors_in_output'} = $include_errors_in_out_text; 

  # set matching mode
  #$ACCEPT_NULL_MATCHES_AS_GOOD = $allow_null_matches;
  $RUNTIME_PARAM{'accept_null_matches'} = $allow_null_matches;

  # $HALT_COUNT = 0;
  $RUNTIME_PARAM{'halt_count'} = 0;
  #$HALT_ON_ERROR_LEVEL = $REGULAR_ERROR;    # Halt on level 1 errors 
  $RUNTIME_PARAM{'halt_on_error_level'} = $REGULAR_ERROR;    # Halt on level 1 errors 

  #$HALT_ON_ERROR_LEVEL = $halt_error_level if defined $halt_error_level;
  $RUNTIME_PARAM{'halt_on_error_level'} = $halt_error_level if defined $halt_error_level;

  $STOP_ON_HALT = $halt_to_stop_on if defined $halt_to_stop_on;

}


sub reset_open_tags {
  foreach my $level (0 ... $#open_tags_at_this_level) {
             #foreach my $key ( keys %{$open_tags_at_this_level[$level]}) {
             #  delete %{$open_tags_at_this_level[$level]}->{$key};
             #}
             $open_tags_at_this_level[$level] = 0;
         }
  @open_tags_at_this_level = [{}];
}


sub parse_document {
  my ($document_chunk,$input_file,$format_file,$include_errors_in_output,
      $rules,$halt_to_stop_on,$halt_error_level,$entities_to_encode,$use_events,
      $allow_null_matching) = @_;


  # sloppy, should just have one global hash.
  &reset_globals_for_document_parse();

  # starting rule (should be txt2XML rule)
  my $first_rule = get_first_child_rule($rules);

  # $DEFAULT_ENTITIES_TO_ENCODE = $entities_to_encode if defined $entities_to_encode;
  $RUNTIME_PARAM{'default_entities_to_encode'} = $entities_to_encode if defined $entities_to_encode;

  # initialize runtime parameters from rules decl first
  &set_runtime_params_from_rules($first_rule);

  # now, if runtime flags where called on the command line OR 
  # the user changed the configuration from gui menus its 
  # possible that we override the runtime defaults with these 
  &set_runtime_params($include_errors_in_output,$halt_to_stop_on, 
                      $halt_error_level, $allow_null_matching, $use_events);

  # start up the XML document, set any parameters defined
  # in the first rule attributes
  #  my $script_version = &get_version_value($first_rule);

  $PREAMBLE_STRING = &do_preamble($input_file,$format_file,$RUNTIME_PARAM{'script_version'});

  # And here's the 'meat' of the code here
  my $remaining_chunk = &parse_this_chunk($document_chunk,$first_rule);

  return ($output_text,&calculate_score($document_chunk,$removed_text_buffer),
          \@events, $error_number);
  #        $error_buffer,\@events,\$rules);

}

sub set_runtime_params_from_rules {
  my ($first_rule) = @_;

  my $attribute_list = $first_rule->getAttributes;
  foreach my $attrib (0 ... ($attribute_list->getLength() -1)) {
    my $item = $attribute_list->item($attrib);
    my $name = $item->getNodeName();
    my $val = $item->getValue();
    if (defined $RUNTIME_PARAM{$name}) {
      # print "SETTING $name : $val [$attrib]\n";
      $RUNTIME_PARAM{$name} = $val;
    } else {
      &print_error("the txt2XML rule has no $name attribute", 3, 'bad attribute'); 
    }
  }

#  $attribute_list->dispose;

}

sub calculate_score {
  my ($doc_chunk,$error_buf) = @_;

  no integer; # we need floating point here 

  my $total_len = length($doc_chunk);
  my $error_len = length($error_buf);

  my $score = $total_len > 0 ? (($total_len - $error_len)/$total_len) : -1; 

  return $score;
}

# This is what gets lead off the top of the printed XML file
sub do_preamble {
  my ($file_to_be_parsed,$format_file,$version) = @_;

  PRINT_OUT("<?xml version=\"$XML_VERSION\"?>\n");

  return &get_stamp_string($file_to_be_parsed,$format_file,$version);
}

sub get_stamp_string {
  my ($file_to_be_parsed,$format_file,$rules_version) = @_;

  my ($mode,$uid,$size,$atime,$mtime) = get_file_stats($file_to_be_parsed);
  ($mode,$uid,$size,$atime,$mtime) = get_file_stats($format_file);

  my $indentation = get_indentation(1);
#  my $txt2XML_element = "$indentation<txt2XML program_version=\"$VERSION\" execution_date=\"$atime\" error_tag_name=\"$ERROR_TAG\" input_file_name=\"$file_to_be_parsed\" input_file_mod_date=\"$mtime\" xml_rules_file_name=\"$format_file\" rules_version=\"$rules_version\" rules_file_mod_date=\"$mtime\"/>\n";
 
  my $txt2XML_element = "$indentation<txt2XML program_version=\"$VERSION\" execution_date=\"$atime\" error_tag_name=\"$RUNTIME_PARAM{'error_tag'}\" input_file_name=\"$file_to_be_parsed\" input_file_mod_date=\"$mtime\" xml_rules_file_name=\"$format_file\" rules_version=\"$rules_version\" rules_file_mod_date=\"$mtime\"/>\n";
  return $txt2XML_element;
}

sub get_file_stats {
  my ($file) = @_;
 
  my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksz,$blocks) =
     stat($file);
 
  my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) =  localtime $mtime ;
  $mon++;
  $year+=1900;
  $mtime = "$mon/$mday/$year-$hour:$min:$sec";

  ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) =  localtime $atime ;
  $mon++;
  $year+=1900;
  $atime = "$mon/$mday/$year-$hour:$min:$sec";

  return ($mode,$uid,$size,$atime,$mtime);
}

# Gets an entire document (file) as a single line text 'chunk' 
# We treat the cases of elimination of leading/trailing spaces
sub get_document_text_chunk ($) {
  my ($file) = @_;

  my $text;
  my $old_input_rec_sep = $/;

  if ($file && -e $file) {
    undef $/; #input rec separator, once newline, now nothing.
            # will cause whole file to be read in one whack 

    open (TXT, "<$file" ); $text = <TXT>; close TXT;
  }

  # well, here's a hack and a half. Returned
  # text has an extra newline character, feh.
  # if we chomp, that character disappears, BUT
  # we then bomb out the reading in of this text
  # to a DOM. (double feh!). Ill just chomp off 
  # that newline and add a space.
  $/ = $old_input_rec_sep;
  chomp $text;
  $text .= " ";

  return $text;
}

sub print_DOM ($) { my ($dom) =@_; print "print_DOM\n"; $dom->printToFileHandle(\*STDOUT); }

# dumps the node and all of its sub (children) nodes
sub dump_node {
  my ($node,$dont_dump_children) = @_;

  $dont_dump_children = 0 if !defined $dont_dump_children;

  my $type = $node->getNodeTypeName();
  return if ($type ne "ELEMENT_NODE"); # we only want element nodes 

  # node properites
  my $node_name = $node->getNodeName();
  my @children = $node->getChildNodes;

  # snagging attributes
  my $tag_value = get_rule_tag_value($node);
  my $start_value = get_rule_start_value($node);
  my $end_value = get_rule_end_value($node);
  my $req_value = get_rule_required_value($node);

  print "NODE[$node_name]:" . 
    "[tag=$tag_value start=\"$start_value\" end=\"$end_value\" required=\"$req_value\"]" .
    " with $#children child elements \n";

  foreach my $child (@children) { dump_node($child) if $child && !$dont_dump_children; } 
}

sub get_version_value { 
  my ($first_node) = @_; 
  
  my $type = &get_rule_type($first_node); 

  my $version;
  if ($type eq "txt2XML") {
    $version = &get_attribute_value($first_node,"script_version"); 
    die "ERROR: 'script_version' attribute not found on txt2XML rule" unless $version;
  } else {
    die "ERROR: Weird first rule type:[$type], was expecting 'txt2XML' rule first!";
  }

  return $version;
}

# heres a set of quicky accessor methods to node attributes
sub get_rule_type ($) { my ($rule) = @_;return $rule->getNodeName(); }
sub get_rule_what_value ($) { my ($node) = @_; return &get_attribute_value ($node,"what"); }
sub get_rule_test_value ($) { my ($node) = @_; return &get_attribute_value ($node,"test"); }
sub get_rule_tag_value ($) { my ($node) = @_; return &get_attribute_value ($node,"tag"); }
sub get_rule_root_tag_value ($) { my ($node) = @_; return &get_attribute_value ($node,"root_tag"); }
sub get_rule_start_value ($) { my ($node) = @_; return &get_attribute_value ($node,"start"); }
sub get_rule_end_value ($) { my ($node) = @_; return &get_attribute_value ($node,"end"); }
sub get_rule_statusOfStart_value ($) { my ($node) = @_; return &get_attribute_value ($node,"statusOfStart"); }
sub get_rule_statusOfEnd_value ($) { my ($node) = @_; return &get_attribute_value ($node,"statusOfEnd"); }
sub get_rule_required_value ($) { my ($node) = @_; return &get_attribute_value ($node,"required"); }
sub get_rule_remainder_value ($) { my ($node) = @_; return &get_attribute_value ($node,"remainder"); }
 
# generalized method for accessing node object attributes
sub get_attribute_value ($$) {
  my ($node,$attrib_name) = @_; 

  my $attribute_list = $node->getAttributes;

  # minimal error checking
  die "ERROR: Requested Attribute List ($attrib_name) From Node without any!"
    unless (defined $attribute_list);
  die "ERROR: Requested Attribute Value From Node without Attribute Name!"
    unless (defined $attrib_name);

  my $attrib_obj = $attribute_list->getNamedItem($attrib_name);

  my $ret_attr_val;
  $ret_attr_val = $attrib_obj->getNodeValue() if $attrib_obj;

  # Was their a defined value? 
  # hardwiring these seems bad to do too.
  #
  if((get_rule_type($node) eq "match" 
         || get_rule_type($node) eq "ignore" 
         || get_rule_type($node) eq "txt2XML" ) 
       && !defined $ret_attr_val
  ) {
    $ret_attr_val = $default_match_attribute_value{$attrib_name};
  } elsif(get_rule_type($node) eq "choose" && !defined $ret_attr_val
  ) {
    $ret_attr_val = $default_choose_attribute_value{$attrib_name};
  } elsif(get_rule_type($node) eq "repeat" && !defined $ret_attr_val
  ) {
    $ret_attr_val = $default_repeat_attribute_value{$attrib_name};
  } elsif(get_rule_type($node) eq "print" && !defined $ret_attr_val
  ) {
    $ret_attr_val = $default_print_attribute_value{$attrib_name};
  } 

  # garbage collection
#  $attribute_list->dispose;

  return $ret_attr_val; # this *could* still return undef if Node 
                        # isnt type "match", "ignore" or "txt2XML" 
}

# UNIX based determination
sub get_memory_use {
  my $buf =  `ps alx | grep txt2`;
  my @vals = split ' ', $buf;
  return $vals[6];
}

sub parse_this_chunk ($$) {
  my ($working_chunk,$first_rule_for_this_chunk) = @_;

#print "CALL TO parse_this_chunk(",get_rule_type($first_rule_for_this_chunk),")" if $EXTREME_RULE_DEBUG;
#print "parse level:[$parse_nest_level] mem:[",&get_memory_use(),"]\n" if $MEM_DEBUG;

  # some sanity checks
  die "ERROR! no chunk to examine for these rules" if (!defined $working_chunk || $working_chunk eq "");
  die "ERROR! no rules to use for this chunk" if !$first_rule_for_this_chunk;

  my $current_rule = &first_rule_at_this_level($first_rule_for_this_chunk);

  # Loop thru rules at the SAME level. We'll desend into child rules 
  # when they exist (and a working chunk is passed to them)

  my $this_level_is_nested_within_repeat = &my_parent_is_a_repeat_rule($current_rule); 

  # Basically we want to loop until we dont match for any given rule
  my $old_chunk = $working_chunk;
  my $success = 0;
  do {

     $working_chunk = &apply_a_rule_to_the_chunk($current_rule,$working_chunk);

     # our test of "success" in parsing. Did we subtract anything
     # from the working chunk?
     $success = 1 if (!($working_chunk eq $old_chunk));
     $old_chunk = $working_chunk;

     # move on to next rule, discard all but element nodes
     $current_rule = get_next_sibling_rule($current_rule);
   
     # hurmm. Did we run out of rules?
     # we should terminate our traversal of the chunk UNLESS
     # the rules at this level are nested within a repeat statement
     # AND during our previous pass we made success in parsing
     # the working chunk AND still have some chunk left. In the case of 
     # repeating, we just reset current rule to the first at the level 
     if(!$current_rule && $this_level_is_nested_within_repeat 
            && $working_chunk && $success) {
       $current_rule = first_rule_at_this_level($first_rule_for_this_chunk);
       $success = 0;
     }

  # } while ($working_chunk && $current_rule && !$HALT_PARSE);
  } while ($current_rule && !$HALT_PARSE);

  # well, we might have some chunk left over. Usually, this is an error
  # condition, however, if remainder="data" is set in the parent, it could
  # be that the data should be written out as cddata (text) within the node
  # of the parent. We have to do this here, before we close the open parent
  # node a few lines below this one
  my $parent = &get_parent_match_rule($first_rule_for_this_chunk);
  $working_chunk = &deal_with_remainder_chunk_from_match($parent, $working_chunk)
                        if(defined $working_chunk && $working_chunk ne "" && $parent 
                           && get_rule_remainder_value($parent) eq "data");

  print "FINISHED PARSING CHUNK at level:[$parse_nest_level] " if $EXTREME_RULE_DEBUG;
  print "REMAINING CHUNK:[$working_chunk]\n"  if $EXTREME_RULE_DEBUG && $working_chunk;
  print "\n" if $EXTREME_RULE_DEBUG;

  # close out any repeat or choose rules at this level
  $choose_rule_at_this_level[$parse_nest_level] = 0;
  $repeat_rule_at_this_level[$parse_nest_level] = 0;

  # close out any open tags at this level
  close_all_open_tags_at_this_level($parse_nest_level);

  return $working_chunk;
}

sub deal_with_remainder_chunk_from_match {
  my ($rule, $working_chunk) = @_;

  # well, should we write this out now? Only if the parent
  # match rule doesnt exist (we are near the root tag level) or
  # if the parent match exists, it does NOT have remainder="data" set 
  # otherwise, we'll  pass this remaining chunk up to the next level
  # (or in the case of no parent match rule) it will error out.
  my $parent = get_parent_match_rule($rule);
  if(!$parent || get_rule_remainder_value($parent) ne "data") {

    # Looks like this remainder data *should be written out* for
    # the current rule, however, we should first do 
    # a little test here. Non-tag match rules arent allowed
    # to have remainder attribute set to anything other than 'error'
    if(!get_rule_tag_value($rule)) {
       &print_error( "$working_chunk", 2,'non-tag match with remainder=data',$working_chunk);
    } else {
#       PRINT_OUT('AFTER CASE' );
       PRINT_OUT(encode_string($working_chunk)); # send this text out 
                                                 # make sure its encoded!
    }
    $working_chunk = ""; # 'subtract' text from working chunk
  }

  return $working_chunk;
}

sub close_all_open_tags_at_this_level {
  my ($parse_level) = @_;

  print "CLOSING TAGS AT LEVEL:[$parse_nest_level]\n" if $EXTREME_RULE_DEBUG;

  foreach my $tagname (keys %{$open_tags_at_this_level[$parse_nest_level]}) {
    while (%{$open_tags_at_this_level[$parse_nest_level]}->{$tagname}) {
      CLOSE_ELEMENT($tagname);
    }
  }
}

sub first_rule_at_this_level {
  my ($rule) = @_;

  $rule = get_next_sibling_rule($rule) unless $rule->getNodeTypeName eq "ELEMENT_NODE";

  return $rule;
}

sub get_next_sibling_rule {
  my ($rule) = @_;

  $rule = $rule->getNextSibling();
  while($rule && $rule->getNodeTypeName ne "ELEMENT_NODE") {
    $rule = $rule->getNextSibling();
  }

  if($rule && $EXTREME_RULE_DEBUG) {
    my $name = get_rule_tag_value($rule); 
    print "GOT NEXT SIBLING:[$name]\n" if $name;
  }

  return $rule;
}

sub get_parent_match_rule {
  my ($rule) = @_;
  return &get_parent_rule($rule,"match");
}

sub get_parent_rule {
  my ($rule,$type) = @_;

  die "get_parent_rule passed empty rule!" unless defined $rule;

  my $parent = $rule->getParentNode();

  while($parent && $type) {
    my $parent_type = get_rule_type($parent);
    last if $parent_type && $parent_type eq $type;
    $parent = $parent->getParentNode();
  }
  
  return $parent;
}

sub get_first_child_rule {
  my ($rule) = @_;

  die "get_first_child_rule passed empty rule!" unless defined $rule;

  my $first_child_rule = $rule->getFirstChild();
  if (defined $first_child_rule) {
    while($first_child_rule && $first_child_rule->getNodeTypeName() ne "ELEMENT_NODE") {
      $first_child_rule = $first_child_rule->getNextSibling();
    }
  }
  $first_child_rule = "" if !defined $first_child_rule;

  return $first_child_rule;
}

sub apply_a_rule_to_the_chunk {
  my ($rule,$working_chunk) = @_;
 
  my $chunk = $working_chunk;

  # create a new rule event
  create_an_event($rule,$ABSOLUTE_CHUNK_START_POSITION,$working_chunk);

  # bump up the parse level 
  $parse_nest_level++; 

print "LOOP STEP level:[$parse_nest_level] [",get_rule_type($rule),"]\n" if $EXTREME_RULE_DEBUG;

  # Ok, given this rule and the working chunk, lets do some good :)
    
  my $ruletype = get_rule_type($rule);

print "LOOP STEP level:[$parse_nest_level] [",get_rule_type($rule),"]\n" if $EXTREME_RULE_DEBUG;

  if($ruletype eq "txt2XML") {      #  <txt2XML> rules
   
    $working_chunk = &do_txt2XML_rule($rule,$working_chunk);

  } elsif($ruletype eq "ignore") { #  <ignore> rules

    $working_chunk = &do_ignore_rule($rule,$working_chunk); 

  } elsif($ruletype eq "match") { #  <match> rules

    $working_chunk = &do_match_rule($rule,$working_chunk); 

  } elsif($ruletype eq "choose") { #  <choose> rules

    $working_chunk = &do_choose_rule($rule,$working_chunk);

  } elsif($ruletype  eq "repeat") { #  <repeat> rules

    $working_chunk = &do_repeat_rule($rule,$working_chunk);

  } elsif($ruletype  eq "print") { #  <print> 
    
    do_print_rule($rule,$working_chunk);

  } elsif($ruletype  eq "halt") { #  <halt> 

    &do_halt_rule();

  } else {

    die "UNKNOWN RULE CALLED:[$ruletype]\n";

  }

  # bump down the parse level 
  $parse_nest_level--; 

  return $working_chunk;
}

sub parse_with_child_rules {
  my ($working_chunk,$rule) = @_; 

  die "parse_with_nested_rules passed empty rule!" unless defined $rule;

  my $tagname = &get_rule_tag_value($rule);
  my $ruletype = get_rule_type($rule);

  # why do we return in this case??
  # return $working_chunk if (!$tagname && $ruletype eq "match");

  my $first_child_rule = &get_first_child_rule($rule);

  $tagname = defined $tagname ? $tagname : "";

  print "PARSE W/CHILDREN [",get_rule_type($rule)," $tagname] CHUNK:[$working_chunk]\n" 
      if $EXTREME_RULE_DEBUG;

  if (defined $working_chunk && $working_chunk ne "" && $first_child_rule) {

    print "SENDING CHILDREN CHUNK:[$working_chunk]\n" if $EXTREME_RULE_DEBUG;
    $working_chunk = &parse_this_chunk($working_chunk,$first_child_rule);

    # do we have any chunk left over ?? If so its an error 
    # UNLESS the current rule wants it as data. 
    if(get_rule_remainder_value($rule) eq "data") {

       # DO NOTHING ...

    } elsif ($working_chunk ne "" && !nested_within_a_repeat_rule() 
           && get_rule_required_value($rule) eq "yes"
    ) {
       # Well, we have some number of possiblities here. 
       # If the remainder chunk is just some whitespace, we dont
       # care too much about it=> eg its a trivial error. Otherwise
       #  this is a regular error.
       my $error_level = $working_chunk =~ m/\S/ ? $REGULAR_ERROR : $TRIVIAL_ERROR;
       &print_error( "$working_chunk", $error_level,'remainder',$working_chunk);
       $working_chunk = ""; # 'subtract' text from working chunk
    }
  }

  # Here we are adding events for parent rules as they finish
  # their children
  if (!$HALT_PARSE && $USE_EVENTS) {
    my $start = defined $CURRENT_EVENT ? 
                $CURRENT_EVENT->{'absolute_chunk_start_position'} : 0;
    &create_an_event($rule,$start,$working_chunk);
    $CURRENT_EVENT->{'end_rule'} = 1;
  }


  return $working_chunk;
}

sub do_txt2XML_rule {
  my($rule,$working_chunk) = @_;

    # just pass the chunk on to its children
    # $working_chunk = &parse_with_child_rules($working_chunk,$rule); 

    # open the root tag
    my $root_tag = &get_rule_root_tag_value($rule);
    if ($root_tag && $root_tag ne "") {
      OPEN_ELEMENT($root_tag); 
      PRINT_OUT($PREAMBLE_STRING) if $PREAMBLE_STRING;
    } else {
      print_error("ERROR: <txt2XML> rule has no root_tag attribute", 2, 'missing root_tag attribute'); 
      OPEN_ELEMENT("NO_ROOT_TAG_SPECIFIED"); 
    }

    # Now, we just treat it as a match rule
    $working_chunk = &do_match_rule($rule,$working_chunk);

    return $working_chunk;
}

# this rule will NOT tag or pass to children the text that
# it matches
sub do_ignore_rule {
  my($rule,$working_chunk) = @_;

  print "    IGNORE RULE[$parse_nest_level]:"
      if ($EXTREME_MATCH_DEBUG || $EXTREME_RULE_DEBUG);

  my($match_success,$last_match,$before,$start_match,$matching_string,$end_match,$after,$tagname) = 
                                &try_to_match_with_rule($rule,$working_chunk);

  $before = "" unless defined $before;
  $start_match = "" unless defined $start_match;
  $matching_string = "" unless defined $matching_string;
  $end_match = "" unless defined $end_match;
  $after = "" unless defined $after;

  # set position for the next chunk
  my $start_match_length = get_rule_statusOfStart_value($rule) eq "drop" ? length($start_match) : 0;
  my $end_match_length = get_rule_statusOfEnd_value($rule) eq "accept" ? length($end_match) : 0;
  my $offset_for_start = get_rule_statusOfEnd_value($rule) eq "donate" ? 0 : length($end_match);
  my $match_length = length($matching_string); # needs to be here, can get set to 0 in if/then below

  my $sibling_next_start = $ABSOLUTE_CHUNK_START_POSITION + length($before) +
                       $match_length + $start_match_length - $end_match_length +
                       $offset_for_start;
  

  # update the current event info
  $CURRENT_EVENT->{'before_chunk_len'} = length $before;
  $CURRENT_EVENT->{'start_match_chunk_len'} = $start_match_length;
  $CURRENT_EVENT->{'matching_chunk_len'} = $match_length;
  $CURRENT_EVENT->{'end_match_chunk_len'} = length $end_match;
  $CURRENT_EVENT->{'after_chunk_len'} = length $after;
  $CURRENT_EVENT->{'statusOfEnd'} = get_rule_statusOfEnd_value($rule);
  if ($DEBUG) {
    $CURRENT_EVENT->{'before_chunk'} = $before;
    $CURRENT_EVENT->{'start_match_chunk'} = $start_match;
    $CURRENT_EVENT->{'matching_chunk'} = $matching_string;
    $CURRENT_EVENT->{'end_match_chunk'} = $end_match;
    $CURRENT_EVENT->{'after_chunk'} = $after;
    $CURRENT_EVENT->{'last_match'} = $last_match;
  }

  # Ok, we got a match, what will we do??
  #if(defined $matching_string ) {
  if(defined $matching_string 
       && ($matching_string ne "" || &check_accept_null_match($match_success,$rule))
  ) {

    $after = &deal_with_match_within_choose($rule,$before,$after);

    # set the start of the chunk for child rules
    $ABSOLUTE_CHUNK_START_POSITION += length($before) + $start_match_length;

    # create the new working chunk sans what we matched and 'used' (eg ignored) 
    $working_chunk = $after;

  }

  $ABSOLUTE_CHUNK_START_POSITION = $sibling_next_start
     unless ($match_length == 0 && get_rule_required_value($rule) eq 'no');

  print "    IGNORE_RULE[$parse_nest_level] RETURNS CHUNK:[$working_chunk]\n"
         if ($EXTREME_RULE_DEBUG || $EXTREME_MATCH_DEBUG);

  return $working_chunk;
}

# this is a bit more complex than do_repeat_rule or do_choose_rule
# the call to the children rules lies within do_something_with_matching_string
# unfortuneately ...
sub do_match_rule {
  my($rule,$working_chunk) = @_;

  print "    MATCH RULE[$parse_nest_level]:" 
      if ($EXTREME_MATCH_DEBUG || $EXTREME_RULE_DEBUG);

  my($match_success,$last_match,$before,$start_match,$matching_string,$end_match,$after,$tagname) = 
                                &try_to_match_with_rule($rule,$working_chunk);

  $before = "" unless defined $before;
  $start_match = "" unless defined $start_match;
  $matching_string = "" unless defined $matching_string;
  $end_match = "" unless defined $end_match;
  $after = "" unless defined $after;
 
  # set position for the next chunk
  my $start_match_length = get_rule_statusOfStart_value($rule) eq "drop" ? length($start_match) : 0;
  my $offset_for_start = get_rule_statusOfEnd_value($rule) eq "donate" ? 0 : length($end_match);
  my $match_length = length($matching_string); # needs to be here, can get set to 0 in if/then below

  #my $end_match_length = get_rule_statusOfEnd_value($rule) eq "accept" ? 0 : length($end_match);
  my $end_match_length = get_rule_statusOfEnd_value($rule) eq "accept" ? length($end_match) : 0;

  my $sibling_next_start = $ABSOLUTE_CHUNK_START_POSITION + length($before) +
                       $match_length + $start_match_length - $end_match_length +
                       $offset_for_start;

  # add event info
  $CURRENT_EVENT->{'before_chunk_len'} = length $before;
  $CURRENT_EVENT->{'start_match_chunk_len'} = $start_match_length;
  $CURRENT_EVENT->{'matching_chunk_len'} = $match_length;
  $CURRENT_EVENT->{'end_match_chunk_len'} = length $end_match;
  $CURRENT_EVENT->{'after_chunk_len'} = length $after;
  $CURRENT_EVENT->{'statusOfEnd'} = get_rule_statusOfEnd_value($rule);
  if ($DEBUG) {
    $CURRENT_EVENT->{'before_chunk'} = $before;
    $CURRENT_EVENT->{'start_match_chunk'} = $start_match;
    $CURRENT_EVENT->{'matching_chunk'} = $matching_string;
    $CURRENT_EVENT->{'end_match_chunk'} = $end_match;
    $CURRENT_EVENT->{'after_chunk'} = $after;
    $CURRENT_EVENT->{'last_match'} = $last_match;
  }

  #if(defined $matching_string && $matching_string ne "") {
  if(defined $matching_string 
       && ($matching_string ne "" || &check_accept_null_match($match_success,$rule))
  ) {

    $after = &deal_with_match_within_choose($rule,$before,$after);

    # set the start of the chunk for child rules
    $ABSOLUTE_CHUNK_START_POSITION += length($before) + $start_match_length;

    $matching_string = &do_something_with_matching_string($matching_string,$rule,$tagname);

    # create the new working chunk sans what we matched and used 
    $working_chunk = $after;
    $working_chunk = $matching_string . $working_chunk if ($matching_string);
  }


  $ABSOLUTE_CHUNK_START_POSITION = $sibling_next_start
     unless ($match_length == 0 && get_rule_required_value($rule) eq 'no');

  print "    MATCH_RULE[$parse_nest_level] RETURNS CHUNK:[$working_chunk]\n"
         if ($EXTREME_RULE_DEBUG || $EXTREME_MATCH_DEBUG);

  return $working_chunk;
}

sub check_accept_null_match {
  my ($good_match,$rule) = @_;
  my $accept_null_match_for_this_rule = 0;

  #if ($good_match && $ACCEPT_NULL_MATCHES_AS_GOOD ) {
  if ($good_match && $RUNTIME_PARAM{'accept_null_matches'}) {
    # special case: null matches for non-required rules that are
    # children of repeat/choose rules DO NOT create empty tags.
    # This prevents spurious empty elements from being opened.


    if( &get_rule_required_value($rule) eq "no"
         && (&my_parent_is_a_repeat_rule($rule) || &my_parent_is_a_choose_rule($rule))
    ) {
      $accept_null_match_for_this_rule = 0;
    } else { 
      $accept_null_match_for_this_rule = 1;
    }
  }

  return $accept_null_match_for_this_rule;
}

sub do_choose_rule { 
  my ($rule,$working_chunk) = @_;

  $choose_rule_at_this_level[$parse_nest_level] = 1; 

  print "    CHOOSE_RULE[$parse_nest_level] GOT CHUNK:[$working_chunk]\n" if $EXTREME_RULE_DEBUG;

  # try pass the chunk on down to any nested rules, should they exist
  $working_chunk = &parse_with_child_rules($working_chunk,$rule);

  print "    CHOOSE_RULE[$parse_nest_level] RETURNS CHUNK:[$working_chunk]\n" if $EXTREME_RULE_DEBUG;

  return $working_chunk;
}

sub do_repeat_rule { 
  my ($rule,$working_chunk) = @_;

  $repeat_rule_at_this_level[$parse_nest_level] = 1; 

  print "    REPEAT_RULE[$parse_nest_level] GOT CHUNK:[$working_chunk]\n" if $EXTREME_RULE_DEBUG;

  # try pass the chunk on down to any nested rules, should they exist
  $working_chunk = &parse_with_child_rules($working_chunk,$rule);

  print "    REPEAT_RULE[$parse_nest_level] RETURNS CHUNK:[$working_chunk]\n" if $EXTREME_RULE_DEBUG;

  return $working_chunk;
}

# a rule used for debugging the format statement
# kinda deprecated now that we can use the gui in
# txt2XML
sub do_print_rule { 
  my ($rule,$working_chunk) = @_;
  
  my $next_rule = &get_next_sibling_rule($rule);
  my $type = &get_rule_type($next_rule);
  my $tagname = &get_rule_tag_value($next_rule);
  $tagname = defined $tagname ? " $tagname" : "";

  my $what = &get_rule_what_value($rule);
 
  my $msg = "";

  if($what eq "chunk") {
    $msg = "CHUNK:[$working_chunk]\n"; 
  } elsif ($what eq "rule") { 
    $msg = "RULE:[$type:$tagname][$parse_nest_level]\n";  
  } else {
    print_error("ERROR: print format statement with unknown value:[$what]\n",$REGULAR_ERROR,'format',"");
  }

  print STDOUT "****DEBUG****\nPRINT $msg****DEBUG****\n";  

}

# a rule used for debugging the format statement
sub do_halt_rule { 
  #  if ($HALT_COUNT++ >= $STOP_ON_HALT) { $HALT_PARSE = 1; }
    if ($RUNTIME_PARAM{'halt_count'}++ >= $STOP_ON_HALT) { $HALT_PARSE = 1; }
}

sub try_to_match_with_rule {
  my ($rule,$working_chunk) = @_;

  my $pattern  = get_match_rule_pattern($rule);
  my $tagname = get_rule_tag_value($rule);
  my $type = get_rule_type($rule);

  print "[$type:",defined $tagname ? $tagname : "" ,"]" 
           if ($EXTREME_MATCH_DEBUG || $EXTREME_RULE_DEBUG);

  # SOme Tests of Perl Regex
  # my $pattern = '(={1,7}\n)([\S\s]*?)(somewhere)';    # successfull
  # my $pattern = '([A-Z,0-9])([\s\S]*?)(somewhere)';    # works
  # my $pattern = '([A-Z])([\s\S]*?)(file)';    # works
  # my $pattern = '(T)([\s\S]*?)(somewhere)';    # works
  # my $pattern = '(^[A-Z,0-9])([\s\S]*?)(file)';      # FAILED

  print "    PATTERN:[$pattern]\n    CHUNK:[$working_chunk]\n" if $EXTREME_MATCH_DEBUG;

  # OK, lets parse with the rules we got..
  $_ = $working_chunk;
  my ($start_match,$matching_string,$end_match) = /$pattern/s;

  my $match_success = 0;

  # these two need to occur here, because another possible test
  # match will occur before we need to use them
  my $before = $`; 
  my $after = $';  

  # New additional requirement, now should a test pattern exist, we
  # will test the just  matched string (as an additional test) to see 
  # if it is what we really want. IF not, we will bail out at this point 
  my $test_pattern = get_rule_test_value($rule);

  my $last_match = $+;

  # the 3rd line allows 'empty matching' 
  # in the case of rules which matched either start_match or end_match
  # (eg $last_match will be defined) AND we have some working_chunk
  if (defined $matching_string && 
#       ($matching_string ne "" || (defined $last_match && $ACCEPT_NULL_MATCHES_AS_GOOD && 
       ($matching_string ne "" || (defined $last_match && $RUNTIME_PARAM{'accept_null_matches'} && 
                                   length($working_chunk) > 0)) 
       && (!$test_pattern || $matching_string =~ m/$test_pattern/)
  ) { 

    # Internal string manipulations based on donate, accept, 
    # drop (default) values for StatusOfEnd StatusOfStart
    $matching_string = $start_match . $matching_string 
      if (&get_rule_statusOfStart_value($rule) eq "accept");
    $matching_string .= $end_match
      if (&get_rule_statusOfEnd_value($rule) eq "accept");
    $after = $end_match . $after
      if (&get_rule_statusOfEnd_value($rule) eq "donate");

    print "***MATCHED \n\tbefore:[$before]\n\tmatch:[$matching_string]\n\tafter:[$after]\n"
           if $EXTREME_MATCH_DEBUG;

    $match_success = 1;

  } else { # no match, were we required to match this rule??

    # its important to zero out the matching string at this point too
    # (yes, we could have a matching string here because we failed a 
    # test above 
    $matching_string = "";

    my $start = get_rule_start_value($rule);
    my $end = get_rule_end_value($rule);
    my $test = get_rule_test_value($rule);
    if(!&my_parent_is_a_choose_rule($rule)) {
       if (get_rule_required_value($rule) eq "yes") {
         my $string = "rule \"<$type tag=\"$tagname\" start=\"$start\"";
         $string .= " test=\"$test\"" if $test;
         $string .= " end=\"$end\" >\" failed to match but is required.";
         print_error($string,$REGULAR_ERROR,'required rule',""); 
       }
       $before = "";
       $start_match = "";
       $end_match = "";
       $after = "";
    }
  } 

  return ($match_success,$last_match,$before,$start_match,$matching_string,$end_match,$after,$tagname);
}

# If this match isnt nested within a 'choose' statement we will
# write an error line for any "before" text that results. Otherwise,
# the $before string is concatenated with $after to become the new working
# chunk.
sub deal_with_match_within_choose {
  my ($rule,$before,$after) = @_;

    if(!&my_parent_is_a_choose_rule($rule)) 
    {

      # hmm. We ARE within a choose loop. It may be that remaining 
      # text belongs to the parent rule. We'll write an error IF 
      # this isnt the case

      my $parent_rule = get_parent_match_rule($rule);

      if($parent_rule && get_rule_remainder_value($parent_rule) ne "error") 
      {

#        PRINT_OUT('BEFORE CASE'); # send it out as data
        PRINT_OUT(encode_string($before)); # send it out as data
                                           # make sure its encoded!

      } 
      else 
      {

        my $type = get_rule_type($rule);
        my $tagname = get_rule_tag_value($rule);
        $tagname = defined $tagname ? $tagname : "";

       # if the string is just whitespace, its a trivial error
       my $error_level = $before =~ m/\S/ ? $REGULAR_ERROR : $TRIVIAL_ERROR;
        print_error("$before", $error_level,'leading string',$before) if($before);

        my $parent_rule = get_parent_rule($rule);

      }

    } 
    else 
    {

      $after = $before . $after if $before;

    }

  return $after;
}

# Now, what do we do with the matching string... an element to open..?
# returns whats left of the matching string. 
sub do_something_with_matching_string {
  my ($matching_string,$rule,$tagname) = @_;

print " Do SOMETHING w/ MATCHED before_mem:[",&get_memory_use(),"]\n" if $EXTREME_MEM_DEBUG;

  if (defined $matching_string) {
    my $first_child_rule = &get_first_child_rule($rule);

    # treat our cases now..
    
    if ($tagname && !$first_child_rule) {

      &OPEN_ELEMENT($tagname,$matching_string,1);
      $matching_string = ""; # is this needed?? 

    } else {

       &OPEN_ELEMENT($tagname,"",0) if $tagname;

       # For non-tag rules, we subset, and parse as a new "sub" working chunk
       if($first_child_rule) {

         print "[lev:$parse_nest_level][",get_rule_type($first_child_rule),"]\n"  
             if $EXTREME_RULE_DEBUG;

         $matching_string = &parse_with_child_rules($matching_string,$rule); 

         if (&get_rule_remainder_value($rule) eq "error") {
           # Any remaining text at this point is an error
           # UNLESS the parent rule explicitly stated that it wanted that text
           # as part of its data
           if (defined $matching_string && $matching_string ne "") {
         #if ($matching_string && get_rule_remainder_value($rule) eq "error") {
             $tagname = defined $tagname ? $tagname : "";
             my $error_level = $matching_string =~ m/\S/ ? $REGULAR_ERROR : $TRIVIAL_ERROR;
             &print_error("$tagname : $matching_string", $error_level , 'match remainder',"$matching_string");
             $matching_string=""; # errored out, delete string 
           }
         } else {
             # special case: and it makes me nervous. Can this be incorrect for some situations?
             # What we hope to do here is close out tags that were opened because of null match
             # was allowed and the tag has children and remainder set="data". However NO data was
             # ever really available to the children and now we just want to 
             # close this element because its still open
             &CLOSE_ELEMENT($tagname) if (!$matching_string && $tagname && 
                 %{$open_tags_at_this_level[$parse_nest_level]}->{$tagname} > 0);
         } 

       } else { 

         # "Tried to pass chunk to non-existing child rules.",
         &print_error("", $SERIOUS_ERROR,'missing rules',$matching_string) if $matching_string;
         $matching_string=""; # errored out, delete string 
       }

    }

  }

  print "MATCHED after_mem:[",&get_memory_use(),"]\n" if $EXTREME_MEM_DEBUG;

  return $matching_string;
}

# If we just need to know if the parent is repeat rule
sub my_parent_is_a_repeat_rule {
  my ($rule) = @_;

  my $parent = &get_parent_rule($rule);
  my $parent_type;
  $parent_type = get_rule_type($parent) if $parent;
  return 1 if defined $parent_type && $parent_type eq "repeat";
  return 0;
}

# we just need to know if the parent is choose rule
sub my_parent_is_a_choose_rule {
  my ($rule) = @_;
  
  my $parent = get_parent_rule($rule);
  my $parent_type;
  $parent_type = get_rule_type($parent) if $parent;
  return 1 if defined $parent_type && $parent_type eq "choose";
  return 0;
}

sub nested_within_a_repeat_rule {

  my $parse_level = $parse_nest_level;
  while ($parse_level-- > 1) {
    return 1 if $repeat_rule_at_this_level[$parse_level];
  }
  return 0;
}

sub nested_within_a_choose_rule {

  my $parse_level = $parse_nest_level;
  while ($parse_level-- > 1) {
    return 1 if $choose_rule_at_this_level[$parse_level];
  }
  return 0;
}

sub encode_string {
  my ($string) = @_;
  
#  return &XML::DOM::encodeText($string,$DEFAULT_ENTITIES_TO_ENCODE)
#    if $DEFAULT_ENTITIES_TO_ENCODE;
  return &XML::DOM::encodeText($string,$RUNTIME_PARAM{'default_entities_to_encode'})
    if $RUNTIME_PARAM{'default_entities_to_encode'};

  return $string;
}

sub OPEN_ELEMENT {
  my ($tagname,$matching_string,$close_now,$attrib_hash_ref) = @_;

  print "OPEN ELEMENT before_mem:[",&get_memory_use(),"] " if $EXTREME_MEM_DEBUG;

  die "ABORT! OPEN_ELEMENT called with no tag name!\n" unless $tagname;

  $matching_string = "" if !defined $matching_string;

  # replace any characters we see here with appropriate entities
  my $output_string = encode_string($matching_string);

  my $indentation = get_indentation($parse_nest_level-1);

  PRINT_OUT("$indentation<$tagname");
  foreach my $attrib (keys %{$attrib_hash_ref}) { 
    PRINT_OUT(" $attrib=\"" . %{$attrib_hash_ref}->{$attrib} . "\"");
  }

  if(defined $close_now && $close_now > 0) {

    PRINT_OUT(">$output_string</$tagname>\n");

  } else {

    %{$open_tags_at_this_level[$parse_nest_level]}->{$tagname}++;
    PRINT_OUT(">$output_string\n"); 

  }

}

sub get_indentation {
  my ($indent_level) = @_;

  my $indent = "";
  while ($indent_level-- > 0) { $indent .= $INDENT_PER_NESTED_LEVEL; }

  return $indent;
}

sub PRINT_OUT { 
   my ($buffer) = @_; 

   if($OUTPUT_FILEHANDLE) {
      print $OUTPUT_FILEHANDLE $buffer; 
   } else {
     $output_text .= "$buffer";
   }

}

sub CLOSE_ELEMENT {
  my ($tagname) = @_;

  die "ABORT! CLOSE_ELEMENT called with no tag name!\n" unless $tagname;
  die "ABORT! CLOSE_ELEMENT called with tag:[$tagname], but its not currently open!\n" 
     if %{$open_tags_at_this_level[$parse_nest_level]}->{$tagname} <= 0;

  %{$open_tags_at_this_level[$parse_nest_level]}->{$tagname}--;

  #my $indentation = get_indentation();
  my $indentation = get_indentation($parse_nest_level-1);

  PRINT_OUT("$indentation</$tagname>\n");
}

sub get_match_rule_pattern {
   my ($rule) = @_;

   my $rule_start = get_rule_start_value($rule);
   my $rule_end = get_rule_end_value($rule);

 # note those '' are important! dont use " to suround strings
   return '(' . $rule_start . ')([' . $ANY_CHAR_MATCH . ']*?)(' . $rule_end . ')';
}

sub print_error { 
  my ($msg,$error_level,$error_type,$removed_text) = @_; 
  
#  my $error_string = $ERROR_TAG;
  my $error_string = $RUNTIME_PARAM{'error_tag'};
  # $error_string .= $error_level if defined $error_level;

  # lets not print more than one line of chunk that
  if ($TRUNCATE_ERROR_CHUNK_MSG) {
    $_ = $msg; $msg = m/^.*\n/;
  }

  #print STDERR $msg if($PRINT_ERRORS_TO_STDERR);
  print STDERR $msg if($RUNTIME_PARAM{'print_errors_to_stderr'});

  # write errors into output XML file
  my %attrib = ( 'level' => $error_level,
                 'type' => $error_type
               );
  print "ERROR " if $EXTREME_MEM_DEBUG;
  # OPEN_ELEMENT($error_string,$msg,1,\%attrib) if $INCLUDE_ERRORS_IN_OUTPUT;
  OPEN_ELEMENT($error_string,$msg,1,\%attrib) if $RUNTIME_PARAM{'include_errors_in_output'};

  # add to removed_text and error buffers 
  $removed_text_buffer .= $removed_text if $removed_text;
#  $error_buffer .= "ERROR:[number:$error_number][level:$error_level] " . $msg . "\n";
  
  # bump up the number of errors
  $error_number++;

  # record this error w/ last rule array
  # DONT use this, not used by txt2XML, AND it really blows
  # up the amount of memory we need to use
  # 
  # Rev 2: lets try this with $msg, instead of $removed_text
  #         for the 'error_chunk'
  if ($USE_EVENTS) {
  #if (0) {
    # $CURRENT_EVENT->{'error'} = "$error_buffer";
    $CURRENT_EVENT->{'error'} = 1;
    $CURRENT_EVENT->{'error_level'} = "$error_level";
    $CURRENT_EVENT->{'error_type'} = "$error_type";
    $CURRENT_EVENT->{'error_msg'} = $msg;
  }

#  $HALT_PARSE = 1 if $error_level >= $HALT_ON_ERROR_LEVEL; 
  $HALT_PARSE = 1 if $error_level >= $RUNTIME_PARAM{'halt_on_error_level'};

  # print "HALT ON ERROR:$HALT_ON_ERROR_LEVEL (stop parse:$HALT_PARSE)\n";
  # exit $error_level if $error_level >= $HALT_ON_ERROR_LEVEL; 

}

# Yes, there are some things we dont want to allow in formatting
# of the rules. 
sub  sanity_check_on_rules {
  my ($first_rule) = @_;
 
  my $rule = $first_rule;
  
  while ($rule) {
    return 0 unless &check_this_rule($rule);
    $rule = get_next_rule($rule);
  }

  return 1; # it went ok 
}

sub check_this_rule {
  my ($rule) = @_;

  my $type = get_rule_type($rule);

  my $attributes = $rule->getAttributes(); 
  
  if ($attributes) {
    my $remainder = get_rule_remainder_value($rule);
    if($remainder && (($type eq "choose") || ($type eq "repeat"))) {
      print STDERR "ERROR in format statement. Rule: ",$type," has a remainder attribute but should\'nt!\n"; 
      exit 1;
    }
    # $attributes->dispose; # garbage collection
  }

  return 1;
}

# ordered traversal of the rules tree
sub get_next_rule {
  my ($rule) = @_;

  die "get_next_rule() passed empty rule!" unless $rule;

  my $first_child = get_first_child_rule($rule);
  return $first_child if $first_child;

  my $sibling = get_next_sibling_rule($rule);
  return $sibling if $sibling;

  my $parent= get_parent_rule($rule);
  if($parent) {
    my $next_parent_sibling = get_next_sibling_rule($parent); 
    return $next_parent_sibling;
  }

  return;
}

sub useage {
  my ($msg) = @_;
  print $msg if $msg;
  print "Useage: $0 [-hv] -f <format_file.xml> <text_file_to_parse>\n";
  exit 0;
}

sub create_an_event {
  my ($rule,$start_pos,$working_chunk) = @_;

  return undef unless $USE_EVENTS;

  my $end_pos = length($working_chunk) + $start_pos;

#print "create event before_mem:[",&get_memory_use(),"] "; # if $EXTREME_RULE_DEBUG;

  push (@events, {});                    # init/create this event
  $CURRENT_EVENT = $events[$#events];

  $CURRENT_EVENT->{'rule'} = $rule;
  $CURRENT_EVENT->{'working_chunk'} = $working_chunk if $DEBUG;
  $CURRENT_EVENT->{'absolute_chunk_start_position'} = $start_pos;
  $CURRENT_EVENT->{'absolute_chunk_end_position'} = $end_pos;

}

1;

__END__; 


