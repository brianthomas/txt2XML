#!/usr/bin/perl -I /usr/local/bin


# /** COPYRIGHT
#    txt2XML.pl Copyright (C) 2000 Brian Thomas,
#    ADC/GSFC-NASA, Code 631, Greenbelt MD, 20771
#@ 
#    This program is free software; it is licensed under the same terms
#    as Perl itself is. Please refer to the file LICENSE which is contained
#    in the distribution that this file came in.
#@ 
#   This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
# */

# ===========================================================================
# Filename    : txt2XML.pl
# Subsystem   : ADC XML Scripts - legacy text parsing 
# Programmer  : Brian Thomas
# Description : GUI based client for interactive debugging of text parsing
#               to an XML document. 
#
# Modules     : Tk.pm, Tk::SplitFrame, WindowTools.pm 
#               Text2XML
#
# RCS: $Id: txt2XML.pl,v 1.34 2000/04/27 14:42:22 thomas Exp thomas $
# ===========================================================================

# Version History 
#  8/6/99 v1.04   First version to merge the commandline and GUI versions of the
#                 program. 
#  8/18/99 v1.10  Implimented ignore command. Fixed some memory wasting code.
#  8/20/99 v1.11  Bugfix version, halt rule was deleteing all rules following it 
#  8/23/99 v1.2   Null matching version.
#  9/1/99  v1.22  Bug fix version for 1.2
# 10/25/99 v1.23  Added test for SplitFrames module. Now split windows will be
#                 used by default on systems that lack the module. 
#  2/28/00 v1.24  Added forward/backward 10 steps ability
#                 Added in click-on-error to take you to event(rule) that caused
#                 that error.
#  2/28/00 v1.26  Skipped versioning to match RCS version, fixed bug in click on
#                 error code   
#  2/29/00 v1.27  Minor interface changes. Uses rules file defined runtime params
#                 as base defaults for several but not all params. These may be
#                 overridden by commandline args still.
#  3/01/00 v1.28  Y2K bug fix in Text2XML.pm, require this library version here.
#  3/06/00 v1.29  Minor change to pass number of errors on score printout
#  3/08/00 v1.30  Allow menu option to edit the output text
#  3/10/00 v1.40  Highlight miss-match errors in the rules  
#  3/15/00 v1.50  Validation of output text (in gui mode) possible
#  3/22/00 v1.60  Made this version work with new libenno. Only changes near line
#                 1840 needed, $node->{Data} becomes $node->getData();
#  4/27/00 v1.61  Bug fix. When match w/ children had statusOfStart==Accept the
#                 highlighting of the string was incorrect.  

  # Finally, something to think about for the memory leak problem:
  # 
  # XML::DOM needs to call $dom->dispose
  # to remove memory leaks
  # eg:
  #> > -- DOM's the Leaker> >
  #> > It seems that the memory leaker here is XML::DOM, and the
  #> > complex way in which it creates circular references.  These
  #> > objects are best killed by:
  #> >
  #> >   $dom->dispose()


# load the modules we'll need
use Tk;
use WindowTools 1.00;        # homegrown windows tools, popupwindows, etc.
use Text2XML 1.35;           # our parser package 

# test for the splitframes module
my $LAYOUT = 'normal';    # may be 'normal' or 'separate' 
unless (eval "require Tk::SplitFrame" ) {
  print "Could'nt load Tk::SplitFrame module, defaulting to split windows display.\n";
  $LAYOUT = 'separate';
}

# pragmas
use strict;

my $toolname = "TXT2XML Tool"; 
my $versdate = "3-22-00";
my $VERSION = 1.61; 

# Signal handling
$SIG{'HUP'} = "my_exit";
$SIG{'INT'} = "my_exit";
$SIG{'QUIT'} = "my_exit";

my $MASTER_TAG_INDEX = 0; # hacky!!! please remove 

# These SHOULD be defined in the XML::DOM module, but 
# arent (eg $XML::DOM::TEXT_NODE) :P
my %dom_node_type = (
                       'UNKNOWN_NODE' => 0,
                       'ELEMENT_NODE' => 1,
                       'ATTRIBUTE_NODE' => 2,
                       'TEXT_NODE' => 3,
                       'CDATA_SECTION_NODE' => 4,
                       'ENTITY_REFERENCE_NODE' => 5,
                       'ENTITY_NODE' => 6,
                       'PROCESSING_INSTRUCTION_NODE' => 7,
                       'COMMENT_NODE' => 8,
                       'DOCUMENT_NODE' => 9,
                       'DOCUMENT_TYPE_NODE' => 10,
                       'DOCUMENT_FRAGMENT_NODE' => 11,
                       'NOTATION_NODE' => 12
                    );

# our (many) global variables, ugh!

# program defs
my $version = "v" . $VERSION . " beta"; 

my $rules_file;        # The XML rules file. This directs how we will parse
my $input_file;         # Text file (in whatever format) we will parse
my $output_file = "Output.xml";        # The XML output file. 

# Runtime parameters
my $USE_GUI = 0; 
my $PRINT_SCORE = 0;
my $DEFAULT_ENTITIES_TO_ENCODE = '"&<>' . "'";
my $ENTITIES_TO_ENCODE = $DEFAULT_ENTITIES_TO_ENCODE;
my $TEXT_WIDGET_WRAP_MODE = 'none';
my $INPUT_TEXT_BREAK = 'end';
my $rules_text_index = '0.1';  # marks the last place we clicked 

my $halt_rule_counter = 0;  
#my $RUNTIME_PARAM{'halt_on_error_level'} = 99;
#my $RUNTIME_PARAM{'accept_null_matches'} = 0;
#my $RUNTIME_PARAM{'include_errors_in_output'} = 1; # yes, include
my $INPUT_CHUNK_VIEW = 'working_chunk';
my $ERROR_TAG_NAME = 'ERROR';
my $DOM_CHECK_WIDGET_ref; # this should default to the rules widget
                      # although we sometimes want to make it output widget 

my $MEM_DEBUG = 0; # debug memory usage
my $DEBUG = 0;

# Global arrays/hash tables, yech
my @PARSE_EVENT = ();
my $PARSE_EVENT_INDEX = -1;
my %HIGHLIGHTED_TAGLIST;
my %RULE_TEXT_TAG_TO_RULE;
my %WIDGET;  # a lookup hash table of ref's to various widgets

# various 'defined' display sizes for our tool
my $TINY_SIZE   = '800x600'; 
my $SMALL_SIZE  = '1024x768'; 
my $NORMAL_SIZE = '1200x1024'; 
my $LARGE_SIZE  = '1600x1200'; 

my $DISPLAY_SIZE = $NORMAL_SIZE; # default size

# window size params
my %frame_dim = (
             'SplitFrameH' =>
                   {
                      'width' => { $TINY_SIZE => 500, $SMALL_SIZE => 850,
                                     $NORMAL_SIZE => 1250, $LARGE_SIZE => 1575
                                   },
                      'height' => { $TINY_SIZE => 450, $SMALL_SIZE => 600,
                                      $NORMAL_SIZE => 850, $LARGE_SIZE => 1017
                                    },
                      'sliderposition' => { $TINY_SIZE => 70, $SMALL_SIZE => 90,
                                        $NORMAL_SIZE => 100, $LARGE_SIZE => 100
                                     }
                    },
             'SplitFrameV1' =>
                   {
                     'width' => { $TINY_SIZE => 500, $SMALL_SIZE => 850,
                                     $NORMAL_SIZE => 1250, $LARGE_SIZE => 1575
                                   }, 
                     'height' => { $TINY_SIZE => 450, $SMALL_SIZE => 600,
                                      $NORMAL_SIZE => 750, $LARGE_SIZE => 917
                                    },
                     'sliderposition' => { $TINY_SIZE => 150, $SMALL_SIZE => 200,
                                        $NORMAL_SIZE => 200, $LARGE_SIZE => 280
                                      }
                   },
             'SplitFrameV2' =>
                   {
                     'width' => { $TINY_SIZE => 500, $SMALL_SIZE => 850,
                                     $NORMAL_SIZE => 850, $LARGE_SIZE => 1095
                                   },
                     'height' => { $TINY_SIZE => 450, $SMALL_SIZE => 500,
                                      $NORMAL_SIZE => 750, $LARGE_SIZE => 917
                                    },
                     'sliderposition' => { $TINY_SIZE => 150, $SMALL_SIZE => 200,
                                        $NORMAL_SIZE => 300, $LARGE_SIZE => 300
                                    }
                   }
                 );                  

my %widget_dim = (
             'error_text' => 
                    { 
                      'height' => { $TINY_SIZE => 5, $SMALL_SIZE => 5,
                                 $NORMAL_SIZE => 10, $LARGE_SIZE => 10
                               },
                      'width'  => { $TINY_SIZE => 45, $SMALL_SIZE => 40,
                                 $NORMAL_SIZE => 80, $LARGE_SIZE => 80
                               }
                    },
             'input_text' => 
                   { 
                     'height' => { $TINY_SIZE => 5, $SMALL_SIZE => 5,
                                 $NORMAL_SIZE => 45, $LARGE_SIZE => 55
                               },
                     'width'  => { $TINY_SIZE => 45, $SMALL_SIZE => 80,
                                 $NORMAL_SIZE => 80, $LARGE_SIZE => 90
                               }
                   },
             'rules_text' => 
                   {
                     'height' => { $TINY_SIZE => 5, $SMALL_SIZE => 5,
                                 $NORMAL_SIZE => 45, $LARGE_SIZE => 55
                               },
                     'width'  => { $TINY_SIZE => 45, $SMALL_SIZE => 80,
                                 $NORMAL_SIZE => 80, $LARGE_SIZE => 90
                               }
                   },
             'output_text' => 
                   {
                     'height' => { $TINY_SIZE => 5, $SMALL_SIZE => 5,
                                 $NORMAL_SIZE => 45, $LARGE_SIZE => 55
                               },
                     'width'  => { $TINY_SIZE => 45, $SMALL_SIZE => 80,
                                 $NORMAL_SIZE => 80, $LARGE_SIZE => 90
                               }
                   }
                 );                  

# Font Defs
my %font = (
             $TINY_SIZE   => '-adobe-fixed-medium-r-normal--10-*-*-*-*-*-*-*',
             $SMALL_SIZE  => '-adobe-fixed-medium-r-normal--12-*-*-*-*-*-*-*',
             $NORMAL_SIZE => '-adobe-fixed-medium-r-normal--14-*-*-*-*-*-*-*',
             $LARGE_SIZE  => '-adobe-fixed-medium-r-normal--18-*-*-*-*-*-*-*'
           );
my %boldfont = (
             $TINY_SIZE   => '-adobe-helvetica-bold-r-normal--14-*-*-*-*-*-*-*',
             $SMALL_SIZE  => '-adobe-helvetica-bold-r-normal--14-*-*-*-*-*-*-*',
             $NORMAL_SIZE => '-adobe-helvetica-bold-r-normal--16-*-*-*-*-*-*-*',
             $LARGE_SIZE  => '-adobe-helvetica-bold-r-normal--18-*-*-*-*-*-*-*'
           );

#color defs
my %Color = ( 'yellow' => '#ff9',
              'mild_yellow' => "#ee8",
              'pink' => "#ebb",
              'seagreen' => 'SeaGreen3',
              'green' => "#6c3",
              'litegreen' => "#9e6",
              'peagreen' => "#8c8",
              'liteblue' => "#4bc",
              'blue' => "#178",
              'brightblue' => "#69f",
              'red' => "#c12",
              'bright_red' => "#f12",
              'grey' => "#bbb",
              'darkgrey' => "#555",
              'offwhite' => "#eee",
              'white' => "#fff",
              'liteorange' => 'orange',
              'orange' => "darkorange",
              'black' => "#111"
            );

# widget color settings
my $baseColor = $Color{'grey'};
my $EnabledWriteColor = $Color{'mild_yellow'}; 
my $labelColor = $Color{'white'};
my $ErrorTextFgColor = $Color{'red'};
my $TextBgColor = $Color{'white'};
my $TextFgColor = $Color{'black'};
my ($msgFgColor, $msgBgColor) = ("white", "black");
my ($buttonFgColor, $buttonBgColor) = ($Color{'black'}, $Color{'green'});
my ($buttonFgColor2, $buttonBgColor2) = ($Color{'black'}, $Color{'orange'});
my ($toggle_buttonFgColor_view_on, $toggle_buttonBgColor_view_on) = ($Color{'black'}, $Color{'pink'});
my ($toggle_buttonFgColor_view_off, $toggle_buttonBgColor_view_off) = ($Color{'black'}, $Color{'yellow'});
my ($start_match_chunk_bg_color, $match_chunk_bg_color, $end_match_chunk_bg_color) = 
       ($Color{'litegreen'}, $Color{'pink'}, $Color{'seagreen'});
my $ignore_chunk_bg_color = $Color{'liteblue'};
my $working_chunk_bg_color = $Color{'yellow'};
my ($load_buttonFgColor, $load_buttonBgColor) = ($Color{'black'}, $Color{'peagreen'}); 
my ($save_buttonFgColor, $save_buttonBgColor) = ($Color{'white'}, 'SeaGreen'); 
my ($save_as_buttonFgColor, $save_as_buttonBgColor) = ($Color{'white'}, 'SeaGreen'); 

# text highlighting
my $input_text_fg_highlight = $Color{'black'};
my $rules_text_fg_error_highlight = $Color{'white'};
my $rules_text_bg_error_highlight = $Color{'bright_red'};

# my $input_text_bg_highlight = $Color{'yellow'};

my $output_text_fg_highlight = $Color{'liteorange'};
my $output_text_bg_highlight = $Color{'liteorange'};

my $rule_text_current_tag_bg_highlight = $Color{'yellow'};
my $rule_text_current_tag_fg_highlight = $Color{'black'};

my $rule_text_show_tag_bg_highlight = $Color{'orange'};
my $rule_text_show_tag_fg_highlight = $Color{'black'};

# HIGHLIGHTING INFO
#
# This (arcane) format will work with simple buffer feed to widget 
# AND for update_text_widget_with_DOM as well. BUT you need
# to be carefull of how you name these elements. end_???_element
# stuff is only used by the buffer to text widget; whereas you
# need to have exact names of the tags you wish to color if 
# you import information from a DOM. 
# 
# meaning of relevance : the higher the number the greater the
# priority for using that coloring scheme. Works to resolve conflicts
# between highlight info entries that would both match a given string. 
#
# Unfortuneately, late in the game I added in code for the new_update_error
# widget that doesnt use the following scheme. :P
 
my %rules_text_highlight_info = ( 
             'txt2XML'          => {
                                    'start_string' => '<txt2XML',
                                    'end_string'   => '>',          
                                    'relevance'    => '2',          
                                    'fgcolor'      => $Color{'liteblue'}
                                  },
            'end_xml_element' => {
                                    'start_string' => '</txt2XML',
                                    'end_string'   => '>',
                                    'relevance'    => '2',
                                    'fgcolor'      => $Color{'liteblue'}
                                  },
             'match' => {
                                    'start_string' => '<match',
                                    'end_string'   => '>',
                                    'relevance'    => '1',
                                    'fgcolor'      => $Color{'red'}
                                  }, 
             'end_match_element' => {
                                    'start_string' => '</match',
                                    'end_string'   => '>',
                                    'relevance'    => '1',
                                    'fgcolor'      => $Color{'red'}
                                  }, 
             'ignore' => {          
                                    'start_string' => '<ignore',
                                    'end_string'   => '>',
                                    'relevance'    => '1',
                                    'fgcolor'      => $Color{'brightblue'}
                                  }, 
             'choose' => {
                                    'start_string' => '<choose',
                                    'end_string'   => '>',
                                    'relevance'    => '1',
                                    'fgcolor'      => $Color{'orange'}
                                  }, 
             'end_choose_element' => {
                                    'start_string' => '</choose',
                                    'end_string'   => '>',
                                    'relevance'    => '1',
                                    'fgcolor'      => $Color{'orange'}
                                  }, 
             'repeat' => {
                                    'start_string' => '<repeat',
                                    'end_string'   => '>',
                                    'relevance'    => '1',
                                    'fgcolor'      => 'purple'
                                  }, 
             'end_repeat_element' => {
                                    'start_string' => '</repeat',
                                    'end_string'   => '>',
                                    'relevance'    => '1',
                                    'fgcolor'      => 'purple'
                                  }, 
             'halt' => {
                                    'start_string' => '<halt',
                                    'end_string'   => '>',
                                    'relevance'    => '1',
                                    'fgcolor'      => $Color{'liteblue'} 
                                  }
                                );

my %output_text_highlight_info = ( 
             'xml_element'     => {
                                    'start_string' => '<?xml',
                                    'end_string'   => '>',
                                    'relevance'    => '1',          
                                    'fgcolor'      => $Color{'liteblue'}
                                  }, 
             'start_error_elements' => {
                                    'start_string' => "<$ERROR_TAG_NAME",
                                    'end_string'   => '>',
                                    'relevance'    => '1',          # more relevant to highlight using this
                                                                    # format than 'elements'. 
                                    'fgcolor'      => $Color{'red'}
                                  }, 
             'end_error_elements' => {
                                    'start_string' => '</ERR',
                                    'end_string'   => '>',
                                    'relevance'    => '1',            # just as relevant to highlight as prior 
                                    'fgcolor'      => $Color{'red'}
                                  }, 
             'comment'         => {
                                    'start_string' => '<!--',
                                    'end_string'   => '-->',
                                    'relevance'    => '1',          # more relevant to highlight using this
                                                                    # format than 'elements'.
                                    'fgcolor'      => 0             # means dont change fg color from default
                                  },
             'elements'       =>  { 
                                    'start_string' => '<',
                                    'end_string'   => '>',
                                    'relevance'    => '0',            # not as relevant to highlight 
                                    'fgcolor'      => $Color{'green'}
                                  }
                               );


# B E G I N  P R O G R A M

# Initialize

  # makes stderr stuff go to GUI popup

  # Help message buffers
  my @aboutmsg = &init_aboutmsg(); 
  my @cmdmsg = &init_cmdmsg(); 
  my @bugmsg = &init_bugmsg(); 

  my %RUNTIME_PARAM = &Text2XML::get_runtime_params();
  &argv_loop();

  print "Before parse memory : ", &get_memory_use(), "\n" if $MEM_DEBUG;
 
  if (!$USE_GUI) {
    &no_gui_parse_text($input_file,$rules_file);
    print "After parse memory : ", &get_memory_use(), "\n" if $MEM_DEBUG;
    exit 0;
  }

  &init_tool($DISPLAY_SIZE);
  # this should default to the rules widget
  $DOM_CHECK_WIDGET_ref = \$WIDGET{'rules_text'}; 

  #&WindowTools::popup_msg_window($WIDGET{'main'},("hi dude"));

  &run_parser() if $input_file && $rules_file;
  &change_display_size($DISPLAY_SIZE);

# Run Event handler
  MainLoop;
 
# S U B R O U T I N E S 

sub init_tool {
  my ($display_size) = @_;

print "INIT TOOL\n" if $DEBUG;

print " INIT WINDOWS" if $DEBUG;
  %WIDGET = &init_gui($display_size);
print "...finished\n" if $DEBUG;

print " INIT WINDOW TOOLS" if $DEBUG;
  &WindowTools::set_font($font{$display_size});
print "...finished\n" if $DEBUG;

print " INIT Key Bindings" if $DEBUG;
  &init_key_bindings();
print "...finished\n" if $DEBUG;

print " INIT WIDGET Bindings" if $DEBUG;
  &init_widget_bindings();
print "...finished\n" if $DEBUG;

# load in rules/input text
  &update_rules_text(&Text2XML::get_document_text_chunk($rules_file)) if($rules_file);
  &update_input_text(&Text2XML::get_document_text_chunk($input_file)) if($input_file);

}

# these lines set up the key bindings 
sub init_key_bindings {

  # bindings for all main (window) widgets
  foreach my $type (('main','ErrorWindow','InputWindow','RulesWindow','OutputWindow')) {
    my $widget = $WIDGET{$type};

    next unless $widget;

    $widget->bind( '<Alt-KeyPress-1>' => sub { &dump_widget_tag_number($WIDGET{'input_text'}); } );

    $widget->bind( '<Alt-KeyPress-2>' => sub { &dump_widget_tag_number($WIDGET{'rules_text'} ); } );

    $widget->bind( '<Alt-KeyPress-3>' => sub { &dump_widget_tag_number($WIDGET{'output_text'} ); } );

    $widget->bind( '<Alt-KeyPress-B>' => sub { &change_current_event(-10); });
    $widget->bind( '<Alt-KeyPress-F>' => sub { &change_current_event(10); });

    $widget->bind( '<Alt-KeyPress-b>' => sub {&change_current_event(-1);} );
    $widget->bind( '<Alt-KeyPress-f>' => sub { &change_current_event(1);} );
    $widget->bind( '<Alt-KeyPress-n>' => \&next_halt);
    $widget->bind( '<Alt-KeyPress-p>' => \&run_parser );
    $widget->bind( '<Alt-KeyPress-q>' => \&my_exit );
    $widget->bind( '<Alt-KeyPress-c>' => sub { 
                &clear_marked_point($WIDGET{'input_text'},'InputTextBreak');});
    $widget->bind( '<Alt-KeyPress-v>' => \&toggle_input_chunk_view);
  }

   $WIDGET{'main'}->bind( '<Alt-KeyPress-o>' => \&open_options_menu );
   $WIDGET{'main'}->bind( '<Alt-KeyPress-l>' => \&toggle_layout );
}

sub init_widget_bindings {

   $WIDGET{'input_text'}->bind( '<Control-ButtonPress-1>' => sub {
                                  &mark_point($WIDGET{'input_text'},'InputTextBreak');
                                                                 } 
                              );

   $WIDGET{'input_text'}->bind( '<Control-ButtonPress-2>' => sub {
                                   &clear_marked_point($WIDGET{'input_text'},'InputTextBreak'); 
                                                                 } 
                              );

   $WIDGET{'rules_text'}->bind( '<1>' => sub {
                                               $rules_text_index = 
                                               &get_cursor_text_index($WIDGET{'rules_text'});
                                             } 
                              );

   $WIDGET{'rules_text'}->bind( '<2>' => sub {
                                               $rules_text_index = 
                                                &get_cursor_text_index($WIDGET{'rules_text'});
                                             } 
                              );

}

sub init_gui {
  my ($display_size) = @_;

  # Lets initialize the important widgets we need to manipulate into a hash table
  # Text widget entries NEED to have _text as part of their names
  my %widget;

  print "INIT MAIN WINDOW\n" if $DEBUG;

  $widget{'main'} = new MainWindow();
  $widget{'main'}->configure ( title => "ADC $toolname $version ($display_size)", bg => $baseColor );

  print "INIT MAIN FRAMES\n" if $DEBUG;

  #frames
  my $menu_bar = $widget{'main'}->Frame->pack(side => 'top', fill => 'x');
  my $topFrame = $widget{'main'}->Frame->pack(fill => 'both');
  my $CmdButtonFrame = $topFrame->Frame->pack(side => 'left');
  my $ScoreFrame = $topFrame->Frame->pack(side => 'right', fill => 'both');

  my $bottomFrame;

  if ($LAYOUT ne 'separate') {
    print "INIT BOTTOM FRAME for MONO LAYOUT\n" if $DEBUG;
    $bottomFrame = $widget{'main'}->Frame()->pack(side => 'bottom', fill => 'both', expand => 1);
    $bottomFrame ->configure( relief => 'raised', bd => 1, bg => $baseColor);
  }
  
  print "INIT CONFIGURE FRAMES\n" if $DEBUG;
  $menu_bar->configure( relief => 'raised', bd => 2, bg => $baseColor );
  $topFrame ->configure ( relief => 'flat', bd => 2, bg => $baseColor );
  $ScoreFrame ->configure ( relief => 'flat', bd => 0, bg => $baseColor );
  $CmdButtonFrame ->configure ( relief => 'flat', bd => 0, bg => $baseColor );

  print "INIT MENU\n" if $DEBUG;
  # menu bar
  my $menuOpt; my $menuParse; my $menuHelp; my $menuEdit;
  $menuOpt = $menu_bar->Menubutton(text => "Options", bg => $baseColor,
                                     -font => $font{$display_size},
                                     -menu => $menuOpt 
                                  )->pack(side => 'left');

  $menuEdit = $menu_bar->Menubutton(text => "Edit", bg => $baseColor,
                                     -font => $font{$display_size},
                                     -menu => $menuEdit
                                  )->pack(side => 'left');

  $menuParse = $menu_bar->Menubutton(text => "Parsing Control", bg => $baseColor,
                                     -font => $font{$display_size},
                                     -menu => $menuParse
                                  )->pack(side => 'left');


  $menuHelp = $menu_bar->Menubutton(text => "Help", bg => $baseColor,
                                     -font => $font{$display_size}, 
                                     -menu => $menuHelp
                                   )->pack(side => 'right');
 
  $widget{'menuOptions'} = $menuOpt;
  $widget{'menuEdit'} = $menuEdit;
  $widget{'menuParse'} = $menuParse;
  $widget{'menuHelp'} = $menuHelp;

  print "INIT OPT MENU\n" if $DEBUG;
  print "INIT OPT MENU--DISPLAY SIZE\n" if $DEBUG;
  $widget{'menuOptions'}->separator; 
  my $menu_cb = 'Change Tool Display Size';
  $widget{'menu_options_size_cascade'} = 
           $widget{'menuOptions'}->cascade(-label => $menu_cb, -font => $font{$display_size});
    my $cm = $widget{'menuOptions'}->cget(-menu);
    my $cc = $cm->Menu;
    #my $cc = $widget{'menuOptions'}->Menu;
    $widget{'menuOptions'}->entryconfigure($menu_cb, -menu => $cc);
    $widget{'menu_opt_size_cas_tiny'} = $cc->command(-label => '   Tiny (800x600)  ', 
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_display_size($TINY_SIZE); });
    $widget{'menu_opt_size_cas_small'} = $cc->command(-label => '  Small (1024x768) ', 
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_display_size($SMALL_SIZE); });
    $widget{'menu_opt_size_cas_normal'} = $cc->command(-label =>'Normal (1280x1024) ', 
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_display_size($NORMAL_SIZE); });
    $widget{'menu_opt_size_cas_large'} = $cc->command(-label => ' Large (1600x1200) ', 
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_display_size($LARGE_SIZE); });
    $cc->invoke(1);

  print "INIT OPT MENU--FONT SIZE\n" if $DEBUG;
  my $menu_cb5 = 'Change Text Font Size';
  $widget{'menu_options_fsize_cascade'} =
           $widget{'menuOptions'}->cascade(-label => $menu_cb5, -font => $font{$display_size});
    my $cm5 = $widget{'menuOptions'}->cget(-menu);
    my $cc5 = $cm5->Menu;
    #my $cc5 = $widget{'menuOptions'}->Menu;
    $widget{'menuOptions'}->entryconfigure($menu_cb5, -menu => $cc5);
    $widget{'menu_opt_fsize_cas_tiny'} = $cc5->command(-label => '  10 pt  ',
                                                     -font => $font{$display_size},
                                                     -command => sub { &change_text_font_size($TINY_SIZE); });
    $widget{'menu_opt_fsize_cas_small'} = $cc5->command(-label => '  12 pt  ',
                                                     -font => $font{$display_size},
                                                     -command => sub { &change_text_font_size($SMALL_SIZE); });
    $widget{'menu_opt_fsize_cas_normal'} = $cc5->command(-label => '  14 pt  ',
                                                     -font => $font{$display_size},
                                                     -command => sub { &change_text_font_size($NORMAL_SIZE); });
    $widget{'menu_opt_fsize_cas_large'} = $cc5->command(-label => '  18 pt  ',
                                                     -font => $font{$display_size},
                                                     -command => sub { &change_text_font_size($LARGE_SIZE); });
    $cc5->invoke(1);

  print "INIT OPT MENU--TEXT COLOR\n" if $DEBUG;
  my $menu_cb2 = 'Change Text Fg/Bg Color';
  $widget{'menu_options_color_cascade'} = 
           $widget{'menuOptions'}->cascade(-label => $menu_cb2, -font => $font{$display_size});
    my $cm2 = $widget{'menuOptions'}->cget(-menu);
    my $cc2 = $cm2->Menu;
    $widget{'menuOptions'}->entryconfigure($menu_cb2, -menu => $cc2);
    $widget{'menu_opt_color_cas_grey'} = $cc2->command(-label => '  Black/Off-White  ',
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_text_color($Color{'black'},$Color{'offwhite'}); });
    $widget{'menu_opt_color_cas_white'} = $cc2->command(-label => '  Black/White  ',
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_text_color($Color{'black'},$Color{'white'}); });
    $widget{'menu_opt_color_cas_black'} = $cc2->command(-label => '  White/Black ',
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_text_color($Color{'white'},$Color{'black'}); });
    $widget{'menu_opt_color_cas_black2'} = $cc2->command(-label => ' OffWhite/Black ',
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_text_color($Color{'offwhite'},$Color{'black'}); });
    $widget{'menu_opt_color_cas_red'} = $cc2->command(-label => '  Red/White ',
                                                     -font => $font{$display_size}, 
                                                     -command => sub { &change_text_color($Color{'red'},$Color{'white'}); });
    $cc2->invoke(1);

  $widget{'menuOptions'}->separator; 
  $widget{'menu_options_quit'} = $widget{'menuOptions'}->command(-label => 'Quit',
                           -font => $font{$display_size}, -command => sub { &my_exit; });

  print "INIT EDIT MENU\n" if $DEBUG;
 # Edit menu
 my $menu_edit_0 = 'Allow Edit Input Text';
  $widget{'menu_edit_allow_input'} =
           $widget{'menuEdit'}->cascade(-label => $menu_edit_0, -font => $font{$display_size});
    my $cm_edit_0 = $widget{'menuEdit'}->cget(-menu);
    my $cc_edit_0 = $cm_edit_0->Menu;
    $widget{'menuEdit'}->entryconfigure($menu_edit_0, -menu => $cc_edit_0);
    $widget{'menu_edit_allow_input_yes'} = $cc_edit_0->radiobutton(-label => '  Yes  ',
                                                     -font => $font{$display_size},
                                                     -command =>
                           sub { &change_widget_write_state($WIDGET{'input_text'},'normal', $WIDGET{'input_label'}); },
                              #                       -value => 0
                                                     );
    $widget{'menu_edit_allow_input_no'} = $cc_edit_0->radiobutton(-label => '  No  ',
                                                     -font => $font{$display_size},
                                                     -command =>
                           sub { &change_widget_write_state($WIDGET{'input_text'},'disabled', $WIDGET{'input_label'}); },
                              #                       -value => 1
                                                     );
    $cc_edit_0->invoke(1);

  my $menu_edit_1 = 'Allow Edit Output Text';
  $widget{'menu_edit_allow_output'} = 
           $widget{'menuEdit'}->cascade(-label => $menu_edit_1, -font => $font{$display_size});
    my $cm_edit_1 = $widget{'menuEdit'}->cget(-menu);
    my $cc_edit_1 = $cm_edit_1->Menu;
    $widget{'menuEdit'}->entryconfigure($menu_edit_1, -menu => $cc_edit_1);
    $widget{'menu_edit_allow_output_yes'} = $cc_edit_1->radiobutton(-label => '  Yes  ',
                                                     -font => $font{$display_size}, 
                                                     -command => 
                           sub { &change_widget_write_state($WIDGET{'output_text'},'normal', $WIDGET{'output_label'}); },
  #                                                   -value => 'normal'
                                                     );
    $widget{'menu_edit_allow_output_no'} = $cc_edit_1->radiobutton(-label => '  No  ',
                                                     -font => $font{$display_size}, 
                                                     -command => 
                           sub { &change_widget_write_state($WIDGET{'output_text'},'disabled', $WIDGET{'output_label'}); },
  #                                                  -value => 'disabled'
                                                     );
    $cc_edit_1->invoke(2);


  print "INIT PARSE MENU\n" if $DEBUG;
  # Parser menu
  my $menu_cb3 = 'Halt Parser on Error Level';
  $widget{'menu_parse_errhalt_cascade'} = 
           $widget{'menuParse'}->cascade(-label => $menu_cb3, -font => $font{$display_size});
    my $cm3 = $widget{'menuParse'}->cget(-menu);
    my $cc3 = $cm3->Menu;
    $widget{'menuParse'}->entryconfigure($menu_cb3, -menu => $cc3);
    $widget{'menu_parse_errhalt_cas_triv'} = $cc3->radiobutton(-label => '  \'Trivial\' (level 0) ',
                                                     -font => $font{$display_size}, 
                                                     -variable => \$RUNTIME_PARAM{'halt_on_error_level'}, -value => 0);

    $widget{'menu_parse_errhalt_cas_norm'} = $cc3->radiobutton(-label => '   \'Normal\' (level 1) ',
                                                     -font => $font{$display_size}, 
                                                     -variable => \$RUNTIME_PARAM{'halt_on_error_level'}, -value => 1);

    $widget{'menu_parse_errhalt_cas_ser'} = $cc3->radiobutton(-label => '   \'Serious\' (level 2) ',
                                                     -font => $font{$display_size}, 
                                                     -variable => \$RUNTIME_PARAM{'halt_on_error_level'}, -value => 2);

    $widget{'menu_parse_errhalt_cas_no'} = $cc3->radiobutton(-label => '   \'Dont Halt\' (level 99) ',
                                                     -font => $font{$display_size}, 
                                                     -variable => \$RUNTIME_PARAM{'halt_on_error_level'}, -value => 99);
    $cc3->invoke($RUNTIME_PARAM{'halt_on_error_level'} != 99 ? 
                    $RUNTIME_PARAM{'halt_on_error_level'}+1 : 4); 

  my $menu_cb4 = 'INCLUDE Tagged Errors in Output XML Text';
  print "INIT PARSE MENU $menu_cb4 item \n" if $DEBUG;
  $widget{'menu_parse_tagged_cascade'} =
           $widget{'menuParse'}->cascade(-label => $menu_cb4, -font => $font{$display_size});
    my $cm4 = $widget{'menuParse'}->cget(-menu);
    my $cc4 = $cm4->Menu;
    $widget{'menuParse'}->entryconfigure($menu_cb4, -menu => $cc4);
    $widget{'menu_parse_tag_cas_exclude'} = $cc4->radiobutton(-label => '  Yes  ',
                                                     -font => $font{$display_size},
                                                     -variable => \$RUNTIME_PARAM{'include_errors_in_output'}, 
                                                     -value => 1);
    $widget{'menu_parse_tag_cas_include'} = $cc4->radiobutton(-label => '  No  ',
                                                     -font => $font{$display_size},
                                                     -variable => \$RUNTIME_PARAM{'include_errors_in_output'}, 
                                                     -value => 0);

    $cc4->invoke($RUNTIME_PARAM{'include_errors_in_output'} == 0 ? 1:0);

    $menu_cb = 'Entify Chars in Output XML Text';
  print "INIT PARSE MENU $menu_cb item \n" if $DEBUG;
    $widget{'menu_parse_entify_cascade'} =
           $widget{'menuParse'}->cascade(-label => $menu_cb, -font => $font{$display_size});
    $cm = $widget{'menuParse'}->cget(-menu);
    $cc = $cm->Menu;
    $widget{'menuParse'}->entryconfigure($menu_cb, -menu => $cc);
    $widget{'menu_parse_entify_cas_yes'} = $cc->radiobutton(-label => '  Yes  ',
                                                     -font => $font{$display_size},
                                                     -variable => \$ENTITIES_TO_ENCODE, 
                                                     -value => $DEFAULT_ENTITIES_TO_ENCODE);
    $widget{'menu_parse_entify_cas_no'} = $cc->radiobutton(-label => '  No  ',
                                                     -font => $font{$display_size},
                                                     -variable => \$ENTITIES_TO_ENCODE, -value => 0);
    $cc->invoke($ENTITIES_TO_ENCODE == 0 ? 1:0);

  my $menu_cb6 = 'Allow Null Matches in Output XML Text';
  $widget{'menu_parse_null_match_cascade'} =
           $widget{'menuParse'}->cascade(-label => $menu_cb6, -font => $font{$display_size});
    my $cm6 = $widget{'menuParse'}->cget(-menu);
    my $cc6 = $cm6->Menu;
    $widget{'menuParse'}->entryconfigure($menu_cb6, -menu => $cc6);
    $widget{'menu_parse_tag_cas_null_match_true'} = $cc6->radiobutton(-label => '  Yes  ',
                                                     -font => $font{$display_size},
                                                     -variable => \$RUNTIME_PARAM{'accept_null_matches'}, -value => 1);
    $widget{'menu_parse_tag_cas_null_match_false'} = $cc6->radiobutton(-label => '  No   ',
                                                     -font => $font{$display_size},
                                                     -variable => \$RUNTIME_PARAM{'accept_null_matches'}, -value => 0);
    $cc6->invoke($RUNTIME_PARAM{'accept_null_matches'} == 0 ? 1:0);


   print "INIT HELP MENU\n" if $DEBUG;
   # Help menu 
  $widget{'menu_help_about'} = $widget{'menuHelp'}->command(-label => 'About',
                           -font => $font{$display_size}, 
                           -command => sub {&WindowTools::popup_msg_window($widget{'main'},@aboutmsg);});


  $widget{'menu_help_help'} = $widget{'menuHelp'}->command(-label => 'Parsing Text',
                           -font => $font{$display_size}, 
                           -command => sub {&WindowTools::popup_msg_window($widget{'main'},@cmdmsg);});

  $widget{'menu_help_bugs'} = $widget{'menuHelp'}->command(-label => 'Known Bugs',
                           -font => $font{$display_size}, 
                           -command => sub {&WindowTools::popup_msg_window($widget{'main'},@bugmsg);});

  # Main widgets

  $widget{'score_label'} = $ScoreFrame->Label(text => 'Parsing Score:   0.00%', 
                                     -font => $boldfont{$display_size}
                                  )->pack(side => 'right');

  # BUTTONS
  # the ADF logo leads the buttons
  my $adf_logo_label = $CmdButtonFrame->Label( -bg => $baseColor, bd => 2 )->pack(side => 'left');
  my $adf_logo_image = $adf_logo_label->Photo(-data => &adf_logo, -format => 'xpm');
  $adf_logo_label->configure(-image => $adf_logo_image);
  

  $widget{'run_button'} = $CmdButtonFrame->Button(text => "Run",
                             fg => $buttonFgColor, bg => $buttonBgColor,
                             -font => $boldfont{$display_size},
                             command => \&run_parser )->pack( side => 'left', padx => 2);
 
  $widget{'forward_button'} = $CmdButtonFrame->Button(text => "Forward 1 Rule",
                             fg => $buttonFgColor2, bg => $buttonBgColor2,
                             -font => $boldfont{$display_size},
                             command => sub {&change_current_event(1);})->pack( side => 'left', padx => 2);

  $widget{'next_halt_button'} = $CmdButtonFrame->Button(text => "Next Halt",
                             fg => $buttonFgColor2, bg => $buttonBgColor2,
                             -font => $boldfont{$display_size},
                             command => \&next_halt)->pack( side => 'left', padx => 2);
 
  $widget{'back_button'} = $CmdButtonFrame->Button(text => "Back 1 Rule",
                             fg => $buttonFgColor2, bg => $buttonBgColor2,
                             -font => $boldfont{$display_size},
                             command => sub {&change_current_event(-1);})->pack( side => 'left', padx => 2);

  $widget{'input_view_button'} = 
                           $CmdButtonFrame->Button(text => "Toggle Input Chunk View",
                             fg => $toggle_buttonFgColor_view_off, bg => $toggle_buttonBgColor_view_off,
                             -font => $boldfont{$LARGE_SIZE},
                             command => \&toggle_input_chunk_view
                           )->pack( side => 'left', padx => 2);

  $widget{'val_output_button'} = 
                          $CmdButtonFrame->Button(text => "Validate Output",
                             fg => $buttonFgColor2, bg => $buttonBgColor2,
                             -font => $boldfont{$LARGE_SIZE},
                             command => sub { &validate_output_text(); } 
                           )->pack( side => 'left', padx => 2);


  # the ADC logo trails the buttons 
  my $adc_logo_label = $CmdButtonFrame->Label( -bg => $baseColor )->pack(side => 'left');
  my $adc_logo_image = $adc_logo_label->Photo(-data => &adc_logo, -format => 'xpm');
  $adc_logo_label->configure(-image => $adc_logo_image);


  if ($LAYOUT eq 'separate' ) { 
    print "INIT SEPARATE LAYOUT FRAMES\n" if $DEBUG;
    $widget{'ErrorWindow'} = new MainWindow;
    $widget{'InputWindow'} = new MainWindow;
    $widget{'RulesWindow'} = new MainWindow;
    $widget{'OutputWindow'} = new MainWindow;

    $widget{'ErrorFrame'} = $widget{'ErrorWindow'}->Frame()->pack(fill => 'both', expand => 'true');;
    $widget{'InputFrame'} = $widget{'InputWindow'}->Frame()->pack(fill => 'both', expand => 'true');
    $widget{'RulesFrame'} = $widget{'RulesWindow'}->Frame()->pack(fill => 'both', expand => 'true');
    $widget{'OutputFrame'} = $widget{'OutputWindow'}->Frame()->pack(fill => 'both', expand => 'true');
 
    $widget{'ErrorWindow'}->configure(title => 'Error Log');
    $widget{'InputWindow'}->configure(title => 'Input');
    $widget{'RulesWindow'}->configure(title => 'Rules');
    $widget{'OutputWindow'}->configure(title => 'Output');

  } else {

    print "INIT MONO WINDOW LAYOUT FRAMES\n" if $DEBUG;
    $widget{'SplitFrameH'} = &create_splitframe($bottomFrame,'horizontal',$frame_dim{'SplitFrameH'});
    $widget{'ErrorFrame'} = $widget{'SplitFrameH'}->Frame();
    $widget{'SplitFrameV1'} = &create_splitframe($widget{'SplitFrameH'},'vertical',$frame_dim{'SplitFrameV1'});
    $widget{'InputFrame'} = $widget{'SplitFrameV1'}->Frame();
    $widget{'SplitFrameV2'} = &create_splitframe($widget{'SplitFrameV1'},'vertical',$frame_dim{'SplitFrameV2'});
    $widget{'RulesFrame'} = $widget{'SplitFrameV2'}->Frame();
    $widget{'OutputFrame'} = $widget{'SplitFrameV2'}->Frame()->pack(fill => 'both', expand => 'true');
  }

  
  print "INIT ALL WIDGETS\n" if $DEBUG;
  # error log window
  my ($error_label,$error_text_widget,$y_error_scroll,$x_error_scroll) = 
             &create_buttontext_widget($widget{'ErrorFrame'},0,'Error Log',$widget_dim{'error_text'});

  # input text window
  my $load_cmd = sub { $input_file = &popup_load_file_to_widget($WIDGET{'input_text'}, 
              "*","Type in Input File Name Below:","File Filter"); 
                       $WIDGET{'input_label'}->configure(-text => "Input Text ($input_file)");
                     }; 
  my ($input_label,$input_text_widget,$y_input_scroll,$x_input_scroll) = 
             &create_buttontext_widget($widget{'InputFrame'},1,"Input Text ($input_file)",
                                       $widget_dim{'input_text'},$load_cmd,\$input_file);

  # rules text window
  $load_cmd = sub { $rules_file = &popup_load_file_to_widget($WIDGET{'rules_text'}, 
              "*.xml","Type in Rules File Name Below:","File Filter",
              $WIDGET{'rules_label'},0,\%rules_text_highlight_info); 
                    $WIDGET{'rules_label'}->configure(-text => "Rules ($rules_file)");
                  }; 
  my ($rules_label,$rules_text_widget,$y_rules_scroll,$x_rules_scroll) = 
             &create_buttontext_widget($widget{'RulesFrame'},1,"Rules ($rules_file)",
                                       $widget_dim{'rules_text'},$load_cmd,\$rules_file); 
  # output text window
  my ($output_label,$output_text_widget,$y_output_scroll,$x_output_scroll) = 
             &create_buttontext_widget($widget{'OutputFrame'},0,"Output Text ($output_file)",
                                       $widget_dim{'output_text'},0,\$output_file);
   
  # add scrollbars and pack them widgets if not already packed either 
  # explicitly or implicitly (by Splitwindow/TabFrame) before now
  #

  add_horizontal_scrollbar_to_text_widget($error_text_widget,$widget{'SplitFrameH'},'right',$y_error_scroll);

  add_horizontal_and_vertical_scrollbar_to_text_widget($input_text_widget,$widget{'SplitFrameV1'},'right',
       $y_input_scroll,$x_input_scroll);

  add_horizontal_and_vertical_scrollbar_to_text_widget($rules_text_widget,$widget{'SplitFrameV2'},'right',
       $y_rules_scroll,$x_rules_scroll);

  add_horizontal_and_vertical_scrollbar_to_text_widget($output_text_widget,
      $widget{'OutputFrame'},'right',$y_output_scroll,$x_output_scroll);


  # Lastly, lets initialize the important widgets we need to manipulate
  # into a hash table

  $widget{'error_label'} = $error_label; 
  $widget{'rules_label'} = $rules_label; 
  $widget{'input_label'} = $input_label; 
  $widget{'output_label'} = $output_label; 
  $widget{'rules_text'} = $rules_text_widget;
  $widget{'error_text'} = $error_text_widget;
  $widget{'output_text'} = $output_text_widget;
  $widget{'input_text'} = $input_text_widget;

  return %widget;
}

sub open_options_menu {

  print "STATE:",  $WIDGET{'menuOptions'}->cget(-state), "\n";
  $WIDGET{'menuOptions'}->configure(-state => 'active');
 
}

sub change_widget_write_state { 
    my ($widget, $state, $label) = @_; 
    return unless $widget; 
    $widget->configure(-state => $state); 
    if($label) {
      if($state eq 'disabled') {
        $label->configure(-bg => $baseColor); 
      } else {
        $label->configure(-bg => $EnabledWriteColor); 
      }
    }
}

sub create_buttontext_widget {
  my ($Frame,$writeable,$label_text,$widget_dim_ref,$load_cmd,$save_file) = @_;

  die "create_buttontext not passed a frame!" unless $Frame;
  die "create_buttontext not passed a ref for widget dimensions!" unless $widget_dim_ref;

  my %widget_dimensions = %{$widget_dim_ref};

  my $labelFrame = $Frame->Frame->pack(side => 'top');

  my $label = $labelFrame->Label(-font => $boldfont{$DISPLAY_SIZE})->pack(side => 'left');;
  $label->configure(-text => $label_text) if $label_text;
  if ($writeable) {
    $label->configure(-bg => $EnabledWriteColor);
  } else {
    $label->configure(-bg => $baseColor);
  }

  my $text_widget = $Frame->Text (
                                height => $widget_dimensions{'height'}->{$DISPLAY_SIZE},
                                width => $widget_dimensions{'width'}->{$DISPLAY_SIZE},
                                font => $font{$DISPLAY_SIZE},
                                wrap => $TEXT_WIDGET_WRAP_MODE,
                                state => $writeable ? 'normal' : 'disabled',
                                fg => $TextFgColor,
                                bg => $TextBgColor
                             ); # DONT pack yet

  my $MyButtonFrame = $Frame->Frame->pack;
  # my $MyButtonFrame = $labelFrame;
  if($load_cmd) {
    $MyButtonFrame->Button(text => "Load File",
                             fg => $load_buttonFgColor, bg => $load_buttonBgColor,
                             command => sub { &$load_cmd if $load_cmd; } 
                         )->pack( side => 'left', padx => 2);
  }

  $MyButtonFrame->Button(text => "Save",
                             fg => $save_buttonFgColor, bg => $save_buttonBgColor,
                             command => sub { 
                                 my $file = ${$save_file} if ref($save_file);
                                 &save_buffer_to_file($file,"*",$text_widget,0);
                                 ${$save_file}  = $file if ref($save_file);
                                        }
                         )->pack( side => 'left', padx => 2);

  $MyButtonFrame->Button(text => "Save As",
                             fg => $save_as_buttonFgColor, bg => $save_as_buttonBgColor,
                             command => sub { 
                                 my $file = ${$save_file} if ref($save_file);
                                 &save_buffer_to_file($file,"*",$text_widget,1);
                                 ${$save_file}  = $file if ref($save_file);
                                        }
                         )->pack( side => 'left', padx => 2);

  my $y_scroll = $Frame->Scrollbar()->pack(side => 'left');
  my $x_scroll = $Frame->Scrollbar(orient =>'h');

  return ($label,$text_widget,$y_scroll,$x_scroll);
}

sub create_splitframe {
  my ($Frame,$orientation,$frame_dim_ref) = @_;

  die "create_horiz_splitframe not passed a frame!" unless $Frame;
  die "create_horiz_splitframe not passed a ref for frame dimensions!" unless $frame_dim_ref;

  my %frame_dimensions = %{$frame_dim_ref};

  return $Frame->SplitFrame(
                                '-orientation' => $orientation,
                                '-trimcolor'  => $Color{'grey'},
                                '-background'  => $Color{'white'},
                                '-sliderposition' => $frame_dimensions{'sliderposition'}->{$DISPLAY_SIZE},
                                '-borderwidth' => 2,
                                '-sliderwidth' => 8,
                                '-relief'      => 'sunken',
                                '-height'      => $frame_dimensions{'height'}->{$DISPLAY_SIZE},
                                '-width'       => $frame_dimensions{'width'}->{$DISPLAY_SIZE},
                                '-padbefore'   => 0,
                                '-padafter'    => 0
                             )->pack( fill => 'both', expand => 'yes');

}

sub add_horizontal_scrollbar_to_text_widget {
  my ($widget,$frame,$barside,$yscroll) = @_;

  $barside = defined $barside ? $barside : "right";
 
  my $widget_side = $barside eq 'right' ? 'left' : 'right';

  $yscroll = $frame->Scrollbar unless $yscroll;
  $yscroll->configure(-command => ['yview', $widget]);
  $widget->configure (-yscrollcommand => ['set', $yscroll]); 
  $widget->pack(side => $widget_side, fill => 'both', expand => 'yes');
  $yscroll->pack(side => $barside, fill => 'y');

}

sub add_horizontal_and_vertical_scrollbar_to_text_widget {
  my ($widget,$frame,$ybarside,$yscroll,$xscroll) = @_;

  $ybarside = defined $ybarside ? $ybarside : "right";
  my $widget_side = $ybarside eq 'right' ? 'left' : 'right';

  $yscroll = $frame->Scrollbar unless $yscroll;
  $yscroll->configure(-command => ['yview', $widget]);

  $xscroll = $frame->Scrollbar( orient => 'h') unless $xscroll;
  $xscroll->configure(-command => ['xview', $widget]);
  $widget->configure ( -yscrollcommand => ['set', $yscroll],
                     -xscrollcommand => ['set', $xscroll]);

  $xscroll->pack(side => 'bottom', fill => 'x');
  $widget->pack(side => $widget_side, fill => 'both', expand => 'yes');
  $yscroll->pack(side => 'right', fill => 'y');

}

sub null_cmd { }

sub my_exit { exit 0; }

sub clear_text { 
  my ($widget) = @_; 
  &delete_all_tags($widget);
  $widget->delete(0.1, 'end'); 
}

sub delete_all_tags {
   my ($widget) = @_;
   foreach my $tag ($widget->tagNames) { $widget->tagDelete($tag); }
}

sub argv_loop {

  # Did we remember to have any runtime arguments??
  # &usage() if ($#ARGV < 0);

  # loop thru and do stuff with globals, etc.
  while ($_ = shift @ARGV) {
    #print $_, "\n";
    if(/-halt_on_error/) { # Set error halt level
      $RUNTIME_PARAM{'halt_on_error_level'} = shift @ARGV;
    } elsif(/-h/) {      # Help
      #&help("Run help from GUI menu to get help");
      &help;
    } elsif(/-small/) { # Set display to small
      $DISPLAY_SIZE = $SMALL_SIZE;
      $USE_GUI = 1;
    } elsif(/-large/) { # Set display to large
      $DISPLAY_SIZE = $LARGE_SIZE;
      $USE_GUI = 1;
    } elsif(/-normal/) { # Set display to large
      $DISPLAY_SIZE = $NORMAL_SIZE;
      $USE_GUI = 1;
    } elsif(/-tiny/) { # Set display to large
      $DISPLAY_SIZE = $TINY_SIZE;
      $USE_GUI = 1;
    } elsif(/-split/) { # Set format file
      $LAYOUT = 'separate'; 
      $USE_GUI = 1;
    } elsif(/-null_match/) { # allow null matches 
      $RUNTIME_PARAM{'accept_null_matches'} = 1;
    } elsif(/-g/) { # use the debugging gui
      $USE_GUI = 1;
    } elsif(/-s/) { # turn on score reporting
      $PRINT_SCORE = 1;
    } elsif(/-include_errors_in_output/) { # turn on errors in output
      $RUNTIME_PARAM{'include_errors_in_output'} = 1;
    } elsif(/-m/) { # turn on memory debugging
      $MEM_DEBUG = 1 ;
      &Text2XML::set_mem_debug_flag(1);
    } elsif(/-no_encode_output/) { # turn off encoding
      $ENTITIES_TO_ENCODE = 0;
    } elsif(/-f/) { # Set format file
      $rules_file = shift @ARGV;
    } elsif(/-v/) { # Set debugging on
      $DEBUG = 1 ;
      &Text2XML::set_debug_flag(1);
    } elsif(/-/) {
      print "\t\"$_\" is an unknown option, $0 aborting\n"; exit (1);
    } else {
      $input_file = $_;
    }
  }
}

sub help {
  my ($buf) = @_;
  my $msg = $buf ? $buf : join "\n", @aboutmsg ;
  print $msg, "\n";
  usage(); exit 0;
}

# the helpful how-to-use statement every program needs
sub usage {
  my ($msg) = @_;
  print $msg if $msg;
  print "Usage: $0 [-g -tiny|small|normal|large] [-h] -f <rules_file.xml> <text_file_to_parse>\n";
  exit 0;
}

sub popup_load_file_to_widget {
  my ($widget,$filter,$msg1,$msg2,$labelwidget,$labelmsg,$highlight_info_ref) = @_;

  die "ERROR : no widget specified in popup_load_file_to_widget()" unless $widget;

  my $file = &WindowTools::popup_file_select($WIDGET{'main'},".",$filter,40,15,
                   $msg1,$msg2,
                  # "Type in XML Rules File:",
                  # "Type in XML rules file or Click on a listed file below.\nFilter:", 
                  "Files","Other Directories");

  if ($file && -e $file) {
    &update_text_widget($widget,&Text2XML::get_document_text_chunk($file),
                        $highlight_info_ref);
    if($labelwidget && $labelmsg) {
      $labelwidget->configure(text => "$labelmsg $file"); 
    }
  } else {
    error("Can\'t find the file:$file\n",1) unless !defined $file;
  }

  return $file;
}

sub get_rules_text { return &get_text_from_widget($WIDGET{'rules_text'}); }
sub get_input_text { return &get_text_from_widget($WIDGET{'input_text'},'InputTextBreak'); }
sub get_output_text { return &get_text_from_widget($WIDGET{'output_text'}); }

# this sucks... some bug in Perl/Tk Text widget
# makes it return a newline rather than empty
# string when there is NO text in the document.
sub get_text_from_widget {
  my ($widget,$tag) = @_;

  my $tagindex;
  if($tag) {
    foreach my $thistag ($widget->tagNames) {
      $tagindex = $widget->index("$tag.first") if $thistag eq $tag;
    }
  }
  my $index = defined $tagindex ? $tagindex : 'end'; 
  my $ret_text = $widget->get(0.1,$index) if $widget;
  return $ret_text;
}

sub update_score {
   my ($new_score) = @_;
 
   if(defined $new_score) {
     my $buf = sprintf("Parsing Score: %5.2f",$new_score*100.0); 
     $buf .= '%';
     $WIDGET{'score_label'}->configure(text => $buf);
   }
}

# new update scheme for error buffer
# its also hardwired, and doesnt use the highlight text scheme
# from above. Well, one day we'll clean it all up. maybe. 
sub new_update_error {

  my $widget= $WIDGET{'error_text'};

  if ($widget) {
    my $widget_is_no_user_edit = $widget->cget('-state');

    my $def_fgcolor = $widget->cget(-fg);
    my $def_bgcolor = $widget->cget(-bg);

    # set widget to normal state so we can write to it
    $widget->configure(-state => 'normal') if $widget_is_no_user_edit eq 'disabled';

    clear_text($widget); # deletes all tags too. 
    
    # ok, spin thru the events list, pick out only those which had errors
    # and print them in the error text buffer
    my $error_number = 0;
    foreach my $event_number (0 ... $#PARSE_EVENT) {
      if ($PARSE_EVENT[$event_number]->{'error'}) {
          $error_number++;
          my $tag = 'errtag' . $event_number;
          my $msgtag = 'errtag' . $event_number . "_msg";
          my $code_ref = sub { 
                            my @taglist = ($tag, $msgtag);
                        &click_on_error_tag($widget,\@taglist,$event_number,$def_fgcolor,'yellow');
                             }; 
          my $level = $PARSE_EVENT[$event_number]->{'error_level'};
          my $type = $PARSE_EVENT[$event_number]->{'error_type'};
          my $msg = $PARSE_EVENT[$event_number]->{'error_msg'};
          my $string = "ERROR:[$error_number][$level][$type]:"; 
          &insert_highlighted_string($widget,$string,$tag,'red',$def_bgcolor,$code_ref, '<1>'); 
          &insert_highlighted_string($widget,"$msg\n",$msgtag,$def_fgcolor,$def_bgcolor,$code_ref, '<1>'); 
      }
    }

    # return widget to disabled state if it started that way
    $widget->configure(-state => 'disabled') if $widget_is_no_user_edit eq 'disabled';
  }

}

sub update_rules_label { my ($text) = @_; &update_label($WIDGET{'rules_label'},$text); }
sub update_label { my ($label,$text) = @_; $label->configure(text => $text); }
sub update_error { my ($chunk) = @_; update_text_widget($WIDGET{'error_text'},$chunk);}
sub update_input_text { my ($chunk) = @_; update_text_widget($WIDGET{'input_text'},$chunk);}
sub update_rules_text { my ($chunk) = @_; update_text_widget($WIDGET{'rules_text'},$chunk,
                        \%rules_text_highlight_info); }
sub update_output_text { my ($chunk) = @_; update_text_widget($WIDGET{'output_text'},$chunk
                         ,\%output_text_highlight_info
                        ); }

# we want to allow the program to update 'non-edit' text
# so we breifly toggle its status in this subroutine..
sub update_text_widget {
  my ($widget,$chunk,$highlightinfo_ref,$dont_clear_text,$code_ref) = @_;
  if ($chunk && $widget) {
    my $widget_is_no_user_edit = $widget->cget('-state');

    # set widget to normal state so we can write to it
    $widget->configure(-state => 'normal') if $widget_is_no_user_edit eq 'disabled';

    clear_text($widget) unless $dont_clear_text;

    # inserting text
    if(defined $highlightinfo_ref) {
      &insert_highlighted_text($widget,$chunk,$highlightinfo_ref,$code_ref);
    } else {
      $widget->insert('end',$chunk) if $chunk;
    }

    # return widget to disabled state if it started that way
    $widget->configure(-state => 'disabled') if $widget_is_no_user_edit eq 'disabled';
  }
}

# this will insert a mixture of highlighted and 
# regular text
sub insert_highlighted_text {
   my ($widget,$chunk,$highlightinfo_ref,$code_ref) = @_;

   my $def_fgcolor = $widget->cget(-fg);
   my $def_bgcolor = $widget->cget(-bg);

   my $chunk_index = -1;
   my $last_char = length($chunk);

   do {

     my ($fgcolor,$next_start_char,$next_end_char) = 
           &find_next_highlight_string($chunk,$chunk_index,$highlightinfo_ref);

     # safeties
     $next_end_char = $last_char if (!defined $next_end_char or $next_end_char < 0);
     $fgcolor = $def_fgcolor unless $fgcolor; 

     # first write out any text before highlight
     my $end_of_substring = $next_start_char-$chunk_index;
     if($chunk_index >= 0 && $chunk_index < $next_start_char) {
       # my $end_of_substring = $next_start_char-$chunk_index;
       my $string = substr($chunk,$chunk_index,$end_of_substring);
       $widget->insert('end',$string) if defined $string;
       #$chunk_index += $end_of_substring;
     }
     $chunk_index += $end_of_substring;

     # now, write out highlighted text
     if($next_start_char >= 0) {
        my $tag = 'highlight' . $chunk_index;
        #my $end_of_substring = $next_end_char-$next_start_char+1;
        $end_of_substring = $next_end_char-$next_start_char+1;
        my $string = substr($chunk,$chunk_index,$end_of_substring);
        &insert_highlighted_string($widget,$string,$tag,$fgcolor,$def_bgcolor,$code_ref,
                                  '<Control-ButtonPress-1>'); 
     }

     $chunk_index = $next_end_char+1;

   } while ($chunk_index < $last_char);
}

sub find_next_highlight_string {
   my ($string,$offset,$highlightinfo_ref) = @_;

   my %highlightinfo = %{$highlightinfo_ref};

   my $start_highlight = -1; 
   my $end_highlight = -1; 
   my $fgcolor = 'black';
   my $relevance;

   foreach my $format (keys %highlightinfo) {

     my $info = $highlightinfo{$format};
     my $start_string = $info->{'start_string'};
     my $end_string = $info->{'end_string'};
     my $relevance_of_this_format = $info->{'relevance'};

     my $start = index($string, $start_string,$offset);

     # bleh, what complicated logic.
     if($start > -1 && 
           (
             ($start < $start_highlight || ($start < $start_highlight && $relevance_of_this_format > $relevance)) 
                 || $start_highlight < 0
           )
     ) {
        $relevance = $relevance_of_this_format;
        $start_highlight = $start;
        $end_highlight = index($string,$end_string,$start_highlight);
        $fgcolor = $info->{'fgcolor'};
     }
   }

   return ($fgcolor,$start_highlight,$end_highlight);
}


sub insert_highlighted_string {
   my ($widget,$string,$tag,$fgcolor,$bgcolor,$code_ref,@bind_list) = @_;

   $fgcolor = defined $fgcolor ? $fgcolor : 'black';
   $bgcolor = defined $bgcolor ? $bgcolor : 'white';

   if($string) {
     $widget->insert('end',$string ,$tag);
     $widget->tagConfigure($tag, -foreground => $fgcolor, -background => $bgcolor);

     # $widget->tagBind($tag, '<Control-ButtonPress-1>', 
    foreach my $bind_sequence (@bind_list) {
     $widget->tagBind($tag, $bind_sequence,
                       sub { &$code_ref();} 
                     ) if ($code_ref);
    }
   }
}

sub tag_exists_in_text_widget {
  my ($widget,$thistag) =@_;

  foreach my $tag ($widget->tagNames) {
    return 1 if $tag eq $thistag;
  }
  return 0; 
}

# what happens when we click on a tag
# in the error msg window
sub click_on_error_tag {
  my ($widget,$taglist_ref,$event_number,$fgcolor,$bgcolor) = @_;

  # set the CURRENT rule event to one the error occured at
  $PARSE_EVENT_INDEX = $event_number;

  &highlight_the_chunk_info_of_this_event($PARSE_EVENT[$PARSE_EVENT_INDEX]);
  &change_current_event(0); # show the current rule for this event
  &highlight_just_these_tags('error_text',$taglist_ref,$fgcolor,$bgcolor);

}

# what happens when we click on a tag
sub click_on_rules_tag {
  my ($widget,$tag,$rule) = @_;

  my $rule_end_tag = $tag . '_end';
  my @list = ();
  push @list, $tag;  # add tag to list 
  push @list, $rule_end_tag if tag_exists_in_text_widget($widget,$rule_end_tag);

  &highlight_just_these_tags('rules_text',\@list,$rule_text_show_tag_fg_highlight,$rule_text_show_tag_bg_highlight);

  # set the CURRENT rule event to first one in parse events array
  foreach my $event_number (0 ... $#PARSE_EVENT) {
    if ($PARSE_EVENT[$event_number]->{'rule'} == $rule) {
        $PARSE_EVENT_INDEX = $event_number; 
        last; 
    } 
  }

  &highlight_the_chunk_info_of_this_event($PARSE_EVENT[$PARSE_EVENT_INDEX]);

}

sub highlight_the_chunk_info_of_this_event {
   my ($event) = @_;

   my $widget = $WIDGET{'input_text'};
   my $working_chunk_start = $event->{'absolute_chunk_start_position'};
   my $working_chunk_end = $event->{'absolute_chunk_end_position'};
   my $rule = $event->{'rule'};
#   my $status_of_start_match = Text2XML::get_rule_statusOfStart_value($rule);
#   my $status_of_end_match = Text2XML::get_rule_statusOfEnd_value($rule);
   my $status_of_end_match = $event->{'statusOfEnd'};

   # clear out the old tagged text, should it exist
   foreach my $highlight_tag (qw (startmatchchunk matchchunk endmatchchunk workchunk)) {
     $widget->tagDelete($highlight_tag);
   }

   # highlight the working chunk
   &highlight_text_chunk($widget,'workchunk',
                         $working_chunk_start, $working_chunk_end, 
                         $input_text_fg_highlight, 
                         $working_chunk_bg_color );

   # extra highlighting of the working chunk as desired..
   # ALSO, this is meaningless highlighting if there is NO
   # matching chunk (its possible to get an end chunk length from
   # a rule that tests 
   if($INPUT_CHUNK_VIEW eq 'match_chunk' && $event->{'matching_chunk_len'}>0) {

     # highlight the start match chunk
     my $chunk_start = $working_chunk_start + $event->{'before_chunk_len'};
     my $chunk_end = $working_chunk_start 
                   + $event->{'before_chunk_len'} 
                   + $event->{'start_match_chunk_len'};

    # $chunk_end -= $event->{'start_match_chunk_len'} 
    #      if ($status_of_start_match eq 'accept');

     &highlight_text_chunk($widget,'startmatchchunk',
                         $chunk_start, $chunk_end, $input_text_fg_highlight,
                         $start_match_chunk_bg_color);

     # highlight the match chunk
     # color depends on if its a 'match' or 'ignore' rule
     my $match_color = &Text2XML::get_rule_type($rule) eq 'ignore' ? $ignore_chunk_bg_color : 
                       $match_chunk_bg_color;
     $chunk_start = $chunk_end;
     $chunk_end = $chunk_start + $event->{'matching_chunk_len'}; 

    # $chunk_end -= $event->{'start_match_chunk_len'} 
    #      if ($status_of_start_match eq 'accept');

    $chunk_end -= $event->{'end_match_chunk_len'}
          if ($status_of_end_match eq 'accept');


     &highlight_text_chunk($widget,'matchchunk',
                         $chunk_start, $chunk_end, $input_text_fg_highlight, 
                         $match_color);

     # highlight the end match chunk
     $chunk_start = $chunk_end;
     $chunk_end = $chunk_start + $event->{'end_match_chunk_len'};

     $chunk_end -= $event->{'end_match_chunk_len'}
          if ($status_of_end_match eq 'accept');

     &highlight_text_chunk($widget,'endmatchchunk',
                         $chunk_start, $chunk_end, $input_text_fg_highlight,
                         $end_match_chunk_bg_color);

   }


   # view the beginning of the chunk
   $widget->see("0.1+$working_chunk_start chars");
}

sub unhighlight_these_tags {
  my ($widget,$tag_list_ref) =@_; 

  my @tag_list = @{$tag_list_ref};
  my $widget_fg_color = $widget->cget(-fg); 
  my $widget_bg_color = $widget->cget(-bg); 
  foreach my $tag (@tag_list) {
    # $widget->tagConfigure($tag, -foreground => $widget_fg_color, -background => $widget_bg_color);
    $widget->tagConfigure($tag, -background => $widget_bg_color);
  }
}

sub highlight_these_tags {
  my ($widget,$tag_list_ref,$fgcolor,$bgcolor) =@_; 

  my @tag_list = @{$tag_list_ref};
  foreach my $tag (@tag_list) {
    # $widget->tagConfigure($tag, -foreground => $fgcolor, -background => $bgcolor);
    $widget->tagConfigure($tag, -background => $bgcolor);
  }
  $widget->see($tag_list[0] . '.first');
}

sub highlight_just_these_tags {
  my ($widget_name, $taglist_ref, $highlight_fgcolor, $highlight_bgcolor ) = @_;

  my $widget = $WIDGET{$widget_name};

  if($HIGHLIGHTED_TAGLIST{$widget_name}) {
    # return old tags to normal
    &unhighlight_these_tags($widget, $HIGHLIGHTED_TAGLIST{$widget_name});
  }

  # highlight the new tags 
  &highlight_these_tags($widget,$taglist_ref,$highlight_fgcolor, $highlight_bgcolor);

  # remember the list of highlighted tags
  $HIGHLIGHTED_TAGLIST{$widget_name} = $taglist_ref;

}

# change the current highlighted event, rule (and
# now, unhighlight the selected error) 
# when the current event (PARSE_EVENT_INDEX value) is
# changed by an arbitrary number of steps
sub change_current_event($) {
  my ($nrof_steps) = @_;

  $PARSE_EVENT_INDEX += $nrof_steps;

  print "LAST RULE: $PARSE_EVENT_INDEX \n" if $DEBUG;

  # did we exceed the event list bounds?
  if ($PARSE_EVENT_INDEX <= -1 || $PARSE_EVENT_INDEX > $#PARSE_EVENT) {
    $PARSE_EVENT_INDEX -= $nrof_steps;
    $WIDGET{'main'}->bell(); # flash an error 
  } else {

    # return highlighted error tags to normal
    if($HIGHLIGHTED_TAGLIST{'error_text'}) {
      &unhighlight_these_tags($WIDGET{'error_text'}, $HIGHLIGHTED_TAGLIST{'error_text'});
    }

    # go ahead change display the new event
    my @rulelist = (&find_tagged_rule_from_event($PARSE_EVENT_INDEX));
    &highlight_just_these_tags('rules_text',\@rulelist,
             $rule_text_current_tag_fg_highlight, $rule_text_current_tag_bg_highlight);

    print_PARSE_EVENT($PARSE_EVENT[$PARSE_EVENT_INDEX]) if $DEBUG;
    &highlight_the_chunk_info_of_this_event($PARSE_EVENT[$PARSE_EVENT_INDEX]);
  }

}

sub find_tagged_rule_from_event {
  my ($event_index) = @_;

  my $event_rule = $PARSE_EVENT[$event_index]->{'rule'}; 
  my $end_event_rule = $PARSE_EVENT[$event_index]->{'end_rule'};

  foreach my $tag (keys %RULE_TEXT_TAG_TO_RULE) {
    return $tag if $event_rule == $RULE_TEXT_TAG_TO_RULE{$tag} && 
           (($tag =~ m/_end/ && $end_event_rule) or 
           ($tag !~ m/_end/ && !$end_event_rule));
  }

  die "Couldnt find a matching rule between rules text and parser events!";

}

# a debugging statement
sub print_PARSE_EVENT {
  my ($event) = @_;

  if (defined $event) {
    my $start_pos = defined $event->{'absolute_chunk_start_position'} ? $event->{'absolute_chunk_start_position'} : "";
    my $end_pos = defined $event->{'absolute_chunk_end_position'} ? $event->{'absolute_chunk_end_position'} : "";
    my $working_chunk = defined $event->{'working_chunk'} ? $event->{'working_chunk'} : "";
    my $matching_chunk = defined $event->{'matching_chunk'} ? $event->{'matching_chunk'} : "";
    my $start_match_chunk = defined $event->{'start_match_chunk'} ? $event->{'start_match_chunk'} : "";
    my $last_match = defined $event->{'last_match'} ? $event->{'last_match'} : "";
    my $end_match_chunk = defined $event->{'end_match_chunk'} ? $event->{'end_match_chunk'} : "";
    my $before_chunk = defined $event->{'before_chunk'} ? $event->{'before_chunk'} : "";
    my $after_chunk = defined $event->{'after_chunk'} ? $event->{'after_chunk'} : "";
    my $rule = defined $event->{'rule'} ? $event->{'rule'} : "";
    my $rule_type = defined $rule ? &Text2XML::get_rule_type($rule) : "";
    my $rule_tag = defined $rule ? &Text2XML::get_rule_tag_value($rule) : "";

    my $before_chunk_len = $event->{'before_chunk_len'} ? $event->{'before_chunk_len'} : "";
    my $start_match_chunk_len = $event->{'start_match_chunk_len'} ? $event->{'start_match_chunk_len'} : "";
    my $end_match_chunk_len = $event->{'end_match_chunk_len'} ? $event->{'end_match_chunk_len'} : "";
    my $matching_chunk_len = $event->{'matching_chunk_len'} ? $event->{'matching_chunk_len'} : "";
    my $after_chunk_len = $event->{'after_chunk_len'} ? $event->{'after_chunk_len'} : "";

    print "\nEVENT: [$rule_type][$rule_tag][$rule]\n"; 
    print "       Start Pos:[$start_pos]\n"; 
    print "       End Pos:[$end_pos]\n"; 
    print "       Work Chunk(",length($working_chunk),"):[$working_chunk]\n"; 
    print "       Before(",$before_chunk_len,"):[$before_chunk]\n"; 
    print "       Start(",$start_match_chunk_len,"):[$start_match_chunk]\n"; 
    print "       Match(",$matching_chunk_len,"):[$matching_chunk]\n"; 
    print "       End(",$end_match_chunk_len,"):[$end_match_chunk]\n"; 
    print "       After(",$after_chunk_len,"):[$after_chunk]\n"; 
    print "       Last_match:[$last_match]\n"; 

  }

}

# loading the rules from the rules text widget
sub load_rules_from_buffer {
  my $rules_text = get_rules_text();
  # get_rules_text never returns less than \n char. bleh!
  return &Text2XML::load_rules_from_text($rules_text) if length($rules_text) > 2;
  return 0;
}

sub next_halt { $halt_rule_counter++; parse_text(); }

sub run_parser {
  $halt_rule_counter = 0; # reset counter
  parse_text();
}

# I really wish I didnt have to do something like this. 
# Its just an example of how weak this code is.
sub reset_globals_for_next_parse {

  @PARSE_EVENT = ();
  $PARSE_EVENT_INDEX = -1;

  foreach my $tag (keys %HIGHLIGHTED_TAGLIST) {
     $HIGHLIGHTED_TAGLIST{$tag} = 0;
  }

  foreach my $tag (keys %RULE_TEXT_TAG_TO_RULE) {
     $RULE_TEXT_TAG_TO_RULE{$tag} = 0;
  }

}

sub no_gui_parse_text {
  my ($input_file,$rules_file) = @_;
 
  my $use_events = 0;

  &usage() unless $input_file && $rules_file;

  reset_globals_for_next_parse() if $use_events;

  my $input_text = &Text2XML::get_document_text_chunk($input_file);
  my ($load_ok,$rules) = &Text2XML::load_rules_from_file($rules_file);

  # make the call to the parser code
  my ($output_text, $score, $junk, $nrof_errors ) = &Text2XML::parse_document( 
                                    $input_text,$input_file,$rules_file,
                                    $RUNTIME_PARAM{'include_errors_in_output'},$rules,
                                    0, $RUNTIME_PARAM{'halt_on_error_level'}, $ENTITIES_TO_ENCODE, $use_events,
                                    $RUNTIME_PARAM{'accept_null_matches'}
                                  );

  if ($PRINT_SCORE) {
    my $scorebuf = sprintf("SCORE(%s:%s:%d errors): %4.1f%s\n",$input_file,
                            $rules_file,$nrof_errors,$score*100,'%');
    print STDERR $scorebuf;
  }


  print STDOUT $output_text;

}

# UNIX based determination
sub get_memory_use {
  my $buf =  `ps alx | grep txt2`;
  my @vals = split ' ', $buf;
  return $vals[6];
}


sub parse_text {

  my $use_events = 1;
  reset_globals_for_next_parse() if $use_events;

  my ($load_ok,$rules) = &load_rules_from_buffer();
  unless ($load_ok) {
    error("You need to load a rules file before parsing!($load_ok)",1);
    return;
  }

  my $input_text = &get_input_text();
  unless ($input_file && length($input_text) > 2 ) {
    error("You need to load input text before parsing!",1); 
    return;
  }

  &update_error(" ");

  &update_rules_text_widget_with_DOM($rules);
  $WIDGET{'rules_text'}->see($rules_text_index);


#  print "PARSING TEXT\n",$input_text," ",$input_file," ",$rules_file," ",
  print "PARSING TEXT\n I:",$input_file," R:",$rules_file," ErrorINText:",
        $RUNTIME_PARAM{'include_errors_in_output'}," RuleObj:",$rules," HaltCounter:",$halt_rule_counter,"\n" if $DEBUG;
  print "THERE ARE $#PARSE_EVENT events\n" if $DEBUG;
  &dump_widget_tag_number($WIDGET{'input_text'} ) if $DEBUG;
  &dump_widget_tag_number($WIDGET{'rules_text'} ) if $DEBUG;
  &dump_widget_tag_number($WIDGET{'output_text'} ) if $DEBUG;

  # make the call to the parser code
  # my ($output_text,$score, $error_buf, $events_ref, $rules_DOM_ref) = 
  my ($output_text,$score, $events_ref ) = 
                       &Text2XML::parse_document($input_text,$input_file,$rules_file,
                                                  $RUNTIME_PARAM{'include_errors_in_output'},$rules,
                                                  $halt_rule_counter, $RUNTIME_PARAM{'halt_on_error_level'},
                                                  $ENTITIES_TO_ENCODE, $use_events, 
                                                  $RUNTIME_PARAM{'accept_null_matches'}
                                                 ); 

  print "After parse memory : ", &get_memory_use(), "\n" if $MEM_DEBUG;

  # update important buffers we need 
  @PARSE_EVENT = @{$events_ref};
  $PARSE_EVENT_INDEX = $#PARSE_EVENT;

  print "Updating GUI buffers \n" if $DEBUG;
  # update widgets
  &update_score($score);
  # &update_error($error_buf);
  &new_update_error();
  &update_output_text($output_text);

  print "Highlighting last rule \n" if $DEBUG;
  # lastly, highlight the last rule we did 
  # and the corresponding working chunk
  my @rulelist = (&find_tagged_rule_from_event($PARSE_EVENT_INDEX));
  &highlight_just_these_tags('rules_text',\@rulelist,
             $rule_text_show_tag_fg_highlight, $rule_text_show_tag_bg_highlight);
  &highlight_the_chunk_info_of_this_event($PARSE_EVENT[$PARSE_EVENT_INDEX]);
  my $first_rule = $rulelist[0];
  $WIDGET{'rules_text'}->see($first_rule . ".first");

  # clean up DOM's which can cause memory leak(??)
  $rules->dispose;

}

sub update_rules_text_widget_with_DOM {
  my ($rules) = @_;

  my $code = sub { &click_on_rules_tag(@_); };

  %RULE_TEXT_TAG_TO_RULE = undef; # reset  

  &update_text_widget_with_DOM($WIDGET{'rules_text'},$rules,\%rules_text_highlight_info,$code);
}

sub encode_string {
  my ($string) = @_;

  return &XML::DOM::encodeText($string,$ENTITIES_TO_ENCODE) if $ENTITIES_TO_ENCODE;

  return $string;
}

# This is the magic text updator that uses a DOM to 
# update the widget in question.
# Based on my_print_DOM, the current version is
# simplistic (doesnt treat all DOM instructions)
# and doesnt encode entities too well
#
sub update_text_widget_with_DOM {
  my ($widget,$dom,$highlightinfo_ref,$code_ref) = @_;

  my $widget_is_no_user_edit = $widget->cget('-state');

  # set widget to normal state so we can write to it
  $widget->configure(-state => 'normal') if $widget_is_no_user_edit eq 'disabled';

  # clear the buffer
  clear_text($widget);
  # reset tag index. Yes this IS crappy.
  $MASTER_TAG_INDEX=0;

  # Now, we go through the rules DOM inserting text
  # as directed by the node type highlight rules and code ref
  &insert_highlighted_DOM($widget,$dom,$highlightinfo_ref,$code_ref);

  # return widget to disabled state if it started that way
  $widget->configure(-state => 'disabled') if $widget_is_no_user_edit eq 'disabled';
}

# damn. a small piece of this is hardwired for rules DOM
# specifically. See the 'code_ref' part below

sub insert_highlighted_DOM {
   my ($widget,$node,$highlightinfo_ref,$code_ref) = @_;

   my $name = $node->getNodeName;
   my $type = $node->getNodeType;
   my $value = $node->getNodeValue;
   my @attrib_list = defined $node->getAttributes ? $node->getAttributes : ();
   my @children = $node->getChildNodes;

   if ($type == $dom_node_type{'TEXT_NODE'}) 
   {
     # $widget->insert('end',&XML::DOM::encodeText($node->{Data},$ENTITIES_TO_ENCODE))
     $widget->insert('end',&encode_string($node->getData()))
       if($node->getData);
   } 
   elsif ($type == $dom_node_type{'COMMENT_NODE'}) 
   {
     my $comment = "<!--" . &XML::DOM::encodeComment ($node->getData) . "-->";
     $widget->insert('end',$comment);
   } 
   elsif ($type == $dom_node_type{'ELEMENT_NODE'}) 
   {
     my $tag = 'Tag' . $MASTER_TAG_INDEX++;
     my $fgcolor = $widget->cget(-fg);
     my $bgcolor = $widget->cget(-bg);

     my %highlight_info = %{$highlightinfo_ref};

     $fgcolor = $highlight_info{$name}->{'fgcolor'};

     my $string = "<$name";

     if(@attrib_list > 0) {
        if (@attrib_list == 1)
        {
            my @name = $attrib_list[0]->getValues; 
            foreach my $val (@name) { 
              my $name = &XML::DOM::encodeAttrValue($val->getName);
              my $v = &XML::DOM::encodeAttrValue($val->getValue);
              $string .= " $name=\"$v\"";
            }
        }
        else
        {
            die "DONT KNOW HOW TO HANDLE MULTI_ATTRIB LIST ";
        }
     }

     # poor coding pops. This is hardwired. Bleh.
     # ditto for the binding sequence :  '<Control-ButtonPress-1>'
     my $code_ref = sub { &click_on_rules_tag($widget,$tag,$node); }; 
     $RULE_TEXT_TAG_TO_RULE{$tag} = $node; # set association between this tag and DOM rule 

     # How we close out this rule
     if(@children) { 

       $string .= ">";
       &insert_highlighted_string($widget,$string,$tag,$fgcolor,$bgcolor,$code_ref, 
                                  '<Control-ButtonPress-1>'); 
       foreach my $kid (@children) { 
         &insert_highlighted_DOM($widget,$kid,$highlightinfo_ref,$code_ref);
       } 
     
       #ending tag
       $string = "</$name>";
       my $end_tag_name = $tag . '_end';
       &insert_highlighted_string($widget,$string,$end_tag_name,$fgcolor,$bgcolor,$code_ref,
                                  '<Control-ButtonPress-1>'); 

       # set association between this tag and DOM rule 
       $RULE_TEXT_TAG_TO_RULE{$end_tag_name} = $node; 

     } else { # close the tag

       $string .= "/>";
       &insert_highlighted_string($widget,$string,$tag,$fgcolor,$bgcolor,$code_ref,
                                  '<Control-ButtonPress-1>'); 

     } 

   } 
   elsif ($type == $dom_node_type{'DOCUMENT_NODE'}) 
   {
     for my $kid (@children) { 
        &insert_highlighted_DOM($widget,$kid,$highlightinfo_ref,$code_ref);
     } 
   } 
   else 
   { 
     die "UNKNOWN RULE NODE TYPE:[$name][$type][$value][@attrib_list]\n";
   }

}

sub dump_widget_tag_number {
   my ($widget) = @_;

   my @number = $widget->tagNames;
   print "There are $#number tags in widget:$widget\n";

}

sub dump_widget_tags {
   my ($widget) = @_;

   foreach my $tag ($widget->tagNames) {
     print $tag, "\n";
   }
}

sub print_stderr_to_error_widget {

  my $buf; my $read_buf; my $bytes = 0;
  # read in all the data we find
  # formally speaking, this is pretty sloppy
  while (($bytes = sysread(\*STDERR, $read_buf, 1))) {
     $buf .= $read_buf;
     sleep 1;
  }

  update_error($buf) if $buf;

}

sub save_buffer_to_file {
  my ($filename,$mask,$widget,$prompt_for_filename) = @_;

   my $ok_to_overwrite = 1;
   my $myfile = $filename;

   if($prompt_for_filename) {
      $myfile = &WindowTools::popup_file_select($WIDGET{'main'},".",$mask,40,15,
                  "Type in File:",
                  "Type in filename or Click on a listed file below.\nFilter:",
                  "$mask files","Other Directories");
   }

   $ok_to_overwrite = &WindowTools::popup_yes_no_dialog($WIDGET{'main'}, 
       "Warning, you are about to overwrite $myfile. Do you wish to do this?") 
     if ($myfile && -e $myfile);

   if ($ok_to_overwrite && $myfile) {
     undef $\; #special chunk output mode
     open(OUTFILE,">$myfile");  
     print OUTFILE &get_text_from_widget($widget);
     close OUTFILE;
   }

}

sub change_text_color {
  my ($fgcolor,$bgcolor) = @_;

  foreach my $widget_name (keys %WIDGET) {

    # text widgets 
    if ($widget_name =~ m/text/ ) {
      my $widget = $WIDGET{$widget_name};
      # the main body
      $widget->configure( fg => $fgcolor, bg => $bgcolor);
      # now change the background colors for highlight tags 
      foreach my $tag ($widget->tagNames) {
        $widget->tagConfigure($tag, -background => $bgcolor) unless $tag =~ /InputTextBreak/;
      }
    }

  }
  
  # should re-run parser to update the colors properly
  # run_parser();

}

sub change_text_font_size {
  my ($display_size) = @_;

  &WindowTools::set_font($font{$display_size});
  foreach my $widget (keys %WIDGET) {
    $WIDGET{$widget}->configure( -font => $font{$display_size}) if ($widget =~ m/text/);
  }
}

sub change_display_size {
  my ($display_size) = @_;

  $WIDGET{'main'}->configure( title => "ADC $toolname $version ($display_size)")
    if $WIDGET{'main'};

  &WindowTools::set_font($font{$display_size});

  foreach my $widget (keys %WIDGET) {
    if ($widget =~ m/text/) {
        $WIDGET{$widget}->configure(-height => $widget_dim{$widget}->{'height'}->{$display_size}, 
                                    -width => $widget_dim{$widget}->{'width'}->{$display_size}, 
                                    -font => $font{$display_size}
                                   );
    }
    if ($widget =~ m/label/ or $widget =~ m/button/ or $widget =~ m/menu/) {
        $WIDGET{$widget}->configure( -font => $boldfont{$display_size});
    }
    if ($widget =~ m/SplitFrame/) {
        $WIDGET{$widget}->configure( 
                            -height => $frame_dim{$widget}->{'height'}->{$display_size},
                            -width => $frame_dim{$widget}->{'width'}->{$display_size},
                          );
        $WIDGET{$widget}->configure( 
                            -sliderposition => $frame_dim{$widget}->{'sliderposition'}->{$display_size}
                          );
    }
  }

}

sub error {
  my ($msg,$make_noise) = @_;

  &WindowTools::popup_msg_window($WIDGET{'main'},$msg);
  $WIDGET{'main'}->bell() if $make_noise; 

}

sub highlight_text_chunk {
  my($widget,$tag,$start_pos,$end_pos,$fgcolor,$bgcolor) = @_;

  my $def_bg_color = $widget->cget(-bg);
  my $def_fg_color = $widget->cget(-fg);

  $widget->tagConfigure($tag, -foreground => $def_fg_color, -background => $def_bg_color);
  $widget->tagDelete($tag);

  $widget->tagAdd($tag, "0.1+$start_pos chars", "0.1+$end_pos chars"); 
  $widget->tagConfigure($tag, -foreground => $fgcolor, -background => $bgcolor);
  #$widget->tagConfigure($tag, -background => $bgcolor);
}

# for any text widget we get the cursor/text position
# and use this to visibly mark that position
sub mark_point {
  my ($widget,$tag,$fgcolor,$bgcolor) = @_;

  $fgcolor = defined $fgcolor ? $fgcolor : 'red';
  $bgcolor = defined $bgcolor ? $bgcolor : 'blue';

  my $e = $widget->XEvent;
  my $text_index_of_cursor = &get_cursor_text_index($widget);

  $widget->tagDelete($tag);
  $widget->tagAdd($tag, $text_index_of_cursor);
  $widget->tagConfigure($tag, 
               -foreground => $fgcolor, 
               -background => $bgcolor );

}

sub get_cursor_text_index {
  my ($widget) = @_;
  my $e = $widget->XEvent;
  return $widget->index("\@" . $e->x . "," . $e->y);
}

sub toggle_input_chunk_view {
  
   my $button = $WIDGET{'input_view_button'};
   if($INPUT_CHUNK_VIEW eq 'working_chunk') {
     $INPUT_CHUNK_VIEW = 'match_chunk';
     $button->configure(fg => $toggle_buttonFgColor_view_on, bg => $toggle_buttonBgColor_view_on );
   } else {
     $INPUT_CHUNK_VIEW = 'working_chunk';
     $button->configure(fg => $toggle_buttonFgColor_view_off, bg => $toggle_buttonBgColor_view_off );
   }

   # update the display
   &highlight_the_chunk_info_of_this_event($PARSE_EVENT[$PARSE_EVENT_INDEX])
      if $PARSE_EVENT_INDEX && $PARSE_EVENT[$PARSE_EVENT_INDEX];
}

sub clear_marked_point { my ($widget,$tag) = @_; $widget->tagDelete($tag); }

sub validate_output_text {

   print STDERR "Validate output text \n" if $DEBUG;

   my $DEFAULT_DOM_CHECK_WIDGET_ref = $DOM_CHECK_WIDGET_ref;

   $DOM_CHECK_WIDGET_ref = \$WIDGET{'output_text'}; 
   if ((my $output_text = &get_output_text())) {
     my $doc = &Text2XML::make_DOM_from_text($output_text);
     $doc->dispose;
   }

   # return to default
   $DOM_CHECK_WIDGET_ref = $DEFAULT_DOM_CHECK_WIDGET_ref;

}

sub toggle_layout {

  if($LAYOUT eq 'separate') {
    $LAYOUT = 'normal';
  } else {
    $LAYOUT = 'separate';
  }


  foreach my $type (keys %WIDGET) {
    if($type =~ m/Window/ or $type =~ /main/) {
      $WIDGET{$type}->destroy;
    }
    delete $WIDGET{$type};
  }

  %WIDGET = &init_tool($DISPLAY_SIZE); 
}

# what to do if we get an error event 
sub Tk::Error {
  my ($widget, $errormsg, @locations) = @_;

  if ($DEBUG) {
  #if (1) {
    print "Txt2XML.pl error msg called:\nWIDGET: $widget\nMSG: $errormsg \n";
    print "LOCATIONS: ", join ' ', @locations, "\n";
  }

  # is this an error from the parser because rules have mismatched tag? 
  # Lets highlight the line in the rules where that error happens
  if (   ($errormsg =~ m/mismatch.*?(\d+),.*?(\d+).*?(\d+).*?/)
      || ($errormsg =~ m/junk.*?(\d+),.*?(\d+).*?(\d+).*?/) 
      || ($errormsg =~ m/not\s+well-formed.*?(\d+),.*?(\d+).*?(\d+).*?/) 
   ) {
  
     &highlight_DOM_ERROR(${$DOM_CHECK_WIDGET_ref}, $1, $2, $3);
     $errormsg = 0; # no need for a popup 

  } 

  # print the error message in a popup window 
  &error($errormsg) if $errormsg;

}

sub highlight_DOM_ERROR {
   my ($widget, $line, $char, $byte) = @_;

     print STDERR "DOM ERROR line:($line) col:($char) byte:($byte)\n" if $DEBUG;
     my $mytag = $widget->tagNames("$line.$char");
     my @list = ("$mytag");
     &highlight_these_tags($widget,\@list, 'white', 'green');

}



sub adc_logo {

  my $buf = '/* XPM */
static char *adc_newlogo-sm[] = {
/* width height num_colors chars_per_pixel */
"    67    50      251            2",
/* colors */
".. c #e8bfc7",
".# c #ead6e0",
".a c #edf7e9",
".b c #fcfaf5",
".c c #fcfdfc",
".d c #fefefe",
".e c #feffff",
".f c #ffffff",
".g c #f4fefe",
".h c #e7fbfb",
".i c #f9f5e6",
".j c #fffdec",
".k c #fefee4",
".l c #ffffe1",
".m c #fbe9e6",
".n c #e7e9e7",
".o c #d2eef6",
".p c #c6fffe",
".q c #ced5ed",
".r c #ecf4cc",
".s c #f9fad6",
".t c #fefedd",
".u c #fbe9d8",
".v c #e8e8da",
".w c #f5f7c8",
".x c #fafccb",
".y c #feffce",
".z c None",
".A c #f8e7cb",
".B c #e6e9ca",
".C c #d9ecd2",
".D c #eed7d3",
".E c #e6d7c8",
".F c #c9d1ce",
".G c #d6d9ca",
".H c #b4c7fb",
".I c #a7f8e6",
".J c #b8fefe",
".K c #abffff",
".L c #a3ffff",
".M c #90fff0",
".N c #9cffff",
".O c #94ffff",
".P c #8cffff",
".Q c #84ffff",
".R c #afeec8",
".S c #91f2d6",
".T c #b0c9c6",
".U c #8bd5d0",
".V c #b0bac3",
".W c #dbdc91",
".X c #c9eeb9",
".Y c #f4d2b2",
".Z c #e7d2a8",
".0 c #e9c6a7",
".1 c #ced2b1",
".2 c #c5cab5",
".3 c #efcb8f",
".4 c #f6c598",
".5 c #e4c599",
".6 c #84e7b3",
".7 c #b6f3b3",
".8 c #b1caa9",
".9 c #bcc4b4",
"#. c #8dcfaf",
"## c #b5c698",
"#a c #f6bfa8",
"#b c #d8b8ab",
"#c c #e9b791",
"#d c #e6b888",
"#e c #d4ad91",
"#f c #8f97a5",
"#g c #aeb4af",
"#h c #b5b7a7",
"#i c #a8b7a7",
"#j c #a7aaa4",
"#k c #93aead",
"#l c #b3b898",
"#m c #a9b39b",
"#n c #a7aa9a",
"#o c #90aa8f",
"#p c #9ba499",
"#q c #9ba38e",
"#r c #ae978f",
"#s c #899591",
"#t c #9d9b98",
"#u c #999989",
"#v c #878685",
"#w c #65bfc1",
"#x c #54d0f2",
"#y c #75fdf1",
"#z c #7cffff",
"#A c #74ffff",
"#B c #6ff8f2",
"#C c #6cffff",
"#D c #63ffff",
"#E c #42eeff",
"#F c #5afdfe",
"#G c #54ffff",
"#H c #48f1fc",
"#I c #4cffff",
"#J c #43feff",
"#K c #6fd7f0",
"#L c #77f4cd",
"#M c #52ecd2",
"#N c #6acccd",
"#O c #51d7c9",
"#P c #31d3de",
"#Q c #2ce2ef",
"#R c #37feff",
"#S c #26fcfe",
"#T c #17f4fb",
"#U c #0dfdff",
"#V c #00feff",
"#W c #00f4ff",
"#X c #00edf4",
"#Y c #00ecff",
"#Z c #01e5ff",
"#0 c #00ccef",
"#1 c #01d9fb",
"#2 c #01d0d8",
"#3 c #008ec0",
"#4 c #1fb1c4",
"#5 c #01b6c8",
"#6 c #69e4bc",
"#7 c #6bccb5",
"#8 c #50d4b8",
"#9 c #5eb3a3",
"a. c #719591",
"a# c #519591",
"aa c #26a199",
"ab c #05acb4",
"ac c #349192",
"ad c #003c8f",
"ae c #006697",
"af c #057382",
"ag c #b8dd63",
"ah c #f5d26c",
"ai c #e49e74",
"aj c #e9b26e",
"ak c #e5a976",
"al c #d9b16d",
"am c #d9a679",
"an c #d39269",
"ao c #eba758",
"ap c #dda254",
"aq c #e49254",
"ar c #d18d4d",
"as c #db9757",
"at c #d88947",
"au c #9ca257",
"av c #8c8f78",
"aw c #edc623",
"ax c #ffc400",
"ay c #e58a2f",
"az c #d78c2f",
"aA c #d7873d",
"aB c #f6b801",
"aC c #fba600",
"aD c #ee8200",
"aE c #ff9a00",
"aF c #ff9400",
"aG c #fe8c00",
"aH c #d58617",
"aI c #b98d26",
"aJ c #00827f",
"aK c #5e8368",
"aL c #778c75",
"aM c #c46e42",
"aN c #965d49",
"aO c #88796e",
"aP c #916c58",
"aQ c #e27b32",
"aR c #cf6f2e",
"aS c #d87b27",
"aT c #c87728",
"aU c #e47709",
"aV c #fe7700",
"aW c #f66900",
"aX c #ea6700",
"aY c #e26c00",
"aZ c #e36400",
"a0 c #d07211",
"a1 c #d76802",
"a2 c #c86600",
"a3 c #f64c00",
"a4 c #e45d00",
"a5 c #c34611",
"a6 c #d55600",
"a7 c #c65700",
"a8 c #d54700",
"a9 c #c74b00",
"b. c #9f692c",
"b# c #ad6605",
"ba c #b76300",
"bb c #a65d00",
"bc c #ba5900",
"bd c #b84700",
"be c #a64700",
"bf c #874806",
"bg c #965401",
"bh c #9c4900",
"bi c #f43600",
"bj c #dc3a00",
"bk c #c53900",
"bl c #941e00",
"bm c #ab2e00",
"bn c #b93c00",
"bo c #645d5d",
"bp c #6d746a",
"bq c #797a7b",
"br c #666567",
"bs c #586665",
"bt c #726659",
"bu c #48625a",
"bv c #586958",
"bw c #4b514d",
"bx c #57565b",
"by c #46464b",
"bz c #424145",
"bA c #0e5263",
"bB c #403e45",
"bC c #002b47",
"bD c #3e3d41",
"bE c #7d4e0d",
"bF c #6e5439",
"bG c #4a4630",
"bH c #3b4336",
"bI c #403d3d",
"bJ c #713206",
"bK c #50290c",
"bL c #6b0b00",
"bM c #681a00",
"bN c #4e0600",
"bO c #451902",
"bP c #172723",
"bQ c #2f302d",
"bR c #383739",
"bS c #292628",
"bT c #342514",
"bU c #34160a",
"bV c #350301",
"bW c #270201",
"bX c #0a1508",
"bY c #180100",
"bZ c #090b0c",
"b0 c #0b0000",
"b1 c #050100",
"b2 c #030000",
"b3 c #000100",
"b4 c #000000",
/* pixels */
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.1.1.1.x.x.z.z.x.x.x.z.z.B.x.1.x.1.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.1.1.z.z.l.b.A.d.Z.u.w.A.d.dalah.d.e.b.z.x.B.1.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.1.z.z.t.talak.saHak.garap.5.Z.d.gaHam.EalaT.gaUaj.l.z.z#h.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.x.1.z.cao.ga9albe.Yamaz#c#ba7a7ala2.5.da7aS.Ea2a2.daT.h.zaR.j.y.z.1.x.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.x.1.z.i.maT.vazapaTar.0.4.s.4.c.b.c.c.m.m.d.b.c.c.uar.cba.daSba.e.b#d.3.z.1.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.1.z.calayaT#daiaS.u.b.d.u#h#kacaa#4abab#3abab#4acac.V#e.b.c.e.Abc.e.5akar.b.A.z#h.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.x.z.yayaU.naTaY.m.u.b.Va#aJ#0#Z#Z#1#1#1#1#0#1#0#1#1#1#1#1#1#5aJa....b.c.ZaS.5alaZam.y.z.1.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.1.z.4.haA.vak.4.d.Eacab#1#X#Z#1#1#1#X#X#0#W#Y#Y#W#W#5#Z#1#1#1#1#Z#Z#2#3a..i.b.ia0am.da1.e.z.1.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.1.zaoaraQ.5aU.j..aJ#2#W#Y#Z#1#1#1#1#XbAbAaeaJ.WbM.Ia3bi#8#O#O#O#8#8#O#1#Z#Y#5a#.m.AalalbbaA.c.z.1.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.1.zaH.ga6.Z.A.bac#2#W#Y#Y#Z#Z#Z#Z#Z#Z#VbC#3aebv.3bJaCbo#4#V#Z#1#X#1#1#X#Q#6#O#6#X#5#s.g.ma7.m#eao.z.1.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.1.zaja1.i.Y.i#bab#V#W#Y#Y#Z#Y#Z#Z#Z#M#6#Mafadb#axaxbbaf#Z#W#Z#Z#Z#Z#Z#Z#Z#Z#Z#Z#X#Q#M#Maa.D.u.ba1ar.d.y#n.z.z.z.z.z.z.z",
".z.z.z.z.z.z#s.zaq.g.day.ba.#X#V#W#W#V#S#R#S#V#6#6#T#X#W#VaIaLafadaeab#W#Z#Y#Y#Y#Y#Z#Y#Z#X#Z#Y#Y#Y#Y#W#Lab.1.4.i.ga0.D.yav.z.z.z.z.z.z",
".z.z.z.z.z.x.z.Ya1a0.0.ca.#X#U#U#W#V#MbVbYbV#T#T#Y#W#Y#Y#W#W#V#V#5af#V#W#Y#Y#Y#Y#Y#Y#Y#Y#Y#Y#Y#Y#Y#Y#Y#W#M#2#e.ba2araM.f.B#h.z.z.z.z.z",
".z.z.z.z.z.z.l.e.AaH.ba.#S#R#S#T#U#VaLb3b4b4#8#V#W#W#V#V#W#U#V#V#V#V#V#W#W#W#W#W#Y#Y#W#W#W#W#W#W#W#W#Y#W#W#L#1.1at.b.map.d#q.1.z.z.z.z",
".z.z.z.z#n.yapa7aA.e#f#R#J#J#J#R#R#SbMb4b0b3bG#S#S#S#SaNbtbtbtbtbt#9#S#U#T#T#T#T#T#U#T#T#T#S#S#T#S#S#T#S#U#6#V#2.#asa9b..c.daO.z.z.z.z",
".z.z.z.z.z.l.gaY.u.##8#F#F#I#I#J#I.Nb4b4bTb3b0#B#J#J#DbWb2b4b4b4b4b4bN#L#S#R#R#R#R#S#R#R#J#R#J#J#R#J#J#I#J#H.6#Sa#.baAar.c.fbqbq.z.z.z",
".z.z.z#h.y.l.d.i.ma##A#C#D#F#G#L.Savb4b3.8b3b2#7#I#I#AbVb4b3b4b4b4b4b4bW#C#I#I#J#J#J#J#G#I#J#I#I#I#I#I#I#I#G.6#J#S#r.u.d.f.f.naO.z.z.z",
".z.z.z.1.l.d.f.d.G#O#z#C#D#F.R#B#DbOb3bY.Jb3b3bG#D#G#zbWb2bY.J.L#.bWb2b4aK#I#G#I#A#sbLbNbM#s#C#G#F#G#G#G#I#L#G#F#J#7.b.c.d.f.fbQbq.z.z",
".z.z.z.z.l.f.e.c#s.P#A#A#D.R#B#D.Kb1b3bs#CbJb4bY.Q#F.NbWb4b0.Q#G#F.Rb4b4bU#C#D.QbUb3b4b4b4b4bO.M#C#G#w#z#D.R#G#G#I#H#b.c.e.d.faObq.z.z",
".z.z.1.l.l.d.d.cac.O.Q#D.7#B#A#Cavb1b4#m.IaOb3b3#.#C.ObWb4b0.O#C#F.Kb0b4bW.Q#zbNb1b3b0bOb2b4b4bT.Q#C#wbV#9#Q#xapau#G#f.c.e.d.f.oaO.x.z",
".z.z#s.d.f.d.c.m#N.O.Q.S.S#z#z.NbOb3b3b4b3b3b3b3bG#z.LbWb4b0.L#A#C.LbYb4b0.O.Ub4b3bW.L.O.KbYb3b3.U#A.Q#wbx.SaXbga1.Sa#.f.f.f.f.fb4#j.z",
".z.z#h.d.d.f.d#t.N.O#z.7#z.Q.Q.pb3b3b3b3b4b3b3b3b1.K.KbWb4b0.K#z#C.Jb2b4bY.NbFb4b4#.#z#A#A#mbKbK#i#A#z#z#PbF.HbEaD.7ac.d.f.f.f.fb4#v.y",
".z.z#h.d.f.f.c#t.L.P.R.Q.P.P.P#ob3b3#i.p.p.paPb3b1.U.JbWb4b0.K.Q.Q.Fb4b4bU.JbKb4b2.J#z#z.Q#z#z.Q.Q.Q.Q.Q#yaFbfb#aB.Qaa.c.d.d.f.fb4br.j",
".z.z#h.c.f.f.d#t.L.O.X.P.P.O.NbNb3b3.J.P.P.Q.8b3b3bT.pbWb3bY.a.2#obYb2b4aL.LbOb4b4.J#z.Q.P.Q#z#z.Q.Q.Q.P#KaGaDawaC.Sa#.c.d.d.f.db3br.k",
".z.z.1.f.d.f.c.#.U.L.R.O.O.O.N##.X##.K.P#K.P.J.7.X.8.pbYb4b3b4b4b3b4b4bW.J.LbKb2b4.p.Q.P.P.I.T.V.I.P.P.P.Q#N.UagaI#Kac.d.d.d.d.db0bs.j",
".z.z.1.b.d.c.d.da#.o.M.L.L.N.L.O.O#A#w#ub2btbs.N.O.P.pbWbXb3bXb3b3b3bK.J.N.LbFb1b4#i.P.P.Nbtb1b4#i.O.N.N.N.N.P.7ah.La..g.c.e.d.obSbo.j",
".z.z.z.z.d#da1.d#9.Q.N#D#D#D#D#D#F#k.c.nb3##avbP.Q#G#Caaaa#9aa#9#O#x#D#J#H#J#Kb4b4bV.o.p.Cb0b4b4#B#J#E#E#G#E#I#.ag#Q.VamaTaM.d#vbRbo.k",
".z.z.z#h.fakaM.0.qbja3bia3bia3bia5.d.f.qb3#iavb3bla3a3a3a3a4a3a3a3bjbjbjbja8aVbOb1b4b3b3b3b3b4bLa6a8a8bka6a8a8a9a8bh.canbd.E.cbHbI#q.k",
".z.z.z.1.y#c.u.g.gb.aBaCaCaCaCaC#r.d.g.Fbv#i#obZb0axaEaEaEaEaEaFaEaEaEaGaFaFaEaCbOb3b3b3b3b3bNaCaEaFaEaFaEaEaEaFaF#t.h#e.a.d.cbSbD.9.l",
".z.z.z.z.z.ta2bk.d.obha2a2a2baa9a.#tavbpbwbybHb4b3a1babcbabcbcbca7bca7bca7a9bca6aVa2bKbTbKa2aVa7a7bca7bca7a7a7a6bJ.fama9a5.c#vbRbx.y.z",
".z.z.z.z#q.y#d.gam.e#paGaCaEaCaE#r.d.d.d.e.C#mbXb3axaEaEaFaFaFaEaGaFaGaGaGaGaGaGaGaGaEaEaEaFaGaGaGaFaGaFaFaFaGa6.o.Dan.f.D.fbZbz#v.y.z",
".z.z.z.z.z.z.camaT.5.cbFbbbabbbd#s.d.d.f.b.1#qbZb3a2bgbgbfbgbgbgbgbhbgbhbhbhbhbebebhbebhbgbebebebebebebdbebdbl#j.c#eanan.dbqbDby.G.z.z",
".z.z.z.z.z.1.z.3#d.Yak.gb.aFaGaG#r.d.d.f.j.9#obXb3aCaVaGaVaVaVaVaVaVaVaVaVaWaVaWaVaWaVaVaVaVaVaVaVaVaVaVaVa3#j.f#caR.d.c.qbTbD#v.y.z.z",
".z.z.z.z.z.z.1.y.0a2#c.d.daPaUaV#n.c.d.d.d.B#mbXb3aFaYaUaYaYaYaZaYaYaZaYaYaZaZaZaZa4aZaZaYaYaZaZaYaZa4a4a9#j.d#caSa0#a.gbRbIbx.w.z.z.z",
".z.z.z.z.z.z.z#n.caj#bas.B.d#fbJaP..#h#g#jaObtbKbOa7bebdbdbdbdbdbdbdbdbdbdbnbnbdbdbnbdbdbdbdbdbdbnbnbnbN.o.faqaQ.h#a.fbwbIbz#g.z.z.z.z",
".z.z.z.z.z.z.z.z.x.b.u.Zaqat.d.hbga4aXaWaXaWaVaVaVaXaYaZaYaXaZaZa4aZa4a4aZa4a4a4aZa4a4a4aZaXaZa4aWbkaO.c.daR.vaSaA.dbxbRbzbq.z.z.z.z.z",
".z.z.z.z.z.z.z.z#h.1.e.4aS.5aH.4.g#gbfa1aYa1a1a1a2a6a7a2a7a9a9a9a9a9a9bda9a9bdbdbdbkbcbdbca9bkbmbF.h.f.f.vakas.c.dbxbRbzbq.y.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z#q.b.sal.#ar#d.i.d.VbKbMbdbebebhbebhbebhbebhbebebebebebmbebnbebnbdbnbkbLaP.o.d.ra7#e.d.4.Y.gbHbDbBbq.y.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.xav.q.cak.Zaka0.E.Y.c.g#vbfbmbna8a8a6a6a6a6a6a8a6a6a9bka8a8bkblblaN.V.d.c.c..a1.caS.d.c#gbQbybzbq.y.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z#h.1.c.taA.4aAaq.g.5.d.f.g.q#uaPbEbMbLbLbLbLbLbLbLbMbFaP.V.o.c.c.w.aaS.1aYaq.u.b.gbvbSbBby#v.y.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z#n#l#p.c.dayaq#ca2.ha9.Y.Z.j.d.d.c.d.d.c.d.d.d.f.d.d.c.caq#d.u#c.5aQa7.Y.d.c#sbQbIbzbr.2.y.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.1#l#s.c.e.Yat#day.5araA.capaT.5a1.ias.dapaSajaR.b.Za2.#as.Zam.l.c.gbpbPbRbIby#s.x.y.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.x#qaObv.2.c.c.b.Ba1aA.c.5at#caA.va9.4as.v#da4.E.dap.f.4.c.b#hbwbQbIbDby#v.B.y.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.zbqavbRbv#p.g.c.c.c.k.Y.m.g.s.Z#d.i.4.b.3.f.c.a.na.bwbPbQbIbBbx#v.B.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z#h#mavbXbQbQbu#n#i#i.V.T.F.T#i#i#k#fbDbHbQbSbRbDbBbx#v.9.y.y.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.x#v.1aO#maObSbSbSbSbSbQbSbQbRbRbBbBbwbq#t.2.z.y.y.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.x#h#n#n#n#n#n#n#n#n#n.G.z.y.y.y.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z",
".z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.y.k.k.k.k.k.k.k.k.l.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z.z"
};';
   return $buf;
}

sub adf_logo {
  my $buf = '/* XPM */
static char *adf_logo_sm[] = {
/* width height num_colors chars_per_pixel */
"    74    50      225            2",
/* colors */
".. c #361315",
".# c #361b1e",
".a c #411b1f",
".b c #1b0c0e",
".c c #2c1e20",
".d c #2b1317",
".e c #231417",
".f c #512732",
".g c #623541",
".h c #3b212a",
".i c #45202c",
".j c #130b0e",
".k c #1b1417",
".l c #221c20",
".m c #452633",
".n c #523040",
".o c #321723",
".p c #321f29",
".q c #2a151f",
".r c #654658",
".s c #382732",
".t c #220d17",
".u c #472e3c",
".v c #12050c",
".w c #3b192b",
".x c #1b0e16",
".y c #3c2132",
".z c #563b4f",
".A c #23151f",
".B c #2b1e29",
".C c #1b0915",
".D c #493547",
".E c #32172c",
".F c #2b1627",
".G c #28262c",
".H c #322031",
".I c #3c2c3d",
".J c #3b223b",
".K c #130d14",
".L c #0b050c",
".M c #241727",
".N c #2c2031",
".O c #241e29",
".P c #1c0e1f",
".Q c #050106",
".R c #1b151f",
".S c #0d0a0f",
".T c #ffffff",
".U c #24102b",
".V c #312d3a",
".W c #281933",
".X c #130d18",
".Y c #2d233f",
".Z c #131417",
".0 c #120c1e",
".1 c #c7c8ff",
".2 c #341786",
".3 c #c5cff0",
".4 c #4223a8",
".5 c #6e5dbf",
".6 c #080416",
".7 c #1a182a",
".8 c #0c0b15",
".9 c #222232",
"#. c #b4baec",
"## c #201655",
"#a c #14151f",
"#b c #a1abd8",
"#c c #34384a",
"#d c #010107",
"#e c #090a0f",
"#f c #1b1e24",
"#g c #0d0e11",
"#h c #203288",
"#i c #04050c",
"#j c #3155c2",
"#k c #090f20",
"#l c #638ddd",
"#m c #416896",
"#n c #090f16",
"#o c #7f97ac",
"#p c #064f85",
"#q c #1988d8",
"#r c #050a0d",
"#s c #56b8f0",
"#t c #30abe7",
"#u c #153e53",
"#v c #226280",
"#w c #146d8d",
"#x c #122f3a",
"#y c #62d1fc",
"#z c #41ccf7",
"#A c #98e0fa",
"#B c #bbf4ff",
"#C c #010506",
"#D c #121f20",
"#E c #748189",
"#F c #20c5cb",
"#G c #036461",
"#H c #22b29f",
"#I c #057561",
"#J c #025b4a",
"#K c #2c5f58",
"#L c #5a7779",
"#M c #18a281",
"#N c #034e38",
"#O c #24a480",
"#P c #023c26",
"#Q c #027547",
"#R c #02472b",
"#S c #0e965f",
"#T c #1e9b6b",
"#U c #025f36",
"#V c #90d9c5",
"#W c #05160e",
"#X c #35a74f",
"#Y c #277c32",
"#Z c #010501",
"#0 c #050a06",
"#1 c #849098",
"#2 c #226426",
"#3 c #449434",
"#4 c #5cb54e",
"#5 c #4a7d2b",
"#6 c #8fc873",
"#7 c #82c744",
"#8 c #669730",
"#9 c #83ad2c",
"a. c #a3d73c",
"a# c #b6db6b",
"aa c #bde83c",
"ab c #acc291",
"ac c #ecffaf",
"ad c #e0ff3c",
"ae c #bdd52d",
"af c #d3ec34",
"ag c #a3b62d",
"ah c #ebff6c",
"ai c #f2ff3c",
"aj c #feff3d",
"ak c #050501",
"al c #bdcec4",
"am c #eeff34",
"an c #e6f433",
"ao c #feff39",
"ap c #feff35",
"aq c #fef432",
"ar c #736d1e",
"as c #fde02d",
"at c #d8c131",
"au c #1a170a",
"av c #0b0a05",
"aw c #100f0a",
"ax c #f1c025",
"ay c #fdca29",
"az c #feb724",
"aA c #eda920",
"aB c #493a1c",
"aC c #966b23",
"aD c #fea520",
"aE c #2d2315",
"aF c #f38f1b",
"aG c #160d02",
"aH c #654823",
"aI c #fe941b",
"aJ c #ba701c",
"aK c #ec8318",
"aL c #fe8317",
"aM c #e27017",
"aN c #3a1c07",
"aO c #fe7314",
"aP c #e06111",
"aQ c #251911",
"aR c #ff6710",
"aS c #ff590a",
"aT c #f0540d",
"aU c #db4c0c",
"aV c #ff5d0f",
"aW c #e95c1e",
"aX c #ff5105",
"aY c #ff510c",
"aZ c #f44605",
"a0 c #c33d0e",
"a1 c #1c1b1c",
"a2 c #ff4203",
"a3 c #e03b07",
"a4 c #ff480a",
"a5 c #fe4a10",
"a6 c #8b280a",
"a7 c #ff501b",
"a8 c #e14d1c",
"a9 c #511b0c",
"b. c #5e2716",
"b# c #823923",
"ba c #ab3918",
"bb c #fd5d31",
"bc c #2e120a",
"bd c #fa6b47",
"be c #fe8364",
"bf c None",
"bg c #ffb3a6",
"bh c #ffccc4",
"bi c #ffdfdf",
"bj c #fff5fc",
"bk c #701f0c",
"bl c #c94629",
"bm c #df593b",
"bn c #220805",
"bo c #130505",
"bp c #4a0703",
"bq c #230d0d",
"br c #050101",
"bs c #0a0405",
"bt c #81565c",
"bu c #0d0a0a",
"bv c #fbffff",
"bw c #c5d5e2",
"bx c #bacad6",
"by c #aebdc9",
"bz c #a4b2bd",
"bA c #9caab4",
"bB c #929fa8",
"bC c #090a0a",
"bD c #050506",
"bE c #000000",
/* pixels */
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf#B#y#F#F#z#z#z#z#z#z#z#z#t#t#t#t#t#t#s#Abfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf#A#F#H#F#F#F#F#F#z#y#z#z#t#t#t#t#t#z#t#t#t#t#t#q#q#q#q#t#Bbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf#B#H#H#F#F#H#H#F#F#p#u.U.caQ.G.l.O.O.Z.Z#D.B.u.h.O#D#v#w#q#q#q#q#q#q#Abfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf#H#O#H#H#H#H#F#M.zau.R.D.G#gau.G.N#g.Oa1.N.B.Z.D.O.l.l.G.Z.G.Iaw#c#u#j#q#j#j#j#bbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbf#H#O#O#H#H#H#H#v.O.B.B.Z#f.O#e.VbC.V.R.Z.VbCbC.Z.I.L.H.K#n#n.l.R.k.7#f.z.sau#c#j#j#j#j#lbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbf#A#O#H#H#H#H#M#I.I.Ga1.N.D.S.Y.kbs.G.V.W#a.maNa6blaPaPaPaPaMaMaMaMaJaCaN.DbC#a.s.I.D.H.V#j.4#j#.bfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbf#O#O#O#M#M#H#I.V#g.G.L#fbD.K.I#e.j.PbE.aa0aSaSaVaVaRaRaRaOaOaOaOaLaLaIaIaIaIaDaKaH.9bC.r.p.c.V.4#j#jbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbf#O#O#O#O#M#M#x#a#g.x.j.l.J.Z#ia1.t.EblaSaYaSaSaVaVaVaRaRaOaOaOaOaLaOaLaIaLaIaIaIaIaIaDaFaBaw#rbC.e.9.4.4bfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbf#O#O#O#T#T#M.N.J.z.N#0brav.7.s.B#dbkaYa4aYaYaSaSaVaRaRaOaRaOaOaMaOaLaLaIaIaIaIaIaIaIaIaDaDazazaAaE#f.Z#Z.2.4.1bfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbf#T#O#T#T#M#M.G.I.u.b.kbr#a.8.Z.d#ea3a4a4a4aYaYaVaVa0b..u#Z#D.SbE.j.l.j#i#e.AaBaJaIaIaIaIaDaDazazayayaxau.n.p.Y.4bfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbf#T#T#T#T#T#S#x.R.s.Y#abD.I.k.Y.x.za5a4a4aYaYaYaUbn#k.VbEbu#gbr.BbE.B.i#i.Zak.8.X.8bEaGaJaDaDazazazazayasasag.PbE.0.4bfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbf#T#T#T#T#T#S#J#i.K.C.cbDbEbu.S.v.Ha2a4a4a4a4aW.S.B.k.F#e.Z.N.6#abs.i.t#e.y.6.B.y.p.8#Z.E.LbEarazazayayayasasasaqaBbE.E.2bfbfbfbfbfbfbf",
"bfbfbfbfbfbf#V#T#T#T#S#S#SbDbE.F.h#f.6#ibu.c.0a3a2a4a4a4b##d.L.P.LbubE.nbrbEbE.F.r.k.8.Z.t.e.q.k.8.EbEbE.j#d.UaCayayayasasaqaqaqar#d.0.5bfbfbfbfbfbf",
"bfbfbfbfbfbf#T#T#T#T#S#S#D.xbE.n.Q.Abr.nbD.ibca2a2a2a4b#.w.D#g.A.x.u.SbEbr.J.xbE#i.8bC.j.R.t.Jbs.ibE.9.B.p.#.i.nbqaraqasasaqaqaqanagbE.2bfbfbfbfbfbf",
"bfbfbfbfbf#V#T#T#S#S#S#S.q.e.K.b.P#a.8.L#i.BaZbh.T.Tbg#k.K.m.obE.mbj.T.T.T.T.Tbjbga6.D.F.A.B.jbf.T.T.Tbj.T.T.Tbiba.CaEaqaqaqapaqananag#d.5bfbfbfbfbf",
"bfbfbfbfbf#X#S#S#S#X#X.G.rbE.l.LbE.EbE.Q.x.XaX.T.T.T.Tbo.H.cbE#naX.T.T.T.T.T.T.T.T.Ta8.XbE.KaUbg.T.T.T.T.T.T.TbjbabE.F.uapapapamamanafar.2bfbfbfbfbf",
"bfbfbfbfbf#X#X#X#X#X#X.DbEbE.L.u.G.R.bbE.s.qa5.T.T.T.Ta6.PbE.sbEaS.T.T.T.T.T.T.T.T.T.Ta9.x.FaUbg.T.T.T.T.T.T.Tbjba.sbD.F.Uajapaiamanafaf.Jbwbfbfbfbf",
"bfbfbfbfbf#4#4#4#4#4#4.q.F.Z.Raw.m.V.Q.B#Cb#bf.T.T.T.TbdbE#r.K.JaX.T.T.T.Tbj.T.T.T.T.Tbd.wbraUbg.T.T.Tbjbjbjbjbia0.y.P.h.qboajaoamananaeaebwbfbfbfbf",
"bfbfbfbf#6#7#7#7#7#4#5bE.x.H.o.k.K#dbsbEbCaT.T.T.T.T.Tbi.Y.8.q.0aS.T.T.TbbaVaYa2.T.T.Tbj.f.SaUbg.T.Tbga0a0a0a0.L.d.n.q.c.w.L#9ajaianafafaealbwbfbfbf",
"bfbfbfbf#6#7#7#7#7#7#8.k.B.L.J.y.7.A.z.i#ia2.T.Tbi.T.T.T...F.o#aaX.T.T.TbmbDawaVbe.T.T.Tbq#iaTbg.T.Tbfb#bkbkbp.f.h.t.M.u.L.M#Zaiamafafaeaeagbwbfbfbf",
"bfbfbfbf#6#7a.a.a.a.#8.A.QbEbsbr.Ba1#i.d.#a7.T.Tbfbf.T.Tbl.N#g.laS.T.T.Tbm.f.zbka2.T.T.Tbk.zaUbg.T.T.T.T.T.T.Tbp.Gbr.F.q.P.8brarafafafaeaeagbxbwbfbf",
"bfbfbfbfa#a.a.a.aaa.a..E.P.0a1.i#a.J.6.Ka6bg.T.Ta5bb.T.Tbf.t#i#daS.T.T.Tbm.a.a.wa2.T.T.Tbk.raUbg.T.T.T.T.T.T.Tbp.M.p.r.o.R.QaQ#Zafaea.agag#9abbwbfbf",
"bfbfbfbfacaaaaaaaaaaafbs.P.xbD.R.z.s.I#faT.T.T.Ta6a2.T.T.T.o.O.DaY.T.T.Tbm.d.c.#a4.T.T.Tb..0aUbg.T.T.T.T.T.T.TbpbD.d#r.K.LbE#r.0aaa.ag#9#9#9#9bxbwbf",
"bfbfbfbfacaaaaaaaaafafbE.K#0.EbE.N.k.J.Oa2.T.Tbvbna2.T.T.T.f.w.HaS.T.T.Tbm.#.u.na4.T.T.Tbk#CaUbg.T.T.Tbibibibibp.Obr.F.JbEbEbE#Za.a.ag#9#9#8#8bxbwbf",
"bfbfbfbfbfadadadadadadar.s.K.Z.b.A.t#k.Ma5.T.T.Tbhbh.T.T.Ta0.P.IaS.T.T.Tbm.n.ib#bf.T.T.T.C.raUbg.T.TbgaXa6ba.D#a#Z.V.q.t.8.b.B#g#8#9#9#9#8#8#8bybxbf",
"bfbfbfbfbfadadaiaiaiaiai.N#C.B.q.l.U#nbkbg.T.T.T.T.T.T.T.Tbe#i.kaS.T.T.TaWbka6be.T.T.TbhbrbuaUbg.T.Tbga4b..z.J.a.n.O.s.X.lbubr.Q#8#9#8#8#8#5#5bybxbf",
"bfbfbfbfbfbfajajajajajaj#9#r.HbC.M.S.aaZ.T.T.T.T.T.T.T.T.Tbj.O.faS.T.T.T.T.T.T.T.T.T.Ta0.y.gaUbg.T.Tbga2a3.m.x#r.6.sbsbu.L.N.i.P#5#8#3#3#5#2#5bzbxbf",
"bfbfbfbfbfbfahajajajajajaj.p.K.gbE#abaa4.T.T.Ta4a7a7a5.T.T.Tb#.WaX.T.T.T.T.T.T.T.T.Tbh.C#a.ja8bg.T.Tbfa4a2#abE.Z.Z.l.P#e.kbEbsbD#3#3#3#5#Y#2#LbAbxbf",
"bfbfbfbfbfbf.2ajajajajaoapap.B.c.i#kaZbd.T.Tbjbr.#.zaX.T.T.Tba#iaX.T.T.T.T.T.T.T.Tbhb..7.y.SaUbg.T.Tbga2a2.Abs.k.E#r#e.H.k.L.I.O#3#3#Y#2#2#2#1bzbxbf",
"bfbfbfbfbfbf.4arajaoaoaoapaqaq.0.C.da2bdbebebb.K#f#DaSbebebebb.8aSbebebebebebebbba.a.K.f.b.7aUbdbebebba2a5.I.DbD#i.o.D.qbo.zbu#D#S#Q#U#U#R#RbBbzbxbf",
"bfbfbfbfbfbf.5.Paeaoapapaqaqaqaq.D.tbc.f.a.g.K.k.O.sbt.....abE.FaG.g.f..bq.gbt.K.o.8#d.f.nbE.f.na3a2a4a2a3brbDbD#ebE.s.R.t.F.h#Q#Q#Q#U#R#R#K#1bzbxbf",
"bfbfbfbfbfbfbf.4.XafapaqaqaqaqasasaH.0#C.wbE.R.m.D.c.tbs.n.JbE.S.D.p#C.p.u.#.C.y.s.YbEbD.w.V.Lb#a4a2a2a2bc.L.r#e.x.c#d.#.X.o#W#Q#Q#U#R#R#P#1bBbybwbf",
"bfbfbfbfbfbfbf.5###aagaqasasasasayasayaC.F.z.t.h.x#d.N.F.r.I.H.x.A.s.cbs.t.z.obr.u.e.o.s.K.ebka4a2a4a2a3#e.j.b.v.e.P.I.0.ubq#I#Q#U#U#R#R#K#1bAbxbfbf",
"bfbfbfbfbfbfbfbf.4.6bDaranasasasayayazaxazaH.I.U#i.K.A.d.u.F.X.o.A.r.y.r.m.g.f.e.h.i.BbE.Ba0aYa4a2a4a5.W.G.zbC.Q.NbE#Z#d.P#N#Q#Q#U#N#R#P#EbBbzbwbfbf",
"bfbfbfbfbfbfbfbfbf.4.0#d#fatasayayazazazazaDaDaJ.D.W.8ak.y.Z#a.v.wbu.A.F.a.I.Ubrbu.6..a0aXa4a4a4a2a2.Q.ubr.Hbsbr.n.p.L.M#D#I#Q#U#R#R#P#E#1bAbxbfbfbf",
"bfbfbfbfbfbfbfbfbf.3.4###i#gaBaxaxazazaDaDaDaIaIaIaIaJbt.K.P.I.B.6.y.r.O.DbEava9a0aSaSaYaYa4aYa4a8.8.z.8.q.u.V.e.S.j#e#Z#I#Q#U#N#R#P#E#1bBbybwbfbfbf",
"bfbfbfbfbfbfbfbfbfbf#..2##.j#i.DaHaAaAaDaFaIaIaIaIaIaIaLaLaLaLaLaOaOaOaOaRaOaRaVaSaSaYaYaYa4aYbk#f.i.ebr#g.S.l.O.x.KbE#I#J#U#N#R#P#E#EbBbzbxbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbf#..2.2.9aka1.MbnaHaKaFaFaLaFaIaIaLaLaLaOaOaOaOaOaOaRaRaVaVaSaVaYaYaYa6.Qbq.#.x.B#Z.x.k.l.z.d.z#I#J#J#N#R#P#L#EbBbzbxbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbf#h.4#h.RbD.8#g.z.xb#aKaFaFaFaLaLaLaLaOaOaOaRaRaRaVaVaRaVaSa8b#.L.n.D.g#d.MbC.H.K.L.LbE#P#I#U#N#N#R#P#E#EbBbzbxbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbf.5#h#h#h#k.Fbo.x.s.v.Q.qaNaHbaaJaMaPaMaPaPaTaMbaa6b.bs.W.d.A.lbE.M.n.x.B.o.j.c.S#P#I#G#J#N#N#R#K#E#1bBbzbxbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbwbx#m#h#h#h#h.7.Sak.l#a#a.c.VbC.p.qbq.R.9.P#C.H.Z.X#d.t.H.Q.P.A.F.j#Z.O.b.Q#x#I#Q#J#J#N#N#N#E#E#1bAbzbxbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbwbxbx#m#h#h#p#h#h.Y.sbq.H.SbDbD.X.E.H.M#Z.A.h.y.A.A.t.H.K.k.Lbs.q.y.A#N#G#J#J#J#N#N#N#L#E#1bBbAbybxbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbwbxbxbybz#m#p#p#p#p#p#p#u#k#k.Xbu.d.O.Abr.M.cbo.q.#.w.C.b.I#u#G#I#G#G#J#J#J#N#K#E#E#1#1bAbzbxbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbwbxbxbybzbz#E#p#p#p#p#p#p#w#w#w#w#p#v#v#p#v#v#w#w#w#w#w#w#G#G#G#J#J#K#E#E#1#1#1bBbzbybwbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbwbxbxbybybzbzbA#o#m#p#p#p#p#p#w#p#p#w#w#w#w#w#w#w#p#G#G#m#E#E#1#1#1bBbAbAbzbybwbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbxbxbxbybybzbzbAbBbAbBbBbBbB#1#1#1#1bB#1#1#1#1#o#1bB#1bBbBbAbzbzbybxbwbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf",
"bfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbwbxbxbxbybybzbzbzbzbAbzbAbAbAbAbAbAbAbAbAbzbzbzbybybxbxbwbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf"
};';
  return $buf
} 

sub init_bugmsg {
  my @bugmsg = ();
  push (@bugmsg, " Known Bug List:"); 
  push (@bugmsg, " - Error text doesnt change to good color when other text changed");
  return @bugmsg;
}
 
sub init_cmdmsg {

  my @cmdmsg = ();
  push (@cmdmsg, " ");
  push (@cmdmsg, " To speed up your work, try using the following shortcuts");
  push (@cmdmsg, " ");
  push (@cmdmsg, " Mouse ShortCuts:");
  push (@cmdmsg, " Using the control key and a left-click will allow the user to");
  push (@cmdmsg, " activate several mouse interface shortcuts/commands.");
  push (@cmdmsg, " ");
  push (@cmdmsg, " - In the Input Text <cntl>-<leftclick> on a section of text will");
  push (@cmdmsg, "   cause a break point to be set (appears as red on blue character).");
  push (@cmdmsg, "   The breakpoint will limit the amount of text that gets parsed to");
  push (@cmdmsg, "   be between the start of the document to the breakpoint.");
  push (@cmdmsg, " ");
  push (@cmdmsg, " - In the Input Text <cntl>-<middleclick> (<cntl>-<rightclick> on W9x");
  push (@cmdmsg, "   machines) will clear the break point.");
  push (@cmdmsg, " ");
  push (@cmdmsg, " - In the Rules Text <cntl>-<leftclick> hops the user to the first event");
  push (@cmdmsg, "   that occurred for that rule. Input text chunk is highlighted as appropriate.");
  push (@cmdmsg, "   For this action, the selected rule is highlighted in orange, and will ");
  push (@cmdmsg, "   highlight the begin and end of the rule (should the rule have children).");
  push (@cmdmsg, " ");
  push (@cmdmsg, " There are currently no mouse driven short cuts for the output text.");
  push (@cmdmsg, " ");
  push (@cmdmsg, " KeyPress ShortCuts: (use in any window)");
  push (@cmdmsg, " ");
  push (@cmdmsg, " Key\tValue ");
  push (@cmdmsg, " ---\t----- ");
  push (@cmdmsg, " Alt b\tStep backward 1 Rule.");
  push (@cmdmsg, " Alt B\tStep backward 10 Rules.");
  push (@cmdmsg, " Alt c\tClear the input text breakpoint.");
  push (@cmdmsg, " Alt f\tStep forward 1 Rule.");
  push (@cmdmsg, " Alt F\tStep forward 10 Rules.");
  push (@cmdmsg, " Alt n\tStep forward to next <halt\> Rule.");
  push (@cmdmsg, " Alt p\t(Re-)run the parser using current input text and rules.");
  push (@cmdmsg, " Alt v\tToggle the input chunk view.");
  push (@cmdmsg, " Alt q\tQuit.");
  push (@cmdmsg, " ");
  push (@cmdmsg, " (All special commands are activated by using Alt key, then the key) ");
  push (@cmdmsg, " ");
  
  return @cmdmsg;
}

sub init_aboutmsg {

  my @aboutmsg = ();
  push (@aboutmsg, " ");
  push (@aboutmsg, " ------------------------------------------------------------");
  push (@aboutmsg, " $toolname Version $version Date: $versdate");
  push (@aboutmsg, " ");
  push (@aboutmsg, " SYNOPSIS: ");
  push (@aboutmsg, "   $toolname is a perltk program to help with the ");
  push (@aboutmsg, " parsing of ASCII to XML text. It may be run in a graphical ");
  push (@aboutmsg, " mode (via -g flag) which features a WYSIWYG interface");
  push (@aboutmsg, " designed to ease the debugging of parsing rules. ");
  push (@aboutmsg, " ------------------------------------------------------------");
  push (@aboutmsg, " ");
  push (@aboutmsg, " ");
  push (@aboutmsg, " DESCRIPTION:");
  push (@aboutmsg, " ");
  push (@aboutmsg, "   This program allows you to parse arbitrarily formated ASCII");
  push (@aboutmsg, " text. To run the program, a set of XML-formated rules must be ");
  push (@aboutmsg, " specified (aka the \"rules\") as well as the ASCII text file to ");
  push (@aboutmsg, " be parsed (the \"input text\"). A successful run will produce XML ");
  push (@aboutmsg, " formated output as instructed by the rules used.");
  push (@aboutmsg, " ");
  push (@aboutmsg, " The parser rules are the heart of this system and understanding");
  push (@aboutmsg, " how they work to select text is critical to achieving success.");
  push (@aboutmsg, " The core concept of the rules is that they may be used to sub-");
  push (@aboutmsg, " divide input text into \"working chunks\" which may either be");
  push (@aboutmsg, " tagged in the output XML document or passed onto child/sibling");
  push (@aboutmsg, " rules. Any part of the working chunk which is not handled by the");
  push (@aboutmsg, " is passed to the next sibling rule.");
  push (@aboutmsg, " If there are no sibling rules left, the text is wrapped by");
  push (@aboutmsg, " an error tag and inserted in the output text.");
  push (@aboutmsg, " ");
  push (@aboutmsg, " The parser will run, converting input text to XML until it is ");
  push (@aboutmsg, " either finished (end of input text or rules) OR it encounters a ");
  push (@aboutmsg, " fatal error (the user may selectively set the error level to halt");
  push (@aboutmsg, " on).");
  push (@aboutmsg, " ");
  push (@aboutmsg, " The graphical mode of this program allows you to interactively run, ");
  push (@aboutmsg, " debug, edit, and re-run the parser any number of times. Output text, ");
  push (@aboutmsg, " edited input and rules text may be saved at any point. Additionally, ");
  push (@aboutmsg, " the user may choose to load new input/rules.");
  push (@aboutmsg, " ");
  push (@aboutmsg, " See the Help-Bugs menu for known bugs.");
  push (@aboutmsg, " ");
  push (@aboutmsg, " CREDITS:");
  push (@aboutmsg, " --------------\n ");
  push (@aboutmsg, " Concept:             Ed Shaya/Brian Thomas, Brian Holmes.");
  push (@aboutmsg, "                         (Raytheon ITSS/NASA-GSFC)");
  push (@aboutmsg, " GUI Design:          Brian Thomas, Ed Shaya and Brian Holmes");
  push (@aboutmsg, " Parser Design:       Brian Thomas, Ed Shaya, and Jim Blackwell");
  push (@aboutmsg, " Code Written by:     Brian Thomas and Ed Shaya");
  push (@aboutmsg, " ");
  
  return @aboutmsg;
}
