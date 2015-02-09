
# /** COPYRIGHT
#    WindowTools.pm Copyright (C) 2000 Brian Thomas,
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

# RCS: $Id: WindowTools.pm,v 1.2 1999/07/27 20:33:16 thomas Exp thomas $

package WindowTools;

use Tk;
use Tk::FileSelect;
use Tk::widgets qw(Button Label Radiobutton Entry Frame Menu Menubutton Text Dialog DialogBox);

# pragmas
use strict;
use vars qw ($VERSION);

$VERSION = 1.00;

# globals
my $font = '-adobe-times-medium-r-normal--18-*-*-*-*-*-*-*' ;

sub set_font { $font = @_; }

sub popup_msg_window {
  my ($main,@msg) = @_;
  my $popup_width = 100;

  if(!$main) { print "ERROR: msg popup needs main window\n"; return; }
  chomp @msg;

  my $size = $#msg > 40 ? 42 : $#msg+3;
  my $top= $main->Toplevel;
  $top->configure(title => "Popup Window");

  # frame
  my $popup = $top->Frame()->pack(side => 'top', expand => 1, fill => 'both');

  # widgets
  my $text = $popup->Text(height => $size-1, -font => $font );
  my $exit = $top->Button(text => "OK", -font => $font, command => sub {$top->destroy;});
  my $foo_height = $popup->Label();
  my $foo_width = $popup->Label();
  my $yscrollbar = $text->Scrollbar(-command => ['yview', $text]);

  #configure
  $text->configure(-yscrollcommand => ['set', $yscrollbar]);
  $text->configure(bg => 'black', fg => 'white');
  $exit->configure(bg => 'red', fg => 'black');
  $foo_height -> configure(height => $size);
  $foo_width -> configure(width => $popup_width);

  #pack it
  $foo_height->pack(side => 'left');
  $foo_width->pack(side => 'top');
  $text->pack(side => 'top', expand => 1, fill => 'both');
  $exit->pack(side => 'bottom');
  $yscrollbar->pack(-side=>'right', fill => 'y');

  for (@msg) {
    $text->insert('end', $_);
    $text->insert('end', "\n");
  }
}

# this dialog is mean to be temporary, it will
# disappear after a set amount of time
sub popup_notice {
  my ($main,$msg,$time,$title) = @_;
  if(!$main) { print "ERROR: popup dialog needs main window\n"; return; }
  if(!$title) { $title = "Popup Dialog"; }
  if(!$time) { $time = 1000; } # defaults to 1 sec 

  my $top = $main->Toplevel;
  $top->configure(title => $title);

  my $text = $top->Label(text => $msg, -font => $font )->pack;
  $text->configure(bg => 'black', fg => 'white');

  $top->after($time, sub { $top->destroy;});
}

# returns true if the user designates
# the yes answer. False return otherwise
sub popup_yes_no_dialog {
  my ($main,$msg,$title) = @_;

  if(!$main) { print "ERROR: Yes/No popup needs main window\n"; return; }
  if(!$title) { $title = "Yes/No Question"; }

  my @buttons;
  (@buttons) = (@buttons, "Yes");
  (@buttons) = (@buttons, "No");

  my $dialog = $main->Dialog(-title => $title, -font => $font, -text => $msg, -buttons => [@buttons]);
  my $selection = $dialog->Show;

  return $selection eq "Yes" ? 1 : 0;
}

sub popup_file_select {
  my ($main,$dir,$filter,$width,$height,$filelabel,$dirlabel,$filelistlabel,$dirlistlabel) = @_;
 
  $filter = "*" if !$filter;
  $dir = "." if !$dir;
 
  my $popup = $main->FileSelect(
                    -filter => "$filter",
                    -directory => $dir,
                    -takefocus => 1,
                    -font => $font 
                   );
 
  # optional configuration
  $popup->configure(-width => $width) if $width;
  $popup->configure(-height => $height) if $height;
  $popup->configure(-filelabel => $filelabel) if $filelabel;
  $popup->configure(-filelistlabel => $filelistlabel) if $filelistlabel;
  $popup->configure(-dirlabel => $dirlabel) if $dirlabel;
  $popup->configure(-dirlistlabel => $dirlistlabel) if $dirlistlabel;
 
  my $selection = $popup->Show;
  return $selection;
}

sub popup_entry {
  my ($main,$msg,$default_value,$title,$ignore_val) = @_;
 
  if(!$main) { print "ERROR: Entry popup needs main window\n"; return; }
  if(!$title) { $title = "Entry Popup"; }
 
  my @buttons;
  (@buttons) = (@buttons, "Ok");
  (@buttons) = (@buttons, "Ignore");
 
  my $dialog = $main->DialogBox(
                      -font => $font, 
                      -title => $title, 
                      -buttons => [@buttons]
                 );
  my $label = $dialog->add('Label', -text => $msg);
  my $entry = $dialog->add('Entry'); 
  $entry->insert(0.0,$default_value) if ($default_value);
  $label->pack;
  $entry->pack;

  my $selection = $dialog->Show;
 
  my $ret_val = $selection eq 'Ok' ? $entry->get : $ignore_val;
  return $ret_val;
}

1;
