#!/usr/bin/env perl
###############################################################################
# This is the main script for Module Versioning System
#
# Name              : $Name: MVS_5_22 $
###############################################################################

package Mvs;
require Exporter;
@ISA = qw(Exporter);
@EXPORT = qw(getUserName getBranchDeliverTagDir getModuleMergeFile getResponsiblesFile getModuleVarsFile getModuleDeliverTagFile getEditor readFromStdin
             getCVSRevision addFileToCVS removeCVSEntry checkValidComment askComment isExistingCVSBug
             checkCvsVersion
             checkCvsRoot checkMvsVersion checkMvsBranch cwdToWorkingDirRoot checkWorkingDir checkIsCheckouted createBranchNameFile getRepositoryVersion
             getListOfBranches isExistingBranch getListOfModules getCheckoutedModules getListOfAllModules isExistingModule wasExistingModule
             readBranchTagFile
             readVarsFile readVarsFileFromStream rGetModuleDir getModuleDependencies getModuleFiles rGetModuleShortDesc
             isExistingTag updateSymbolicLinks
             getSnapIdentifiers hasSnapFormat isExistingSnapIdentifier createSnapIdentifier
             getLastBuildIdentifier getBuildContent hasBuildFormat isExistingBuildIdentifier isBuildIdentifierFrom createBuildIdentifier
             cleanLogCache readTagFile addEntryToTagFile getDeliveredVersion
             exportModule checkoutModule updateModule checkModule diffModule rdiffModule extractBackwareChanges releaseModule
             getModuleFullHistory computeLastMergeTag getSnapFromBuild
             getBranchProperty
             getBranchFromTag checkAuthorizedMerge
             readRespFile getModuleResponsible mayModifyModule getUsersList addEntryToRespFile modifyRespFile
             getComponentDefinitionFile readComponentDefinitionFile readComponentDefinitionFileFromStream modifyEntryToComponentDefinitionFile modifyComponentDefinition
             getListOfAggragateModules getContainingComponent getListOfUsedComponents getComponentDependencies getComponentsDependencies
             getListOfComponents getListOfAllComponents
             isExistingComponent wasExistingComponent
             isExistingComponentBuildIdentifier getComponentBuildIdentifiers
             getComponentTagFile readComponentTagFile addEntryToComponentTagFile
             computeComponentLastMergeTag
             addEntryToBranchListFile readEntryFromBranchListFile
             VERSION
             MVSROOT_DIR HISTORY_DIR BRANCHES_LIST_FILE COMPONENTS_DIR COMPONENTS_LIST_FILE COMPONENTS_DEFINITIONS_DIR DUMMY_COMPONENT_DEF_FILE VERSION_FILE VARS_DIR DUMMY_VARS_FILE
             IMPORT_BRANCH
             START_TAG SNAP_TAG BUILD_TAG MERGE_TAG END_TAG
             BRANCH_STATE BRANCH_COMMENT BRANCH_MANDATORY_TICKET BRANCH_MERGE_FROM BRANCH_RESPONSIBLES
             MODULE_DIR MODULE_DEPS MODULE_EXPORT MODULE_SCRIPT
             COMP_AGGR COMP_COMMENT COMP_DEPS COMP_MERGE_FROM COMP_TOKENS
             ONERROR_RETURN ONERROR_EXIT ONERROR_PRINT
             getModuleArchs getComponentArchs getModuleSrc
             sortComponentsByDependentOrder getListOfComponentsByDependentOrder sendNotification 
            );

use strict;

# List of constants which may be use outside. The vars pragma changes
# nothing for the calling modules but allows to check that there's no
# mispelling error in the current one...
use vars qw (
            );

use constant VERSION => 5.23;

use File::Path;
use File::Find;
use File::Basename;
use Cwd;
use Time::Local;

use HTTP::Request::Common qw(POST);
use LWP::UserAgent;

# Some constants

my $TMP_DIR=$ENV{"TMPDIR"};
if (! $TMP_DIR) {
    $TMP_DIR="/tmp";
}
if (! -d $TMP_DIR) {
    # We may have some problems if we use an unexisting tmp directory
    print STDERR "Warning: Your TMPDIR environment variable is set to an unexisting directory ($TMP_DIR). Continuing with /tmp\n";
    $TMP_DIR="/tmp";
    $ENV{"TMPDIR"}=$TMP_DIR;
}
use constant BRANCH_NAME_FILE => ".branchName";
use constant MVSROOT_DIR => "MVSROOT";
use constant HISTORY_DIR => MVSROOT_DIR."/history";
use constant BRANCHES_DIR => HISTORY_DIR."/branches";
use constant BRANCHES_LIST_FILE => HISTORY_DIR."/branchesList";
use constant COMPONENTS_DIR => HISTORY_DIR."/components";
use constant COMPONENTS_LIST_FILE => HISTORY_DIR."/componentsList";
use constant COMPONENTS_DEFINITIONS_DIR => COMPONENTS_DIR."/definitions";
use constant DUMMY_COMPONENT_DEF_FILE => COMPONENTS_DEFINITIONS_DIR."/.dummy";
use constant VERSION_FILE => MVSROOT_DIR."/Version";
use constant CVS_VERSION_FILE => MVSROOT_DIR."/cvsVersion";
use constant VARS_DIR => "vars";
use constant DUMMY_VARS_FILE => VARS_DIR."/.dummy";
use constant CVS_PASSWD_FILE => "CVSROOT/passwd";
use constant TAGS_DIR => "tags";
my $SVNURL=$ENV{"SVNURL"};

# For debug
my $DROP_ERROR="2> /dev/null";
my $DROP_OUTPUT="> /dev/null";

# Maxximum number of try for the commit of a MVS administrative file
# (they may fails because of concurrent access)
use constant MAX_TRY => 2;

# CVS name of the administrator
use constant SUPER_USER_NAME => "itg";

# Name of the branch for external product import
use constant IMPORT_BRANCH => "IMPORT";

# Modules tags files tokens:
use constant START_TAG => "start";
use constant SNAP_TAG => "snap";
use constant BUILD_TAG => "build";
use constant MERGE_TAG => "merge";
use constant END_TAG => "end";

# Branch properties file tokens:
use constant BRANCH_STATE => "BRANCH_STATE";
use constant BRANCH_COMMENT => "BRANCH_COMMENT";
use constant BRANCH_MANDATORY_TICKET => "BRANCH_MANDATORY_TICKET";
use constant BRANCH_MERGE_FROM => "BRANCH_MERGE_FROM";
use constant BRANCH_RESPONSIBLES => "BRANCH_RESPONSIBLES";

# Module definitions file tokens:
use constant MODULE_DIR => "MODULE_DIR";
use constant MODULE_DEPS => "MODULE_DEPS";
use constant MODULE_EXPORT => "MODULE_EXPORT";
use constant MODULE_SCRIPT => "MODULE_SCRIPT";
use constant MODULE_ARCH => "MODULE_ARCH";
use constant MODULE_SRC => "MODULE_SRC";

# Component definitions file tokens:
use constant COMP_AGGR => "COMP_AGGR";
use constant COMP_COMMENT => "COMP_COMMENT";
use constant COMP_DEPS => "COMP_DEPS";
use constant COMP_MERGE_FROM => "COMP_MERGE_FROM";
use constant COMP_TOKENS => "COMP_AGGR COMP_COMMENT COMP_DEPS COMP_MERGE_FROM";

# Error mode: They are used by some functions to modify their
# behaviour in case of error
use constant ONERROR_RETURN => 0; # Return null value in case of error
use constant ONERROR_EXIT => 1;   # Exit in case of error
use constant ONERROR_PRINT => 2;  # Display error messages


# Some variables

# Cache for the tags files (we assume that they don't change during
# the execution of one mvs command)
# The key is "MOD branchName_moduleName" or "COMP branchName_componentName"
# or "BRANCH branchName_branchName"
my %logFilesCache_;

# Cache for the vars files (we assume that they don't change during
# the execution of one mvs command)
# The key is "identifier_moduleName" where identifier may be a branch name,
# a snap or a build identifier or the empty string for the localy available
# file
my %varsFilesCache_;

# Cache for the responsibles files (we assume that they don't change during
# the execution of one mvs command.
# The key is "branchName"
my %respFilesCache_;

# Directory part of the CVSROOT
my $cvsRootDir_;
# Cache for the list of existing users
my %usersList_;

# Cache for the branch properties files
# The key is "branchName"
my %branchPropertiesFilesCache_;

# Cache for the list of branches
my @listOfBranchesCache_;

# Cache for the list of all components
my @listOfAllComponentsCache_;

# Cache for the list of components for a specific identifier
my %listOfComponentsCache_;

# Cache for the component definition files
my %componentDefinitionFilesCache_;

# -q, -Q or nothing. It allows to set the verbose level for all CVS
# displaying something to the end user (not used for internal CVS commands)
my $cvsVerbose_ = "--quiet";

# We have to deal with some cvs bugs depending on versions.
# This variable is used to keep traces of them
my %cvsBugs_ = { };

# In order to get stdout and stderr outputs in the right order when the
# output of this command is a file or a pipe
$| = 1;


#########################
# Some accessors independant from CVS and the working environment
#########################


# Get the directory containing the module tag files
#
# @param branchName branch to use
#
# @return the dir name

sub getBranchDeliverTagDir {
    (my $branchName) =  @_;
    return BRANCHES_DIR."/$branchName";
}



# Get the name of the file used to store the merge information in the
# local working directory
#
# @param moduleName name of the module
#
# @return the file name

sub getModuleMergeFile {
    (my $moduleName) =  @_;
    return ".merge$moduleName";
}



# Get the name of file giving the list of module responsibles for a branch
#
# @param branchName the name of the branch
#
# @return the file name

sub getResponsiblesFile {
    (my $branchName) =  @_;
    return getBranchDeliverTagDir($branchName)."/responsibles.txt";
}



# Get the name of the file describing the module (usualy named the
# vars file).
#
# @param moduleName name of the module
#
# @return the file name

sub getModuleVarsFile {
    (my $moduleName) =  @_;
    return VARS_DIR."/$moduleName.vars";
}



# Get the name of the file containing the snap and build tags
# Lines of this file have the following format:
# [snapId]:[D for deliver snap]:
# [buildId]:[snapId]:
# M:[tagId]:[tagId]:
#
# @param branchName branch to use
# @param moduleName name of the module
#
# @return the file name

sub getModuleDeliverTagFile {
    (my $branchName, my $moduleName) =  @_;
    return getBranchDeliverTagDir($branchName)."/$moduleName.tags";
}



# Return the name of the editor to use for the snap comments
#
# @return name of the editor

sub getEditor {
    my $editor = $ENV{"MVSEDITOR"};
    unless ($editor) {
        $editor = $ENV{"CVSEDITOR"};
    }
    unless ($editor) {
        $editor = $ENV{"EDITOR"};
    }
    unless ($editor) {
        $editor = "vi";
    }
    return($editor);
}



# Read a line from STDIN.
# We have a problem with SSH: it closes STDIN and opens it again.
# It works fine when STDIN is really a tty but when we use a file
# (for instance in automatic tests with the << EOF syntax) we lose all the
# lines !
# This function is a workaround. When STDIN is a file, we read its
# content before starting on anything else. Calls to this function will
# then restore content of the "file"
# When STDIN is not a file or when the buffer is empty, read STDIN as usual.
# When an error occurs, die
#
# @return a string

my @stdinBuf;
if (-f STDIN) {
    @stdinBuf = <STDIN>;
}

sub readFromStdin {
    if ($#stdinBuf > -1) {
        my $resp = shift @stdinBuf;
        # Just to see the response on stdout like with a tty
        print "$resp";
        return($resp);
    }
    my $resp=<STDIN>;
    unless (defined $resp) {
        die "Unable to read from STDIN. Stopped";
    }
    return($resp);
}


# Return the current date. If the MVSDATE variable is set, this method
# uses its contents (YYYYMMDD) else it use the system time. The goal is
# to be able to replay automatic tests
#
# @return same list as the localtime method

sub getCurrentTime {
    my $mvsdate = $ENV{"MVSDATE"};
    my $mytime;
    if ($mvsdate) {
        (my $year, my $mon, my $mday) = ($mvsdate =~ /^([1-2][0-9][0-9][0-9])([0-1][0-9])([0-3][0-9])$/o) ;
        die "MVSDATE not in the expected format (YYYMMDD) : $mvsdate. Stopped" unless ($mon);
        $mon = $mon - 1;
        $mytime = timelocal(0, 1, 0, $mday, $mon, $year);
    }
    else {
        $mytime = time;
    }
    return(localtime($mytime));
}



# Check if a comment is a valid one
# This method displays an error on STDERR in case of not valid message
#
# @param branchName name of the branch (content of the comment is depending
#        on the branch because of the "mandatory ticket" property
# @param comment the comment which has to be checked
#
# @return 1 or 0

sub checkValidComment {
    (my $branchName, my $comment) = @_;
    if ($comment =~ /:/o) {
        print STDERR "':' not allowed in comment\n";
        return(0);
    }
    if ($comment =~ /\n/o) {
        print STDERR "'NewLine' not allowed in comment\n";
        return(0);
    }
    if (getBranchProperty($branchName, BRANCH_MANDATORY_TICKET)) {
        # Ticket identifiers start with a # and have at least 4 digits
        # unless ($comment =~ /#[0-9][0-9][0-9][0-9]+/o) { #old ticket number format
        unless ($comment =~ /#[A-Za-z][A-Za-z][A-Za-z\-]+[0-9]+/o) {
            print STDERR "You have to give a ticket identifier (#[A-Za-z][A-Za-z][A-Za-z\-]+[0-9]+ from ClearQuest or JIRA) for $branchName branch\n";
            return(0);
        }
    }
    return(1);
}



# Ask for a log to the user thanks to an editor. Check if it is in the
# right format
#
# @param branchName name of the branch
# @param defaultComment default comment to put into the file
#
# @return a list (code message) where
#         code = 0 if the message is OK (empty message are supported)
#         code = 1 if the user cancels the operation

sub askComment {
    (my $branchName, my $defaultComment) = @_;
    my $tmpFile = $TMP_DIR."/mvs$$";
    open(MESSFILE, ">$tmpFile") || die "Cannot open $tmpFile for writing";
    print MESSFILE "$defaultComment\n";
    print MESSFILE "MVS: ----------------------------------------------------------------------\n";
    print MESSFILE "MVS: Enter Log. Lines beginning with `MVS:' are removed automatically\n";
    print MESSFILE "MVS:            newline and ':' characters are not authorized\n";
    print MESSFILE "MVS: \n";
    if (getBranchProperty($branchName, BRANCH_MANDATORY_TICKET)) {
        print MESSFILE "MVS: Ticket identifier is mandatory for this branch. It should be give in the form:\n";
        print MESSFILE "MVS: #CCCNNNNNNNN where CCC is ClearQuest database name, NNNNNNNN is the identifier\n";
        print MESSFILE "MVS: \n";
    }
    print MESSFILE "MVS: ----------------------------------------------------------------------\n";
    close MESSFILE;
    my $editor = getEditor();
    my $comment;
    GET_MESS: while (! $comment) {
        if (system("$editor $tmpFile")) {
            print STDERR "$editor ends with error: $!\n";
        }
        open(MESSFILE, "$tmpFile");
        while(<MESSFILE>) {
            chomp;
            if ( /^MVS:/o || /^\s*$/ ) { # Skip lines starting with MVS:
                next;                    # and empty lines
            };
            if ($comment) {
                $comment = "\n$_";
            }
            else {
                $comment = $_;
            }
        }
        close MESSFILE;
        # If there's no message we ask for (and it is possible to continu
        # without message
        unless ($comment) {
            print STDERR "Log comment not specified\n";
            while (1) {
                print "Do you want to [a]bort, [c]ontinue or [e]dit the message again ? ";
                my $resp=readFromStdin();
                chop $resp;
                if ( $resp =~ /^[Aa]/o ) {
                    unlink($tmpFile);
                    return(1, "");
                }
                if ( $resp =~ /^[Cc]/o ) {
                    last GET_MESS;
                }
                if ( $resp =~ /^[Ee]/o ) {
                    next GET_MESS;
                }
            }
        }
        # Now we just check if the message is valid
        unless (checkValidComment($branchName, $comment)) {
            while (1) {
                print "Do you want to [a]bort or [e]dit the message again ? ";
                my $resp=readFromStdin();
                chop $resp;
                if ( $resp =~ /^[Aa]/o ) {
                    print STDERR "Comment saved in $tmpFile\n";
                    return(1, $comment)
                }
                if ( $resp =~ /^[Ee]/o ) {
                    $comment = "";
                    next GET_MESS;
                }
            }
        }
    }
    unlink($tmpFile);

    return(0, $comment);
}



#########################
# Functions checking environment and working directory
# They have to be called at least one time before starting on changes
#########################

# Check the environment of the user. If it detects an error it exits.
#
# @global cvsRootDir_ directory part of the CVSROOT variable

sub checkCvsRoot {

    # CVSROOT should be defined
    my $CVSROOT = $ENV{"SVNURL"};
    if ( $CVSROOT eq "" ) {
        print STDERR "SVNURL no set\n";
        exit 1;
    }
    if ( $CVSROOT =~ /^svn:(.*)/o ) {
        # Remove port number if present
        ($cvsRootDir_ = $2) =~ s@^[^/]*@@;
    }
    elsif ( $CVSROOT =~ m/^:ext:([^@]*)@([^:]*):(.*)/o ) {
        $cvsRootDir_ = $3;
    }
    # Just to be able to test responsible mechanism in the local mode
    elsif ( $CVSROOT =~ m@/@ ) {
        $cvsRootDir_ = $CVSROOT;
    }
    else {
        print STDERR "Not supported format for CVSROOT: $CVSROOT\n";
        exit(1);
    }
}



# Get the repository version
#
# @return the repository version

sub getRepositoryVersion {
    my $version;
    #print STDOUT "svn $cvsVerbose_ checkout  $SVNURL/".VERSION_FILE." |";
    open(VERS_FILE, "svn cat  $SVNURL/".VERSION_FILE." |") || die "$?\nStopped";
    while (<VERS_FILE>) {
        chomp;
        s/#.*$//;
        if ( m/VERSION\s*:\s*([.0-9]+)\s*$/o ) {
            $version = $1;
            last;
        }
    }
    close(VERS_FILE) || die "Cannot checkout ".VERSION_FILE.". Stopped";
    ($version) || die "Cannot find version in ".VERSION_FILE.". Stopped";
    return($version);
}



# The major version number of used MVS base should be the same as the current
# scripts version. Major version has to be incremented only if
# something changes in the MVS structure itself. For correction in a script
# only the minor number has to be modified

sub checkMvsVersion {
    my $version = getRepositoryVersion();
    my $baseMaj;
    {
        use integer;
        $baseMaj = $version + 0;
    }
    my $baseMin = $version - $baseMaj;

    my $scriptMaj;
    {
        use integer;
        $scriptMaj = VERSION + 0;
    }
    my $scriptMin = VERSION - $scriptMaj;
    unless ($baseMaj == $scriptMaj) {
        printf STDERR "Your MVS version (%.2f) doesn't match version of the MVS\nrepository (%.2f). Please update all your mvs scripts\n", VERSION, $version;
        print STDERR "Use \"mvs install\" to retrieve the right version\n";
        exit 1;
    }
    unless ($baseMin == $scriptMin) {
        printf STDERR "The version %.2f of MVS is now available\n", $version;
        print STDERR "Use \"mvs install\" to retrieve it\n";
    }
}



# Check CVS version and update the list of known bugs for this version.
#
# @global cvsBugs_ hash list of known CVS bugs
#
# @return the CVS version

sub checkCvsVersion {
    my $version=" 1.6.12";
    return($version);
}



# Check if a CVS bug is existing with teh current CVS version
#
# @param bugId identifier of the bug
#
# @return undef or the decription of the bug

sub isExistingCVSBug {
    (my $bugId) = @_;
    return($cvsBugs_{$bugId});
}



# Check if the MVSBRANCH environment variable is set, else exit.
# if an argument is provided and the MVSBRANCH environment variable is
# set verify that both values are the same, else warm the user.
#
# @param branchName the name of the branch (or empty)
#
# @return the branch name to use (after verifying that it is existing)

sub checkMvsBranch {
    (my $branchName) = @_;

    # MVSBRANCH should be definied or should be provided as argument
    # Check consistency if both are provided
    my $mvsBranch = $ENV{"MVSBRANCH"};
    if ( $mvsBranch eq "" ) {
        if ( $branchName eq "" ) {
            print STDERR "MVSBRANCH no set\n";
            exit 1;
        }
    }
    else {
        if ( $branchName eq "" ) {
            $branchName = $mvsBranch;
        }
        elsif ( not $branchName eq $mvsBranch ) {
            print STDERR "Warning: Specified branch ($branchName) isn't the same as your MVSBRANCH ($mvsBranch)\n";
        }
    }
    isExistingBranch($branchName, ONERROR_PRINT + ONERROR_EXIT);
    return($branchName);
}



# Create the .branchName file at the root of the working directory
# This file is used by MVS in order to know where is the root of the
# working directory and what is the current branch.
#
# @param branchName the name of the current branch

sub createBranchNameFile {
    (my $branchName) = @_;

    # If the file is already existing, we are sure thanks
    # to the checkWorkingDir method that it contains the same branch name
    unless (-f BRANCH_NAME_FILE) {
        open(BRANCHFILE, ">".BRANCH_NAME_FILE) or die "Can't create ".BRANCH_NAME_FILE.". Stopped";
        print BRANCHFILE "# This file is a MVS administration file.\n";
        print BRANCHFILE "# It may never be modified by hand.\n";
        print BRANCHFILE "branchName: $branchName\n";
        close BRANCHFILE;
    }
}



# If this method is called from a MVS working directory, it change dir
# to its root and return the value of the branch stored in the
# .branchName file.
# Else, it returns an empty string.
#
# @return a branchName or an empty string

sub cwdToWorkingDirRoot {

    # Get the current directory and search in the current path and
    # in all parents if there's a .branchName file.
    # It is a conveniant way to get the root of the working environment
    # so the user doesn' have to chdir before MVS use
    my $currentWorkDir = cwd();
    while ((! -f "$currentWorkDir/".BRANCH_NAME_FILE) && ($currentWorkDir ne "/")) {
        $currentWorkDir = dirname($currentWorkDir);
    }

    if (-f "$currentWorkDir/".BRANCH_NAME_FILE) {
        # The root of the working tree has been found. We change the
        # current directory before continuing
        chdir($currentWorkDir);

        # We check that the branch is the same one
        open(BRANCHFILE, "<".BRANCH_NAME_FILE) || die "$!";
        my $brName="";
        while (my $line = <BRANCHFILE>) {
            chomp $line;
            $line =~ s/#.*$//o;
            if ( $line =~ s/branchName:[ \t]*(.*)$/$1/o ) {
                ($brName = $line) =~ s/[ \t]*$//o;
                last;
            }
        }
        close BRANCHFILE;
        $brName eq "" && die "Unexpected ".BRANCH_NAME_FILE." format. Stopped";
        return $brName;
    }
    return "";
}



# Check if the working directory is based on a given branch.
# If not, it ask to the user if he wants to continue with the
# value of the .branchName file.
#
# @param branchName the name of the branch
# @param force indicates that the question should not be ask
# @param createWorkDir indicates that, if the current directory is not
#        a working dir but can be change to, the operation has to be
#        done.
#
# @return the branchName

sub checkWorkingDir {
    (my $branchName, my $force, my $createWorkDir) = @_;

    my $brName = cwdToWorkingDirRoot();
	
    # If we are in a CVS working directory, we compare the CVSROOT values
    #if ( -f VARS_DIR."/CVS/Root" ) {
    #    open(ROOT, VARS_DIR."/CVS/Root") || die "$!\nStopped";
    #    my $root = <ROOT>;
    #    chomp $root;
    #    close ROOT;
    #    unless ($root eq $ENV{"CVSROOT"}) {
    #        print STDERR "Your CVSROOT variable is set with $ENV{CVSROOT} but you local working directory seems to come from $root\n";
    #        print STDERR "Update your CVSROOT variable before trying again\n";
    #        exit(1);
    #    }
        # For unknown reason, the CVS directory loose write permission
        # Check it at try to restore them
    #    (undef, undef, my $mode, undef, undef, undef, undef, undef, undef, undef, undef, undef, undef) = stat VARS_DIR."/CVS";
    #    ($mode) || die "Cannot get permission of ".VARS_DIR."/CVS. Stopped";
    #    my $newMode = $mode | 0200;
    #    if ($mode != $newMode) {
    #        print STDERR "Warning: ".VARS_DIR."/CVS doesn't have the write permission for user\n";
    #        print STDERR "Please contact your MVS administrator\n";
    #        exit(1);
    #    }
    #}
	
	
    if ($brName) {
        # We are at the root of a MVS working directory
        # We check if the branches are matching
        if ( $brName ne $branchName ) {
            print STDERR "The branch name ($branchName) isn't the same as in your local working directory ($brName)\n";
            while (! $force) {
                print "Do you want to continue with $brName [y/n]: ";
                my $resp=readFromStdin();
                chop $resp;
                if ( $resp =~ /^[Yy]/o ) {
                    last;
                }
                if ( $resp =~ /^[Nn]/o ) {
                    print STDERR "Command aborted by user\n";
                    exit 1;
                }
            }
            $branchName = $brName;
            print STDERR "Continuing with $branchName\n";
        }
    }
	
	# no use for svn 
    elsif (-d VARS_DIR) {
        # We are not at the root of a development tree but there's a
        # vars directory. Perhaps the user exported something here.
        # It should be possible to do a working directory...
        my $localBranch;
        if (-d VARS_DIR."/.svn") {
            # Try to get the branch name from already checkouted vars
            open RESULT,"svn $cvsVerbose_ status ".VARS_DIR." |";
            while (<RESULT>) {
                chomp $_;
                if (/\s+Sticky Tag:\s*(\S*)\s+\(branch:.*\)/) {
                    if ($localBranch) {
                        unless ($localBranch eq $1) {
                            print STDERR "You're not in a MVS working directory and the ".VARS_DIR." directory contains files from $localBranch and $1 branches\n";
                            exit(1);
                        }
                    }
                    $localBranch = $1;
                }
                elsif (/\s+Sticky Tag:\s*\(none\)/) {
                    if ($localBranch) {
                        unless ($localBranch eq $1) {
                            print STDERR "You're not in a MVS working directory and the ".VARS_DIR." directory contains files from $localBranch and HEAD branches\n";
                            exit(1);
                        }
                    }
                    $localBranch = "HEAD";
                }
            }
            close(RESULT) || die "Unable to get status of ".VARS_DIR." directory. Stopped";
            die "Unable to find branch name from your local ".VARS_DIR." directory. Stopped" unless ($localBranch);
        }
        else {
            # No vars directory, we continu with the wanted branch
            $localBranch = $branchName;
        }
        print STDERR "You're not in a MVS working directory\n";
        unless ($createWorkDir) {
            exit 1;
        }
        print STDERR "Anyway, it seems possible to create one at this location";
        if ($localBranch eq $branchName) {
            print STDERR "\n";
        }
        else {
            print STDERR " but for the $localBranch branch\n";
        }
        while (! $force) {
            print "Do you want to continue [y/n]: ";
            my $resp=readFromStdin();
            chop $resp;
            if ( $resp =~ /^[Yy]/o ) {
                last;
            }
            if ( $resp =~ /^[Nn]/o ) {
                print STDERR "Command aborted by user\n";
                exit 1;
            }
        }
        $branchName = $localBranch;
        # CVS fails if the vars directory exists but not vars/CVS (and it
        # can occur if the user just did an export before).
        # So we checkout the dummy vars files using a temporary directory
        # an we move the CVS directory and the dummy file into the user
        # vars directory
        if ($createWorkDir && (! -d VARS_DIR."/.svn")) {
            my $newDir = "vars.new";
            while (-e $newDir) {
                $newDir = $newDir."x";
            }
            system("svn co -r $branchName -d $newDir ".DUMMY_VARS_FILE);
            ((-d "$newDir/CVS") && (-f "$newDir/".basename(DUMMY_VARS_FILE))) || die "Cannot checkout ".DUMMY_VARS_FILE." into $newDir. Stopped";
            rename("$newDir/CVS", VARS_DIR."/CVS") || die "$!. Stopped";
            rename("$newDir/".basename(DUMMY_VARS_FILE), DUMMY_VARS_FILE) || die "$!. Stopped";
            rmtree(($newDir), 0, 0);
            (-d $newDir) && die "Unable to remove $newDir directory. Stopped";
            (-d VARS_DIR."/CVS") || die "Unable to simulate ".VARS_DIR." checkout. Stopped";
            removeCVSEntry(DUMMY_VARS_FILE);
            createBranchNameFile($branchName);
        }
    }
    else {
        # We are not in a working directory and there's no vars directory,
        # we accept to continue only if the current directory is empty
        opendir DIR, ".";
        my @allDirs = grep !/^\.\.?$/, readdir DIR;
        closedir DIR;
        if ($#allDirs != -1) {
            print STDERR ". isn't the root of a working directory\n";
            print STDERR "You should be into an empty directory if you want to create a new working directory\n";
            exit 1;
        }
        createBranchNameFile($branchName);
    }
    return($branchName);
}



# Check if the module has been checkouted in the working directory.
# If not, it displays an error and exits.
#
# @param moduleName the name of the module
# @param errorMode indicates the expected behaviour in case of not checkouted
#        module
#
# @return 1 if the module is checkouted, 0 else

sub checkIsCheckouted {
    (my $moduleName, my $errorMode) = @_;

    my $moduleVarsFile = getModuleVarsFile($moduleName);
    unless (-f $moduleVarsFile) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "Module $moduleName not in your local working directory\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit 1;
        }
        return(0);
    }
    my $moduleDir = rGetModuleDir(undef, $moduleName, $errorMode);
    unless ($moduleDir) {
        return(0);
    }
    unless (-d $moduleDir) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "Inconsistency detected\n $moduleVarsFile is present but $moduleDir is not a directory\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit 1;
        }
        return(0);
    }
    unless (-d "$moduleDir/.svn") {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "$moduleName is not a checkouted module\n";
            print STDERR "Perhaps you did a \"mvs export $moduleName\" or you created the $moduleDir directory by hand\n";
            print STDERR "Use \"mvs release -nocheck $moduleName\" to remove it\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit 1;
        }
        return(0);
    }
    return(1);
}



#########################
# Access methods working with the CVS repository and/or the
# working directory
#########################

# Get the list of branches. This method is based on the content of
# the branchesList file.
#
# @global listOfBranchesCache_ cache for the list of existing branches
#         we are expecting that this list doesn't change during the
#         execution of a command
#
# @return the list of branches

sub getListOfBranches {
    if ( $#listOfBranchesCache_ != -1) {
        return @listOfBranchesCache_;
    }
    my $error = 0;
    my $errorMode = ONERROR_PRINT + ONERROR_EXIT;
    open(BRANCHLIST, "svn cat  -r HEAD $SVNURL".BRANCHES_LIST_FILE." |") || die "$?\nStopped";
    while(<BRANCHLIST>) {
        chomp;
        my $value;
        my %result;
        next if ( m/^\s*$/o );
        next if ( m/^#.*$/o );
        if ( m/^([^:]*):(.*)$/o ) {
            my $branchName = $1;
            if (exists $branchPropertiesFilesCache_{$branchName}) {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "Duplicated entry for $branchName branch\n";
                }
                $error = 1;
                next;
            }
            push @listOfBranchesCache_, $branchName;

            (my $state, my $ticket, my $mergeList, my $respList, my $comment) = split(/:/, $2);

            if ( $state =~ /close/io ) {
                $value = "close";
            }
            elsif ( $state =~ /open/io ) {
                $value = "open";
            }
            else {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "Invalid ".BRANCH_STATE." property in ".BRANCHES_LIST_FILE.": $state\n";
                }
                $error = 1;
            }
            $result{+BRANCH_STATE} = $value;

            if (( $ticket =~ /Yy/ ) || ( $ticket =~ /yes/i ) || ( $ticket eq "1")) {
                $value = 1;
            }
            elsif (( $ticket =~ /Nn/ ) || ( $ticket =~ /no/i ) || ( $ticket eq "0" )) {
                $value = 0;
            }
            else {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "Invalid ".BRANCH_MANDATORY_TICKET." property in ".BRANCHES_LIST_FILE.": $ticket\n";
                }
                $error = 1;
            }
            $result{+BRANCH_MANDATORY_TICKET} = $value;

            $result{+BRANCH_COMMENT} = $comment;

            my @branchList = split /\s*[,\s]\s*/, $mergeList;
            $result{+BRANCH_MERGE_FROM} = \@branchList;

            my @admList = split /\s*[,\s]\s*/, $respList;
            my %admHash;
            foreach (@admList) {
                $admHash{$_} = 1;
            }
            $result{+BRANCH_RESPONSIBLES} = \%admHash;

            $branchPropertiesFilesCache_{${branchName}} = \%result;
        }
        else {
            if ($errorMode & ONERROR_PRINT) {
                print STDERR "Unexpected line in ".BRANCHES_LIST_FILE.":\n$_\n";
            }
            $error = 1;
        }
    };

    close(BRANCHLIST) || die "Cannot checkout ".BRANCHES_LIST_FILE."\nStopped";

    if ($error) {
        # We stop only at the end of the read, it allows to display all
        # errors at the same time...
        if ($errorMode & ONERROR_EXIT) {
            exit(1);
        }
    }

    @listOfBranchesCache_ = sort(@listOfBranchesCache_);
    return @listOfBranchesCache_;
}



# Check if a branch is existing.
#
# @param branchName name of the branch
# @param errorMode indicates the expected behaviour in case of unexisting
#        branch
#
# @return 1 or 0

sub isExistingBranch {
    my ($branchName, my $errorMode) = @_;
    foreach ( getListOfBranches() ) {
       if ( $_ eq $branchName ) {
           return 1;
       }
    }
    if ($errorMode & ONERROR_PRINT) {
        print STDERR "Unknown branch $branchName\n";
    }
    if ($errorMode & ONERROR_EXIT) {
        exit(2);
    }
    return 0;
}



# Get the list of existing modules. This method is based on the
# content of the vars directory for the branch
#
# @param branchName the branch name or a build identifier for this branch
#
# @return the list of modules

sub getListOfModules {
    (my $identifier) = @_;
    my @allFiles;
    my $pattern;
    my $vars_url;
    (my $branch, undef) = hasSnapFormat($identifier);
    if ($branch) {
           $vars_url="$SVNURL/$branch/tags/$identifier/".VARS_DIR; 
    }
    unless($branch){
        ($branch, undef) = hasBuildFormat($identifier);
        if ($branch) {
           $vars_url="$SVNURL/$branch/tags/$identifier/".VARS_DIR;
        }
    }
    unless ($branch){ 
        if (isExistingBranch($identifier, 0)) {
           $vars_url="$SVNURL/$identifier/main/".VARS_DIR; 
        }
    } 
    
    #TODO comment the -r parameter for SVN, must be fixed 
    #open(FILELIST, "svn list $SVNURL/$identifier/main/".VARS_DIR."  |") || die "$?. Stopped";
    open(FILELIST, "svn list $vars_url  |") || die "$?. Stopped";
    #open(FILELIST, "svn list -r $identifier $SVNURL/$identifier/main/".VARS_DIR."  |") || die "$?. Stopped";
    $pattern = "(.+).vars";
    while (<FILELIST>) {
        chomp;
        if ( /^$pattern$/o ) {
            push @allFiles, $1;
        }
    }
    # The command may fails if the tag doesn't exist. It is a normal behavior
    # so we don't test the error code
    close(FILELIST);
    return @allFiles;
}



# Get the list of checkouted modules.
# At the same time we check if the directory is constistant. It means all
# checkouted modules should belong to the same branch and the directory
# must be available
#
# @return the list (may be empty)

sub getCheckoutedModules {
    my @result;
    # If there's no vars directory or no CVS directory into the vars one,
    # no module are checkouted
    unless ( -d VARS_DIR && -d VARS_DIR."/.svn" ) {
        return @result;
    }

    # At the same time, we check vars consistency...
    my $branchName;
    my $currentFile;
    open RESULT,"svn $cvsVerbose_ status ".VARS_DIR." |";
    while (<RESULT>) {
        chomp $_;
        if (/^File:\s*(\S*)\s*Status:/) {
            $currentFile = $1;
            (my $mod = $1) =~ s/\.vars//o;
            push @result, $mod;
        }
        elsif (/\s+Sticky Tag:\s*(\S*)\s+\(branch:.*\)/) {
            if ($branchName) {
                unless ($branchName eq $1) {
                    print STDERR VARS_DIR." directory contains files from $branchName branch but $currentFile belongs to $1 branch\n";
                    exit(1);
                }
            }
            $branchName = $1;
        }
        elsif (/\s+Sticky Tag:\s*\(none\)/) {
            if ($branchName) {
                unless ($branchName eq "HEAD") {
                    print STDERR "vars directory contains files from $branchName branch but $currentFile belongs to HEAD branch\n";
                    exit(1);
                }
            }
            $branchName = "HEAD";
        }
    }
    close(RESULT);

    # Check if the modules are really here...
    my $error = 0;
    foreach my $module (@result) {
        unless (checkIsCheckouted($module, ONERROR_PRINT)) {
            $error = 1;
        }
    }
    if ($error) {
        exit(1);
    }
    return @result;
}



# Display an elapsed time in the form hours minutes seconds
# For debug purpose
#
# @param timeInSec elasped time in seconds
# @param mess message to display before the elapsed time

sub displayElapsedTime {
    (my $timeInSec, my $mess) = @_;
    my $hours = int $timeInSec / 3600;
    my $min = int(($timeInSec - $hours * 3600) / 60);
    my $sec = $timeInSec - $hours * 3600 - $min * 60;
    my $str = sprintf "%02d h %02d m %02d s", ($hours, $min, $sec);
    print "$mess $str\n";
}



# Get the list of all existing modules whatever the branch.
# A first request ask for short diff between 1.1 and 1.2 revisions in
# vars file. We get:
# - Files modified in HEAD since the creation
#     File vars/<module>.vars changed from revision 1.1 to 1.2
# - File create in another branch and then merged in the HEAD
#     File vars/<module>.vars is new; current revision 1.2
# - File create in HEAD and never modified
#     File vars/<module>.vars is removed; not included in release tag 1.2
# - File create in HEAD and then removed (without change)
#     JFM ????
#
# A second request ask for short diff between 1.1 and 1.1.2.1 revisions in
# vars file. We get:
# - Files not branched from 1.1 (already available with the previous request)
#     File vars/<module>.vars is removed; not included in release tag 1.1.2.1
# - Files created in a branch (even when they have never been merged to HEAD)
#     File vars/<module>.vars is new; current revision 1.1.2.1
#
# With a hash list to remove duplicated entries, it looks like the faster way
# to find all existing modules:
# - It is more efficient than getting the list of branches and then the
#   list of modules
# - It allows to get the list of removed modules for a branch (these
#   modules don't appear when we use getListOfModules on the branch
#   because the .vars don't exist anymore)
#
# @return the list of modules

sub getListOfAllModules {
    # We use a hash list to prevent from duplicated entries
    my %modulesList;
    my $pattern = "(.*)\.vars";
    #open(FILELIST, "svn list -r HEAD $SVNURL/HEAD/main/".VARS_DIR." |") || die "$?. Stopped";
    #print STDOUT "svn diff -r HEAD $SVNURL".VARS_DIR."  2>/dev/null|";
    #open(FILELIST, "svn diff -r 1:HEAD $SVNURL".VARS_DIR." 2>/dev/null |") || die "$?. Stopped";
	foreach (getListOfBranches()) {
		open(FILELIST, "svn list -r HEAD $SVNURL/$_/main/".VARS_DIR." |") || die "$?. Stopped";
		while (<FILELIST>) {
			chomp;
			if ( /^$pattern/o ) {
				$modulesList{$1} = 1;
			}
		}
		close(FILELIST) || die "Cannot diff ".VARS_DIR.". Stopped";
	}
    #open(FILELIST, "svn rdiff -r 1 -r 1.1.2.1 -s ".VARS_DIR." 2>/dev/null |") || die "$?. Stopped";
    #while (<FILELIST>) {
    #    chomp;
    #    if ( /^$pattern/o ) {
    #        $modulesList{$1} = 1;
    #    }
    #}
    #close(FILELIST) || die "Cannot diff ".VARS_DIR.". Stopped";

    return (sort (keys %modulesList));
}



# Check if a module is existing.
#
# @param identifier name of the branch or build tag
# @param moduleName name of the module
# @param errorMode indicates the expected behaviour in case of unexisting
#        module
#
# @return 1 or 0

sub isExistingModule {
    (my $identifier, my $moduleName, my $errorMode) = @_;
# First solution, not very efficient because of the cost for the get of the
# list of modules
#    foreach (getListOfModules($identifier) ) {
#       if ( $_ eq $moduleName ) {
#           return 1;
#       }
#    }
    # If the vars file exists for this identifier, the module exists
    # Another advantage is to put the vars file into the cache. I guess if
    # we test existance of the module we will need the content of this file
    # soon
    #print STDOUT "isExistingModule Reading  $moduleName vars file for $identifier\n";
    if (readVarsFile($identifier, $moduleName, ONERROR_RETURN)) {
        return(1);
    }
    if ($errorMode == ONERROR_RETURN) {
        return(0);
    }

    # Not found, check which error message has to be displayed...
    if (hasSnapFormat($identifier) || hasBuildFormat($identifier)) {
        if ( $errorMode & ONERROR_PRINT ) {
            print STDERR "Module $moduleName not existing for $identifier\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(2);
        }
        else {
            return(0);
        }
    }

    #check the branch for output message
    if (isExistingBranch($identifier, $errorMode)) {
        if ( $errorMode & ONERROR_PRINT ) {
            print STDERR "Module $moduleName NOT existing in $identifier branch\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(2);
        }
        else {
            return(0);
        }
    }
    return 0;
}



# Check if a module was existing in a branch, i.e if its log file
# exists.
#
# @param branchName name of the branch
# @param moduleName name of the module
# @param errorMode indicates the expected behaviour in case of unexisting
#        module
#
# @return 1 or 0

sub wasExistingModule {
    (my $branchName, my $moduleName, my $errorMode) = @_;
    my @result = readTagFile($branchName, $moduleName);
    if ($#result ==  -1) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "Module $moduleName never existing in $branchName branch\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(2);
        }
        return(0);
    }
    else {
        return(1);
    }
}



# Get the content of the "<module>.vars" file for a specific version
# of a module.
#
# @param identifier a branch or a build identifier. If it is null, we assume
#        that the vars file is locally available
# @param moduleName the name of the module
# @param errorMode indicates the expected behaviour in case of error during the
#        read
#
# @return the vars definition hash list or null

sub readVarsFile {
    (my $identifier, my $moduleName, my $errorMode) = @_;
    if (exists $varsFilesCache_{"${identifier}_${moduleName}"}) {
        return %{$varsFilesCache_{"${identifier}_${moduleName}"}};
    }
    my $varsFile = getModuleVarsFile($moduleName);
    my %def;
    my $tmpDir;
    if ($identifier) {
	    my $dirName ;
            (my $branch, undef) = hasSnapFormat($identifier);
            unless ($branch) {
	            ($branch, undef) = hasBuildFormat($identifier);
	    }
	    unless ($branch) {
		# It should be a branch name
		$branch = $identifier;
            }
	    else {
	      # We don't complain if the tag is a build or a snap
	      # from another branch because it is a normal
	      # behaviour with components
	      #$branch =""; #$identifier;
            }
	    #print STDOUT "Mvs.pm readVarsFile svn cat   $SVNURL/$branch/main/$varsFile\n";	
        open(VARSFILE, "svn cat $SVNURL/$branch/main/$varsFile  $DROP_ERROR|") || die "Cannot checkout $varsFile. Stopped";
    }
    else {
        unless (open(VARSFILE, $varsFile)) {
            if ($errorMode & ONERROR_PRINT) {
                print STDERR "readVarsFile Cannot open $varsFile\n";
            }
            if ($errorMode & ONERROR_EXIT) {
                # We did the print (thanks to the die) for backward
                # compatibility
                die "Cannot open $varsFile. Stopped";
            }
            undef %def;
            return(%def);
        };
        # In case of local read, we have to display errors whatever
        # the mode
        $errorMode |= ONERROR_PRINT;
    }
    %def = readVarsFileFromStream(\*VARSFILE, $varsFile, $errorMode);
    # We don't check the error code here because svn command may fails if
    # the build identifier doesn't exist
    close(VARSFILE);
    $varsFilesCache_{"${identifier}_${moduleName}"} = \%def;
    if ($tmpDir) {
        rmtree(($tmpDir), 0, 0);
    }
    return(%def);
}



# Get the content of the "<module>.vars" file using an already opened stream.
#
# @param fileRef reference to the stream to use
# @param filename name of the file, it is only use to display error messages
# @param errorMode indicates the expected behaviour in case of error during the
#        read
#
# @return the vars content as a hash list with the following format:
#         MODULE_DIR => moduleDirectory
#         MODULE_DEPS => { moduleName => 1, ... }
#         MODULE_EXPORT => (fileName, ... )
#         MODULE_SCRIPT => fileName
#         MODULE_ARCH => archs
#         If an error occurs return a undefined hash list

sub readVarsFileFromStream {
    (my $fileRef, my $filename, my $errorMode) = @_;
    my %result;
    # If we detected an error, we just set this variable, it allows
    # to continue the parsing
    my $error = 0;
    my $prevLine;
    #print STDERR "Reading vars file : $filename\n";
    while (<$fileRef>) {
        chomp;
        # Remove comments
        s/#.*$//o;
        # Manage lines ending with a \ as uniq line
        if ( m/(.*)\\$/o ) {
            $prevLine = $prevLine.$1;
            next;
        }
        $_ = $prevLine.$_;
        $prevLine="";
        my $property;
        my $value;

        if ( m/^MODULE_DIR\s*:\s*(.*)$/o ) {
            $property = MODULE_DIR;
            ($value = $1) =~ s/\s*$//;
            unless ($value) {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "Null value for $property in $filename\n";
                }
                $error = 1;
            }
        }
        elsif ( m/^MODULE_DEPS\s*:\s*([A-Za-z0-9_\s]*)\s*$/o ) {
            $property = MODULE_DEPS;
            my @depsList = split /\s+/, $1;
            my %depsHash;
            foreach (@depsList) {
                $depsHash{$_} = 1;
            }
            $value = \%depsHash;
        }
        elsif ( m/^MODULE_EXPORT\s*:\s*(.*)\s*$/o ) {
            $property = MODULE_EXPORT;
            my @depsList = split /\s+/, $1;
            $value = \@depsList;
        }
        elsif ( m/^MODULE_SCRIPT\s*:\s*([^\s]+)/o ) {
            $property = MODULE_SCRIPT;
            $value = $1;
        }
        elsif ( m/^MODULE_ARCH\s*:\s*(.*)/o ) {
            if ($1) {
              $property = MODULE_ARCH;
              my @archs = split /\s+/,$1;
              $value = \@archs;
            }
        }
        elsif ( m/^MODULE_SRC\s*:\s*(.*)\s*$/o ) {
             $property = MODULE_SRC;
              my @depsList = split /\s+/, $1;
              $value = \@depsList;
	      #print STDOUT " $property in $filename is $value\n";
        }
        else {
            # No error, the vars may contain some other thing used by the
            # factory
        }
        if ($property) {
            if (exists $result{$property}) {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "Duplicated entry for $property in $filename\n";
                }
                $error = 1;
            }
            $result{$property} = $value;
        }
    }
    # Check if mandatory properties are defined
    for my $property (MODULE_DIR)  {
        unless (exists($result{$property})) {
            if ($errorMode & ONERROR_PRINT) {
                print STDERR "$property not found in $filename\n";
            }
            $error = 1;
        }
    }
    if ($error) {
        # We stop only at the end of the read, it allows to display all
        # errors at the same time...
        if ($errorMode & ONERROR_EXIT) {
            close($fileRef);
            exit(1);
        }
        undef(%result);
    }
    return %result;
}



# Get the base directory for module. It is based on the value of the
# MODULE_DIR variable in the module vars file. This method looks in the
# CVS repository.
#
# @param ident name of the branch or specific tag or null
# @param moduleName name of the module
# @param errorMode indicates the expected behaviour in case of error during the
#        read
#
# @return the directory name

sub rGetModuleDir {
    (my $ident, my $moduleName, my $errorMode) = @_;
    my %res = readVarsFile($ident, $moduleName, $errorMode);
    my $dirName = $res{+MODULE_DIR};
    unless ($dirName) {
       if ($errorMode & ONERROR_PRINT) {
           if ($ident) {
               print STDERR "No MODULE_DIR in $moduleName vars file for $ident identifier";
           }
           else {
               print STDERR "No MODULE_DIR in $moduleName vars file";
           }
       }
       if ($errorMode & ONERROR_EXIT) {
           exit(1);
       }
    }
    return $dirName;
}



# Get the module dependencies for a module
#
# @param identifier name of the branch or build identifier
# @param moduleName name of the module
# @param recur indicates that all dependencies must be returned and not only
#        the first level
#
# @return a hash list { module -> branch|tag }

sub getModuleDependencies {
    (my $identifier, my $moduleName, my $recur, my $errorMode) = @_;

    # Search if the module is part of a component
    my $componentName = getContainingComponent($identifier, $moduleName);

    # This hash list contains the build identifiers for the used components
    # and the current one
    my %usedComponents;
    my %modToComp;
    if ($componentName) {
        if ($recur) {
            %usedComponents = getComponentDependencies($identifier, $componentName, $recur);
        }
        else {
            %usedComponents = getListOfUsedComponents($identifier, $componentName);
        }
        $usedComponents{$componentName} = $identifier;

        # Build a new hash list moduleName -> componentName
        # Because we will need to search the module in a lot of cases it is more
        # efficient to use this kind of list
        my $nbErrors = 0;
        foreach my $comp (keys %usedComponents) {
            my %mods = getListOfAggragateModules($usedComponents{$comp}, $comp);
            foreach my $mod (keys %mods) {
                if (exists $modToComp{$mod}) {
                    if ($errorMode & ONERROR_PRINT) {
                        print STDERR "$mod module is existing into $comp!$usedComponents{$comp} and $modToComp{$mod}!$usedComponents{$modToComp{$mod}} components. Don't known which one has to be used.\n";
                    }
                    $nbErrors++;
                    next;
                }
                $modToComp{$mod} = $comp;
            }
        }
        if ($nbErrors) {
            if ($errorMode & ONERROR_EXIT) {
                exit(1);
            }
            return;
        }
    }
    else {
        $usedComponents{$componentName} = $identifier;
        foreach (getListOfModules($identifier)) {
            $modToComp{$_} = $componentName;
        }
    }

    my @modList = ($moduleName);
    my %result = ($moduleName => $identifier);
    my $nbErrors = 0;
    while ($#modList >= 0) {
        my $modName = pop @modList;
        my %varsDef = readVarsFile($result{$modName}, $modName, $errorMode & (ONERROR_PRINT + ONERROR_RETURN));
        unless (%varsDef) {
            $nbErrors++;
            next;
        }

        # If there's no dependency, we have nothing to do...
        unless ($varsDef{+MODULE_DEPS}) {
            next;
        }
        my $searchTag = $result{$modName};
        foreach my $module (sort (keys %{$varsDef{+MODULE_DEPS}})) {
            # Search the containing component and then its tags
            unless (exists $modToComp{$module}) {
                # Because this method is used by deps2dot to get dependencies
                # of all modules in the "reverse" mode. We have to take into
                # account modules which are not in a component (for one
                # reason or another) and then not to stop if a dependency
                # is wrong
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "$modName module is depending on $module but there's no way to find it\n";
                }
                $nbErrors++;
                next;
            }
            my $myComp = $modToComp{$module};
            my $myTag = $usedComponents{$myComp};
            # results contains the list of vars already explored
            if (exists $result{$module}) {
                unless ($result{$module} eq $myTag) {
                    if ($errorMode & ONERROR_PRINT) {
                        print STDERR "Two versions of $module module found ($result{$module} and $myTag). Don't know which one has to be used\n";
                    }
                    $nbErrors++;
                }
                next;
            }
            if ($recur) {
                push @modList, $module;
            }
            $result{$module} = $myTag;
        }
    }
    if ($nbErrors > 0) {
        if ($errorMode & ONERROR_EXIT) {
            exit(1);
        }
    }

    # Remove the initial module from the list !
    delete $result{$moduleName};
    return %result
}



# Get the module archs for a module
#
# @param identifier name of the branch or build identifier
# @param moduleName name of the module
#
# @return the list of archs

sub getModuleArchs {
    (my $identifier, my $moduleName, my $errorMode) = @_;
    
    my %varsDef = readVarsFile($identifier, $moduleName, $errorMode);
    my $archs = $varsDef{MODULE_ARCH};
    if($archs) {
    	return @{$archs};
    } else {
    	return ();
    }
}

# Get the module archs for a module
#
# @param identifier name of the branch or build identifier
# @param moduleName name of the module
#
# @return the list of archs

sub getModuleSrc {
   (my $identifier, my $moduleName, my $errorMode) = @_;

   my %varsDef = readVarsFile($identifier, $moduleName, $errorMode);
   #print STDOUT "Read Module Source $moduleName\n";
   my $module_src = $varsDef{MODULE_SRC};
   if($module_src) {
        return @{$module_src};
   } else {
        return ();
   }
}


# Internal function used by getModuleFiles in order to get the list of files
# for a module.
# It is called by "find" for each files/directory and just adds the
# file name in the fileList variable
#
# @global fileList list of module files.

sub pushFileInFileList {
  if ( -d and (m@/.svn$@ || $_ eq ".svn") ) {
      $File::Find::prune = 1;
  }
  elsif ( -f ) {
      (basename($_) =~ m/^\.#/o) && return;        # Temporary files for merge
      m/~$/o && return;          # Back files with some editors
      m/\.bak$/io && return;      # Back files with some editors
      m/\.sav$/io && return;      # Because I don't like .sav extension
      m/\.old$/io && return;      # Why do you want to take care of old files
      m/\.class$/o && return;    # At this time there's no class files in CVS
      push @::fileList, $File::Find::name;
  }
}



# Returns the list of files for a module (without the var file).
#
# @param moduleName name of the module
#
# @return the list of files

sub getModuleFiles {
    (my $moduleName) = @_;
    my $moduleDir = rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
    unless(-d $moduleDir) {
        die "$moduleDir not a directory";
    }
    local @::fileList;
    find { wanted => \&pushFileInFileList, no_chdir => 1 }, $moduleDir;
    return @::fileList;
}



# Returns the minimum list of files/directories to use as cvs
# argument to be able to tag all files of a module (i.e. files of the
# module plus the MVS administration files for this module).
# Because the result of this method may be used for a "cvs tag", we
# put the vars file before the directory name. The reason is that on
# empty module, if we put the directory first we get an error because
# of unexisting tag...
#
# @param ident name of the branch or specific tag or null
# @param moduleName name of the module
#
# @return the list of files

sub rGetModuleShortDesc {
    (my $ident, my $moduleName) = @_;
    return (getModuleVarsFile($moduleName), rGetModuleDir($ident, $moduleName, ONERROR_PRINT | ONERROR_EXIT));
}



# Get the CVS revision of a list of files
#
# @param ident CVS tag or branch name
# @param filesRef reference to a list of file names (or directories)
#
# @return the a hash list filename -> revision (x.y.z)

sub getCVSRevision {
    (my $ident, my $filesRef) = @_;
    my %result;
    my @files = @{$filesRef};
    # Not possible to use a simple open because the filenames may contain
    # shell meta-characters (like $, &) or blanks
    my $pid = open(RES, "-|");
    defined($pid) || die "Cannot fork. $!. Stopped at";
    unless ($pid) {
        # We are in the child, we want to read STDERR only (STDOUT is
        # not needed)
        # Redirect STDERR to STDOUT and force flush
        select STDERR;
        $! = 1;
        open SAVE_ERR, ">&STDERR";
        open STDERR, ">&STDOUT";
        select STDERR; $! = 1;

        # Redirect STDOUT to null
        select STDOUT;
        $! = 1;
        open SAVE_OUT, ">&STDOUT";
        open STDOUT, ">", "/dev/null";
        select STDOUT; $! = 1;

        if (isExistingCVSBug("pOption")) {
            my $tmpDir = $TMP_DIR."/mvs.gcvsr.$$";
            mkpath(($tmpDir), 0, 0755) || die "Can't create $tmpDir. Stopped";
            # If the tag is existing this command wil add it to teh val-tags
            # file. The next -p command should not assert
            system("cd $tmpDir; svn checkout -r $ident ".VARS_DIR." $DROP_OUTPUT $DROP_ERROR");
            rmtree(($tmpDir), 0, 0);
        }
        # Exec command
        exec("svn", "co","-p", "-r", $ident, @files);
        # Should never occur. Write error message on save handle of STDERR
        print SAVE_ERR "Unable to exec svn co -p -r $ident @files. $!\n";
        exit(1);
    }

    # We are in the father, read result
    my $file;
    while (<RES>) {
        chomp;
        if ( /^Checking out (.*)/ ) {
            $file = $1;
        }
        if ( /^VERS: ([0-9\.]+)/ ) {
            ($file) || die "Version without file: $_.\nStopped";
            (exists $result{$file}) && die "To much version for $file. Stopped";
            $result{$file} = $1;
        }
    }
    close(RES) || die "Cannot check out @files: $!\nStopped";
    return(%result);
}

sub getSVNRevision {
    (my $ident, my $filesRef) = @_;
    my %result;

	return (%result);
}



# Add a file or a directory into CVS repository. All intermediate
# directories are added too
#
# @param branchName name of the branch
# @param fullPath full path of the file to add to the CVS repository
# @param tmpDir temporary directory where the file should exist (else an
#        empty version is created)

sub addFileToCVS {
    (my $branchName, my $fullPath, my $tmpDir) = @_;
    my $lastName = basename($fullPath);
    my $dirName = dirname($fullPath);
    my $CVSROOT = $ENV{"SVNURL"};
    mkpath(("$tmpDir/$dirName"), 0, 0755);
    # Build the list of all directories
    my @dirList;
    while (($dirName ne ".") && ($dirName)) {
        push @dirList, basename($dirName);
        $dirName = dirname($dirName);
    }

    # If there's no CVS directory at the top level (i.e. in the tmp
    # directory) and at the first level (in case of directory checkout,
    # there's no CVS at the top level) we have to checkout the root first
    unless (-d "$tmpDir/.svn" || -d "$tmpDir/$dirList[$#dirList]/.svn") {
        if ($branchName eq "HEAD") {
            system("cd $tmpDir; svn $cvsVerbose_ checkout $CVSROOT/$fullPath");
        }
        else {
            system("cd $tmpDir; svn $cvsVerbose_ checkout -r $branchName $CVSROOT/$fullPath");
        }
    }

    # Loop on directories and add them to CVS if it is not already done
    $dirName = "$tmpDir";
    foreach (reverse @dirList) {
        die ("$dirName/$_ not a directory. Stopped") unless (-d "$dirName/$_");
        unless (-d "$dirName/$_/.svn") {
            system("cd $dirName; svn $cvsVerbose_ add $_ $DROP_OUTPUT $DROP_ERROR");
        }
        $dirName = "$dirName/$_";
    }

    # Now add the file (if it doesn't exist, we just create an empty one)
    unless (-e "$tmpDir/$fullPath") {
        open(FILE, ">$tmpDir/$fullPath") || die $!;
        close(FILE);
    }
    unless (-d "$dirName/$lastName/.svn") {
        system("cd $dirName; svn $cvsVerbose_ add $lastName $DROP_OUTPUT $DROP_ERROR");
    }
}



# Remove a file from the working directory and remove its
# entry into CVS files
#
# @param fileName the name of the file

sub removeCVSEntry {
    (my $fileName) = @_;

    unlink($fileName);
    (-e $fileName) && die "$fileName still existing. Stopped";
    my $entryFile = dirname($fileName)."/CVS/Entries";
    my $baseName = basename($fileName);
    # The remove has only to be done if the file exist, so it
    # allows to release an exported module
    if (-f $entryFile) {
        open(ENTRIES, "$entryFile") || die "Cannot open $entryFile. Stopped";
        open(NEWENTRIES, ">$entryFile.new") || die "Cannot open $entryFile.new. Stopped";
        my $found = 0;
        while ( <ENTRIES> ) {
            chomp;
            if ( m@^/$baseName/@ ) {
                $found = 1;
            }
            else {
                print NEWENTRIES "$_\n";
            }
        }
        close ENTRIES;
        close NEWENTRIES;
        # We want to do something only if the file has really been
        # modified
        if ($found) {
            rename("$entryFile", "$entryFile.old") || die "Cannot rename $entryFile. Stopped";
            rename("$entryFile.new", "$entryFile") || die "Cannot rename $entryFile.new. Stopped";
            # Because Entries file is a very important file, we check if it is
            # existing before continuing
            (-f $entryFile) || die "$entryFile not a file. Stopped";
            unlink("$entryFile.old");
        }
        else {
            unlink("$entryFile.new");
        }
    }
}



#########################
# Methods dealing with snaps
#########################

# Returns the list of snap identifiers for the module in a given branch
# This list is based on the content of the <module>.tag file.
#
# @param branchName name of the branch
# @param moduleName name of the module
#
# @return a hash list of snaps (snapId -> 1)

sub getSnapIdentifiers {
    (my $branchName, my $moduleName) = @_;
    my %snapList;
    foreach my $lineRef ( readTagFile($branchName, $moduleName) ) {
        if ( $lineRef->[0] eq SNAP_TAG ) {
            $snapList{$lineRef->[1]} = 1;
        }
    }
    return %snapList;
}



# Check if the identifier looks like a snap identifier. It doesn't means
# that the snap exists !
#
# @param snapId the snap identifier to test
#
# @return a list (branchName, moduleName) if it is a snap identifier else null.

sub hasSnapFormat {
    (my $snapId) = @_;
    if ( $snapId =~ m/^([^_]+)_([^_]+)_[1-9][0-9][0-9][0-9]W[0-5][0-9][a-z]*$/o ) {
	    #print "Mvs.pm hasSnapFormat found branch $2 and module $1 in snap id $snapId.\n";
        return ($2, $1);
    }
    else {
        return(0);
    }
}



# Test if a snap identifier exists
#
# @param branchName name of the branch
# @param moduleName name of the module
# @param snapId the snap identifier
# @param errorMode indicates the expected behaviour in case of unexisting snap
#
# @return 0 or 1

sub isExistingSnapIdentifier {
    (my $branchName, my $moduleName, my $snapId, my $errorMode) = @_;
    my %snapsHash = getSnapIdentifiers($branchName, $moduleName);
    if ($snapsHash{$snapId}) {
        return(1);
    }
    if ( $errorMode & ONERROR_PRINT ) {
        isExistingModule($branchName, $moduleName, ONERROR_PRINT);
        print STDERR "$snapId not a $moduleName snap identifier\n";
    }
    if ( $errorMode & ONERROR_EXIT ) {
	print STDOUT "Snap $snapId is NOT Found in $branchName branch.\n";
        exit(2);
    }
    return(0);
}



# Compute the week number for a given date.
# Week starts on Monday
# The last/first week of the year belongs to the year with the highest number
# of day in this week.
#
# @param year year in the 4 digits format
# @param month month number (0 = january)
# @param mday day of the month (1..31)
#
# @return (year, week)

sub weekOfTheYear {
    (my $year, my $month, my $mday) = @_;
    my $nbDays = (localtime(timelocal(0, 1, 0, $mday, $month, $year)))[7];
    # Get the day of the week for the 01/01 of the year. We wants 0 for Monday,
    # for Tuesday...
    my $fistDayOfTheYear = (localtime(timelocal(0, 1, 0, 1, 0, $year)))[6] - 1;
    $fistDayOfTheYear %= 7;
    # First day of the year is Friday, Saturday or Sunday : it is in fact in
    # the last week of the previous year
    if ($fistDayOfTheYear > 3) {
        # Remove these days from the number of days in the year
        $nbDays -= (7 - $fistDayOfTheYear);
    }
    else {
        # Add the remaining days of the previous year
        $nbDays += $fistDayOfTheYear;
    }
    my $week;
    if ($nbDays < 0) {
        # The firsts day of the year are in fact in the last week
        # of the previous year. It can be the week 52 or 53...
        $week = weekOfTheYear($year-1, 11, 31);
        $year += 1899;
    }
    elsif ($nbDays >= 364) {
        # If last day of the year is Monday to Wednesday, it is in the
        # first week of the next year
        my $lastDayOfTheYear = (localtime(timelocal(0, 1, 0, 31, 11, $year)))[6] - 1;
        $lastDayOfTheYear %= 7;
        if ($lastDayOfTheYear < 3) {
            $week = 1;
            $year += 1901;
        }
        else {
            # modulo 54 is only here to get an integer...
            $week = ($nbDays / 7) % 54 +1;
            $year += 1900;
        }
    }
    else
    {
        # modulo 54 is only here to get an integer...
        $week = ($nbDays / 7) % 54 +1;
        $year += 1900;
    }
    return ($year, $week);
}




# Builds a snap identifier.
# In order keep some compatibility with the previous mechanism
# snap identifiers have the following format:
# {moduleName}_{branchName}_{year}W{weekNumber}[a-z]
#
# @param branchName name of the branch
# @param moduleName name of the module
#
# @return the new snap identifier

sub createSnapIdentifier {
    (my $branchName, my $moduleName) = @_;
    (undef, undef, undef, my $mday, my $month, my $year, undef, undef, undef) = getCurrentTime();
    ($year, my $week) = weekOfTheYear($year, $month, $mday);

    my $tag = sprintf "%s_%s_%sW%02d", ($moduleName, $branchName, $year, $week);
    # If a snap has already be done during this week, we add a 'a',
    # 'b', ... until we find an unexisting tag
    my %snapsHash = getSnapIdentifiers($branchName, $moduleName);
    my $ext='';
    while ($snapsHash{"$tag$ext"}) {
        # It is not possible to rely on ++ after the z because it returns
        # aa and breaks the alphabetical order...
        my $oldExt = $ext;
        ++$ext;
        if (($oldExt gt $ext) || ($oldExt eq '')) {
          $ext = "${oldExt}a";
        }
    };
    return("$tag$ext");
}



#########################
# Methods dealing with builds
#########################

# Returns the list of all build identifiers in a given branch i.e.
# list of the branch build identifier (if any) plus list of the components
# build identifiers if (any)
#
# @param branchName name of the branch
#
# @return the list of builds in chronological order

sub getAllBuildIdentifiers {
    (my $branchName) = @_;

    # We have to do a merge of the branch build identifiers and of the
    # component build identifiers. We should not have duplicated entries
    my @result = getBranchBuildIdentifiers($branchName);
    for my $comp (getListOfComponents($branchName)) {
        push @result, getComponentBuildIdentifiers($branchName, $comp);
    }
    return(sort(@result));
}



# Return the couple branch/component corresponding to a build identifier.
# The component name may be undefined if the build is a buld of a branch
# without component.
#
# @param buildId the build identifier
# @param errorMode indicates the expected behaviour in case of unexisting build
#
# @return a list (branchName, componentName) or undef

sub isBuildIdentifierFrom {
    (my $buildId, my $errorMode) = @_;

    (my $branch, undef) = hasBuildFormat($buildId);
    unless ($branch) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "$buildId is not a build identifier\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(1);
        }
        return;
    }
    # Check first if it is a branch build identifier
    my @result = getBranchBuildIdentifiers($branch);
    foreach (getBranchBuildIdentifiers($branch)) {
        if ($_ eq $buildId) {
            return($branch, undef);
        }
    }
    # No check if it is a component build identifier
    for my $comp (getListOfComponents($branch)) {
        foreach (getComponentBuildIdentifiers($branch, $comp)) {
            if ($_ eq $buildId) {
                return($branch, $comp);
            }
        }
    }
    if ($errorMode & ONERROR_PRINT) {
        print STDERR "$buildId not a $branch build identifier\n";
    }
    if ($errorMode & ONERROR_EXIT) {
        exit(1);
    }
    return;
}



# Returns the list of all build identifiers for a given branch
#
# @param branchName name of the branch
#
# @return the list of builds in chronological order

sub getBranchBuildIdentifiers {
    (my $branchName) = @_;
    my @buildList;
    foreach my $lineRef ( readBranchTagFile($branchName) ) {
        my $tag = $lineRef->[0];
        if ( $tag eq BUILD_TAG ) {
            push @buildList, $lineRef->[1];
        }
    }
    return @buildList;
}



# Get the content of the <branch>.log file.
# This method just open the file and call readComponentTagFileFromStream with
# the resulting stream
#
# @param branchName name of the branch
#
# @return a list of listes (see readComponentTagFileFromStream comment)

sub readBranchTagFile {
    (my $branchName) = @_;
    if (exists $logFilesCache_{"BRANCH ${branchName}_${branchName}"}) {
        return @{$logFilesCache_{"BRANCH ${branchName}_${branchName}"}};
    }
    # It is not possible to have a module or a component with the same
    # name...
    if (exists $logFilesCache_{"MOD ${branchName}_${branchName}"}) {
        return(()) ;
    }
    if (exists $logFilesCache_{"COMP ${branchName}_${branchName}"}) {
        return(()) ;
    }
    my $tagsFile = getComponentTagFile($branchName, $branchName);
    open(BRANCHTAGS, "svn cat  $SVNURL/$tagsFile  |");
    my @result = readComponentTagFileFromStream($branchName, $branchName, \*BRANCHTAGS);
    close BRANCHTAGS;
    if ($#result > -1) {
        $logFilesCache_{"BRANCH ${branchName}_${branchName}"} = [ @result ];
    }
    return @result;
}



# Returns the last build identifier in a given branch for a given module or
# component.
# The last build identifier may differs from one module to another because
# of the component: if the module is not part of the latter built component,
# it doesn't have the last available build into the branch.
#
# WARNING : Because os ascending compatiblity (before MVS 3.00 this
# method was defined into the build command) we have take care of the
# behaviour when only the branchName is specified: The method has to
# return the last build identifier of the branch without taking into
# account component or null not build has been done in the branch
#
# @param branchName name of the branch
# @param modOrCompName name of the module or the component. May be null, for
#        the last build in the branch whatever the module...
# @param recur indicates that if no build have been done into the branch,
#        the build used for the opening of the branch has to be used
# @param errorMode indicates the expected behaviour in case of unexisting tag
#
# @return the last build identifier

sub getLastBuildIdentifier {
    (my $branchName, my $modOrCompName, my $recur, my $errorMode) = @_;

    if ($modOrCompName) {
        # If it is a component returns its last build

        if (wasExistingComponent($branchName, $modOrCompName, ONERROR_RETURN)) {
            return(getComponentLastBuildIdentifier($branchName, $modOrCompName, $recur, $errorMode));
        }

        # If the module is part of a component, its last build identifier
        # is the component last build identifier (if the component has been
        # built)
        my $componentName = getContainingComponent($branchName, $modOrCompName);
        if ($componentName) {
            my $lastBuild = getComponentLastBuildIdentifier($branchName, $componentName, $recur, $errorMode);
            if ($lastBuild) {
                return($lastBuild);
            }
        }
    }
    # Search the last build in the branch. We parse the <branch>.log file
    # instead of using getBranchBuildIdentifiers because we want to catch the
    # build used for the opening of the branch
    my $lastBuild;
    foreach my $lineRef ( readBranchTagFile($branchName, $branchName) ) {
        my $tag = $lineRef->[0];
        if ( $recur && ($tag eq START_TAG)) {
            $lastBuild = $lineRef->[2];
        }
        elsif ( $tag eq BUILD_TAG ) {
            $lastBuild = $lineRef->[1];
        }
    }
    unless ($lastBuild) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "No build has been done in $branchName branch\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(1);
        }
    }
    return($lastBuild);
}



# Get the list of all identifiers used for a build.
#
# @param buildId the build identifier
# @param snapMode indicates that if the build has been done from another
#        build identifier, the initial snap identifier has to be find
#
# @return a list ("module:snapId" "module:snapId" ...)

sub getBuildContent {
    (my $buildId, my $snapMode) = @_;
    (my $branchName, undef) = hasBuildFormat($buildId);
    die "Unable to find a branch name from $buildId. Stopped" unless ($branchName);
    my $tmpDir = $TMP_DIR."/mvs.gbc.$$";
    mkpath(($tmpDir), 0, 0755) || die "Can't create $tmpDir. Stopped";
    my $branchDir = getBranchDeliverTagDir($branchName);
    system("cd $tmpDir; svn $cvsVerbose_ checkout  ${SVNURL}$branchDir  $branchDir");
    opendir DIR, "$tmpDir/$branchDir";
    my @tagsFiles = grep /\.tags$/o, readdir DIR;
    closedir DIR;
    my @listOfSnaps;
    foreach my $file ( @tagsFiles ) {
        (my $module = $file) =~ s/\.tags$//o;
        open(TAGSFILE, "$tmpDir/$branchDir/$file") || die "Cannot open $tmpDir/$branchDir/$file ";
        foreach my $lineRef (readTagFileFromStream($branchName, $module, \*TAGSFILE)) {
            my $tag = $lineRef->[0];
            if ( $tag eq BUILD_TAG ) {
                if ($lineRef->[1] eq $buildId) {
                    my $snapId = $lineRef->[2];
                    if ($snapMode) {
                        if (hasBuildFormat($snapId)) {
                            $snapId = getSnapFromBuild($module, $snapId);
                        }
                    }
                    push @listOfSnaps, "$module:$snapId";
                    last;
                }
            }
        }
        close TAGSFILE;
    }
    mtree(($tmpDir), 0, 0);
    return @listOfSnaps;
}



# Check if the identifier looks like a build identifier. It doesn't mean
# that the build exist !
#
# @param buildId the build identifier to test
#
# @return a list (branchName, date) if it is a build identifier else null.

sub hasBuildFormat {
    (my $buildId) = @_;
    if ( $buildId =~ m/^([^_]+)_([1-9][0-9][0-9][0-9][0-1][0-9][0-3][0-9])[a-z]*$/o ) {
        return ($1, $2);
    }
    else {
        return(0);
    }
}



# Test if a build identifier exists
#
# @param branchName name of the branch
# @param buildId the build identifier
# @param errorMode indicates the expected behaviour in case of unexisting build
#        identifier
#
# @return 0 or 1

sub isExistingBuildIdentifier {
    (my $branchName, my $buildId, my $errorMode) = @_;
    # Test the branch first, else we will get an svn error in the
    # getAllBuildIdentifiers method
    unless (isExistingBranch($branchName, $errorMode)) {
        return(0);
    }
    foreach (getAllBuildIdentifiers($branchName)) {
        if ($_ eq $buildId) {
            return(1);
        }
    }
    if ($errorMode & ONERROR_PRINT) {
        print STDERR "$buildId not a $branchName build identifier\n";
    }
    if ($errorMode & ONERROR_EXIT) {
        exit(2);
    }
    return(0);
}



# Create a build identifier.
# In order keep some compatibility with the previous mechanism
# build identifiers have the following format:
# {branchName}_{year}{month}{day}[a-z]*
#
# @param branchName name of the branch
#
# @return the new build identifier

sub createBuildIdentifier {
    (my $branchName) = @_;
    (undef, undef, undef, my $mday, my $mon, my $year, undef, undef, undef) = getCurrentTime();
    $year += 1900;
    $mon += 1;
    my $tag = sprintf "%s_%04d%02d%02d", ($branchName, $year, $mon, $mday);
    # We only keep the list of module tags dealing with the current day
    # If it is empty, it is OK, we have the new build, else we add a 'a',
    # 'b', ... until we find an unexisting tag
    my @shortTagList = grep /$tag.*/, getAllBuildIdentifiers($branchName);
    my $ext='';
    do {
        my @res = grep /$tag$ext/, @shortTagList;
        if ( $#res < 0 ) {
            return "$tag$ext";
        }
        # It is not possible to rely on ++ after the z because it returns
        # aa and breaks the alphabetical order...
        my $oldExt = $ext;
        ++$ext;
        if (($oldExt gt $ext) || ($oldExt eq '')) {
          $ext = "${oldExt}a";
        }
    } while ( 1 );
    # This point should never be reached because of the return inside the
    # previous loop
    die "Unexpected execution ";
}



#########################
# Methods for the management of the "ModuleDeliverTag" file
#########################

# Remove data from the log cache
#
# @param branchName name of the branch (if empty, all branches)
# @param modCompOrBrName name of the module, component or branch (if empty, all
#        modules, components for this branch and the branch log itself)
#
# @global logFilesCache_ hash list for the module logs cache

sub cleanLogCache {
    (my $branchName, my $modCompOrBrName) = @_;
    if ($branchName && $modCompOrBrName) {
        delete $logFilesCache_{"MOD ${branchName}_${modCompOrBrName}"};
        delete $logFilesCache_{"COMP ${branchName}_${modCompOrBrName}"};
        delete $logFilesCache_{"BRANCH ${branchName}_${modCompOrBrName}"};
    }
    elsif ($branchName) {
        foreach (keys %logFilesCache_) {
            if (m/ ${branchName}_/) {
                delete $logFilesCache_{$_};
            }
        }
    }
    elsif ($modCompOrBrName) {
        foreach (keys %logFilesCache_) {
            if (m/_${modCompOrBrName}$/) {
                delete $logFilesCache_{$_};
            }
        }
    }
    else {
        %logFilesCache_=();
    }
}



# Get the content of the "ModuleDeliverTag" file.
# This method just open the file and call readTagFileFromStream with
# the resulting stream
#
# @param branchName name of the branch
# @param moduleName name of the module
#
# @return a list of listes (see readTagFileFromStream comment)

sub readTagFile {
    (my $branchName, my $moduleName) = @_;
    if (exists $logFilesCache_{"MOD ${branchName}_${moduleName}"}) {
        return @{$logFilesCache_{"MOD ${branchName}_${moduleName}"}};
    }
    # It is not possible to have a component or a branch with the same
    # name...
    if (exists $logFilesCache_{"COMP ${branchName}_${moduleName}"}) {
        return(()) ;
    }
    if (exists $logFilesCache_{"BRANCH ${branchName}_${moduleName}"}) {
        return(()) ;
    }
    #print STDOUT "Mvs.pm readTagFile for module $moduleName from $branchName branch.\n";
    my $tagsFile = getModuleDeliverTagFile($branchName, $moduleName);


    open(BRANCHTAGS, "svn  blame --verbose $SVNURL/$tagsFile $DROP_ERROR |") || die "$?\nStopped";
    my @result = readTagFileFromStream($branchName, $moduleName, \*BRANCHTAGS);
    # We don't test the result of the checkout because the file may not exist
    close(BRANCHTAGS);
    return @result;
}



# Get the content of the "ModuleDeliverTag" file using a stream as input.
# Instead of parsing this file from several places in the code, this
# method is in charge to do the parse and to build a list of entries.
# Then you just have to parse this list which should not change even if
# format of the "ModuleDeliverTag" file changes.
#
# @param branchName name of the branch
# @param moduleName name of the module
# @param fileRef stream on the "ModuleDeliverTag" file
#
# @global logFilesCache_ hash list of log files already read (set into this
#         method and not readTagFile because it may be called from
#         getBuildContent too)
#
# @return a list of listes (one line per entry)
#        (type field1 field2 field3, .... )
#        where:
#           type = start for the start tag
#           type = snap for lines describing a snap
#           type = build for lines describing a build
#           type = end for the end tag (module deleted in the branch)
my %MONTH_MAPPING = (
    Jan => "01",
    Feb => "02",
    Mar => "03",
    Apr => "04",
    May => "05",
    Jun => "06",
    Jul => "07",
    Aug => "08",
    Sep => "09",
    Oct => "10",
    Nov => "11",
    Dec => "12"
);
sub readTagFileFromStream {
    (my $branchName, my $moduleName, my $fileRef) = @_;
    if (exists $logFilesCache_{"MOD ${branchName}_${moduleName}"}) {
        return @{$logFilesCache_{"MOD ${branchName}_${moduleName}"}};
    }
    my @result;
    while (<$fileRef>) {
        chomp;
	# parse annotate
	# print STDOUT "Mvs.pm readTagFileFromStream read line from file $_.\n";
        my $version;
        my $user;
	my $date;
	
	#if( m/^([0-9\.]+)\s*\(([^\s]+)\s+([^\)]+)\):\s*(.*)$/ ) {
	if (m/\s*([0-9]*)\s*([^\s]*)\s*([0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]).*\)\s*(.*)$/){
	    $version = $1;
            $user = $2;
            $date = $3;
	    #my @dateFields = split /-/, $date;
	    #$dateFields[1] = $MONTH_MAPPING{$dateFields[1]};
            #$date = "20$dateFields[2]-$dateFields[1]-$dateFields[0]";
            $_ = $4;
	    #print STDOUT "User $user checked in Version $version at $date, remaining part is \"$_\".\n";
        } else {
            # skip header
            next;
        }

        if ( m/^${branchName}_START:/ ) {
	    #	print STDOUT "Mvs.pm readTagFileFromStream read START_TAG $_.\n";
            push @result, [ START_TAG, split /:/ ];
        }
        elsif ( m/^${moduleName}_${branchName}_[0-9][0-9][0-9][0-9]W[0-9][0-9][a-z]*:/ ) {
            my @fields = split /:/;
            push @fields, $date;
            push @fields, $user;

            push @result, [ SNAP_TAG, @fields ];
        }
        elsif ( m/^${branchName}_[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][a-z]*:/ ) {
            push @result, [ BUILD_TAG, split /:/ ];
        }
        elsif ( m/^M:([^:])*:([^:])/o ) {
            my @fields = split /:/;
            push @fields, $date;
            push @fields, $user;

            push @result, [ MERGE_TAG, @fields ];
        }
        elsif ( m/^${branchName}_END:/ ) {
            push @result, [ END_TAG, split /:/ ];
        }
        else {
            die "Unexpected line in $moduleName log file in $branchName branch.\n$_\nStopped";
        }
    }
    # We save the value only if it is not empty (because this method
    # may be call with a component name just to test if it exists
    if ($#result > -1) {
        $logFilesCache_{"MOD ${branchName}_${moduleName}"} = [ @result ];
    }
    return @result;
}



# Add/modify lines in the "ModuleDeliverTag" file.
# Exit from the process (die) in case of problem.
#
# @param branchName name of the branch
# @param moduleName name of the module
# @param entryListRef a reference to a list with the following format:
#        (field1 field2 field3 ... )
#        If a field must not be changed, undef has to be used for its value
# @param logMess message to use for the cvs commit
# @param createIfNeeded indicates that the file must be created if it is
#        not already existing into CVS repository

sub addEntryToTagFile {
    (my $branchName, my $moduleName, my $entryListRef, my $logMess, my $createIfNeeded) = @_;
    my $tagFile = getModuleDeliverTagFile($branchName, $moduleName);
    my $tagDir = getBranchDeliverTagDir($branchName);

    # Build a hash list from the given list in order to find faster when
    # a line has to been modified in the file. The used key is the first
    # element in the list, the value is the list without the first element.
    # We don't take care of lines with the "M" key because they are always
    # added and never modified
    my %linesToAdd;
    foreach (@$entryListRef) {
        my @line = @$_;
        my $key = shift @line;
        unless ($key eq "M") {
            $linesToAdd{$key} = [ @line ];
        }
    }

    my $try=1;
    my $currentDir=cwd();
    # This loop allows to retry the changes several times in cases of
    # problems. It may occur because another change is done at the same
    # time...
    my $tmpDir = $TMP_DIR."/mvs.aettf.$$";
    while (1) {
        mkpath(($tmpDir), 0, 0755) || die "Can't create $tmpDir. Stopped";
        chdir($tmpDir) || die "Unable to change dir to $tmpDir. Stopped";
        my $returnCode=0;
        if ($DROP_OUTPUT) {
            open SAVEOUT, ">&STDOUT";
            open STDOUT, ">/dev/null";
        }
        if ($DROP_ERROR) {
            open SAVEERR, ">&STDERR";
            open STDERR, ">/dev/null";
        }
        my @args = ("svn", "$cvsVerbose_", "checkout", "$tagFile");
        $returnCode = system("svn $cvsVerbose_ checkout $SVNURL/$tagDir  $tmpDir/$tagDir");
        if ($DROP_OUTPUT) {
            close STDOUT;
            open STDOUT, ">&SAVEOUT";
        }
        if ($DROP_ERROR) {
            close STDERR;
            open STDERR, ">&SAVEERR";
        }
# For debug only
#        if ($try == 1) {
#            $returnCode = 512;
#        }
# End of the debug
        if ($returnCode) {
            # If we are not into the "createIfNeeded" mode, we assume
            # it is an error. Else, it may be normal (file not existing)
            if ($createIfNeeded) {
                # We create the file in the HEAD branch (MVS management files
                # are always in the main branch)
                addFileToCVS("HEAD", $tagFile, $tmpDir);
            }
            else {
                print STDERR "@args exits with non zero status ($returnCode)\n";
                next;
            }
        }
        open(NEWBRANCHTAGS, "> $tmpDir/$tagFile.new") || die "$!. Stopped";
        open(OLDBRANCHTAGS, "$tmpDir/$tagFile") || die "$!. Stopped";
        my $startFound = 0;
        while (<OLDBRANCHTAGS>) {
            chomp;
            next if ( m/^\s*$/o );
            if ( m/^([^:]*):(.*)$/o ) {
                if ( exists $linesToAdd{$1} ) {
                    # This line has to be modified
                    my @newTagVal = @{$linesToAdd{$1}};
                    my @oldTagVal = split /:/, $2;
                    print NEWBRANCHTAGS "$1:";
                    # Loop on the new and old field values
                    # If the new value is defined, we use it, else we use the
                    # old value
                    for (my $i=0 ; ($i < @newTagVal) || ($i < @oldTagVal) ; $i++) {
                        if (defined $newTagVal[$i]) {
                            print NEWBRANCHTAGS "$newTagVal[$i]:";
                        }
                        else {
                            print NEWBRANCHTAGS "$oldTagVal[$i]:";
                        }
                    }
                    print NEWBRANCHTAGS "\n";
                    delete $linesToAdd{$1};
                }
                else {
                    print NEWBRANCHTAGS "$_\n";
                }
            }
            else {
                die "Unexpected format for $tagFile:\n$_\nStopped";
            }
        }
        close OLDBRANCHTAGS;

        # Now add the new lines
        foreach (@$entryListRef) {
            my @tagVal = @$_;
            my $key = shift @tagVal;
            if ((exists $linesToAdd{$key}) || ($key eq "M")) {
                print NEWBRANCHTAGS "$key:";
                foreach ( @tagVal ) {
                    print NEWBRANCHTAGS "$_:";
                }
                print NEWBRANCHTAGS "\n";
            }
        }
        close NEWBRANCHTAGS;
        rename "$tmpDir/$tagFile.new", "$tmpDir/$tagFile" || die "Cannot rename $tagFile";

        if ($DROP_OUTPUT) {
            open SAVEOUT, ">&STDOUT";
            open STDOUT, ">/dev/null";
        }
        if ($DROP_ERROR) {
            open SAVEERR, ">&STDERR";
            open STDERR, ">/dev/null";
        }
	#@args = ("svn", "$cvsVerbose_", "commit", "-m", $logMess, $tagFile);
        $returnCode = system( "cd $tmpDir/$tagDir; svn $cvsVerbose_ commit -m \"$logMess\" ");
        if ($DROP_OUTPUT) {
            close STDOUT;
            open STDOUT, ">&SAVEOUT";
        }
        if ($DROP_ERROR) {
            close STDERR;
            open STDERR, ">&SAVEERR";
        }
# For debug only
#        if ($try == 1) {
#            $returnCode = 512;
#        }
# End of the debug
        unless ( $returnCode == 0) {
            next;
        }
        # The tagfile is commited. We can exit from the loop.
        last;
    }
    continue {
        # The attempt to update the tagfile has failed.
        rmtree(($tmpDir), 0, 0);
        $try++;
        if ($try <= MAX_TRY) {
            print STDERR "Retry .....\n";
        }
        else {
            print STDERR "Sorry, MVS cannot complete successfully the command.\n";
            print STDERR "Please to restart your MVS command.\n";
            exit 1;
        }
    }
    chdir($currentDir) || die "Unable to change dir to $currentDir. Stopped";
    cleanLogCache($branchName, $moduleName);
    rmtree(($tmpDir), 0, 0);
}



#########################
# Methods dealing with modules responsibles
#########################

# Get the content of the "Responsibles" file.
# This method just open the file and call readRespFileFromStream with
# the resulting stream
#
# @param branchName name of the branch
#
# @return a hash list: moduleName -> list of responsibles

sub readRespFile {
    (my $branchName) = @_;
    if (exists $respFilesCache_{"${branchName}"}) {
        return %{$respFilesCache_{"${branchName}"}};
    }
    my $respFile = getResponsiblesFile($branchName);
    open(BRANCHRESP, "svn $cvsVerbose_ cat -p $SVNURL/$respFile $DROP_ERROR |") || die "$?\nStopped";
    my %result = readRespFileFromStream($branchName, \*BRANCHRESP);
    # We don't check if the checkout success because the file may not
    # exist
    close(BRANCHRESP);
    return %result;
}



# Get the content of the "Responsibles" file using a stream as input.
# Instead of parsing this file from several places in the code, this
# method is in charge to do the parse and to build a list of entries.
# Then you just have to parse this list which should not change even if
# format of the "Responsibles" file changes.
#
# @param branchName name of the branch
# @param fileRef stream on the "Responsibles" file
#
# @global respFilesCache_ hash list of responsibles files already read
#
# @return a hash list: moduleName -> list of responsibles

sub readRespFileFromStream {
    (my $branchName, my $fileRef) = @_;
    if (exists $respFilesCache_{"${branchName}"}) {
        return %{$respFilesCache_{"${branchName}"}};
    }
    my %result;
    my $lineNb=0;
    while (<$fileRef>) {
        chomp;
        $lineNb++;
        s/\s*//go; # No blanks expected in this file
        next if ( m/^$/o );
        next if ( m/^#/o );
        if ( m/^([^:]+):(.*)$/o ) {
            if (exists $result{$1}) {
                die "Duplicated entry for $1 in $branchName responsibles file, line $lineNb:\n$_\nStopped"
            }
            $result{$1} = [ split /,/, $2 ];
        }
        else {
            die "Unexpected format in $branchName responsibles file, line $lineNb:\n$_\nStopped";
        }
    }
    $respFilesCache_{"${branchName}"} = \%result;
    return %result;
}



# Add/modify lines in the "responsibles" File
# If the format of this file change, the mkbranchExecCmd function of mvsadmin
# has to be modified too
#
# @param branchName name of the branch
# @param entryListRef a reference to a list with the following format:
#        (moduleName (responsible1 responsible2)
# @param logMess message to use for the cvs commit

sub addEntryToRespFile {
    (my $branchName, my $entryListRef, my $logMess) = @_;
    my $tmpDir = $TMP_DIR."/mvs.aetrf.$$";
    mkpath(($tmpDir), 0, 0755) || die "Can't create $tmpDir. Stopped";
    my $respFile = getResponsiblesFile($branchName);

    my $try=1;
    my $currentDir=cwd();
    chdir($tmpDir) || die "Unable to change dir to $tmpDir. Stopped";
    while (1) {
        my $returnCode=0;
        my @args = ("svn", "$cvsVerbose_", "checkout", $respFile);
        system(@args);

        # In some cases the file doesn't exist, it just means that it is
        # the first case we add a module responsible for this branch
        unless (-f "$tmpDir/$respFile") {
            addFileToCVS("HEAD", $respFile, $tmpDir);
        }
        modifyRespFile("$tmpDir/$respFile", $entryListRef);
        if ($DROP_OUTPUT) {
            open SAVEOUT, ">&STDOUT";
            open STDOUT, ">/dev/null";
        }
        if ($DROP_ERROR) {
            open SAVEERR, ">&STDERR";
            open STDERR, ">/dev/null";
        }
        @args = ("svn", "$cvsVerbose_", "commit", "-m", $logMess, $respFile);
        $returnCode = system(@args);
        if ($DROP_OUTPUT) {
            close STDOUT;
            open STDOUT, ">&SAVEOUT";
        }
        if ($DROP_ERROR) {
            close STDERR;
            open STDERR, ">&SAVEERR";
        }
        unless ( $returnCode == 0) {
            next;
        }
        # The file is commited. We can exit from the loop.
        last;
    }
    continue {
        # The attempt to update the file has failed.
        unlink("$tmpDir/$respFile");
        unlink("$tmpDir/$respFile.new");
        $try++;
        if ($try <= MAX_TRY) {
            print STDERR "Retry .....\n ";
        }
        else {
            print STDERR "Sorry, MVS cannot complete successfully the command. \n";
            print STDERR "Please to restart your MVS command.\n";
            rmtree(($tmpDir), 0, 0);
            exit 1;
        }
    }
    chdir($currentDir) || die "Unable to change dir to $currentDir. Stopped";
    delete $respFilesCache_{$branchName};
    rmtree(($tmpDir), 0, 0);
}



# Add/modify lines in the "responsibles" File
# If the format of this file change, the mkbranchExecCmd function of mvsadmin
# has to be modified too
#
# @param branchName name of the branch
# @param entryListRef a reference to a list with the following format:
#        (moduleName (responsible1 responsible2)
# @param logMess message to use for the cvs commit

sub modifyRespFile {
    (my $respFile, my $entryListRef) = @_;

    # Build a hash list from the given list in order to find faster when
    # a line has to been modified in the file. The used key is the first
    # element in the list, the value is the list without the first element.
    my %linesToAdd;
    foreach (@$entryListRef) {
        my @line = @$_;
        my $key = shift @line;
        $linesToAdd{$key} = [ @line ];
    }

    open(NEWRESPFILE, "> $respFile.new") || die "$!\nStopped";
    # It is possible to have no previous version of the file
    open(OLDRESPFILE, "$respFile");
    while (<OLDRESPFILE>) {
        chomp;
        next if ( m/^\s*$/o );
        if ( m/^([^:]*):.*$/o ) {
            if ( exists $linesToAdd{$1} ) {
                # This line has to be modified
                my @newRespVal = @{$linesToAdd{$1}};
                print NEWRESPFILE "$1:";
                print NEWRESPFILE shift @newRespVal;
                foreach my $resp (@newRespVal) {
                    print NEWRESPFILE ",$resp";
                }
                print NEWRESPFILE "\n";
                delete $linesToAdd{$1};
            }
            else {
                print NEWRESPFILE "$_\n";
            }
        }
        elsif ( m/^#/o ) {
            # We keep comments
            print NEWRESPFILE "$_\n";
        }
        else {
            die "Unexpected format for $respFile:\n$_\nStopped";
        }
    }
    close OLDRESPFILE;

    # Now add the new lines
    foreach (@$entryListRef) {
        my @tagVal = @$_;
        my $key = shift @tagVal;
        if (exists $linesToAdd{$key}) {
            my @newRespVal = @{$linesToAdd{$key}};
            print NEWRESPFILE "$key:";
            print NEWRESPFILE shift @newRespVal;
            foreach my $resp (@newRespVal) {
                print NEWRESPFILE ",$resp";
            }
            print NEWRESPFILE "\n";
        }
    }
    close NEWRESPFILE;
    rename "$respFile.new", "$respFile" || die "Cannot rename $respFile. Stopped";
}



# This method returns the responsibles of the module for a branch
#
# @param branchName name of the branch
# @param moduleName name of the module
#
# @return the list of responsibles (which may be empty)

sub getModuleResponsible {
    (my $branchName, my $moduleName) = @_;
    my %respList = readRespFile($branchName);
    my $resp = $respList{$moduleName};
    if ($resp) {
        return @{$resp};
    }
    else {
        return ();
    }
}



# Check if the current user has the authorization
#
# @param branchName the name of the branch
# @param usersList list of authorized users
#
# @return 1 or 0

sub isAuthorized {
    (my $branchName, my @usersList) = @_;

    if (getUserName() eq SUPER_USER_NAME) {
        return(1);
    }
    if ($#usersList == -1) {
        return(1);
    }
    foreach (@usersList) {
        if (getUserName() eq $_) {
            return(1);
        }
    }
    my %admList = %{getBranchProperty($branchName, BRANCH_RESPONSIBLES)};
    if ($admList{+getUserName()}) {
        return(1);
    }
    return(0);
}



# Check is the current user may modify a module in a given branch.
# If not, displays a message.
#
# @param branchName name of the branch
# @param moduleName name of the module
# @param operation kind of operation ("deliver", "commit", "mksnap"...). Not
#        use at this time excepted for the error message but for future use
#
# @return 1 if the operation is allowed, else 0

sub mayModifyModule {
    (my $branchName, my $moduleName, my $operation) = @_;
    my @respList = getModuleResponsible($branchName, $moduleName);
    unless (isAuthorized($branchName, @respList)) {
        print STDERR getUserName()." is not allowed to $operation $moduleName module in $branchName branch\n";
        print STDERR "This operation may only be done by ".shift @respList;
        foreach (@respList) {
            print STDERR " or $_";
        }
        print STDERR "\n";
        return(0);
    }
    return(1);
}



# Get the content of the CVS passwd file.
#
# @return a hash list: userName -> (passwd, unix_login)

sub getUsersList {
    if (%usersList_) {
        return(%usersList_);
    }
    open(PASSWD, "svn cat $SVNURL/MVSROOT/passwd |") || die "$?\nStopped";
    my $lineNb=0;
    while (<PASSWD>) {
        chomp;
        $lineNb++;
        next if ( m/^\s*$/o ); # Blank line
        next if ( m/^#/o );
        if ( m/^([^:]+):([^:]*):([^:]*)$/o ) {
            if (exists $usersList_{$1}) {
                die "Duplicated entry for $1 in ".CVS_PASSWD_FILE." file, line $lineNb:\n$_\nStopped"
            }
            $usersList_{$1} = [ ($2, $3) ];
        }
        else {
            die "Unexpected format in ".CVS_PASSWD_FILE." file, line $lineNb:\n$_\nStopped";
        }
    }
    close(PASSWD) || die "Cannot checkout ".CVS_PASSWD_FILE."\nStopped";
    return %usersList_;
}



#########################
#
#########################

# Get what should be the delivered tag for a module (i.e. the tag which
# should be used for the build). There's three possibilities:
# - There's a delivered version: it will be used
# - There's no delivered version: the last build done in this branch will be
#   used. Take care because last means, last in the file (we are expecting
#   that nobody modifies the content of this file by hand)
# - There's no build in this branch: if the module has been put in the
#   branch thanks to a build identifier, we used it, else (new module or
#   module added thanks to a snap identifier after the branch creation) there's
#   no delivery tag.
#
# @param branchName name of the branch
# @param moduleName name of the module

sub getDeliveredVersion {
    (my $branchName, my $moduleName) = @_;
    my $lastSnapWithBuild = "";
    my $lastSnapWithD = "";
    my $startTagId = "";
    foreach my $lineRef ( readTagFile($branchName, $moduleName) ) {
        my $tag = $lineRef->[0];
        SWITCH: {
            ( $tag eq START_TAG ) && do {
                $startTagId = $lineRef->[2];
                last SWITCH;
            };
            ( $tag eq SNAP_TAG ) && do {
                if ( $lineRef->[2] eq "D" ) {
                    $lastSnapWithD = $lineRef->[1];
                }
                last SWITCH;
            };
            ( $tag eq BUILD_TAG ) && do {
                $lastSnapWithBuild = $lineRef->[1];
                last SWITCH;
            };
        }
    }
    if ($lastSnapWithD) {
        return($lastSnapWithD);
    }
    elsif ($lastSnapWithBuild) {
        return($lastSnapWithBuild);
    }
    elsif (hasBuildFormat($startTagId)) {
        return($startTagId);
    }
    else {
        return("");
    }
}



# Create/update a symbolic link for all .lnk files of a module.
# When a file sample.lnk contains the line anotherFile, we create a
# symbolic link: sample -> anotherFile
#
# @param moduleName the name of the module

sub updateSymbolicLinks {
    (my $moduleName) = @_;
    my @lnkfiles = grep /\.lnk$/, getModuleFiles($moduleName);
    my $lnkFile;
    foreach $lnkFile ( @lnkfiles ) {
        open(LNKFILE, $lnkFile) || die "Can't open $lnkFile. Stopped";
        my $linkedFile = <LNKFILE>;
        close(LNKFILE);
        chomp $linkedFile;
        $lnkFile =~ s/\.lnk$//o;
        # If a link is already existing, we check if it has to be
        # modified or not. If yes, we just remove it in this first step.
        my $oldLinkedFile = readlink $lnkFile;
        if ( $oldLinkedFile ) {
            if ($oldLinkedFile ne $linkedFile) {
                print "$lnkFile link has been modified\n";
                unlink($lnkFile);
                $oldLinkedFile = undef;
            }
        }
        # Create the link if needed. If we are not able to do that, we just
        # display a warning message
        unless ($oldLinkedFile) {
            unless (symlink $linkedFile, $lnkFile) {
                print STDERR "WARNING: cannot create $lnkFile link\n";
            }
        }
    }
}



# Export a module using a given tag. Create the symbolics links.
#
# @param moduleName name of the module
# @param tagId the tag to use
# @param noLnk indicates that the symbolics links must not be created
#
# @return 1 if OK, else 0

sub exportModule {
    (my $moduleName, my $tagId, my $noLnk) = @_;

    my $varsFile = getModuleVarsFile($moduleName);
    if (isExistingCVSBug("localExport")) {
        if (-e VARS_DIR."/CVS") {
            # To prevent CVS from removing the directory at the end of the
            # export
            (-e VARS_DIR."/CVS.sav") && die "Unexpected ".VARS_DIR."/CVS.sav.\nPlease call your MVS administrator. Stopped";
            rename(VARS_DIR."/CVS", VARS_DIR."/CVS.sav") || die "Cannot rename ".VARS_DIR."/CVS. Stopped";
        }
    }
    my $ret = system("svn $cvsVerbose_ export -r $tagId $varsFile");
    if (-e VARS_DIR."/CVS.sav") {
        # Since svn 1.11.1p1, the CVS directory is created even in the
        # pserver mode ! So it is not possible to restore the previous version
        if (-d VARS_DIR."/CVS") {
            # The Entries file must be empty
            (undef, undef, undef, undef, undef, undef, undef, my $size, undef, undef, undef, undef, undef) = stat VARS_DIR."/CVS/Entries";
            ($size == 0) || die "Unexpected ".VARS_DIR."/CVS/Entries file.\nPlease call your MVS administrator. Stopped";
            rmtree(VARS_DIR."/CVS", 0, 0);
        }
        rename(VARS_DIR."/CVS.sav", VARS_DIR."/CVS") || die "Cannot restore ".VARS_DIR."/CVS.\nPlease call your MVS administrator. Stopped";
    }
    if ($ret) {
        return(0);
    }
    my $dirName= rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
    $ret = system("svn $cvsVerbose_ export -r $tagId $dirName");
    if ($ret) {
        return(0);
    }
    # If the directory name doesn't exist, it means that the module is
    # empty. We just have to create it
    unless (-e $dirName) {
        mkpath(($dirName), 0, 0755) || print STDERR "Can't create $dirName\n$!\n";
    }
    unless (-d $dirName) {
        print STDERR "$dirName not a directory\n";
        return(0);
    }

    # Create symbolik links for .lnk files
    unless ($noLnk) {
        updateSymbolicLinks($moduleName);
    }
    return(1);
}



# Checkout a module using a given tag. Create the symbolics links.
#
# @param moduleName name of the module
# @param ident the tag or the branch name to use
# @param noLnk indicates that the symbolics links must not be created
# @param cvsTags some special CVS tags
#
# @return 1 if OK, else 0

sub checkoutModule {
	(my $moduleName, my $ident, my $noLnk, my $cvsTags) = @_;
	(my $branch, undef) = hasSnapFormat($ident);
	unless ($branch) {
		($branch, undef) = hasBuildFormat($ident);
	}
	
	my $ret;
	unless ($branch) {
		# It should be a branch name,so  we get the module and module var file form branch/main
		$branch = $ident;
		
		#get the VAR dir, if no .we checkout it from branch main. otherwise  wo update it from branch main
		if (-d VARS_DIR){
			$ret = system("cd ".VARS_DIR."; svn $cvsVerbose_ update; cd ..");
		}else{
			$ret = system("svn $cvsVerbose_ checkout  $SVNURL/$branch/main/".VARS_DIR." ".VARS_DIR);
		}

		if ($ret) {
			return(0);
		}		
		
		#then  we will get the module dir
		my $dirName= rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
		$ret = system("svn $cvsVerbose_ checkout  $SVNURL/$branch/main/$dirName $dirName");
		if ($ret) {
			return(0);
		}
	}
	else {
		my $rev =  getRevision($moduleName, $ident);
		#get the VAR dir, if no .we checkout it from branch main. otherwise  wo update it from branch main
		if (-d VARS_DIR){
			$ret = system("cd ".VARS_DIR."; svn $cvsVerbose_ update; cd ..");
		}else{
			$ret = system("svn $cvsVerbose_ checkout  $SVNURL/$branch/main/".VARS_DIR." ".VARS_DIR);
		}

		if ($ret) {
			return(0);
		}
		
		#then  we will get the module dir
		my $dirName= rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
		$ret = system("svn $cvsVerbose_ checkout -r $rev $SVNURL/$branch/main/$dirName $dirName");
		if ($ret) {
			return(0);
		}
		
		
	}
	
	# Create symbolik links for .lnk files
    unless ($noLnk) {
        updateSymbolicLinks($moduleName);
    }

    return(1);
}



# Update a module using a given tag. Create the symbolics links.
#
# @param moduleName name of the module
# @param ident the tag or the branch name to use
# @param noLnk indicates that the symbolics links must not be created
# @param cvsTags some special CVS tags
#
# @return 1 if OK, else 0

sub updateModule {
	(my $moduleName, my $ident, my $noLnk, my $cvsTags) = @_;
    my $varsFile = getModuleVarsFile($moduleName);
    my $oldDirName = rGetModuleDir(undef, $moduleName);
    if (($ident eq "HEAD") || (! $ident)){
        my $ret = system("svn --quiet update  $varsFile");
        if ($ret) {
            return(0);
        }
        my $dirName = rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
        if ($oldDirName ne $dirName) {
            print "Module directory changes from $oldDirName to $dirName. You have to delete the $oldDirName by hand\n";
            $ret = system("svn $cvsVerbose_ checkout  $dirName");
        }
        else {
            $ret = system("svn $cvsVerbose_ update  $dirName");
        }
        if ($ret) {
            return(0);
        }
    }
    else {
	my $rev = getRevision($moduleName, $ident);
	print STDOUT "Mvs.pm updateModule: svn $cvsVerbose_ update  -r $rev $varsFile\n";
        my $ret = system("svn $cvsVerbose_ update   $varsFile -r $rev");
        if ($ret) {
            return(0);
        }
        my $dirName= rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
        if ($oldDirName ne $dirName) {
            print "Module directory changes from $oldDirName to $dirName. You have to delete the $oldDirName by hand\n";
            $ret = system("svn $cvsVerbose_ checkout   $dirName -r $rev");
        }
        else {
            $ret = system("svn $cvsVerbose_ update   $dirName -r $rev");
        }
        if ($ret) {
            return(0);
        }
        # Because of the -P option, the module directory may be removed
        # if the module contains nothing, we have to checkout it again
        #  but it is not possible to use the same solution as for the HEAD
        # (see comment of the checkoutModule funtion)
        unless (-d $dirName) {
            $ret = system("svn -q checkout -l $dirName");
            if ($ret) {
                return(0);
            }
            $ret = system("svn -q update -l -r $ident $dirName");
            if ($ret) {
                return(0);
            }
        }
    }

    # Create symbolik links for .lnk files
    unless ($noLnk) {
        updateSymbolicLinks($moduleName);
    }

    return(1);































    (my $moduleName, my $ident,my $oldIdent, my $noLnk, my $cvsTags) = @_;
	#print STDOUT "Mvs.pm updateModule (my $moduleName, my $ident, my $noLnk, my $cvsTags)\n";
	
	my $ret;
	if($ident) {
		(my $branch, undef) = hasSnapFormat($ident);
		unless ($branch) {
			($branch, undef) = hasBuildFormat($ident);
		}
		
		my $oldDirName = rGetModuleDir(undef, $moduleName);
		if (!$branch) {
			# It should be a branch name,so  we get the module and module var file form branch/main
			$branch = $ident;
			#get the VAR dir, if no .we checkout it from branch main. otherwise  wo update it from branch main
			if (-d VARS_DIR){
				$ret = system("cd ".VARS_DIR."; svn $cvsVerbose_ update; cd ..");
			}else{
				$ret = system("svn $cvsVerbose_ checkout  $SVNURL/$branch/main/".VARS_DIR." ".VARS_DIR);
			}

			if ($ret) {
				return(0);
			}		
			
			my $dirName= rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
			if ($oldDirName ne $dirName) {
				print STDOUT "Module directory changes from $oldDirName to $dirName. You have to delete the $oldDirName by hand\n";
				$ret = system("svn  $cvsVerbose_  checkout  $SVNURL/$branch/main/$dirName $dirName");
				if ($ret) {
					return(0);
				}	
			}
			else {
				unless (-d $dirName) {
					$ret = system("svn  $cvsVerbose_ checkout  $SVNURL/$branch/main/$dirName $dirName");
				}else{
					$ret = system("svn    update   $dirName");
				}
			}	
			if ($ret) {
				return(0);
			}
		}
		else {
			#get the VAR dir, if no .we checkout it from branch main. otherwise  wo update it from branch main
			if (-d VARS_DIR){
				$ret = system("cd ".VARS_DIR."; svn $cvsVerbose_ update; cd ..");
			}else{
				$ret = system("svn $cvsVerbose_ checkout  $SVNURL/$branch/main/".VARS_DIR." ".VARS_DIR);
			}

			if ($ret) {
				return(0);
			}
			
			my $rev = getRevision($moduleName, $ident);
			my $dirName= rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
			if ($oldDirName ne $dirName) {
				print STDOUT "Module directory changes from $oldDirName to $dirName. You have to delete the $oldDirName by hand\n";
				$ret = system("svn  $cvsVerbose_  checkout -r $rev $SVNURL/$branch/tags/$ident/$dirName $dirName");
				if ($ret) {
					return(0);
				}
			}
			else {
				unless (-d $dirName) {
					$ret = system("svn  $cvsVerbose_ checkout -r $rev $SVNURL/$branch/tags/$ident/$dirName $dirName");
									
					if ($ret) {
							print STDOUT "do module svn update or checkout  failed.\n";
							return(0);
					}
				}else{
					my $flag;
					my $diffs;
					if($oldIdent){
						my $oldrev = getRevision($moduleName,$oldIdent);
						(my $oldBranch, undef) = hasSnapFormat($oldIdent);
						unless ($oldBranch) {
							($oldBranch, undef) = hasBuildFormat($oldIdent);
						}
						$diffs =`svn diff -r $oldrev:$rev --old=$SVNURL/$oldBranch/tags/$oldIdent/$dirName  --new=$SVNURL/$branch/tags/$ident/$dirName --summarize`;
					}else {
						$flag="true";
					}
					
					if ($flag || $diffs) {
						#update to  the $ident version
						print STDOUT "$ident and $oldIdent diffs:\n $diffs\n";
						my $currentDir = getcwd;
						my $tmpDir = "$TMP_DIR/mvs.udp.$$";
						mkpath(($tmpDir), 0, 0755) || die "Can't create $tmpDir. Stopped";
						chdir($tmpDir) || die "Unable to change dir to $tmpDir. Stopped";
						$ret = system("svn  $cvsVerbose_ checkout  $SVNURL/$branch/tags/$ident/$dirName $dirName");
						if ($ret) {
							print STDOUT "svn  $cvsVerbose_ checkout  $SVNURL/$branch/tags/$ident/$dirName $dirName error\n";
							return(0);
						}
						
						
						$ret = system("cp -rfp $dirName $currentDir");
						chdir($currentDir) || die "Unable to change dir to $currentDir. Stopped";
						if ($ret) {
							print STDOUT "copy $dirName to old $dirName dir error";
							rmtree(($tmpDir), 0, 0);
							return(0);
						}
						
						rmtree(($tmpDir), 0, 0);
						
					} else {
						print STDOUT "$ident and $oldIdent nodiffs.\n";
					}
					
					#$ret = system("cd $dirName;svn  update -r ".$rev." $dirName".";cd ..");
				}		
			}	
		}	

	} else {
		if (-d VARS_DIR){
				$ret = system("cd ".VARS_DIR."; svn  update; cd ..");
		}
		if ($ret) {
            return(0);
		}	
		
		my $dirName= rGetModuleDir(undef, $moduleName, ONERROR_EXIT);
		if (-d $dirName) {
				$ret = system("svn update $dirName");
		}
		if ($ret) {
            return(0);
     }
	}
	 	
	# Create symbolik links for .lnk files
    unless ($noLnk) {
        updateSymbolicLinks($moduleName);
    }

    return(1);
}



# Analyze the output of a "cvs status" command for one file
# We assume the it looks like this
#
# File: short file name		Status: status
#
#    Working revision:		revision
#    Repository revision:	revision fullRepositoryName
#    Sticky Tag:                branchName (branch: revision)
#
# with of course some delta according with the exact file status...
#
# @param fileRef reference to the output stream. This method read it until
#        the end of one file description or until the end of file
#
# @return a list or undef at the end of the stream
#     file : basename of the file
#     status : file status
#     revision : working revision (may be "new")
#     longName : full file name (may be undef)
#     branch : file branch (may be undef)

sub readFileStatusFromStream {
    (my $fileRef) = @_;

    my $fileFound = 0;
    my $file = "";
    my $longName;
    my $status;
    my $revision;
    my $branch;
    while (<$fileRef>) {
        chomp;
		print "file:$_\n";
        SWITCH: {
            ( /^=+$/ ) && do {
                # It is the separator between files, we don't know if we will
                # get it has the first line or the at the last one, so we stop
                # only if the file has be found before...
                if ($fileFound) {
                    return($file, $status, $revision, $longName, $branch);
                }
                # We are sure, the next one is the end
                $fileFound = 1;
                last SWITCH;
            };

            # We have to take care of blanks into the file name.
            # It doesn't work if the first or the last character is a blank...
            (( /File: no file (.*[^\s])\s+Status: (.*)$/o ) ||
             ( /File: (.*[^\s])\s+Status: (.*)$/o )) && do {
                ($file eq "") || die "$_\nRepository revision not found for $file. Stopped";
                $file = $1;
                $status = $2;
                $fileFound = 1;
                last SWITCH;
            };

            ( /Working revision:\sNo entry for (.*)/o ) && do {
                $revision = "new";
                ($file) || die "$_\nNo previous file. Stopped";
                $fileFound = 1;
                last SWITCH;
            };

            ( /Working revision:\s([0-9\.]+)/o ) && do {
                $revision = $1;
                ($file) || die "$_\nNo previous file. Stopped";
                $fileFound = 1;
  	        last SWITCH;
  	    };

            ( m@Repository revision:\s([0-9\.]+)\s$cvsRootDir_/(.*),v$@o ) && do {
                ($longName = $2) =~ s@/Attic/@/@;
                $fileFound = 1;
                # "File" and "Working revision" entries must have been
                # found before...
                ((basename $longName) eq $file) || die "$_\nExpecting line for $file. Stopped";
                ($status) || die "$_\nNo status found before. Stopped";
                last SWITCH;
            };
            ( /Repository revision: No revision control file/ ) && do {
                # Added file, there's no repository version
                $fileFound = 1;
                ($file) || die "$_\nNo previous file. Stopped";
                ($status eq "Locally Added") || die "$_\nPrevious status was $status. Stopped";
                ($revision eq "new") || die "$_\nPrevious revision was $revision. Stopped";
            };
            ( /Sticky Tag:\s*(.*)$/o ) && do {
                # Check if there's no file from another branch
                my $stickyTag = $1;
                $fileFound = 1;
                if ( $stickyTag eq "(none)" ) {
                    $branch = "HEAD";
                }
                elsif ( $stickyTag =~ m/^([^\s]+)\s*\(branch:.*/o ) {
                    $branch = $1;
                }
                elsif ( $stickyTag =~ m/^([^\s]+)\s*- MISSING from RCS file.*/o ) {
                    # Added file
                    my $tagId = $1;
                    ($branch, undef) = hasSnapFormat($tagId);
                    unless ($branch) {
                        ($branch, undef) = hasBuildFormat($tagId);
                    }
                    unless ($branch) {
                        # It should be a branch name
                        $branch = $tagId;
                    }
                    else {
                        # We don't complain if the tag is a build or a snap
                        # from another branch because it is a normal
                        # behaviour with components
                        $branch = "";
                    }
                }
                elsif ( $stickyTag =~ m/^([^\s]+)\s*\(revision:.*/o ) {
                    my $tagId = $1;
                    ($branch, undef) = hasSnapFormat($tagId);
                    unless ($branch) {
                        ($branch, undef) = hasBuildFormat($tagId);
                    }
                    unless ($branch) {
                        die "Tag for $longName is not a snap nor a build identifier ($tagId). Stopped";
                    }
                    # We don't complain if the tag is a build or a snap from
                    # another branch because it is a normal behaviour with
                    # components
                    $branch = "";
                }
                else {
                    die "Unexpected sticky tag for $longName: $stickyTag. Stopped";
                }
            }
        }
    }
    if ($fileFound) {
        return($file, $status, $revision, $longName, $branch);
    }
    return;
}



# Check the status (cvs status) of one file
#
# @param filename name of the file
# @branchname name of the branch
#
# @return the status ("Up-to-date", "Unknown", ...

sub checkFileStatus {
    (my $filename, my $branchName) = @_;

    my $dirname = dirname($filename);
    unless (-d "$dirname/.svn") {
        return("Unknown");
    }

    # Because of statusCheckout bug, we have to remove the write permission
    # to the CVS directory before running the command and to restore it after...
    # We ignore ^C during the execution of the command to be able
    # to restore directory rights
    {
        local $SIG{INT} = 'IGNORE';
        my $mode;
        if (isExistingCVSBug("statusCheckout")) {
            (undef, undef, $mode, undef, undef, undef, undef, undef, undef, undef, undef, undef, undef) = stat "$dirname/.svn";
            ($mode) || die "Cannot get permission of $dirname/.svn. Stopped";
            chmod 0555, "$dirname/.svn"; # We don't take care if it succed or not
        }
        unless (open(STATUS, "svn $cvsVerbose_ status $filename 2>/dev/null |")) {
            my $error = $!;
            if ($mode) {
                chmod $mode, "$dirname/.svn"; # We don't take care if it succed or not
            }
            die "$error\nStopped";
        }
        (my $file, my $status, my $revision, my $longName, my $branch) = readFileStatusFromStream(\*STATUS);
        if ($mode) {
            chmod $mode, "$dirname/.svn"; # We don't take care if it succed or not
        }
        # It is not possible to check the returned code of the command because
        # in the case of exported module it failed
        close(STATUS);

        return($status);
    }
}



# Check a module i.e display the list of changes between the content
# of the working directory and the content of the CVS repository.
# At the same time we verify the sticky tag for all files, it allows
# to detect inconsistencies in the working directory. It may occur
# when the user did some "cvs checkout" on a already existing MVS
# working directory.
#
# @param moduleName name of the module
# @param branchName name of the branch, only used to test consistency of
#        the working repository
#
# @return a list of listes. Each of them has the following format
#         (state filename revision)
#         The state is the kind of changes ("Up-to-date", "Locally Modified"...)
#         revision is the local CVS revision of the file (when it exist)
sub checkModule {
    (my $moduleName, my $branchName) = @_;
    my @resultFiles;

    # Build a hash list with all existing files in the module
    my %moduleFiles;
    foreach (getModuleFiles($moduleName)) {
        $moduleFiles{$_} = 1;
    }
    my %newFiles;

    my $varsFile = getModuleVarsFile($moduleName);
    my $dirName = rGetModuleDir(undef, $moduleName, ONERROR_RETURN);
    {
        local $SIG{INT} = 'IGNORE';
        my $mode;
        my %ignoredFiles;
		print STDOUT "checkModule svn --verbose  status $varsFile $dirName \n";
        unless (open(STATUS, "svn -q  status $varsFile $dirName 2>/dev/null |")) {
            my $error = $!;
            if ($mode) {
                chmod $mode, VARS_DIR."/.svn"; # We don't take care if it succed or not
            }
            die "$error\nStopped";
        }
        while ((my $file, my $status, my $revision, my $longName, my $branch) = readFileStatusFromStream(\*STATUS)) {
            # Check if the branch is matching the current one...
            # For exported file, when the content of the file is
            # the same as in the HEAD branch, sticky tag is set
            # to none but it doesn't mind that the file is
            # comming from the HEAD...
			print STDOUT "File $longName status is $status\n";
            if ($branch && ($branch ne $branchName)) {
                if ($mode) {
                    chmod $mode, VARS_DIR."/.svn"; # We don't take care if it succed or not
                }
                print STDERR "File $longName seems to be a file from $branch branch but your working directory is based on $branchName\n";
                print STDERR "You can lose some changes or corrupt the CVS database. Please, call immediately your MVS administrator\n";
                exit(1);
            }
            if ($longName) {
                # It has been possible to find the real file name,
                # remove it from the list of module's files
                push @resultFiles, [ ($status, $longName, $revision) ];
                delete $moduleFiles{$longName};

                if ( $longName =~ s/\.lnk$//o ) {
                    # It is a .lnk file, check if the link is existing
                    my $linkedFile = readlink $longName;
                    unless ( $linkedFile ) {
                        # The link is not existing, if the file has been
                        # remove, it is not normal. If the file is
                        # still here, do nothing; the check of the value
                        # will be done dring the "Unknown" files analysis
                        unless ($status eq "Locally Removed") {
                            (my $nf = $longName) =~ s/\.lnk$//o;
                            push @resultFiles, [ ("Missing Symbolic Link", $nf)];
                        }
                    }
                }
            }

            if ($status eq "Locally Added") {
                # Added file, the problem is that we don't know the
                # exact name, we will have to do a new CVS request
                if (exists $newFiles{$file}) {
                    $newFiles{$file}++;
                }
                else {
                    $newFiles{$file} = 1;
                }
            };
        }
        if ($mode) {
            chmod $mode, VARS_DIR."/.svn"; # We don't take care if it succed or not
        }
        # It is not possible to check the returned code of the command because
        # in the case of exported module it failed
        close(STATUS);
    }

    # Now the hash list only contains files which aren't known by CVS or
    # which are locally added
    # First loop to check locally added ones. During this loop, we may
    # detect some linked files which have to be removed from the list of
    # unknown files.
    # Because it is not possible to remove files from hash list we are looping
    # on, we have to use another variable...
    my %foundFiles;
    while ((my $file, undef) = each %moduleFiles) {
        my $shortName = basename($file);
        if ((exists $newFiles{$shortName}) && ($newFiles{$shortName} > 0)) {
            my $status = checkFileStatus($file);
            if ($status eq "Locally Added") {
                $newFiles{$shortName}--;
                $foundFiles{$file} = 1;
                push @resultFiles, [ ($status, $file) ];
                if ( $file =~ s/\.lnk$//o ) {
                    my $linkedFile = readlink $file;
                    unless ( $linkedFile ) {
                        (my $nf = $file) =~ s/\.lnk$//o;
                        push @resultFiles, [ ("Missing Symbolic Link", $nf)];
                        $foundFiles{$nf} = 1;
                    }
                }
            }
        }
    }
    # Remove from the list files which have been found
    while ((my $file, undef) = each %foundFiles) {
        delete $moduleFiles{$file};
    }

    # Now the hash list only contains file which aren't known by SVN 
    while ((my $file, undef) = each %moduleFiles) {
        # Check first if it is a symbolic link
        my $linkedFile = readlink $file;
        if ( $linkedFile ) {
            # Check if the corresponding .lnk file exists
            if ( -f "$file.lnk" ) {
                open(LNKFILE, "$file.lnk") || die "Can't open $file.lnk Stopped";
                my $storedLinkedFile = <LNKFILE>;
                close(LNKFILE);
                chomp $storedLinkedFile;
                if ($storedLinkedFile ne $linkedFile) {
                    push @resultFiles, [ ("Locally Modified Symbolic Link", $file) ];
                }
            }
            else {
                push @resultFiles, [ ("Unknown Symbolic Link", $file) ];
            }
        }
        else {
            push @resultFiles, [ ("Unknown", $file) ];
            if ( $file =~ s/\.lnk$//o ) {
                $linkedFile = readlink $file;
                unless ( $linkedFile ) {
                    push @resultFiles, [ ("Missing Symbolic Link", $file) ];
                }
            }
        }
    }
    # Sort files...
    # Files in alphabetical order excepted for Unknown ones which are
    # put at the beginning
    @resultFiles =
              sort {
                  if (($a->[0] =~ /^Unknown/) && !($b->[0] =~ /^Unknown/ )) {
                      -1;
                  }
                  elsif (!($a->[0] =~ /Unknown/) && ($b->[0] =~ /Unknown/)) {
                      1;
                  }
                  else {
                      $a->[1] cmp $b->[1];
                  }
              } @resultFiles;

     # Last entry if for uncommit merge if any
     if (-f getModuleMergeFile($moduleName)) {
         push @resultFiles, [ "Uncommited merge", $moduleName];
     }
     return(@resultFiles);
}



# Diff a module i.e display the list of changes between the content
# of the working directory and a specific version in CVS repository
#
# @param moduleName name of the module
# @param tagId tag to use for the comparison
#
# @return the list of changes
#         ( ("Modified" filename revision1 revision2)
#           ("Added" filename)
#           ("Removed" filename)
#           ...
#         )
#   revision2 is set with an empty string when the file is locally modified

sub diffModule {
    (my $moduleName, my $tagId) = @_;
    my @result;
    my $mvsBranch = $ENV{"MVSBRANCH"};
    my $varsFile = getModuleVarsFile($moduleName);
    # SHJ: Undef value is used as parameter to rGetModuleDir function in original version.
    # Undef is changed to $branchName_ to avoid the problem. 
    my $dirName = rGetModuleDir( $mvsBranch, $moduleName, ONERROR_RETURN);

    # Unfortunately the cvs diff works only on checkouted directories, so
    # we don't see files removed since the tagId if the directory is empty
    # now. The solution is to get the list of files with the tagId and to
    # compare with the list of checkouted files
    my @oldDirName = (rGetModuleDir($tagId, $moduleName, ONERROR_PRINT + ONERROR_EXIT));
    my %oldFiles = getCVSRevision($tagId, \@oldDirName);
	
    open(DIFF, "svn diff --brief -r $tagId $varsFile $dirName --summarize >&1 |") || die "$!\nStopped";
    while (<DIFF>) {
        chomp;
        # Take care messages are not exactly the same with pserver and direct
        # CVS access
        SWITCH: {
            ( /^Index:\s(.*)$/o ) && do {
                push @result, [ "Modified", $1 ];
                delete ${oldFiles{$1}};
                last SWITCH;
            };
            ( /^diff --brief -r([0-9\.]+) (.*)$/o ) && do {
                ($result[$#result][0] eq "Modified") || die "diff without modified file...: $_\. Stopped";
                my $rev1 = $1;
                my $rev2= "";
                my $field2 = $2;
                # If the file is locally modified, the second field is the
                # filename, else it is the second revision number
                if ( $field2 =~ /-r([0-9\.]+)$/o ) {
                    $rev2 = $1;
                }
                push @{$result[$#result]}, ($rev1, $rev2);
                last SWITCH;
            };

            ( /^cvs [a-z]+: tag ([^\s]*)\sis not in file (.*)$/o ) && do {
                die "Tag is not matching in line\n$_\nStopped" unless ($1 eq $tagId);
                push @result, [ "Added", $2 ];
                delete ${oldFiles{$1}};
                last SWITCH;
            };
            ( /^cvs [a-z]+: ([^\s]*)\sis a new entry,/o ) && do {
                push @result, [ "Added", $1 ];
                delete ${oldFiles{$1}};
                last SWITCH;
            };
            ( /^cvs [a-z]+: ([^\s]*) no longer exists/o ) && do {
                push @result, [ "Removed", $1, $oldFiles{$1} ];
                delete ${oldFiles{$1}};
                last SWITCH;
            };
            ( /^cvs [a-z]+: ([^\s]*) was removed,/o ) && do {
                push @result, [ "Removed", $1, $oldFiles{$1} ];
                delete ${oldFiles{$1}};
                last SWITCH;
            };
        }
    }
    # Not possible to test the returned code of the diff because it is not
    # null if there's a difference...
    close(DIFF);
    # Loop on files not already found by the diff. If they don't
    # exist it means that they have been removed
    foreach (sort (keys %oldFiles)) {
        unless (-f $_) {
            push @result, [ "Removed", $_, $oldFiles{$_} ];
        }
    }
    return(@result);
}



# Rdiff a module i.e display the list of changes between two specific
# versions in CVS repository
#
# @param moduleName name of the module
# @param fromTag first tag to use for the comparison
# @param toTag second tag to use for the comparison
#
# @return the list of differences (same format as diffModule)

sub rdiffModule {
    (my $moduleName, my $fromTag, my $toTag) = @_;
	my @result;
	
    my $varsFile = getModuleVarsFile($moduleName);
    # What is the directory name of the module ? We said it is the version
    # stored with the toTag excepted if there's no directory (it may occur if
    # the module doesn't exist for this tag)
    my $dirName = rGetModuleDir($toTag, $moduleName, ONERROR_RETURN);
    unless ($dirName) {
        $dirName = rGetModuleDir($fromTag, $moduleName, ONERROR_EXIT);
    }
	
    #my $fromBranchName = getBranchName($fromTag);
    #my $toBranchName = getBranchName($toTag);
    #open(DIFF, "svn rdiff -s -r $fromTag -r $toTag $varsFile $dirName 2>&1 |") || die "$!\nStopped";
    #print STDOUT "svn diff $SVNURL/$fromBranchName/tags/$fromTag $SVNURL/$toBranchName/tags/$toTag\n";
	
	#get the module Url from fromTag and toTag
	my $fromUrl;
	my $toUrl;
	(my $branch, undef) = hasSnapFormat($fromTag);
	unless ($branch) {
		($branch, undef) = hasBuildFormat($fromTag);
	}
	unless ($branch) {
		$branch = $fromTag;
		$fromUrl = "$SVNURL/$branch/main/";
	} else {
		$fromUrl = "$SVNURL/$branch/tags/$fromTag/";
	}
	
	($branch, undef) = hasSnapFormat($toTag);
	unless ($branch) {
		($branch, undef) = hasBuildFormat($toTag);
	}
	unless ($branch) {
		$branch = $toTag;
		$toUrl = "$SVNURL/$branch/main/";
	} else {
		$toUrl = "$SVNURL/$branch/tags/$toTag/";
	}
	
    #open(DIFF, "svn diff $SVNURL/$fromBranchName/tags/$fromTag $SVNURL/$toBranchName/tags/$toTag --summarize>&1 |") || die "$!\nStopped";
	
	my @diffFiles=($varsFile,$dirName);
	my $tmp;
	foreach $tmp (@diffFiles){
		open(DIFF, "svn diff  ${fromUrl}${tmp} ${toUrl}${tmp} --summarize>&1 |") || die "$!\nStopped";
		while(<DIFF>) {
			chomp;
			SWITCH: {
				( /^D (.*)/o ) && do {
					my $file =$1;
					push @result, ["Removed", $1];
					last SWITCH;
				};
				
				( /^M (.*)/o ) && do {
						my $file =$1;
						push @result, ["Modified", $1];
						last SWITCH;
				};
				
				( /^MM (.*)/o ) && do {
						my $file =$1;
						push @result, ["Modified", $1];
						last SWITCH;
				};
				
				( /^A (.*)/o ) && do { 
						my $file =$1;
						push @result, ["Added", $1];
						last SWITCH;
				};
				
				( /^MA (.*)/o ) && do { 
						my $file =$1;
						push @result, ["Added", $1];
						last SWITCH;
				};
				
				( /^AM (.*)/o ) && do { 
						my $file =$1;
						push @result, ["Added", $1];
						last SWITCH;
				};
				
			}
		}
		close(DIFF) || die "Cannot get diff between ${fromUrl}${tmp} ${toUrl}${tmp}  \nStopped";
	}

    return(@result);
}



# Compare two versions.
# They must have the format x[.y]* where x, y are integers
#
# @param vers1 first version
# @param vers2 second version
#
# @return -1 when vers1 < vers2
#          0 when vers1 = vers2
#          1 when vers1 > vers2

sub compareVersions {
    (my $vers1, my $vers2) = @_;
    my @rev1 = split /\./, $vers1;
    my @rev2 = split /\./, $vers2;
    if ($#rev1 > $#rev2) {
        for my $i ( $#rev2+1 .. $#rev1) {
            $rev2[$i] = "0";
        }
    }
    if ($#rev2 > $#rev1) {
        for my $i ( $#rev1+1 .. $#rev2) {
            $rev1[$i] = "0";
        }
    }
    # Now both revisions have the same number of digits
    for my $i ( 0 .. $#rev1 ) {
        if ($rev1[$i] < $rev2[$i]) {
            return(-1);
        }
        if ($rev1[$i] > $rev2[$i]) {
            return(1);
        }
    }
    return(0);
}



# Search in a list of changes, which ones are corresponding to backware
# changes. i.e.
#   The new revision number is smaller than the old one
#   The file is removed but still in the branch
#   The file is added but doesn't exist in the branch
#
# @param branchName which branch to use for add and remove check
# @param diffListRef reference to a diff list (same format as diffModule)
#
# @return a subset of the initial list

sub extractBackwareChanges {
    (my $branchName, my $diffListRef) = @_;
    my @result;
    print STDOUT "Mvs.pm extractBackwareChanges for branch $branchName.\n";
    foreach my $diffRef (@{$diffListRef}) {
        my $type = $diffRef->[0];
        SWITCH: {
            ( $type eq "Modified" ) && do {
                # Compare CVS revisions
                my $res = compareVersions($diffRef->[2], $diffRef->[3]);
		#comment by SHJ for rdiffModule is not fuly implemented
		#($res == 0) && die "Same CVS revision : @{$diffRef}. Stopped";
                if ($res == 1) {
                    push @result, $diffRef;
                }
                last SWITCH;
            };
            ( $type eq "Added" ) && do {
                my @files = ($diffRef->[1]);
                unless (getSVNRevision($branchName, \@files)) {
                    push @result, $diffRef;
                }
                last SWITCH;
            };
            ( $type eq "Removed" ) && do {
                my @files = ($diffRef->[1]);
                if (getSVNRevision($branchName, \@files)) {
                    push @result, $diffRef;
                }
                last SWITCH;
            };
        }
    }
    return(@result);
}



# Release a module i.e remove the vars file and the module directory from
# the working directory. This method doesn't check if something has not
# been commited, we expecting that it has already been done before.
# This method works even if the module is partialy available (only the
# vars) but it is unable to remove the directory if the vars is not
# available (because it doesn't known its name)
#
# @param moduleName name of the module

sub releaseModule {
    (my $moduleName) = @_;
    my $dirName= rGetModuleDir(undef, $moduleName, ONERROR_EXIT);

    # Remove the directory
    if (-d $dirName) {
        rmtree(($dirName), 0, 0);
    }
    # It should not occur excepted in case of problem with the
    # rmtree or if directory is not a directory
    (-e $dirName) && die "$dirName still existing. Stopped";

    # Remove the merge file (we are sure to be able to do that)
    my $mergeFile = getModuleMergeFile($moduleName);
    if (-f $mergeFile) {
        unlink($mergeFile);
    }
    # It should not occur excepted in case of problem with the
    # unlink or if mergeFile is not a file
    (-e $mergeFile) && die "$mergeFile still existing. Stopped";

    # Remove the var file.
    # cvs release doesn't work on a file, so we just remove the
    # vars file. The drawback is that the entry for this file is still
    # existing in vars/CVS/Entries, so we have to remove it too.
    my $varsFile = getModuleVarsFile($moduleName);
    removeCVSEntry($varsFile);

    # Now remove .# files from the vars directory if any
    opendir DIR, dirname($varsFile);
    my @allDFiles = grep /^\.#.*$/o, readdir DIR;
    closedir DIR;
    my $varsBaseName = basename($varsFile);
    foreach (@allDFiles) {
        if ( /.\#$varsBaseName\.[0-9]+\./ ) {
            my $oldFile = dirname($varsFile)."/".$_;
            if (-f $oldFile) {  # Just to be sure not to remove a directory
                unlink($oldFile);
            }
        }
    }
}



###############################################################
# Methods dealing with the module merge
###############################################################

# Return the snap identifier corresponding to a build identifier even if
# it is not in the same branch (it may occurs if the module has never been
# delivered again since the branch creation)
#
# @param moduleName the name of the module
# @param buildId the build identifier
#
# @return a snap identifier.

sub getSnapFromBuild {
    (my $moduleName, my $buildId) = @_;
    (my $branch, undef) = hasBuildFormat($buildId);
    die "$buildId not a build identifier" unless ($branch);
    my @tagFileContent = readTagFile($branch, $moduleName);
    for (reverse @tagFileContent) {
        my @line = @{$_};
        if ($line[0] eq BUILD_TAG) {
            if ($line[1] eq $buildId) {
                if (hasSnapFormat($line[2])) {
                    return($line[2]);
                }
                else {
                    # Build has been made using another build (it means
                    # that no delivery has been done between the two
                    # builds). There's two cases: the build is in the same
                    # branch or the build is from another branch
                    (my $newBranch, undef) = hasBuildFormat($line[2]);
                    die "$line[2] not a build identifier" unless ($newBranch);
                    if ($newBranch eq $branch) {
                        # Same branch, because the loop is in the reverse
                        # order, we must find the build forward...
                        $buildId = $line[2];
                    }
                    else {
                        # New branch, we continue the search into it
                        return(getSnapFromBuild($moduleName, $line[2]));
                    }
                }
            }
        }
    }
    die "$buildId not find for module $moduleName. Stopped";
}



# Return the history of identifiers (snap only) for a module
# between two tags. The search is starting from the last tag and stops
# when the first tag has been found or when the creation of the module
# has been reach.
#
# @param moduleName name of the module
# @param startTag snap or build identifier from which the history has to be
#        compute. If it is a branch name, history starts with the last version
#        in the branch
# @param endTag snap for the end of the search (may be undef)
#
# @return a list of snaps identifiers giving the module history in chronologic
#         reverse order, including the startTag and the endTag (or the START
#         one if there's no endTag or if it has not be found)

sub getModuleFullHistory {
    (my $moduleName, my $startTag, my $endTag) = @_;
    (my $branch, undef) = hasSnapFormat($startTag);
    my $found = 0;
    unless ($branch) {
        ($branch, undef) = hasBuildFormat($startTag);
        if ($branch) {
            $startTag = getSnapFromBuild($moduleName, $startTag);
        }
    }
    unless ($branch) {
        if (isExistingBranch($startTag, ONERROR_RETURN)) {
            $branch = $startTag;
            # We take everything in the branch, so we don't have to
            # search first the starting point
            $found = 1;
        }
    }
    die "Cannot find branch name in $startTag. Stopped" unless ($branch);

    my @result;
    # We assume that snap identifiers in the tag file are in chronologic
    # order
    for (reverse readTagFile($branch, $moduleName)) {
        my @line = @{$_};
        if ($line[0] eq SNAP_TAG ) {
            if ($line[1] eq $startTag) {
                $found = 1;
            }
            if ($found) {
                push @result, [ $line[1], $line[3], $line[4], $line[5] ];
            }
            if ($endTag && ($line[1] eq $endTag)) {
                last;
            }
        }
        elsif ( $line[0] eq START_TAG ) {
            # It is the beginning of the branch, we have to explore
            # the mother branch starting from the creation point (if it
            # exists)
            if ($line[2]) {
                @result = (@result, &getModuleFullHistory($moduleName, $line[2], $endTag));
            }
            else {
                push @result, [ $line[1], "", "", "" ];
            }
        }
    }
    return(@result);
}



# Explore a branch (in reverse order) in order to find a way to reach one of
# the identifiers stored in the hash list
#
# @param startTag, the tag from which the exploration has to start. It may
#        be a snap identifier, a build identifier or a branch name
# @param moduleName name of the module
# @param fromVersionsPtr reference to a hash list containing the snap
#        identifiers to find and their rank
#
# @return the smaller rank in the hash list reached from startTag

sub exploreBranch {
    (my $startTag, my $moduleName, my $fromVersionsPtr) = @_;
    # Compute the branch name from the tag (else we expect to get it
    # directly as first argument
    (my $branch, undef) = hasSnapFormat($startTag);
    my $found = 0;
    unless ($branch) {
        ($branch, undef) = hasBuildFormat($startTag);
        if ($branch) {
            $startTag = getSnapFromBuild($moduleName, $startTag);
        }
    }
    unless ($branch) {
        if (isExistingBranch($startTag, ONERROR_RETURN)) {
            $branch = $startTag;
            $found = 1;
        }
    }
    die "Cannot find branch name in $startTag. Stopped" unless ($branch);

    # When we find a merge, there's no need to explore two times
    # the same branch, so we store the already explored branches in
    # a hash list
    my %alreadyExploredBranches;

    # We initialize the rank with the size of the hash list
    my $rank = keys %$fromVersionsPtr;

    # If the module was not existing in the branch, we don't have to
    # continu. It is just a way to prevent from error when trying to read
    # the .tags file
    unless (wasExistingModule($branch, $moduleName, ONERROR_RETURN)) {
        return($rank);
    }

    # Loop on the existing tags in the branch. We expect that snap and
    # merge identifiers are in chronological order in the tag file
    for (reverse readTagFile($branch, $moduleName)) {
        my @line = @{$_};
        if ($line[0] eq SNAP_TAG) {
            if ($line[1] eq $startTag) {
                $found = 1;
            }
            if ($found) {
                if (exists $$fromVersionsPtr{$line[1]}) {
                    my $newRank = $$fromVersionsPtr{$line[1]};
                    if ($newRank < $rank) {
                        return($newRank);
                    }
                    else {
                        return($rank);
                    }
                }
            }
        }
        elsif ( $line[0] eq MERGE_TAG ) {
            if ($found) {
                # A merge has been done from another branch in this one,
                # we have to explore this branch too starting from the
                # merging point
                (my $brName, undef) = hasSnapFormat($line[3]);
                ($brName) || die "$line[3] not a snap identifier\n";
                # If a merge has already be done from the same branch,
                # there's no need to explore the branch again (because
                # we are in the chronological reverse order)
                unless (exists $alreadyExploredBranches{$brName}) {
                    my $newRank = exploreBranch($line[3], $moduleName, $fromVersionsPtr);
                    if ($newRank < $rank) {
                        $rank = $newRank;
                    }
                    $alreadyExploredBranches{$brName} = 1;
                }
            }
        }
        elsif ( $line[0] eq START_TAG ) {
            # It is the beginning of the branch, we have to explore
            # the mother branch starting from the creation point (if it
            # exists)
            if ($line[2]) {
                my $newRank = exploreBranch($line[2], $moduleName, $fromVersionsPtr);
                if ($newRank < $rank) {
                    $rank = $newRank;
                }
            }
        }
    }
    return($rank);
}



# Compute which should be the snap identifier to use at the first reference
# for a snap from a given tag. The reason is that by default CVS merges
# all changes from one branch to another one. For the first merge, it
# works fine but for the second one CVS tries to apply the same changes
# again, so there was conflicts at the first time, you get them again.
# The solution is to merge only changes done between the last merge and the
# new one.
# This method tries to find the point used for the last merge (or the
# branch creation point if no merge have been done). The system is the
# following:
# - First we compute the history of the source branch (starting from the
#   given tag until the module creation). We give a rank to each point in
#   in this list, the newest snap has the lower rank number.
# - Then we search for all ways to reach one of these points from the target
#   branch.
# - The solution is the reached point with the lower rank.
#
# @param branchName name of the branch we want to merge to
# @param moduleName name of the module to merge
# @param mergeFromTag name of the identifier to use as endding point for
#        the merge
#
# @return snap identifier to use as starting point for the merge

sub computeLastMergeTag {
    (my $branchName, my $moduleName, my $mergeFromTag) = @_;

    # First loop on source branch. We create a hash list with all snaps
    # numbered from the source snap identifier to the HEAD branch.
    my %fromVersions;
    my $pos = 1;
    for (getModuleFullHistory($moduleName, $mergeFromTag, undef)) {
        my $snap = $_->[0];
        $fromVersions{$snap} = $pos;
        $pos++;
    }

    # Now explore the target branch from its head in order to
    # find all ways to reach one of the snaps existing in the fromVersions
    # hash list. The newer snap (i.e. the snap with the lower rank) is
    # the snap to use for the merge
    my $tagRank = exploreBranch($branchName, $moduleName, \%fromVersions);

    # We have the rank of the snap to use for the merge, we just return
    # it
    for (keys %fromVersions) {
        if ($fromVersions{$_} == $tagRank) {
            return($_);
        }
    }

    # This point should never been reached
    die "No snap with the rank $tagRank. Stopped";
}


###############################################################
# Methods dealing with the "branchProperties" file
###############################################################

# Get a branch property attribut
#
# @param branchName branch to use
# @param propertyName name of the property (please, use the defined constants)
#
# @return the property value

sub getBranchProperty {
    (my $branchName, my $propertyName) =  @_;

    unless (exists $branchPropertiesFilesCache_{$branchName}) {
        # Get the list of branches with their properties
        getListOfBranches();
    }
    (exists $branchPropertiesFilesCache_{$branchName}) || die "Unable to find properties for $branchName branch. Stopped";
    return $branchPropertiesFilesCache_{$branchName}->{$propertyName};
}



# Extract the branch name from a given tag
# Not used at this time.
#
# @param moduleName name of the module
# @param tagId snap or build identifier
#
# @return the branch name or an empty string
#
#sub getBranchFromTag {
#    (my $moduleName, my $startTag) = @_;
#
#    (my $branch, undef) = hasSnapFormat($startTag);
#    if ($branch) {
#        return($branch);
#    }
#    ($branch, undef) = hasBuildFormat($startTag);
#    if ($branch) {
#        return($branch);
#    }
#    if (isExistingBranch($startTag, 0)) {
#        return($startTag);
#    }
#    return "";
#}



# Verify if a tag (snap or build) is existing for a module
#
# @param name name of the module
# @param tagId snap or build identifier
# @param errorMode indicates the expected behaviour in case of unexisting tag
#
# @return the branch name or an empty string

sub isExistingTag {
    (my $name, my $tag, my $errorMode) = @_;

    (my $branch, my $modName) = hasSnapFormat($tag);
    if ($branch) {
        if (isExistingSnapIdentifier($branch, $modName, $tag, $errorMode)) {
            unless ($modName eq $name) {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "$tag is not a snap identifier of $name\n";
                }
                if ($errorMode & ONERROR_EXIT) {
                    exit(2);
                }
                else {
                    return("");
                }
            }
            return($branch);
        }
        else {
            return("");
        }
    }
    ($branch, undef) = hasBuildFormat($tag);
    if ($branch) {
        if (isExistingBuildIdentifier($branch, $tag, $errorMode)) {
            if (isExistingModule($tag, $name, ONERROR_RETURN)) {
                return($branch);
            }
            elsif (isExistingComponent($tag, $name, ONERROR_RETURN)) {
                return($branch);
            }
            else {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "$tag is not a build identifier of $name\n";
                }
                if ($errorMode & ONERROR_EXIT) {
                    exit(2);
                }
                return("");
            }
        }
        else {
            return("");
        }
    }
    if ($errorMode & ONERROR_PRINT) {
        print STDERR "$tag not a snap nor a build identifier\n";
    }
    if ($errorMode & ONERROR_EXIT) {
        exit(2);
    }
    return "";
}



# Check if the merge is authorized. If the module belongs to a component
# and this component has a "merge from" property, use it else use the
# branch "merge from" property.
# If the property is existing but is empty it means that no merge is
# allowed.
#
# @param modOrCompName name of the module or of the component
# @param mergeFrom name of the branch to merge from
# @param mergeTo name of the branch to merge to
#
# @return 0 (merge not authorized) or 1 (merge authorized)

sub checkAuthorizedMerge {
    (my $modOrCompName, my $mergeFrom, my $mergeTo) = @_;

    my @branchesToExplore;
    my $compName;
    # Check if it is a component name
    if (wasExistingComponent($mergeFrom, $modOrCompName, ONERROR_RETURN)) {
        $compName = $modOrCompName;
    }
    else {
        # If the module belongs to a component, get first the component
        # permission
        $compName = getContainingComponent($mergeTo, $modOrCompName);
    }
    if ($compName) {
        my %def = readComponentDefinitionFile($mergeTo, $compName, ONERROR_RETURN);
        if (exists $def{+COMP_MERGE_FROM}) {
            @branchesToExplore = keys %{$def{+COMP_MERGE_FROM}};
        }
        else {
            @branchesToExplore = @{getBranchProperty($mergeTo, BRANCH_MERGE_FROM)};
        }
    }
    else {
        @branchesToExplore = @{getBranchProperty($mergeTo, BRANCH_MERGE_FROM)};
    }
    for my $branch (@branchesToExplore) {
        if ( $branch eq $mergeFrom ) {
            return(1);
        }
    }
    return(0);
}



#########################
# Methods for the management of the <components>.def File
#########################



# Get the full name of the file describing the component (usualy named the
# def file).
#
# @param moduleName name of the module
#
# @return the file name

sub getComponentDefinitionFile {
    (my $componentName) = @_;
    return COMPONENTS_DEFINITIONS_DIR."/$componentName.def";
}



# Get the list of components a component is depending on
# The method is not the same when we want the list for a given build
# or for a branch
#
# @param ident name of the branch or build identifer
# @param componentName name of the component
#
# @return a hash list { component -> branch|buildId }

sub getListOfUsedComponents {
    (my $ident, my $componentName) = @_;
    my %result;
    (my $branch, undef) = hasBuildFormat($ident);
    if ($branch) {
        # ident is a build identifier, we use the tag file in order to
        # know which versions of components have been used for the build
        my $found = 0;
        foreach my $lineRef (readComponentTagFile($branch, $componentName)) {
            if (($lineRef->[0] eq BUILD_TAG) && ($lineRef->[1] eq $ident)) {
                $found = 1;
                if ($lineRef->[2]) {
                    for my $deps (split /\s/, $lineRef->[2]) {
                        if ($deps =~ m/^([^!]+)\!(.+)$/) {
                            $result{$1} = $2;
                        }
                        else {
                            die "$deps doesn't look like a dependency description for $componentName!$ident. Stopped";
                        }
                    }
                }
            }
        }
        unless ($found) {
            die "$ident build not found in $componentName tag file. Stopped";
        }
    }
    else {
        # ident is a branch name, we use the definition file in order to
        # know which components are needed
        my %def = readComponentDefinitionFile($ident, $componentName, ONERROR_RETURN);
        if ($def{+COMP_DEPS}) {
            %result = %{$def{+COMP_DEPS}};
            # Loop on the dependencies to replace empty values by the branch
            # name
            foreach my $cName (keys %result) {
                unless ($result{$cName}) {
                    $result{$cName} = $ident;
                }
            }
        }
    }
    return %result
}



# Get the list of components a component is depending on
#
# @param identifier name of the branch or build identifer
# @param componentName name of the component
# @param recur indicates that all dependencies must be returned and not only
#        the first level
#
# @return a hash list { component -> branch|buildId }

sub getComponentDependencies {
    (my $identifier, my $componentName, my $recur) = @_;
    my %depsHash = ( $componentName => $identifier);
    my %depsAddBy;
    my @depsList = keys %depsHash;
    while ($#depsList >= 0) {
        my $comp = pop @depsList;
        my %newDeps = getListOfUsedComponents($depsHash{$comp}, $comp);
        foreach my $newComp (sort (keys %newDeps)) {
            if (exists $depsHash{$newComp}) {
                unless ($depsHash{$newComp} eq $newDeps{$newComp}) {
                    print STDERR "Warning: $comp!$depsHash{$comp} is depending on $newComp!$newDeps{$newComp} but $depsAddBy{$newComp}!$depsHash{$depsAddBy{$newComp}} is depending on $newComp!$depsHash{$newComp}.\n";
                }
                next;
            }
            $depsHash{$newComp} = $newDeps{$newComp};
            # Only used to display where the inconsistency is coming from...
            $depsAddBy{$newComp} = $comp;
            if ($recur) {
                push @depsList, $newComp;
            }
        }
    }
    # Remove the component itself...
    delete $depsHash{$componentName};
    return %depsHash;
}



# Search dependencies for a list of components. Display a warning when
# an inconsistency is found.
#
# @param componentVersionRef a reference to a hash list
#        componentName => build or branch
#
# @return a hash list (copy of the parameter) more all components needed by
#         the components available in the initial list

sub getComponentsDependencies {
    (my $componentVersionRef) = @_;

    my %result = %{$componentVersionRef};
    foreach my $componentName (sort (keys %{$componentVersionRef})) {
        my $ident = $componentVersionRef->{$componentName};
        # We have to get all components recusively even if we are not in the
        # recur mode because of tool modules
        my %neededComponents = getComponentDependencies($ident, $componentName, 1);
        foreach (keys %neededComponents) {
            if (exists $result{$_}) {
                unless ($result{$_} eq $neededComponents{$_}) {
                    print STDERR "Warning: Dependency on $_!$result{$_} and $_!$neededComponents{$_} found.\n";
                }
                next;
            }
            $result{$_} = $neededComponents{$_};
        }
    }
    return(%result);
}



# Search archs for a components. Display a warning when
# an inconsistency is found.
#
# @param identifier name of the branch or build identifer
# @param componentName
#
# @return a list of archs

sub getComponentArchs {
    (my $identifier, my $componentName, my$errorMode) = @_;

    my %result = ();
    my %modules = getListOfAggragateModules($identifier, $componentName);
    foreach my $moduleName (keys %modules) {
    	my @archs = getModuleArchs($identifier, $moduleName, $errorMode);
    	foreach (@archs) {
            $result{$_} = "";
    	}
    }
    
    return keys %result;
}



# Get the list of the modules defined in a given component for a specified
# branch or build
#
# @param identifier name of the branch or build identifier
# @param componentName name of the component
#
# @return a hash list of modules included into the component for the given
#         version

sub getListOfAggragateModules {
    (my $identifier, my $componentName) = @_;

    my %def = readComponentDefinitionFile($identifier, $componentName, ONERROR_RETURN);
    if ($def{+COMP_AGGR}) {
	    #print STDOUT "getListOfAggragateModules done\n";
        return (%{$def{+COMP_AGGR}});
    }
    print STDOUT "getListOfAggragateModules done\n";
    return();
}



# Return the component containing a given module
#
# @param identifier branch name or build identifier to use
# @moduleName name of the module
#
# @return the component name or null

sub getContainingComponent {
    (my $identifier, my $moduleName) = @_;
    foreach my $compName (getListOfComponents($identifier)) {
        my %modList = getListOfAggragateModules($identifier, $compName);
        if (exists $modList{$moduleName}) {
           return($compName);
        }
    }
    return("");
}



# Check if a component is existing.
#
# @param identifier name of the branch or build identifier
# @param componentName name of the component
# @param errorMode indicates the expected behaviour in case of unexisting
#        component
#
# @return 1 or 0

sub isExistingComponent {
    (my $identifier, my $componentName, my $errorMode) = @_;
# First solution, not very efficient because of the cost for the get of the
# list of components
#    foreach (getListOfComponents($identifier) ) {
#       if ( $_ eq $componentName ) {
#           return 1;
#       }
#    }

    # If the def file exists for this identifier, the component exists
    # Another advantage is to put the def file into the cache. I guess if
    # we test existance of the component we will need the content of this file
    # soon
    if (readComponentDefinitionFile($identifier, $componentName, ONERROR_RETURN)) {
        return(1);
    }
    #print STDERR "Mvs.pm isExistingComponent $componentName is not Exist in $identifier.\n";
    if ($errorMode == ONERROR_RETURN) {
        return(0);
    }

    # Additional tests to know which error message has to be displayed
    (my $branch, undef) = hasBuildFormat($identifier);
    if ($branch) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "$componentName component not existing for $identifier build\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(2);
        }
        return(0);
    }

    ($branch, undef) = hasSnapFormat($identifier);
    if ($branch) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "$identifier snap may not be used as reference for $componentName component\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(2);
        }
        return(0);
    }
    if (isExistingBranch($identifier, $errorMode)) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "No component named $componentName in $identifier branch\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(2);
        }
        return(0);
    }
    return(0);
}



# Check if a component is existing or was exiting in a branch
# i.e. test existance of the <component>.log file instead of the <component>.def
# one
#
# @param branchName name of the branch
# @param componentName name of the component
# @param errorMode indicates the expected behaviour in case of unexisting
#        component
#
# @return 1 or 0

sub wasExistingComponent {
    (my $branchName, my $componentName, my $errorMode) = @_;
    my @result = readComponentTagFile($branchName, $componentName);
    if ($#result ==  -1) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "Component $componentName never existing in $branchName branch\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(2);
        }
        return(0);
    }
    else {
        return(1);
    }
}



# Modify lines in the "Definition" File
#
# @param branchName name of the branch
# @param action what we have to do ("add" or "remove")
# @param componentName name of the component
# @param entryListRef a reference to a list. See modifyComponentDefinition
#        method for details about this parameter
# @param logMess message to use for the cvs commit

sub modifyEntryToComponentDefinitionFile {
    (my $branchName, my $action, my $componentName, my $entryListRef, my $logMess) = @_;
    my $tmpDir = $TMP_DIR."/mvs.metcdf.$$";
    mkpath(($tmpDir), 0, 0755) || die "Can't create $tmpDir. Stopped";
    my $defFile = getComponentDefinitionFile($componentName);
    my $try=1;
    my $currentDir=cwd();
    chdir($tmpDir) || die "Unable to change dir to $tmpDir. Stopped";
    while (1) {
        my $returnCode=0;
	#my @args = ("svn", "$cvsVerbose_", "checkout");
        if ($branchName eq "HEAD") {
		#push @args, $defFile;
		print STDOUT "modifyEntryToComponentDefinitionFile cd $tmpDir; svn co -q $SVNURL/".COMPONENTS_DEFINITIONS_DIR."  .\n";
		system("cd $tmpDir; svn co -q $SVNURL/$branchName/main/".COMPONENTS_DEFINITIONS_DIR."  $tmpDir/".COMPONENTS_DEFINITIONS_DIR) ;
		#||  die "$? , Could not check out dir ".COMPONENTS_DEFINITIONS_DIR;
        }
        else {
		system("cd $tmpDir; svn co -q $SVNURL/$branchName/main/".COMPONENTS_DEFINITIONS_DIR." $tmpDir/".COMPONENTS_DEFINITIONS_DIR);# ||  die "$?, Could not check out dir ".COMPONENTS_DEFINITIONS_DIR;
        }
	#system(@args);
        modifyComponentDefinition ("$tmpDir/$defFile", $action, $entryListRef);
	#my @args = ("svn", "$cvsVerbose_", "commit", "-m", $logMess, $defFile);
        $returnCode = system("cd $tmpDir/".COMPONENTS_DEFINITIONS_DIR."; svn $cvsVerbose_ commit -m \"$logMess\"");
        unless ( $returnCode == 0) {
            next;
        }
        # The file is commited. We can exit from the loop.
        last;
    }
    continue {
        # The attempt to update the file has failed.
        unlink("$tmpDir/$defFile");
        unlink("$tmpDir/$defFile.new");
        $try++;
        if ($try <= MAX_TRY) {
            print STDERR "Retry .....\n ";
        }
        else {
            print STDERR "Sorry, MVS cannot complete successfully the command. \n";
            print STDERR "Please to restart your MVS command.\n";
            rmtree(($tmpDir), 0, 0);
            exit 1;
        }
    }
    chdir($currentDir) || die "Unable to change dir to $currentDir. Stopped";
    rmtree(($tmpDir), 0, 0);
}



# Modify lines in a component definition file
#
# @param $defFile the component definition file name
# @param action what we have to do ("add" or "remove")
# @param entryListRef a reference to a list with the following format:
#          [ (property1, (value11, value12, ...),
#            (property2, ((value21, value22, ...),
#            ...
#          ]
#        where propertyN is one of the component property name

sub modifyComponentDefinition {
    (my $defFile, my $action, my $entryListRef) = @_;
    # Build a hash list from the given list in order to find faster when
    # a line has to been modified in the file. The used key is the first
    # element in the list, the value is the list without the first element.
    my %linesToModify;
    foreach (@$entryListRef) {
        my @line = @$_;
        my $key = shift @line;
        $linesToModify{$key} = [ @line ];
    }

    open(NEWDEFFILE, "> $defFile.new") || die $!;
    open(OLDDEFFILE, "$defFile") || die $!;
    # The user may modify this file so we did a copy of each line
    # (including empty and comments) and we try to do as less changes
    # as possible
    my $continuingLine = 0;
    my $propertyValue = "";
    my $property;
    my $endOfPreviousLine = "";
    while (<OLDDEFFILE>) {
        chomp;
        unless ($continuingLine) {
            # Search for the beginning of a property definition
            # It is only possible at the beginning of a line
            if ( m/^(\s*)$/ ||
                 m/^(#)(.*)$/o ||
                 m/^([^:]*):(\s*)(.*)$/o ) {
                # We found a new property, add info for the previous one
                # if any
                if ($property) {
                    if (exists $linesToModify{$property} && ($action eq "add")) {
                        foreach (@{$linesToModify{$property}}) {
                            print NEWDEFFILE " $_";
                        }
                        delete $linesToModify{$property};
                    }
                }
                print NEWDEFFILE $endOfPreviousLine;
                $endOfPreviousLine = "";
                if ( $1 =~ m/^\s*$/ ) {
                    $propertyValue = $1;
                    $property = "empty";
                }
                elsif ($1 eq "#") {
                    print NEWDEFFILE "$1";
                    $propertyValue = $2;
                    $property = "comment";
                }
                else {
                    print NEWDEFFILE "$1:$2";
                    $propertyValue = $3;
                    ($property = $1) =~ s/\s//og;
                }
            }
        }
        else {
            $propertyValue = $_;
        }
        if ($propertyValue =~ /\\$/) {
            $continuingLine = 1;
            $propertyValue =~ s/\\$//;
        }
        else {
            $continuingLine = 0;
        }
        my $modified = 0;
        if (exists $linesToModify{$property} ) {
            # Remove values. We have to take into account several cases
            # - the line contains only the value
            # - the line starts with the value
            # - the line ends with the value
            # - the line contains the value somewhere in the middle
            if ( $action eq "remove" ) {
                my @remVal = @{$linesToModify{$property}};
                my $oldPropertyValue = $propertyValue;
                foreach (@remVal) {
                    $propertyValue =~ s/^${_}$//;
                    $propertyValue =~ s/^${_}\s//;
                    $propertyValue =~ s/\s${_}\s/ /;
                    $propertyValue =~ s/\s${_}$//;
                }
                $modified = ($oldPropertyValue ne $propertyValue);
            }
        }
        if ($modified && ($propertyValue =~ /^\s*$/)) {
            # If the new line is empty we don't print it
            unless ($continuingLine) {
                $endOfPreviousLine = "\n";
            }
        }
        else {
            print NEWDEFFILE $endOfPreviousLine;
            print NEWDEFFILE "$propertyValue";
            if ($continuingLine) {
                $endOfPreviousLine = "\\\n";
            }
            else {
                $endOfPreviousLine = "\n";
            }
        }
    }
    print NEWDEFFILE "\n";
    close OLDDEFFILE;
    close NEWDEFFILE;
    rename "$defFile.new", "$defFile" || die "Cannot rename $defFile";
}



#########################
# Methods dealing with component builds
#########################

# Test if a build identifier exists for a component
#
# @param branchName name of the branch
# @param componentName name of the component
# @param buildId the build identifier
# @param errorMode indicates the expected behaviour in case of unexisting
#        build
#
# @return 0 or 1

sub isExistingComponentBuildIdentifier {
    (my $branchName, my $componentName, my $buildId, my $errorMode) = @_;
    foreach (getComponentBuildIdentifiers($branchName, $componentName)) {
        if ($_ eq $buildId) {
            return(1);
        }
    }
    if ($errorMode == ONERROR_RETURN) {
        return(0);
    }

    # Additional test to know which error message has to be displayed
    if (isExistingComponent($branchName, $componentName, $errorMode)) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "$buildId not a $componentName build identifier\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(2);
        }
    }
    return(0);
}



# Returns the list of build identifiers for the component in a given branch
# This list is based on the content of the <component>.log file.
#
# @param branchName name of the branch
# @param componentName name of the component
#
# @return the list of build

sub getComponentBuildIdentifiers {
    (my $branchName, my $componentName) = @_;
    my @buildList;
    foreach my $lineRef ( readComponentTagFile($branchName, $componentName) ) {
        my $tag = $lineRef->[0];
        if ( $tag eq BUILD_TAG ) {
            push @buildList, $lineRef->[1];
        }
    }
    return @buildList;
}



# Returns the last build identifier for a component in a given branch
#
# @param branchName name of the branch
# @param componentName name of the component
# @param errorMode indicates the expected behaviour in case of unexisting tag
#
# @return the list of build

sub getComponentLastBuildIdentifier {
    (my $branchName, my $componentName, my $recur, my $errorMode) = @_;

    my $lastBuild;
    foreach my $lineRef ( readComponentTagFile($branchName, $componentName) ) {
        my $tag = $lineRef->[0];
	#print STDOUT "Mvs.pm getComponentLastBuildIdentifier for $componentName, $tag, $$lineRef->[1]\n";
        if ( $recur && ($tag eq START_TAG)) {
            $lastBuild = $lineRef->[2];
        }
        elsif ( $tag eq BUILD_TAG ) {
            $lastBuild = $lineRef->[1];
        }
    }
    unless ($lastBuild) {
        if ($errorMode & ONERROR_PRINT) {
            print STDERR "Mvs.pm getComponentLastBuildIdentifier: No build have been done in $branchName branch for $componentName component\n";
        }
        if ($errorMode & ONERROR_EXIT) {
            exit(1);
        }
    }
    return($lastBuild);
}



#########################
# Methods for the management of the <component>.def file
#########################



# Get the content of the "<component>.def" file for a specific version
# of a component.
#
# @param identifier a branch or a build identifier
# @param componentName the name of the component
# @param errorMode indicates the expected behaviour in case of error during the
#        read
#
# @return the component definition hash list. May be udefined if the component
#         doesn't exist for the given identifier

sub readComponentDefinitionFile {
    (my $identifier, my $componentName, my $errorMode) = @_;
    if (exists $componentDefinitionFilesCache_{"${identifier}-${componentName}"}) {
        return %{$componentDefinitionFilesCache_{"${identifier}-${componentName}"}};
    }
    my $componentDefFile = getComponentDefinitionFile($componentName);
    my $tmpDir;
    #print STDOUT "readComponentDefinitionFile Running Svn command svn cat  -r $identifier $SVNURL/$componentDefFile\n"; 
    #SHJ removed -r parameter, To be fixed
    my $bname=getBranchName($identifier);
    open(COMP_DEF_FILE, "svn cat $SVNURL/$bname/main/$componentDefFile  $DROP_ERROR |") || die "Cannot run svn command. Stopped";
    #print STDOUT "readComponentDefinitionFile  $componentDefFile  $errorMode $componentName  from branch $identifier\n";
    my %def = readComponentDefinitionFileFromStream(\*COMP_DEF_FILE, $componentDefFile, $errorMode);
    # We check the error code only in is "exit" mode because cvs command may
    # fails if the build identifier doesn't exist
    if ($errorMode & ONERROR_EXIT) {
        close(COMP_DEF_FILE) || die "Unable to checkout $componentDefFile for $identifier identifier. Stopped";
    }
    else {
        close(COMP_DEF_FILE);
    }
    if ($tmpDir) {
        rmtree(($tmpDir), 0, 0);
    }
    #print STDOUT "Mvs.pm readComponentDefinitionFile end. \n";
    $componentDefinitionFilesCache_{"${identifier}-${componentName}"} = \%def;
    return(%def);
}



# Get the content of the "<component>.def" file using a stream.
# Display errors on stderr.
#
# @param fileRef reference to the stream to use
# @param filename name of the file, it is only use to display error messages
# @param errorMode indicates the expected behaviour in case of error during the
#        read
#
# @return the branchProperties hash list or undef
#         This hash list has the following format
#         COMP_AGGR => { ModuleName -> 1 }
#         COMP_COMMENT => comment
#         COMP_DEPS => { ComponentName => branchName }

sub readComponentDefinitionFileFromStream {
    (my $fileRef, my $filename, my $errorMode) = @_;

    my %result;
    # If we detected an error, we just set this variable, it allows
    # to continu the parsing
    my $error = 0;
    my $prevLine;
    while (<$fileRef>) {
        chomp;
        # Remove comments and emptied lines
        next if /^#/o;
        next if /^\s*$/o;
        # Manage lines ending with a \ as uniq line
        if ( m/(.*)\\$/o ) {
            $prevLine = "$prevLine$1";
            next;
        }
        $_ = $prevLine.$_;
        $prevLine="";
        my $property;
        my $value;

        if ( m/^COMP_AGGR\s*:\s*(.*)\s*$/o ) {
            $property = COMP_AGGR;
            my @modList = split /\s+/, $1;
            my %modHash;
            foreach (@modList) {
                $modHash{$_} = 1;
            }
            $value = \%modHash;
        }
        elsif ( m/^COMP_DEPS\s*:\s*(.*)\s*$/o ) {
            $_ = $1;
            unless ( m/^[A-Za-z0-9_\s!]*$/o ) {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "Unexpected value for COMP_DEPS property in $filename:\n$_\n";
                }
                $error = 1;
                next;
            }
            $property = COMP_DEPS;
            my @depsList = split /\s+/, $_;
            my %depsHash;
            foreach (@depsList) {
                my $cName;
                my $bName;
                if (m/^([^!]+)\!(.+)$/) {
                    $cName = $1;
                    $bName = $2;
                }
                else {
                    # No branch, the dependency is on the current one...
                    $cName = $_;
                    $bName = "";
                }
                if (exists $depsHash{$cName}) {
                    if ($errorMode & ONERROR_PRINT) {
                        print STDERR "Duplicated dependency on $cName component in $filename\n";
                    }
                    $error = 1;
                }
                $depsHash{$cName} = $bName;
            }
            $value = \%depsHash;
        }
        elsif ( m/^COMP_COMMENT\s*:\s*(.*)\s*$/o ) {
            $property = COMP_COMMENT;
            $value = $1;
        }
        elsif ( m/^COMP_MERGE_FROM\s*:\s*(.*)\s*$/o ) {
            $_ = $1;
            unless ( m/^[A-Za-z0-9_\s]*$/o ) {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "Unexpected value for COMP_MERGE_FROM property in $filename:\n$_\n";
                }
                $error = 1;
                next;
            }
            $property = COMP_MERGE_FROM;
            my @brList = split /\s+/, $_;
            my %brHash;
            foreach (@brList) {
                $brHash{$_} = 1;
            }
            $value = \%brHash;
        }
        elsif ( m/^(COMP_[A-Z_]*)\s*:\s*(.*)\s*$/o ) {
            # It is not an error. The goal is to be compatible with new
            # properties added in a next release...
            print STDERR "Warning: Unexpected $1 property in $filename:\n";
            $property = $1;
            $value = $2;
        }
        else {
            # It is an error !
            print STDERR "Unexpected line in $filename:\n$_\n";
            $error = 1;
        }
        if ($property) {
            if (exists $result{$property}) {
                if ($errorMode & ONERROR_PRINT) {
                    print STDERR "Duplicated entry for $property in $filename\n";
                }
                $error = 1;
            }
            $result{$property} = $value;
        }
    }
    # Add default values if needed
    unless (exists($result{+COMP_COMMENT})) {
        $result{+COMP_COMMENT} = "";
    }
    # Check if mandatory properties are defined
    for my $property (COMP_AGGR, COMP_DEPS)  {
        unless (exists($result{$property})) {
            if ($errorMode & ONERROR_PRINT) {
                print STDERR "$property not found in $filename\n";
            }
            $error = 1;
        }
    }
    if ($error) {
        # We stop only at the end of the read, it allows to display all
        # errors at the same time...
        if ($errorMode & ONERROR_EXIT) {
            close($fileRef);
            exit(1);
        }
        undef %result;
    }
    return(%result);
}



#########################
# Methods for the management of the "componentsList" file
#########################


# Get the list of existing components. This method is based on the
# content of the components/definitions directory for the branch
#
# @param branchName the branch name or a build identifier for this branch
#
# @return the list of components

sub getListOfComponents {
    (my $identifier) = @_;
    if (exists $listOfComponentsCache_{$identifier}) {
        return( @{$listOfComponentsCache_{$identifier}});
    }
    my @allFiles;
    #print STDOUT "getListOfComponents svn co  -r $identifier $SVNURL".COMPONENTS_DEFINITIONS_DIR."\n" ;
    #open(FILELIST, "svn list  -r $identifier $SVNURL".COMPONENTS_DEFINITIONS_DIR."  |") || die "$?. Stopped";
	open(FILELIST, "svn list  $SVNURL".$identifier."/main/".COMPONENTS_DEFINITIONS_DIR."  |") || die "$?. Stopped";
    my $pattern = "(.+).def";
    while (<FILELIST>) {
        chomp;
        if ( /^$pattern$/o ) {
            push @allFiles, $1;
        }
    }
    # We don't test if the operation success because it may fail if the
    # identifier is not existing
    close(FILELIST);
    $listOfComponentsCache_{$identifier} = [ @allFiles ];
    return @allFiles;
}



sub sortComponentsByDependentOrder {
    (my $identifier, my $components) = @_;
    my @result = sort {
    	my $leftComponent = $a;
    	my $rightComponent = $b;
        my %leftComponentDependent = getComponentDependencies($identifier, $leftComponent, 1);
	my %rightComponentDependent = getComponentDependencies($identifier, $rightComponent, 1);
	my $leftDependentCount = scalar keys %leftComponentDependent; 
	my $rightDependentCount = scalar keys %rightComponentDependent;
	unless ($leftDependentCount == $rightDependentCount) {
            return $leftDependentCount <=> $rightDependentCount;
        }
        if(exists $rightComponentDependent{$leftComponent}) {
            return -1;
        } elsif(exists $leftComponentDependent{$rightComponent}) {
            return 1;        	
        } else {
            return 0;
        }
    } @{$components};
    return @result;
}



sub getListOfComponentsByDependentOrder {
    (my $identifier) = @_;
    my $key = $identifier.'_sorted';
    if (exists $listOfComponentsCache_{key}) {
        return( @{$listOfComponentsCache_{key}});
    }
    my @allFiles = getListOfComponents($identifier);
    @allFiles = sortComponentsByDependentOrder($identifier, \@allFiles);
    
    $listOfComponentsCache_{key} = [ @allFiles ];
    return @allFiles;
}



# Get the list of existing component names.
#
# @global listOfAllComponentsCache_ cache containing the list of existing
#         components
#
# @return the list of component names

sub getListOfAllComponents () {
    if ($#listOfAllComponentsCache_ != -1) {
        return @listOfAllComponentsCache_;
    }
	
	open(COMPLIST, "svn cat  -r HEAD $SVNURL".COMPONENTS_LIST_FILE." $DROP_ERROR |") || die "$?\nStopped";
	while (<COMPLIST>) {
		chomp;
		next if ( m/^\s*$/o );
		next if ( m/^#/o );
		push @listOfAllComponentsCache_, $_;
	}
	close(COMPLIST) || die "Cannot checkout ".COMPONENTS_LIST_FILE."\nStopped";
	
    
    @listOfAllComponentsCache_ = sort(@listOfAllComponentsCache_);
    return @listOfAllComponentsCache_;
}



#########################
# Methods for the management of the <component>.log file
#########################

# Get the name of the file containing the build tags
#
# @param branchName branch to use
# @param component name of the component
#
# @return the file name

sub getComponentTagFile {
    (my $branchName, my $componentName) =  @_;
    my $dirName = getBranchDeliverTagDir($branchName);
    return "$dirName/$componentName.log";
}



# Get the content of the <component>.log file.
# This method just open the file and call readComponentTagFileFromStream with
# the resulting stream
#
# @param branchName name of the branch
# @param componentName name of the component
#
# @return a list of listes (see readComponentTagFileFromStream comment)

sub readComponentTagFile {
    (my $branchName, my $componentName) = @_;
    if (exists $logFilesCache_{"COMP ${branchName}_${componentName}"}) {
        return @{$logFilesCache_{"COMP ${branchName}_${componentName}"}};
    }
    # It is not possible to have a module or a branch with the same
    # name...
    if (exists $logFilesCache_{"MOD ${branchName}_${componentName}"}) {
        return(()) ;
    }
    if (exists $logFilesCache_{"BRANCH ${branchName}_${componentName}"}) {
        return(()) ;
    }
    my $tagsFile = getComponentTagFile($branchName, $componentName);
    #print STDOUT "Mvs.pm readComponentTagFile svn cat $SVNURL/$tagsFile\n";
    open(BRANCHTAGS, "svn cat $SVNURL/$tagsFile  $DROP_ERROR |");
    my @result = readComponentTagFileFromStream($branchName, $componentName, \*BRANCHTAGS);
    close BRANCHTAGS;
    # We save the value only if it is not empty (because this method
    # may be call with a name just to test if it exists
    if ($#result > -1) {
        $logFilesCache_{"COMP ${branchName}_${componentName}"} = [ @result ];
    }
    return @result;
}



# Get the content of the <component>.log file using a stream as input.
# Instead of parsing this file from several places in the code, this
# method is in charge to do the parse and to build a list of entries.
# Then you just have to parse this list which should not change even if
# format of the "ComponentTag" file changes.
# Lines of this file have the following format:
# START:buildId:
# buildId:appliA!buildIdA,FWK!buildIdFWK:
#
# This method works for the <branch>.log file too
#
# @param branchName name of the branch
# @param componentName name of the component
# @param fileRef stream on the "ComponentTag" file
#
# @return a list of listes (one line per entry)
#        (type field1 field2 field3, .... )
#        where:
#           type = start for the start tag
#           type = snap for lines describing a snap
#           type = build for lines describing a build

sub readComponentTagFileFromStream {
    (my $branchName, my $componentName, my $fileRef) = @_;
    my @result;
    while (<$fileRef>) {
        chomp;
        if ( m/^${branchName}_START:/ ) {
	    #print STDOUT "Mvs.pm readComponentTagFileFromStream start tag founded \n";
            push @result, [ START_TAG, split /:/ ];
        }
        elsif ( m/^${branchName}_[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][a-z]*:/ ) {
            push @result, [ BUILD_TAG, split /:/ ];
        }
        elsif ( m/^M:([^:])*:([^:])/ ) {
            push @result, [ MERGE_TAG, split /:/ ];
        }
        else {
            die "Unexpected line in $fileRef.\n$_\n.Stopped";
        }
    }
    return @result;
}



# Add/modify lines in the <component>.log File
#
# @param branchName name of the branch
# @param ComponentName name of the component
# @param entryListRef a reference to a list with the following format:
#        (field1 field2 field3 ... )
#        If a field must not be changed, undef has to be used for its value
# @param logMess message to use for the cvs commit

sub addEntryToComponentTagFile {
    (my $branchName, my $componentName, my $entryListRef, my $logMess) = @_;
    my $tmpDir = $TMP_DIR."/mvs.aetctf.$$";
    mkpath(($tmpDir), 0, 0755) || die "Can't create $tmpDir. Stopped";
    #my $tagFile = getComponentTagFile($branchName, $componentName);
    my $tagFile = "$branchName/$componentName.log";
    my $tagDir = getBranchDeliverTagDir($branchName);
    print STDOUT "addEntryToComponentTagFile $tagFile $tagDir \n";
    # Build a hash list from the given list in order to find faster when
    # a line has to been modified in the file. The used key is the first
    # element in the list, the value is the list without the first element.
    # We don't take care of lines with the "M" key because they are always
    # added and never modified
    my %linesToAdd;
    foreach (@$entryListRef) {
        my @line = @$_;
        my $key = shift @line;
        unless ($key eq "M") {
            $linesToAdd{$key} = [ @line ];
        }
    }

    my $try=1;
    my $currentDir=cwd();
    chdir($tmpDir) || die "Unable to change dir to $tmpDir. Stopped";
    while (1) {
        my $returnCode=0;
	print STDOUT "Checking out $tagFile\n";
        my @args = ("svn", "$cvsVerbose_", "checkout", "$SVNURL/$tagDir");
        system(@args);# || die "Unable to checkout $tagFile";
	 print STDOUT "Checked out $tagFile\n";

        # In some cases the file doesn't exist, it just means that the module
        # has just been created in this branch. We create the file in the
        # HEAD branch (MVS management files are always in the main branch)
	unless (-f "$tmpDir/$tagFile") {
		print STDOUT " Adding file to SVN $tagFile, $tmpDir\n";
            addFileToCVS("HEAD", $tagFile, $tmpDir);
        }
	print STDOUT "Changing the log file\n";
        open(NEWBRANCHTAGS, "> $tmpDir/$tagFile.new") || die $!;
        open(OLDBRANCHTAGS, "$tmpDir/$tagFile") || die $!;
        while (<OLDBRANCHTAGS>) {
            chomp;
            next if ( m/^\s*$/ );
            if ( m/^([^:]*):(.*)$/ ) {
                if ( exists $linesToAdd{$1} ) {
                    # This line has to be modified
                    my @newTagVal = @{$linesToAdd{$1}};
                    my @oldTagVal = split /:/, $2;
                    print NEWBRANCHTAGS "$1:";
                    # Loop on the new and old field values
                    # If the new value is defined, we use it, else we use the
                    # old value
                    for (my $i=0 ; ($i < @newTagVal) || ($i < @oldTagVal) ; $i++) {
                        if (defined $newTagVal[$i]) {
                            print NEWBRANCHTAGS "$newTagVal[$i]:";
                        }
                        else {
                            print NEWBRANCHTAGS "$oldTagVal[$i]:";
                        }
                    }
                    print NEWBRANCHTAGS "\n";
                    delete $linesToAdd{$1};
                }
                else {
                    print NEWBRANCHTAGS "$_\n";
                }
            }
            else {
                die "Unexpected format for $tagFile:\n$_\nStopped";
            }
        }
        close OLDBRANCHTAGS;
	print STDOUT "OLDBRANCHTAGS is changed \n";


        # Now add the new lines
        foreach (@$entryListRef) {
            my @tagVal = @$_;
            my $key = shift @tagVal;
            if ((exists $linesToAdd{$key}) || ($key eq "M")) {
                print NEWBRANCHTAGS "$key:";
                foreach ( @tagVal ) {
                    print NEWBRANCHTAGS "$_:";
                }
                print NEWBRANCHTAGS "\n";
            }
        }
        close NEWBRANCHTAGS;
	print STDOUT "NEWBRANCHTAGS is changed , renameing\n";
        rename "$tmpDir/$tagFile.new", "$tmpDir/$tagFile" || die "Cannot rename $tagFile";
	print STDOUT "$tagFile.new has renamed to $tagFile\n";
	#if ($DROP_OUTPUT) {
	#    open SAVEOUT, ">&STDOUT";
	#    open STDOUT, ">/dev/null";
	#}
	#if ($DROP_ERROR) {
	#    open SAVEERR, ">&STDERR";
	#    open STDERR, ">/dev/null";
	#}
	print STDOUT "Modified, prepare to checkin \n";
        @args = ("svn", "$cvsVerbose_", "commit", "-m", $logMess, $tagFile);
        $returnCode = system(@args);
        if ($DROP_OUTPUT) {
            close STDOUT;
            open STDOUT, ">&SAVEOUT";
        }
        if ($DROP_ERROR) {
            close STDERR;
            open STDERR, ">&SAVEERR";
        }
        unless ( $returnCode == 0) {
            next;
        }
        # The tagfile is commited. We can exit from the loop.
        last;
    }
    continue {
        # The attempt to update the tagfile has failed.
        unlink("$tmpDir/$tagFile");
        unlink("$tmpDir/$tagFile.new");
        $try++;
        if ($try <= MAX_TRY) {
            print STDERR "Retry .....\n ";
        }
        else {
            print STDERR "Sorry, MVS cannot complete successfully the command. \n";
            print STDERR "Please to restart your MVS command.\n";
	    #rmtree(($tmpDir), 0, 0);
            exit 1;
        }
    }
    chdir($currentDir) || die "Unable to change dir to $currentDir. Stopped";
    cleanLogCache($branchName, $componentName);
    rmtree(($tmpDir), 0, 0);
}



###############################################################
# Methods dealing with the component merge
###############################################################

# Return the history of identifiers (build only) for a component
# starting from a given tag and until the component creation.
#
# @param compName name of the component
# @param startTag build identifier from which the history has to be
#        compute. If it is a branch name, history starts with the last version
#        in the branch
#
# @return a list of build identifiers giving the coponent history in chronologic
#         reverse order

sub getComponentHistory {
    (my $compName, my $startTag) = @_;
    my $found = 0;
    (my $branch, undef) = hasBuildFormat($startTag);
    unless ($branch) {
        if (isExistingBranch($startTag, ONERROR_RETURN)) {
            $branch = $startTag;
            # We take everything in the branch, so we don't have to
            # search first the starting point
            $found = 1;
        }
    }
    die "Cannot find branch name in $startTag. Stopped" unless ($branch);

    my @result;
    # We assume that build identifiers in the tag file are in chronologic
    # order
    for (reverse readComponentTagFile($branch, $compName)) {
        my @line = @{$_};
        if ($line[0] eq BUILD_TAG ) {
            if ($line[1] eq $startTag) {
                $found = 1;
            }
            if ($found) {
                push @result, $line[1];
            }
        }
        elsif ( $line[0] eq START_TAG ) {
            # It is the beginning of the branch, we have to explore
            # the mother branch starting from the creation point (if it
            # exists)
            if ($line[2]) {
                @result = (@result, &getComponentHistory($compName, $line[2]));
            }
            else {
                push @result, $line[1];
            }
        }
    }
    return(@result);
}



# Explore a branch (in reverse order) in order to find a way to reach one of
# the identifiers stored in the hash list
#
# @param startTag, the tag from which the exploration has to start. It may
#        be a snap identifier, a build identifier or a branch name
# @param moduleName name of the module
# @param fromVersionsPtr reference to a hash list containing the snap
#        identifiers to find and their rank
#
# @return the smaller rank in the hash list reached from startTag

sub exploreComponentBranch {
    (my $startTag, my $compName, my $fromVersionsPtr) = @_;
    # Compute the branch name from the tag (else we expect to get it
    # directly as first argument
    my $found = 0;
    (my $branch, undef) = hasBuildFormat($startTag);
    unless ($branch) {
        if (isExistingBranch($startTag, ONERROR_RETURN)) {
            $branch = $startTag;
            $found = 1;
        }
    }
    die "Cannot find branch name in $startTag. Stopped" unless ($branch);

    # When we find a merge, there's no need to explore two times
    # the same branch, so we store the already explored branches in
    # a hash list
    my %alreadyExploredBranches;

    # We initialize the rank with the size of the hash list
    my $rank = keys %$fromVersionsPtr;

    # If the module was not existing in the branch, we don't have to
    # continu. It is just a way to prevent from error when trying to read
    # the .log file
    unless (wasExistingComponent($branch, $compName, ONERROR_RETURN)) {
        return($rank);
    }

    # Loop on the existing tags in the branch. We expect that build and
    # merge identifiers are in chronological order in the tag file
    for (reverse readComponentTagFile($branch, $compName)) {
        my @line = @{$_};
        if ($line[0] eq BUILD_TAG) {
            if ($line[1] eq $startTag) {
                $found = 1;
            }
            if ($found) {
                if (exists $$fromVersionsPtr{$line[1]}) {
                    my $newRank = $$fromVersionsPtr{$line[1]};
                    if ($newRank < $rank) {
                        return($newRank);
                    }
                    else {
                        return($rank);
                    }
                }
            }
        }
        elsif ( $line[0] eq MERGE_TAG ) {
            if ($found) {
                # A merge has been done from another branch in this one,
                # we have to explore this branch too starting from the
                # merging point
                (my $brName, undef) = hasBuildFormat($line[3]);
                ($brName) || die "$line[3] not a build identifier\n";
                # If a merge has already be done from the same branch,
                # there's no need to explore the branch again (because
                # we are in the chronological reverse order)
                unless (exists $alreadyExploredBranches{$brName}) {
                    my $newRank = exploreComponentBranch($line[3], $compName, $fromVersionsPtr);
                    if ($newRank < $rank) {
                        $rank = $newRank;
                    }
                    $alreadyExploredBranches{$brName} = 1;
                }
            }
        }
        elsif ( $line[0] eq START_TAG ) {
            # It is the beginning of the branch, we have to explore
            # the mother branch starting from the creation point (if it
            # exists)
            if ($line[2]) {
                my $newRank = exploreComponentBranch($line[2], $compName, $fromVersionsPtr);
                if ($newRank < $rank) {
                    $rank = $newRank;
                }
            }
        }
    }
    return($rank);
}



# Compute which should be the build identifier to use at the first reference
# for a component from a given tag.
# This method tries to find the point used for the last merge (or the
# branch creation point if no merge have been done). The system is the
# following:
# - First we compute the history of the source branch (starting from the
#   given tag until the component creation). We give a rank to each point in
#   in this list, the newest build has the lower rank number.
# - Then we search for all ways to reach one of these points from the target
#   branch.
# - The solution is the reached point with the lower rank.
#
# @param branchName name of the branch we want to merge to
# @param compName name of the component to merge
# @param mergeFromTag name of the identifier to use as endding point for
#        the merge
#
# @return build identifier to use as starting point for the merge

sub computeComponentLastMergeTag {
    (my $branchName, my $compName, my $mergeFromTag) = @_;

    # First loop on source branch. We create a hash list with all builds
    # numbered from the source build identifier to the HEAD branch.
    my %fromVersions;
    my $pos = 1;
    for (getComponentHistory($compName, $mergeFromTag)) {
        $fromVersions{$_} = $pos;
        $pos++;
    }

    # Now explore the target branch from its head in order to
    # find all ways to reach one of the snaps existing in the fromVersions
    # hash list. The newer snap (i.e. the snap with the lower rank) is
    # the snap to use for the merge
    my $tagRank = exploreComponentBranch($branchName, $compName, \%fromVersions);

    # We have the rank of the snap to use for the merge, we just return
    # it
    for (keys %fromVersions) {
        if ($fromVersions{$_} == $tagRank) {
            return($_);
        }
    }

    # This point should never been reached
    die "No build with the rank $tagRank. Stopped";
}

###############################################################

# Add or modify branch entry in the branch list file
#
# @param branchName name of the branch to add
# @entryPropRefFile temporary file containing branch properties
# @param tmpDir temporary directory where the branch list file should exist

sub addEntryToBranchListFile {
    (my $branchName, my $tmpDir, my $entryPropRef) = @_;

    my %entryProp = %$entryPropRef;

    # Modify the branch list file
    my $new=1;
    my $branchListFile = BRANCHES_LIST_FILE;
    open(OLDBRANCHLIST, "$tmpDir/$branchListFile") || die $!;
    open(NEWBRANCHLIST, "> $tmpDir/$branchListFile.new") || die $!;
    while (<OLDBRANCHLIST>) {
       chomp;
       next if ( m/^\s*$/o );
       if ( m/^#.*$/o ) {
               print NEWBRANCHLIST "$_\n";
       }
       elsif ( m/^([^:]*):(.*)$/o ) {
           if ( $branchName eq $1 ) {
              # This line has to be modified
              writeEntryToBranchListFile ($branchName, \*NEWBRANCHLIST, $entryPropRef);
              $new = 0;
           }
           else {
               print NEWBRANCHLIST "$_\n";
           }
       }
       else {
          die "Unexpected format for $branchListFile:\n$_\nStopped";
       }
    }

    # If it's a new branch, add it to the end of the branch list file
    if ($new) {
       writeEntryToBranchListFile ($branchName, \*NEWBRANCHLIST, $entryPropRef);
    }

    close(NEWBRANCHLIST);
    close(OLDBRANCHLIST);
    rename "$tmpDir/$branchListFile.new", "$tmpDir/$branchListFile" || die "Cannot rename $branchListFile";
}


# Write a new branch entry in the branch list file
#
# @param branchName name of the branch
# @param fileRef branch list descriptor
# @param entryPropRef branch properties
#
sub writeEntryToBranchListFile  {
    (my $branchName, my $fileRef, my $entryPropRef) = @_;

    my %entryProp = %$entryPropRef;

    print $fileRef "${branchName}:";

    print $fileRef "$entryProp{+BRANCH_STATE}:";

    if ($entryProp{+BRANCH_MANDATORY_TICKET} == 0) {
       print $fileRef "no:";
    }
    else {
       print $fileRef "yes:";
    }

    if (exists $entryProp{+BRANCH_MERGE_FROM}) {
       my @mergeList = sort @{$entryProp{+BRANCH_MERGE_FROM}};
       if ( $#mergeList >= 0) {
          print $fileRef shift @mergeList;
          foreach (@mergeList) {
             print $fileRef " $_";
          }
       }
    }
    print $fileRef ":";

    if (exists $entryProp{+BRANCH_RESPONSIBLES}) {
       my %list = %{$entryProp{+BRANCH_RESPONSIBLES}};
       my @listKeys = sort(keys %list);
       print $fileRef pop @listKeys;
       foreach (@listKeys) {
          print $fileRef " $_";
       }
    }
    print $fileRef ":";

    print $fileRef "$entryProp{+BRANCH_COMMENT}:\n";
}


# Read branch properties from the branch list file and write it the temporary file given in parameter.
#
# @param branchName name of the branch
# @param entryPropRefFile full name of the temporary file
#
# @return branch properties hash table
#
sub readEntryFromBranchListFile {
    (my $branchName) = @_;

    my %branchProperties;

    # Open the branch properties temporary file

    # Read the branch list file
    open(BRANCHLIST, "svn cat -r HEAD ".$SVNURL.BRANCHES_LIST_FILE." |") || die "$?\nStopped";
    while(<BRANCHLIST>) {
        chomp;
        my $value;
        next if ( m/^\s*$/o );
        next if ( m/^#.*$/o );
        if ( m/^([^:]*):(.*)$/o ) {
           if ( $branchName eq $1 ) {
               my $state, my $ticket,my $mergeList,my $respList,my $comment;
               ($state, $ticket, $mergeList, $respList, $comment) = split(/:/, $2);


               $branchProperties{+BRANCH_STATE} = $state;
               $branchProperties{+BRANCH_MANDATORY_TICKET} = $ticket;
               $branchProperties{+BRANCH_COMMENT} = $comment;

               # Support comma or space as separator
               my @admList = split /\s*[,\s]\s*/, $respList;
               my %admHash;
               foreach (@admList) {
                   $admHash{$_} = 1;
               }
               $branchProperties{+BRANCH_RESPONSIBLES} = \%admHash;

               # Support comma or space as separator
               my @branchList = sort split /\s*[,\s]\s*/, $mergeList;
               $branchProperties{+BRANCH_MERGE_FROM} = \@branchList;
            }
        }
    };
    close(BRANCHLIST) || die "Cannot checkout ".BRANCHES_LIST_FILE."\nStopped";
    return (\%branchProperties);
}


# Keep these variables declarations at the end of the file to be sure that
# nobody is using them before...

# Name of the current user
my $user_ ="admin";

sub getUserName {
	my $SVNURL = $ENV{"SVNURL"};
    if ( $SVNURL eq "" ) {
        print STDERR "SVNURL no set\n";
        exit 1;
    }
	
	#get the current svn server path
	my $svnServerPath;
	if($SVNURL=~/^(svn|http):\/\/(\d{1,3}).(\d{1,3}).(\d{1,3}).(\d{1,3})(:|\/)/) {
		$svnServerPath="$1://$2.$3.$4.$5";
	}else {
		print STDERR "SVNURL set Not in the correct format\n" ;
        exit 1;
	}
	
	#get the current  svn Repository UUID
	my $svnInfo = `svn info --xml $SVNURL`;
	my $repo_uuid;
	if($svnInfo=~ /<uuid>(.*)<\/uuid>/) {
		$repo_uuid=$1;
	}
	
	my $filePath=`cd ~/.subversion/auth/svn.simple;pwd`;
	chomp($filePath);
	my @line=`cd ~/.subversion/auth/svn.simple;ls`;
	foreach(@line) {
		my $svnRepository;
		my $username;
		open(FILE,"$filePath/$_");
		my @records = <FILE>;
		$svnRepository=$records[11];
		$username=$records[15];
		close(FILE);
		if($svnRepository=~/$svnServerPath/) {
			return $username;
		}
	}
	
	#/.subversion/auth/svn.simple has no svn user data ,exit
	print STDERR "cant find the current svn user login data\n" ;
	exit 1;
}

# We need to identify user for the responsible mechanisms. The way to do
# that is depending on the CVS access mode...
# Take care for ssh and rsh will need special configuration on server side

# @return the user name

sub getUserName1 {
    if (defined $user_) {
        return($user_);
    }
    my $CVSROOT = $ENV{"CVSROOT"};
    $user_ = getpwuid ($<);
    if ( $CVSROOT =~ /^:pserver:([^@]*)@[^:]*:(.*)/o ) {
        $user_ = $1;
    }
    elsif ( $CVSROOT =~ m/^:ext:([^@]*)@([^:]*):(.*)/o ) {
        my $remoteUser=$1;
        my $remoteHost=$2;
        $cvsRootDir_ = $3;
        my $remoteCmd = $ENV{"CVS_RSH"};
        unless ($remoteCmd) {
            $remoteCmd="rsh";
        }
        open(RES, "$remoteCmd -l $remoteUser $remoteHost echo \\\$CVS_USER |");
        while (<RES>) {
            chomp;
            $user_ = $_;
        }
        unless(close(RES)) {
            print STDERR "Error during remote username get\n$!\n";
            exit(1);
        }
    }
    elsif ( $CVSROOT =~ m@/@ ) {
        # Just to be able to test responsible mechanism in the local mode
        if ($ENV{"MVSUSER"}) {
            $user_ = $ENV{"MVSUSER"};
        }
    }
    else {
        print STDERR "Not supported format for CVSROOT: $CVSROOT\n";
        exit(1);
    }
}

sub sendNotification {
    (my $branchName, my $moduleName, my $context, my $logMess) = @_;
    my $event = $context->{event};
    if($event eq 'snapped' || $event eq 'delivered' || $event eq 'snapped and delivered') {
	my $snapId = $context->{snapId};
	my $comment= $context->{comment};
	if ($comment =~ /#([A-Za-z][A-Za-z][A-Za-z\-]+[0-9]+)/o) {
            my $issueKey = $1;
	    my $user = getUserName();
	    my $message = "The '$snapId' has been $event by $user.\n$comment";
	    if($event eq 'snapped' || $event eq 'snapped and delivered') {
		# add changed file list
		my $lastDeliveredTag = $context->{lastDeliveredTag};
		if ($lastDeliveredTag) {
		    my @diff = rdiffModule($moduleName, $lastDeliveredTag, $snapId);
		    my $nbDiff = $#diff + 1;
		    $message .= "\n\n*$nbDiff* difference".(($nbDiff > 1)?"s":"")." detected with $lastDeliveredTag tag";
		    foreach my $line (@diff) {
                        if ($line->[0] eq "Modified") {
			    my $filename = $line->[1];
			    my $oldRevision = $line->[2];
			    my $newRevision = $line->[3];
                            $message .= "\n* {color:#999933}*MODIFY*{color} [$filename|http://lilas/view/$filename]  Rev.[$newRevision|http://lilas/view/$filename?revision=$newRevision] [(diffs)|http://lilas/view/$filename?r1=$oldRevision&r2=$newRevision]";
                        } elsif ($line->[0] eq "Added") {
			    my $filename = $line->[1];
			    $message .= "\n* {color:#009900}*ADD*{color} [$filename|http://lilas/view/$filename]";
                        } elsif ($line->[0] eq "Removed") {
			    my $filename = $line->[1];
			    $message .= "\n* {color:#990000}*DEL*{color} [$filename|http://lilas/view/$filename]";
                        }
                    }
		} else {
		    $message .= "\nFirst delivery of $moduleName in $branchName branch.";
		}
	    }

	    my $ua = LWP::UserAgent->new;
	    my $req = POST 'http://arum:8080/jira/secure/AddComment.jspa',
                [ os_username => 'mvs', os_password => 'mvs', key => "$issueKey", comment => "$message" ];
	    my $resp = $ua->request($req);
	    return $resp->code;
        }
    }
}

sub getRevision{
	(my $moduleName, my $ident) = @_;
	(my $branch, undef) = hasSnapFormat($ident);
        if ($branch eq 0) {
             ( $branch, undef) = hasBuildFormat($ident);
        }
	print STDOUT "Mvs.pm getRevision for $ident:$moduleName\n";
	#my $cmd = `svn log $SVNURL/$branch/tags/$ident/vars --stop-on-copy  -l1 |grep \\| | sed  's/r\\([0-9]*\\)\\s.*/\\1/'`;
	my $cmd = `svn info $SVNURL/$branch/tags/$ident/$moduleName | grep 'Last Changed Rev'  | sed 's/Last Changed Rev: \\([0-9]*\\)/\\1/' | tr -d "\n"`; 
	print STDOUT "Revision for tag $ident:$moduleName is $cmd\n";
	return $cmd;
}

sub getBranchName{
    (my $identifier) = @_;
    if ($identifier) {
	(my $branch, undef) = hasSnapFormat($identifier);
	unless ($branch) {
		($branch, undef) = hasBuildFormat($identifier);
	}
	unless ($branch) {
		# It should be a branch name
 		$branch = $identifier;
	}
	return $branch;
    }else {
               # We don't complain if the tag is a build or a snap
              # from another branch because it is a normal
              # behaviour with components
              #$branch =""; #$identifier;
    }
}


# We must return a not null value
1;
