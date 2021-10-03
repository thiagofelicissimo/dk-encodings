\ProvidesClass{StandardTemplate}

\LoadClass[12pt]{article}



\renewcommand{\familydefault}{\sfdefault}
\usepackage{lmodern}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{float}
\usepackage{graphicx}
\usepackage{courier}
\usepackage{amsmath, amssymb, amsthm}
\usepackage{subfloat}
\usepackage{parskip}
\usepackage{fancyhdr}

\setlength{\textwidth}{\paperwidth}
\addtolength{\textwidth}{-2in}
\setlength{\oddsidemargin}{0pt}
\setlength{\evensidemargin}{0pt}

\setlength{\headheight}{15pt}
\setlength{\headsep}{15pt}
\setlength{\topmargin}{0in}
\addtolength{\topmargin}{-\headheight}
\addtolength{\topmargin}{-\headsep}
\setlength{\footskip}{29pt}
\setlength{\textheight}{\paperheight}
\addtolength{\textheight}{-2.2in}

\setlength{\marginparwidth}{.5in}
\setlength{\marginparsep}{5pt}



\newtheoremstyle{mystyle}%                % Name
  {4pt}%                                     % Space above
  {4pt}%                                     % Space below
  {\itshape}%                                     % Body font
  {}%                                     % Indent amount
  {\bfseries}%                            % Theorem head font
  {}%                                    % Punctuation after theorem head
  {.5em}%                                    % Space after theorem head, ' ', or \newline
  {\thmname{#1}\thmnumber{ #2}\thmnote{ (#3)}}%                                     % Theorem head spec (can be left empty, meaning `normal')

\theoremstyle{mystyle}


\newtheorem{thm}{Theorem}[section]
%\newtheorem{claim}{Claim}[section]
\newtheorem{prop}{Proposition}[section]
\newtheorem{lem}{Lemma}[section]
\newtheorem{cor}{Corollary}[section]
\renewcommand{\qedsymbol}{$\blacksquare$}

\newtheoremstyle{definition}%                % Name
  {4pt}%                                     % Space above
  {4pt}%                                     % Space below
  {\it}
  {}%                                     % Indent amount
  {\bfseries}%                            % Theorem head font
  {}%                                    % Punctuation after theorem head
  {.5em}%                                    % Space after theorem head, ' ', or \newline
  {\thmname{#1}\thmnumber{ #2}\thmnote{ (#3)}}%                                     % Theorem head spec (can be left empty, meaning `normal')

\theoremstyle{definition}

\newtheorem{definition}{Definition}[section]

\newtheorem{assumption}{Assumption}[section]

\makeatletter         
\def\@maketitle{
{\raggedright % Note the extra {
  \begin{center}

{\LARGE  \bfseries \@title }\\[2ex] 
{\large  \@author}\\[1.6ex] 

\end{center}

}} % Note the extra }
\makeatother

\usepackage{hyperref}
\hypersetup{
    colorlinks,
    citecolor=black,
    filecolor=black,
    linkcolor=blue,
    urlcolor=cyan
}

\author{Thiago F Cesar}
