,          // cell0 = input()
>+         // cell1 = 1

<          // goto cell0
-----      // deduct 5 from cell0

[          // if(cell0 != 0)
    >-     //     clear "else flag" in cell1
    >      //     go to empty cell2
           //     print "!="
    ++++[->++++++++<]>+.--[->++<]>-.
    <<<    //     return to c0:"then flag"

]>         // to c1:"else flag"
[          // else
    -      //     clear c1:"else flag"
    >      //     go to empty cell2
           //     print "=="
    ----[---->+<]>--..
    <<     //     return to c1:"else flag"
]




