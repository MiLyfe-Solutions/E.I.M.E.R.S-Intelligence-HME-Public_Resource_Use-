import V185TrunkScan23Chunk0713

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4221747 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 3]
def baseStart_4221747 : Nat := 118140960795 + 4221747 * 2 ^ 59
def prefixEnd_4221747 : Nat := 4983230072969 + 3 ^ 40 * 4221747 * 2
def baseEnd_4221747 : Nat := 2167785412676999129147045

theorem tailTrace_4221747 : CollatzResearch.WordTrace tailWord_4221747 prefixEnd_4221747 2167785412676999129147045 := by
  unfold tailWord_4221747
  simp only [CollatzResearch.WordTrace]
  refine ⟨153979763036339110829615495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102653175357559407219743663 153979763036339110829615495)
  ·
    refine ⟨230969644554508666244423243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153979763036339110829615495 230969644554508666244423243)
    ·
      refine ⟨346454466831762999366634865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230969644554508666244423243 346454466831762999366634865)
      ·
        refine ⟨259840850123822249524976149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346454466831762999366634865 259840850123822249524976149)
        ·
          refine ⟨12180039849554167946483257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 259840850123822249524976149 12180039849554167946483257)
          ·
            refine ⟨9135029887165625959862443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12180039849554167946483257 9135029887165625959862443)
            ·
              refine ⟨13702544830748438939793665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9135029887165625959862443 13702544830748438939793665)
              ·
                refine ⟨10276908623061329204845249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13702544830748438939793665 10276908623061329204845249)
                ·
                  refine ⟨7707681467295996903633937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10276908623061329204845249 7707681467295996903633937)
                  ·
                    refine ⟨5780761100471997677725453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7707681467295996903633937 5780761100471997677725453)
                    ·
                      refine ⟨2167785412676999129147045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5780761100471997677725453 2167785412676999129147045)
                      ·
                        rfl

theorem cell23_4221747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_4221747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221747 prefixEnd_4221747 := by exact prefixLift 4221747
  have htrace : WordTrace (prefixWord ++ tailWord_4221747) baseStart_4221747 baseEnd_4221747 := by
    simpa [prefixWord, tailWord_4221747, baseEnd_4221747] using wordTrace_append hprefix tailTrace_4221747
  have hstable : (prefixWord ++ tailWord_4221747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221747).length < 2 ^ (prefixWord ++ tailWord_4221747).sum := by decide
  have hdescent : baseEnd_4221747 < baseStart_4221747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221754 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_4221754 : Nat := 118140960795 + 4221754 * 2 ^ 59
def prefixEnd_4221754 : Nat := 4983230072969 + 3 ^ 40 * 4221754 * 2
def baseEnd_4221754 : Nat := 722596335680526867253171

theorem tailTrace_4221754 : CollatzResearch.WordTrace tailWord_4221754 prefixEnd_4221754 722596335680526867253171 := by
  unfold tailWord_4221754
  simp only [CollatzResearch.WordTrace]
  refine ⟨38495004586828437756280079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102653345564875834016746877 38495004586828437756280079)
  ·
    refine ⟨57742506880242656634420119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38495004586828437756280079 57742506880242656634420119)
    ·
      refine ⟨86613760320363984951630179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57742506880242656634420119 86613760320363984951630179)
      ·
        refine ⟨129920640480545977427445269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86613760320363984951630179 129920640480545977427445269)
        ·
          refine ⟨6090030022525592691911497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129920640480545977427445269 6090030022525592691911497)
          ·
            refine ⟨4567522516894194518933623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6090030022525592691911497 4567522516894194518933623)
            ·
              refine ⟨6851283775341291778400435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4567522516894194518933623 6851283775341291778400435)
              ·
                refine ⟨10276925663011937667600653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6851283775341291778400435 10276925663011937667600653)
                ·
                  refine ⟨3853847123629476625350245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10276925663011937667600653 3853847123629476625350245)
                  ·
                    refine ⟨722596335680526867253171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853847123629476625350245 722596335680526867253171)
                    ·
                      rfl

theorem cell23_4221754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_4221754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221754 prefixEnd_4221754 := by exact prefixLift 4221754
  have htrace : WordTrace (prefixWord ++ tailWord_4221754) baseStart_4221754 baseEnd_4221754 := by
    simpa [prefixWord, tailWord_4221754, baseEnd_4221754] using wordTrace_append hprefix tailTrace_4221754
  have hstable : (prefixWord ++ tailWord_4221754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221754).length < 2 ^ (prefixWord ++ tailWord_4221754).sum := by decide
  have hdescent : baseEnd_4221754 < baseStart_4221754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221811 : List Nat := [1, 1, 1, 2, 2, 1, 8, 2, 1, 1, 3]
def baseStart_4221811 : Nat := 118140960795 + 4221811 * 2 ^ 59
def prefixEnd_4221811 : Nat := 4983230072969 + 3 ^ 40 * 4221811 * 2
def baseEnd_4221811 : Nat := 2167818275438886878746751

theorem tailTrace_4221811 : CollatzResearch.WordTrace tailWord_4221811 prefixEnd_4221811 2167818275438886878746751 := by
  unfold tailWord_4221811
  simp only [CollatzResearch.WordTrace]
  refine ⟨153982097308107249759945287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102654731538738166506630191 153982097308107249759945287)
  ·
    refine ⟨230973145962160874639917931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153982097308107249759945287 230973145962160874639917931)
    ·
      refine ⟨346459718943241311959876897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230973145962160874639917931 346459718943241311959876897)
      ·
        refine ⟨259844789207430983969907673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346459718943241311959876897 259844789207430983969907673)
        ·
          refine ⟨194883591905573237977430755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259844789207430983969907673 194883591905573237977430755)
          ·
            refine ⟨292325387858359856966146133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194883591905573237977430755 292325387858359856966146133)
            ·
              refine ⟨3425688138965154573822025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 292325387858359856966146133 3425688138965154573822025)
              ·
                refine ⟨2569266104223865930366519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425688138965154573822025 2569266104223865930366519)
                ·
                  refine ⟨3853899156335798895549779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2569266104223865930366519 3853899156335798895549779)
                  ·
                    refine ⟨5780848734503698343324669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853899156335798895549779 5780848734503698343324669)
                    ·
                      refine ⟨2167818275438886878746751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5780848734503698343324669 2167818275438886878746751)
                      ·
                        rfl

theorem cell23_4221811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 1, 3].length) (baseStart_4221811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221811 prefixEnd_4221811 := by exact prefixLift 4221811
  have htrace : WordTrace (prefixWord ++ tailWord_4221811) baseStart_4221811 baseEnd_4221811 := by
    simpa [prefixWord, tailWord_4221811, baseEnd_4221811] using wordTrace_append hprefix tailTrace_4221811
  have hstable : (prefixWord ++ tailWord_4221811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221811).length < 2 ^ (prefixWord ++ tailWord_4221811).sum := by decide
  have hdescent : baseEnd_4221811 < baseStart_4221811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221820 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_4221820 : Nat := 118140960795 + 4221820 * 2 ^ 59
def prefixEnd_4221820 : Nat := 4983230072969 + 3 ^ 40 * 4221820 * 2
def baseEnd_4221820 : Nat := 2167822896764777343534209

theorem tailTrace_4221820 : CollatzResearch.WordTrace tailWord_4221820 prefixEnd_4221820 2167822896764777343534209 := by
  unfold tailWord_4221820
  simp only [CollatzResearch.WordTrace]
  refine ⟨76991212782537322148511457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102654950376716429531348609 76991212782537322148511457)
  ·
    refine ⟨57743409586902991611383593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76991212782537322148511457 57743409586902991611383593)
    ·
      refine ⟨43307557190177243708537695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57743409586902991611383593 43307557190177243708537695)
      ·
        refine ⟨64961335785265865562806543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43307557190177243708537695 64961335785265865562806543)
        ·
          refine ⟨97442003677898798344209815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64961335785265865562806543 97442003677898798344209815)
          ·
            refine ⟨146163005516848197516314723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97442003677898798344209815 146163005516848197516314723)
            ·
              refine ⟨219244508275272296274472085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146163005516848197516314723 219244508275272296274472085)
              ·
                refine ⟨10277086325403388887865879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 219244508275272296274472085 10277086325403388887865879)
                ·
                  refine ⟨15415629488105083331798819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10277086325403388887865879 15415629488105083331798819)
                  ·
                    refine ⟨23123444232157624997698229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15415629488105083331798819 23123444232157624997698229)
                    ·
                      refine ⟨2167822896764777343534209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23123444232157624997698229 2167822896764777343534209)
                      ·
                        rfl

theorem cell23_4221820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_4221820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221820 prefixEnd_4221820 := by exact prefixLift 4221820
  have htrace : WordTrace (prefixWord ++ tailWord_4221820) baseStart_4221820 baseEnd_4221820 := by
    simpa [prefixWord, tailWord_4221820, baseEnd_4221820] using wordTrace_append hprefix tailTrace_4221820
  have hstable : (prefixWord ++ tailWord_4221820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221820).length < 2 ^ (prefixWord ++ tailWord_4221820).sum := by decide
  have hdescent : baseEnd_4221820 < baseStart_4221820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221827 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 2, 4]
def baseStart_4221827 : Nat := 118140960795 + 4221827 * 2 ^ 59
def prefixEnd_4221827 : Nat := 4983230072969 + 3 ^ 40 * 4221827 * 2
def baseEnd_4221827 : Nat := 722608830376452938715559

theorem tailTrace_4221827 : CollatzResearch.WordTrace tailWord_4221827 prefixEnd_4221827 722608830376452938715559 := by
  unfold tailWord_4221827
  simp only [CollatzResearch.WordTrace]
  refine ⟨153982680876049284492527735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102655120584032856328351823 153982680876049284492527735)
  ·
    refine ⟨230974021314073926738791603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153982680876049284492527735 230974021314073926738791603)
    ·
      refine ⟨346461031971110890108187405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230974021314073926738791603 346461031971110890108187405)
      ·
        refine ⟨129922886989166583790570277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346461031971110890108187405 129922886989166583790570277)
        ·
          refine ⟨24360541310468734460731927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129922886989166583790570277 24360541310468734460731927)
          ·
            refine ⟨36540811965703101691097891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24360541310468734460731927 36540811965703101691097891)
            ·
              refine ⟨54811217948554652536646837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36540811965703101691097891 54811217948554652536646837)
              ·
                refine ⟨5138551682676998675310641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54811217948554652536646837 5138551682676998675310641)
                ·
                  refine ⟨3853913762007749006482981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5138551682676998675310641 3853913762007749006482981)
                  ·
                    refine ⟨722608830376452938715559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853913762007749006482981 722608830376452938715559)
                    ·
                      rfl

theorem cell23_4221827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 4].length) (baseStart_4221827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221827 prefixEnd_4221827 := by exact prefixLift 4221827
  have htrace : WordTrace (prefixWord ++ tailWord_4221827) baseStart_4221827 baseEnd_4221827 := by
    simpa [prefixWord, tailWord_4221827, baseEnd_4221827] using wordTrace_append hprefix tailTrace_4221827
  have hstable : (prefixWord ++ tailWord_4221827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221827).length < 2 ^ (prefixWord ++ tailWord_4221827).sum := by decide
  have hdescent : baseEnd_4221827 < baseStart_4221827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221867 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 3]
def baseStart_4221867 : Nat := 118140960795 + 4221867 * 2 ^ 59
def prefixEnd_4221867 : Nat := 4983230072969 + 3 ^ 40 * 4221867 * 2
def baseEnd_4221867 : Nat := 2167847030355538659646493

theorem tailTrace_4221867 : CollatzResearch.WordTrace tailWord_4221867 prefixEnd_4221867 2167847030355538659646493 := by
  unfold tailWord_4221867
  simp only [CollatzResearch.WordTrace]
  refine ⟨153984139795904371323983855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102656093197269580882655903 153984139795904371323983855)
  ·
    refine ⟨230976209693856556985975783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153984139795904371323983855 230976209693856556985975783)
    ·
      refine ⟨346464314540784835478963675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230976209693856556985975783 346464314540784835478963675)
      ·
        refine ⟨519696471811177253218445513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346464314540784835478963675 519696471811177253218445513)
        ·
          refine ⟨389772353858382939913834135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519696471811177253218445513 389772353858382939913834135)
          ·
            refine ⟨584658530787574409870751203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389772353858382939913834135 584658530787574409870751203)
            ·
              refine ⟨876987796181361614806126805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584658530787574409870751203 876987796181361614806126805)
              ·
                refine ⟨20554401473000662847018597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 876987796181361614806126805 20554401473000662847018597)
                ·
                  refine ⟨3853950276187624283815987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20554401473000662847018597 3853950276187624283815987)
                  ·
                    refine ⟨5780925414281436425723981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853950276187624283815987 5780925414281436425723981)
                    ·
                      refine ⟨2167847030355538659646493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5780925414281436425723981 2167847030355538659646493)
                      ·
                        rfl

theorem cell23_4221867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 3].length) (baseStart_4221867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221867 prefixEnd_4221867 := by exact prefixLift 4221867
  have htrace : WordTrace (prefixWord ++ tailWord_4221867) baseStart_4221867 baseEnd_4221867 := by
    simpa [prefixWord, tailWord_4221867, baseEnd_4221867] using wordTrace_append hprefix tailTrace_4221867
  have hstable : (prefixWord ++ tailWord_4221867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221867).length < 2 ^ (prefixWord ++ tailWord_4221867).sum := by decide
  have hdescent : baseEnd_4221867 < baseStart_4221867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221977 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 2, 5]
def baseStart_4221977 : Nat := 118140960795 + 4221977 * 2 ^ 59
def prefixEnd_4221977 : Nat := 4983230072969 + 3 ^ 40 * 4221977 * 2
def baseEnd_4221977 : Nat := 722634504409177743090329

theorem tailTrace_4221977 : CollatzResearch.WordTrace tailWord_4221977 prefixEnd_4221977 722634504409177743090329 := by
  unfold tailWord_4221977
  simp only [CollatzResearch.WordTrace]
  refine ⟨153988151825505860110488185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102658767883670573406992123 153988151825505860110488185)
  ·
    refine ⟨115491113869129395082866139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153988151825505860110488185 115491113869129395082866139)
    ·
      refine ⟨173236670803694092624299209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115491113869129395082866139 173236670803694092624299209)
      ·
        refine ⟨129927503102770569468224407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173236670803694092624299209 129927503102770569468224407)
        ·
          refine ⟨194891254654155854202336611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129927503102770569468224407 194891254654155854202336611)
          ·
            refine ⟨292336881981233781303504917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194891254654155854202336611 292336881981233781303504917)
            ·
              refine ⟨13703291342870333498601793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 292336881981233781303504917 13703291342870333498601793)
              ·
                refine ⟨10277468507152750123951345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13703291342870333498601793 10277468507152750123951345)
                ·
                  refine ⟨7708101380364562592963509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10277468507152750123951345 7708101380364562592963509)
                  ·
                    refine ⟨722634504409177743090329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7708101380364562592963509 722634504409177743090329)
                    ·
                      rfl

theorem cell23_4221977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_4221977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221977 prefixEnd_4221977 := by exact prefixLift 4221977
  have htrace : WordTrace (prefixWord ++ tailWord_4221977) baseStart_4221977 baseEnd_4221977 := by
    simpa [prefixWord, tailWord_4221977, baseEnd_4221977] using wordTrace_append hprefix tailTrace_4221977
  have hstable : (prefixWord ++ tailWord_4221977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221977).length < 2 ^ (prefixWord ++ tailWord_4221977).sum := by decide
  have hdescent : baseEnd_4221977 < baseStart_4221977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221981 : List Nat := [1, 4, 2, 2, 3, 1, 1, 4, 5]
def baseStart_4221981 : Nat := 118140960795 + 4221981 * 2 ^ 59
def prefixEnd_4221981 : Nat := 4983230072969 + 3 ^ 40 * 4221981 * 2
def baseEnd_4221981 : Nat := 240878396350016801513441

theorem tailTrace_4221981 : CollatzResearch.WordTrace tailWord_4221981 prefixEnd_4221981 240878396350016801513441 := by
  unfold tailWord_4221981
  simp only [CollatzResearch.WordTrace]
  refine ⟨153988297717491368793633797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102658865144994245862422531 153988297717491368793633797)
  ·
    refine ⟨28872805822029631648806337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153988297717491368793633797 28872805822029631648806337)
    ·
      refine ⟨21654604366522223736604753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28872805822029631648806337 21654604366522223736604753)
      ·
        refine ⟨16240953274891667802453565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21654604366522223736604753 16240953274891667802453565)
        ·
          refine ⟨6090357478084375425920087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16240953274891667802453565 6090357478084375425920087)
          ·
            refine ⟨9135536217126563138880131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6090357478084375425920087 9135536217126563138880131)
            ·
              refine ⟨13703304325689844708320197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9135536217126563138880131 13703304325689844708320197)
              ·
                refine ⟨2569369561066845882810037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13703304325689844708320197 2569369561066845882810037)
                ·
                  refine ⟨240878396350016801513441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2569369561066845882810037 240878396350016801513441)
                  ·
                    rfl

theorem cell23_4221981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_4221981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221981 prefixEnd_4221981 := by exact prefixLift 4221981
  have htrace : WordTrace (prefixWord ++ tailWord_4221981) baseStart_4221981 baseEnd_4221981 := by
    simpa [prefixWord, tailWord_4221981, baseEnd_4221981] using wordTrace_append hprefix tailTrace_4221981
  have hstable : (prefixWord ++ tailWord_4221981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221981).length < 2 ^ (prefixWord ++ tailWord_4221981).sum := by decide
  have hdescent : baseEnd_4221981 < baseStart_4221981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221987 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5]
def baseStart_4221987 : Nat := 118140960795 + 4221987 * 2 ^ 59
def prefixEnd_4221987 : Nat := 4983230072969 + 3 ^ 40 * 4221987 * 2
def baseEnd_4221987 : Nat := 2167908648034078190145941

theorem tailTrace_4221987 : CollatzResearch.WordTrace tailWord_4221987 prefixEnd_4221987 2167908648034078190145941 := by
  unfold tailWord_4221987
  simp only [CollatzResearch.WordTrace]
  refine ⟨153988516555469631818352215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102659011036979754545568143 153988516555469631818352215)
  ·
    refine ⟨230982774833204447727528323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153988516555469631818352215 230982774833204447727528323)
    ·
      refine ⟨346474162249806671591292485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230982774833204447727528323 346474162249806671591292485)
      ·
        refine ⟨64963905421838750923367341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346474162249806671591292485 64963905421838750923367341)
        ·
          refine ⟨24361464533189531596262753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64963905421838750923367341 24361464533189531596262753)
          ·
            refine ⟨18271098399892148697197065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24361464533189531596262753 18271098399892148697197065)
            ·
              refine ⟨13703323799919111522897799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18271098399892148697197065 13703323799919111522897799)
              ·
                refine ⟨20554985699878667284346699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13703323799919111522897799 20554985699878667284346699)
                ·
                  refine ⟨30832478549818000926520049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20554985699878667284346699 30832478549818000926520049)
                  ·
                    refine ⟨23124358912363500694890037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30832478549818000926520049 23124358912363500694890037)
                    ·
                      refine ⟨2167908648034078190145941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23124358912363500694890037 2167908648034078190145941)
                      ·
                        rfl

theorem cell23_4221987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_4221987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221987 prefixEnd_4221987 := by exact prefixLift 4221987
  have htrace : WordTrace (prefixWord ++ tailWord_4221987) baseStart_4221987 baseEnd_4221987 := by
    simpa [prefixWord, tailWord_4221987, baseEnd_4221987] using wordTrace_append hprefix tailTrace_4221987
  have hstable : (prefixWord ++ tailWord_4221987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221987).length < 2 ^ (prefixWord ++ tailWord_4221987).sum := by decide
  have hdescent : baseEnd_4221987 < baseStart_4221987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221991 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4221991 : Nat := 118140960795 + 4221991 * 2 ^ 59
def prefixEnd_4221991 : Nat := 4983230072969 + 3 ^ 40 * 4221991 * 2
def baseEnd_4221991 : Nat := 2167910701956696174495923

theorem tailTrace_4221991 : CollatzResearch.WordTrace tailWord_4221991 prefixEnd_4221991 2167910701956696174495923 := by
  unfold tailWord_4221991
  simp only [CollatzResearch.WordTrace]
  refine ⟨153988662447455140501497827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102659108298303427000998551 153988662447455140501497827)
  ·
    refine ⟨230982993671182710752246741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153988662447455140501497827 230982993671182710752246741)
    ·
      refine ⟨5413663914168344783255783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 230982993671182710752246741 5413663914168344783255783)
      ·
        refine ⟨8120495871252517174883675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5413663914168344783255783 8120495871252517174883675)
        ·
          refine ⟨12180743806878775762325513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8120495871252517174883675 12180743806878775762325513)
          ·
            refine ⟨9135557855159081821744135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12180743806878775762325513 9135557855159081821744135)
            ·
              refine ⟨13703336782738622732616203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9135557855159081821744135 13703336782738622732616203)
              ·
                refine ⟨20555005174107934098924305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13703336782738622732616203 20555005174107934098924305)
                ·
                  refine ⟨15416253880580950574193229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20555005174107934098924305 15416253880580950574193229)
                  ·
                    refine ⟨5781095205217856465322461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15416253880580950574193229 5781095205217856465322461)
                    ·
                      refine ⟨2167910701956696174495923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781095205217856465322461 2167910701956696174495923)
                      ·
                        rfl

theorem cell23_4221991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4221991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221991 prefixEnd_4221991 := by exact prefixLift 4221991
  have htrace : WordTrace (prefixWord ++ tailWord_4221991) baseStart_4221991 baseEnd_4221991 := by
    simpa [prefixWord, tailWord_4221991, baseEnd_4221991] using wordTrace_append hprefix tailTrace_4221991
  have hstable : (prefixWord ++ tailWord_4221991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221991).length < 2 ^ (prefixWord ++ tailWord_4221991).sum := by decide
  have hdescent : baseEnd_4221991 < baseStart_4221991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222037 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 8]
def baseStart_4222037 : Nat := 118140960795 + 4222037 * 2 ^ 59
def prefixEnd_4222037 : Nat := 4983230072969 + 3 ^ 40 * 4222037 * 2
def baseEnd_4222037 : Nat := 240881591340755888280079

theorem tailTrace_4222037 : CollatzResearch.WordTrace tailWord_4222037 prefixEnd_4222037 240881591340755888280079 := by
  unfold tailWord_4222037
  simp only [CollatzResearch.WordTrace]
  refine ⟨153990340205288490357672365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102660226803525660238448243 153990340205288490357672365)
  ·
    refine ⟨57746377576983183884127137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153990340205288490357672365 57746377576983183884127137)
    ·
      refine ⟨43309783182737387913095353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57746377576983183884127137 43309783182737387913095353)
      ·
        refine ⟨32482337387053040934821515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43309783182737387913095353 32482337387053040934821515)
        ·
          refine ⟨48723506080579561402232273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32482337387053040934821515 48723506080579561402232273)
          ·
            refine ⟨36542629560434671051674205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48723506080579561402232273 36542629560434671051674205)
            ·
              refine ⟨13703486085163001644377827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36542629560434671051674205 13703486085163001644377827)
              ·
                refine ⟨20555229127744502466566741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13703486085163001644377827 20555229127744502466566741)
                ·
                  refine ⟨240881591340755888280079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20555229127744502466566741 240881591340755888280079)
                  ·
                    rfl

theorem cell23_4222037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_4222037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222037 prefixEnd_4222037 := by exact prefixLift 4222037
  have htrace : WordTrace (prefixWord ++ tailWord_4222037) baseStart_4222037 baseEnd_4222037 := by
    simpa [prefixWord, tailWord_4222037, baseEnd_4222037] using wordTrace_append hprefix tailTrace_4222037
  have hstable : (prefixWord ++ tailWord_4222037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222037).length < 2 ^ (prefixWord ++ tailWord_4222037).sum := by decide
  have hdescent : baseEnd_4222037 < baseStart_4222037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222098 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_4222098 : Nat := 118140960795 + 4222098 * 2 ^ 59
def prefixEnd_4222098 : Nat := 4983230072969 + 3 ^ 40 * 4222098 * 2
def baseEnd_4222098 : Nat := 2167965644386727255857931

theorem tailTrace_4222098 : CollatzResearch.WordTrace tailWord_4222098 prefixEnd_4222098 2167965644386727255857931 := by
  unfold tailWord_4222098
  simp only [CollatzResearch.WordTrace]
  refine ⟨38498141264516874443910737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102661710038711665183761965 38498141264516874443910737)
  ·
    refine ⟨28873605948387655832933053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38498141264516874443910737 28873605948387655832933053)
    ·
      refine ⟨10827602230645370937349895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28873605948387655832933053 10827602230645370937349895)
      ·
        refine ⟨16241403345968056406024843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10827602230645370937349895 16241403345968056406024843)
        ·
          refine ⟨24362105018952084609037265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16241403345968056406024843 24362105018952084609037265)
          ·
            refine ⟨18271578764214063456777949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24362105018952084609037265 18271578764214063456777949)
            ·
              refine ⟨6851842036580273796291731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18271578764214063456777949 6851842036580273796291731)
              ·
                refine ⟨10277763054870410694437597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6851842036580273796291731 10277763054870410694437597)
                ·
                  refine ⟨3854161145576404010414099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10277763054870410694437597 3854161145576404010414099)
                  ·
                    refine ⟨5781241718364606015621149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3854161145576404010414099 5781241718364606015621149)
                    ·
                      refine ⟨2167965644386727255857931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781241718364606015621149 2167965644386727255857931)
                      ·
                        rfl

theorem cell23_4222098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_4222098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222098 prefixEnd_4222098 := by exact prefixLift 4222098
  have htrace : WordTrace (prefixWord ++ tailWord_4222098) baseStart_4222098 baseEnd_4222098 := by
    simpa [prefixWord, tailWord_4222098, baseEnd_4222098] using wordTrace_append hprefix tailTrace_4222098
  have hstable : (prefixWord ++ tailWord_4222098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222098).length < 2 ^ (prefixWord ++ tailWord_4222098).sum := by decide
  have hdescent : baseEnd_4222098 < baseStart_4222098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222125 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_4222125 : Nat := 118140960795 + 4222125 * 2 ^ 59
def prefixEnd_4222125 : Nat := 4983230072969 + 3 ^ 40 * 4222125 * 2
def baseEnd_4222125 : Nat := 2167979508364398650220307

theorem tailTrace_4222125 : CollatzResearch.WordTrace tailWord_4222125 prefixEnd_4222125 2167979508364398650220307 := by
  unfold tailWord_4222125
  simp only [CollatzResearch.WordTrace]
  refine ⟨153993549828969681386875829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102662366552646454257917219 153993549828969681386875829)
  ·
    refine ⟨14436895296465907630019609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153993549828969681386875829 14436895296465907630019609)
    ·
      refine ⟨10827671472349430722514707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14436895296465907630019609 10827671472349430722514707)
      ·
        refine ⟨16241507208524146083772061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10827671472349430722514707 16241507208524146083772061)
        ·
          refine ⟨6090565203196554781414523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16241507208524146083772061 6090565203196554781414523)
          ·
            refine ⟨9135847804794832172121785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6090565203196554781414523 9135847804794832172121785)
            ·
              refine ⟨6851885853596124129091339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9135847804794832172121785 6851885853596124129091339)
              ·
                refine ⟨10277828780394186193637009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6851885853596124129091339 10277828780394186193637009)
                ·
                  refine ⟨7708371585295639645227757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10277828780394186193637009 7708371585295639645227757)
                  ·
                    refine ⟨2890639344485864866960409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7708371585295639645227757 2890639344485864866960409)
                    ·
                      refine ⟨2167979508364398650220307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2890639344485864866960409 2167979508364398650220307)
                      ·
                        rfl

theorem cell23_4222125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_4222125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222125 prefixEnd_4222125 := by exact prefixLift 4222125
  have htrace : WordTrace (prefixWord ++ tailWord_4222125) baseStart_4222125 baseEnd_4222125 := by
    simpa [prefixWord, tailWord_4222125, baseEnd_4222125] using wordTrace_append hprefix tailTrace_4222125
  have hstable : (prefixWord ++ tailWord_4222125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222125).length < 2 ^ (prefixWord ++ tailWord_4222125).sum := by decide
  have hdescent : baseEnd_4222125 < baseStart_4222125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222127 : List Nat := [1, 1, 2, 1, 2, 3, 4, 9]
def baseStart_4222127 : Nat := 118140960795 + 4222127 * 2 ^ 59
def prefixEnd_4222127 : Nat := 4983230072969 + 3 ^ 40 * 4222127 * 2
def baseEnd_4222127 : Nat := 80295575382433616385011

theorem tailTrace_4222127 : CollatzResearch.WordTrace tailWord_4222127 prefixEnd_4222127 80295575382433616385011 := by
  unfold tailWord_4222127
  simp only [CollatzResearch.WordTrace]
  refine ⟨153993622774962435728448635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102662415183308290485632423 153993622774962435728448635)
  ·
    refine ⟨230990434162443653592672953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153993622774962435728448635 230990434162443653592672953)
    ·
      refine ⟨173242825621832740194504715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230990434162443653592672953 173242825621832740194504715)
      ·
        refine ⟨259864238432749110291757073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173242825621832740194504715 259864238432749110291757073)
        ·
          refine ⟨194898178824561832718817805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259864238432749110291757073 194898178824561832718817805)
          ·
            refine ⟨73086817059210687269556677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194898178824561832718817805 73086817059210687269556677)
            ·
              refine ⟨13703778198602003863041877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73086817059210687269556677 13703778198602003863041877)
              ·
                refine ⟨80295575382433616385011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13703778198602003863041877 80295575382433616385011)
                ·
                  rfl

theorem cell23_4222127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 9].length) (baseStart_4222127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222127 prefixEnd_4222127 := by exact prefixLift 4222127
  have htrace : WordTrace (prefixWord ++ tailWord_4222127) baseStart_4222127 baseEnd_4222127 := by
    simpa [prefixWord, tailWord_4222127, baseEnd_4222127] using wordTrace_append hprefix tailTrace_4222127
  have hstable : (prefixWord ++ tailWord_4222127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222127).length < 2 ^ (prefixWord ++ tailWord_4222127).sum := by decide
  have hdescent : baseEnd_4222127 < baseStart_4222127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222141 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_4222141 : Nat := 118140960795 + 4222141 * 2 ^ 59
def prefixEnd_4222141 : Nat := 4983230072969 + 3 ^ 40 * 4222141 * 2
def baseEnd_4222141 : Nat := 2167987724054870587620233

theorem tailTrace_4222141 : CollatzResearch.WordTrace tailWord_4222141 prefixEnd_4222141 2167987724054870587620233 := by
  unfold tailWord_4222141
  simp only [CollatzResearch.WordTrace]
  refine ⟨153994133396911716119458277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102662755597941144079638851 153994133396911716119458277)
  ·
    refine ⟨28873900011920946772398427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153994133396911716119458277 28873900011920946772398427)
    ·
      refine ⟨43310850017881420158597641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28873900011920946772398427 43310850017881420158597641)
      ·
        refine ⟨32483137513411065118948231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43310850017881420158597641 32483137513411065118948231)
        ·
          refine ⟨48724706270116597678422347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32483137513411065118948231 48724706270116597678422347)
          ·
            refine ⟨73087059405174896517633521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48724706270116597678422347 73087059405174896517633521)
            ·
              refine ⟨54815294553881172388225141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73087059405174896517633521 54815294553881172388225141)
              ·
                refine ⟨5138933864426359911396107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54815294553881172388225141 5138933864426359911396107)
                ·
                  refine ⟨7708400796639539867094161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5138933864426359911396107 7708400796639539867094161)
                  ·
                    refine ⟨5781300597479654900320621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7708400796639539867094161 5781300597479654900320621)
                    ·
                      refine ⟨2167987724054870587620233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781300597479654900320621 2167987724054870587620233)
                      ·
                        rfl

theorem cell23_4222141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_4222141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222141 prefixEnd_4222141 := by exact prefixLift 4222141
  have htrace : WordTrace (prefixWord ++ tailWord_4222141) baseStart_4222141 baseEnd_4222141 := by
    simpa [prefixWord, tailWord_4222141, baseEnd_4222141] using wordTrace_append hprefix tailTrace_4222141
  have hstable : (prefixWord ++ tailWord_4222141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222141).length < 2 ^ (prefixWord ++ tailWord_4222141).sum := by decide
  have hdescent : baseEnd_4222141 < baseStart_4222141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222144 : List Nat := [2, 1, 1, 2, 7, 10]
def baseStart_4222144 : Nat := 118140960795 + 4222144 * 2 ^ 59
def prefixEnd_4222144 : Nat := 4983230072969 + 3 ^ 40 * 4222144 * 2
def baseEnd_4222144 : Nat := 8921766520563103192933

theorem tailTrace_4222144 : CollatzResearch.WordTrace tailWord_4222144 prefixEnd_4222144 8921766520563103192933 := by
  unfold tailWord_4222144
  simp only [CollatzResearch.WordTrace]
  refine ⟨76997121407950423815908743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102662828543933898421211657 76997121407950423815908743)
  ·
    refine ⟨115495682111925635723863115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76997121407950423815908743 115495682111925635723863115)
    ·
      refine ⟨173243523167888453585794673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115495682111925635723863115 173243523167888453585794673)
      ·
        refine ⟨129932642375916340189346005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173243523167888453585794673 129932642375916340189346005)
        ·
          refine ⟨3045296305685539223187797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 129932642375916340189346005 3045296305685539223187797)
          ·
            refine ⟨8921766520563103192933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3045296305685539223187797 8921766520563103192933)
            ·
              rfl

theorem cell23_4222144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 10].length) (baseStart_4222144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222144 prefixEnd_4222144 := by exact prefixLift 4222144
  have htrace : WordTrace (prefixWord ++ tailWord_4222144) baseStart_4222144 baseEnd_4222144 := by
    simpa [prefixWord, tailWord_4222144, baseEnd_4222144] using wordTrace_append hprefix tailTrace_4222144
  have hstable : (prefixWord ++ tailWord_4222144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222144).length < 2 ^ (prefixWord ++ tailWord_4222144).sum := by decide
  have hdescent : baseEnd_4222144 < baseStart_4222144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222147 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6]
def baseStart_4222147 : Nat := 118140960795 + 4222147 * 2 ^ 59
def prefixEnd_4222147 : Nat := 4983230072969 + 3 ^ 40 * 4222147 * 2
def baseEnd_4222147 : Nat := 2167990804938797564145205

theorem tailTrace_4222147 : CollatzResearch.WordTrace tailWord_4222147 prefixEnd_4222147 2167990804938797564145205 := by
  unfold tailWord_4222147
  simp only [CollatzResearch.WordTrace]
  refine ⟨153994352234889979144176695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102662901489926652762784463 153994352234889979144176695)
  ·
    refine ⟨230991528352334968716265043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153994352234889979144176695 230991528352334968716265043)
    ·
      refine ⟨346487292528502453074397565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230991528352334968716265043 346487292528502453074397565)
      ·
        refine ⟨129932734698188419902899087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346487292528502453074397565 129932734698188419902899087)
        ·
          refine ⟨194899102047282629854348631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129932734698188419902899087 194899102047282629854348631)
          ·
            refine ⟨292348653070923944781522947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194899102047282629854348631 292348653070923944781522947)
            ·
              refine ⟨438522979606385917172284421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292348653070923944781522947 438522979606385917172284421)
              ·
                refine ⟨82223058676197359469803329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438522979606385917172284421 82223058676197359469803329)
                ·
                  refine ⟨61667294007148019602352497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82223058676197359469803329 61667294007148019602352497)
                  ·
                    refine ⟨46250470505361014701764373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61667294007148019602352497 46250470505361014701764373)
                    ·
                      refine ⟨2167990804938797564145205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46250470505361014701764373 2167990804938797564145205)
                      ·
                        rfl

theorem cell23_4222147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_4222147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222147 prefixEnd_4222147 := by exact prefixLift 4222147
  have htrace : WordTrace (prefixWord ++ tailWord_4222147) baseStart_4222147 baseEnd_4222147 := by
    simpa [prefixWord, tailWord_4222147, baseEnd_4222147] using wordTrace_append hprefix tailTrace_4222147
  have hstable : (prefixWord ++ tailWord_4222147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222147).length < 2 ^ (prefixWord ++ tailWord_4222147).sum := by decide
  have hdescent : baseEnd_4222147 < baseStart_4222147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222184 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4222184 : Nat := 118140960795 + 4222184 * 2 ^ 59
def prefixEnd_4222184 : Nat := 4983230072969 + 3 ^ 40 * 4222184 * 2
def baseEnd_4222184 : Nat := 2168009803723013919382535

theorem tailTrace_4222184 : CollatzResearch.WordTrace tailWord_4222184 prefixEnd_4222184 2168009803723013919382535 := by
  unfold tailWord_4222184
  simp only [CollatzResearch.WordTrace]
  refine ⟨76997850867877967231636803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102663801157170622975515737 76997850867877967231636803)
  ·
    refine ⟨115496776301816950847455205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76997850867877967231636803 115496776301816950847455205)
    ·
      refine ⟨21655645556590678283897851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115496776301816950847455205 21655645556590678283897851)
      ·
        refine ⟨32483468334886017425846777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21655645556590678283897851 32483468334886017425846777)
        ·
          refine ⟨24362601251164513069385083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32483468334886017425846777 24362601251164513069385083)
          ·
            refine ⟨36543901876746769604077625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24362601251164513069385083 36543901876746769604077625)
            ·
              refine ⟨27407926407560077203058219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36543901876746769604077625 27407926407560077203058219)
              ·
                refine ⟨41111889611340115804587329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27407926407560077203058219 41111889611340115804587329)
                ·
                  refine ⟨30833917208505086853440497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41111889611340115804587329 30833917208505086853440497)
                  ·
                    refine ⟨23125437906378815140080373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30833917208505086853440497 23125437906378815140080373)
                    ·
                      refine ⟨2168009803723013919382535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23125437906378815140080373 2168009803723013919382535)
                      ·
                        rfl

theorem cell23_4222184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4222184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222184 prefixEnd_4222184 := by exact prefixLift 4222184
  have htrace : WordTrace (prefixWord ++ tailWord_4222184) baseStart_4222184 baseEnd_4222184 := by
    simpa [prefixWord, tailWord_4222184, baseEnd_4222184] using wordTrace_append hprefix tailTrace_4222184
  have hstable : (prefixWord ++ tailWord_4222184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222184).length < 2 ^ (prefixWord ++ tailWord_4222184).sum := by decide
  have hdescent : baseEnd_4222184 < baseStart_4222184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222341 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 6]
def baseStart_4222341 : Nat := 118140960795 + 4222341 * 2 ^ 59
def prefixEnd_4222341 : Nat := 4983230072969 + 3 ^ 40 * 4222341 * 2
def baseEnd_4222341 : Nat := 240898935576196645013257

theorem tailTrace_4222341 : CollatzResearch.WordTrace tailWord_4222341 prefixEnd_4222341 240898935576196645013257 := by
  unfold tailWord_4222341
  simp only [CollatzResearch.WordTrace]
  refine ⟨154001427996187150276738877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102667618664124766851159251 154001427996187150276738877)
  ·
    refine ⟨57750535498570181353777079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154001427996187150276738877 57750535498570181353777079)
    ·
      refine ⟨86625803247855272030665619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57750535498570181353777079 86625803247855272030665619)
      ·
        refine ⟨129938704871782908045998429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86625803247855272030665619 129938704871782908045998429)
        ·
          refine ⟨48727014326918590517249411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129938704871782908045998429 48727014326918590517249411)
          ·
            refine ⟨73090521490377885775874117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48727014326918590517249411 73090521490377885775874117)
            ·
              refine ⟨13704472779445853582976397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73090521490377885775874117 13704472779445853582976397)
              ·
                refine ⟨5139177292292195093616149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13704472779445853582976397 5139177292292195093616149)
                ·
                  refine ⟨240898935576196645013257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5139177292292195093616149 240898935576196645013257)
                  ·
                    rfl

theorem cell23_4222341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_4222341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222341 prefixEnd_4222341 := by exact prefixLift 4222341
  have htrace : WordTrace (prefixWord ++ tailWord_4222341) baseStart_4222341 baseEnd_4222341 := by
    simpa [prefixWord, tailWord_4222341, baseEnd_4222341] using wordTrace_append hprefix tailTrace_4222341
  have hstable : (prefixWord ++ tailWord_4222341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222341).length < 2 ^ (prefixWord ++ tailWord_4222341).sum := by decide
  have hdescent : baseEnd_4222341 < baseStart_4222341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222368 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 5, 1, 3]
def baseStart_4222368 : Nat := 118140960795 + 4222368 * 2 ^ 59
def prefixEnd_4222368 : Nat := 4983230072969 + 3 ^ 40 * 4222368 * 2
def baseEnd_4222368 : Nat := 2168104284163441199481689

theorem tailTrace_4222368 : CollatzResearch.WordTrace tailWord_4222368 prefixEnd_4222368 2168104284163441199481689 := by
  unfold tailWord_4222368
  simp only [CollatzResearch.WordTrace]
  refine ⟨77001206383544666943985879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102668275178059555925314505 77001206383544666943985879)
  ·
    refine ⟨115501809575317000415978819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77001206383544666943985879 115501809575317000415978819)
    ·
      refine ⟨173252714362975500623968229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115501809575317000415978819 173252714362975500623968229)
      ·
        refine ⟨32484883943057906366994043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173252714362975500623968229 32484883943057906366994043)
        ·
          refine ⟨48727325914586859550491065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32484883943057906366994043 48727325914586859550491065)
          ·
            refine ⟨36545494435940144662868299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48727325914586859550491065 36545494435940144662868299)
            ·
              refine ⟨54818241653910216994302449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36545494435940144662868299 54818241653910216994302449)
              ·
                refine ⟨41113681240432662745726837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54818241653910216994302449 41113681240432662745726837)
                ·
                  refine ⟨3854407616290562132411891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41113681240432662745726837 3854407616290562132411891)
                  ·
                    refine ⟨5781611424435843198617837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3854407616290562132411891 5781611424435843198617837)
                    ·
                      refine ⟨2168104284163441199481689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781611424435843198617837 2168104284163441199481689)
                      ·
                        rfl

theorem cell23_4222368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_4222368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222368 prefixEnd_4222368 := by exact prefixLift 4222368
  have htrace : WordTrace (prefixWord ++ tailWord_4222368) baseStart_4222368 baseEnd_4222368 := by
    simpa [prefixWord, tailWord_4222368, baseEnd_4222368] using wordTrace_append hprefix tailTrace_4222368
  have hstable : (prefixWord ++ tailWord_4222368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222368).length < 2 ^ (prefixWord ++ tailWord_4222368).sum := by decide
  have hdescent : baseEnd_4222368 < baseStart_4222368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222385 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4222385 : Nat := 118140960795 + 4222385 * 2 ^ 59
def prefixEnd_4222385 : Nat := 4983230072969 + 3 ^ 40 * 4222385 * 2
def baseEnd_4222385 : Nat := 2168113013334567632969111

theorem tailTrace_4222385 : CollatzResearch.WordTrace tailWord_4222385 prefixEnd_4222385 2168113013334567632969111 := by
  unfold tailWord_4222385
  simp only [CollatzResearch.WordTrace]
  refine ⟨154003032808027745791340609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102668688538685163860893739 154003032808027745791340609)
  ·
    refine ⟨115502274606020809343505457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154003032808027745791340609 115502274606020809343505457)
    ·
      refine ⟨86626705954515607007629093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115502274606020809343505457 86626705954515607007629093)
      ·
        refine ⟨16242507366471676313930455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86626705954515607007629093 16242507366471676313930455)
        ·
          refine ⟨24363761049707514470895683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16242507366471676313930455 24363761049707514470895683)
          ·
            refine ⟨36545641574561271706343525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24363761049707514470895683 36545641574561271706343525)
            ·
              refine ⟨6852307795230238444939411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36545641574561271706343525 6852307795230238444939411)
              ·
                refine ⟨10278461692845357667409117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6852307795230238444939411 10278461692845357667409117)
                ·
                  refine ⟨3854423134817009125278419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10278461692845357667409117 3854423134817009125278419)
                  ·
                    refine ⟨5781634702225513687917629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3854423134817009125278419 5781634702225513687917629)
                    ·
                      refine ⟨2168113013334567632969111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781634702225513687917629 2168113013334567632969111)
                      ·
                        rfl

theorem cell23_4222385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4222385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222385 prefixEnd_4222385 := by exact prefixLift 4222385
  have htrace : WordTrace (prefixWord ++ tailWord_4222385) baseStart_4222385 baseEnd_4222385 := by
    simpa [prefixWord, tailWord_4222385, baseEnd_4222385] using wordTrace_append hprefix tailTrace_4222385
  have hstable : (prefixWord ++ tailWord_4222385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222385).length < 2 ^ (prefixWord ++ tailWord_4222385).sum := by decide
  have hdescent : baseEnd_4222385 < baseStart_4222385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222408 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_4222408 : Nat := 118140960795 + 4222408 * 2 ^ 59
def prefixEnd_4222408 : Nat := 4983230072969 + 3 ^ 40 * 4222408 * 2
def baseEnd_4222408 : Nat := 2168124823389621042981505

theorem tailTrace_4222408 : CollatzResearch.WordTrace tailWord_4222408 prefixEnd_4222408 2168124823389621042981505 := by
  unfold tailWord_4222408
  simp only [CollatzResearch.WordTrace]
  refine ⟨77001935843472210359713939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102669247791296280479618585 77001935843472210359713939)
  ·
    refine ⟨115502903765208315539570909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77001935843472210359713939 115502903765208315539570909)
    ·
      refine ⟨43313588911953118327339091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115502903765208315539570909 43313588911953118327339091)
      ·
        refine ⟨64970383367929677491008637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43313588911953118327339091 64970383367929677491008637)
        ·
          refine ⟨24363893762973629059128239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64970383367929677491008637 24363893762973629059128239)
          ·
            refine ⟨36545840644460443588692359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24363893762973629059128239 36545840644460443588692359)
            ·
              refine ⟨54818760966690665383038539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36545840644460443588692359 54818760966690665383038539)
              ·
                refine ⟨82228141450035998074557809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54818760966690665383038539 82228141450035998074557809)
                ·
                  refine ⟨61671106087526998555918357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82228141450035998074557809 61671106087526998555918357)
                  ·
                    refine ⟨2890833097852828057308673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61671106087526998555918357 2890833097852828057308673)
                    ·
                      refine ⟨2168124823389621042981505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2890833097852828057308673 2168124823389621042981505)
                      ·
                        rfl

theorem cell23_4222408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_4222408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222408 prefixEnd_4222408 := by exact prefixLift 4222408
  have htrace : WordTrace (prefixWord ++ tailWord_4222408) baseStart_4222408 baseEnd_4222408 := by
    simpa [prefixWord, tailWord_4222408, baseEnd_4222408] using wordTrace_append hprefix tailTrace_4222408
  have hstable : (prefixWord ++ tailWord_4222408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222408).length < 2 ^ (prefixWord ++ tailWord_4222408).sum := by decide
  have hdescent : baseEnd_4222408 < baseStart_4222408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222458 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_4222458 : Nat := 118140960795 + 4222458 * 2 ^ 59
def prefixEnd_4222458 : Nat := 4983230072969 + 3 ^ 40 * 4222458 * 2
def baseEnd_4222458 : Nat := 2168150497422345847356275

theorem tailTrace_4222458 : CollatzResearch.WordTrace tailWord_4222458 prefixEnd_4222458 2168150497422345847356275 := by
  unfold tailWord_4222458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38501423834190819814687007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102670463557842186172498685 38501423834190819814687007)
  ·
    refine ⟨57752135751286229722030511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38501423834190819814687007 57752135751286229722030511)
    ·
      refine ⟨86628203626929344583045767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57752135751286229722030511 86628203626929344583045767)
      ·
        refine ⟨129942305440394016874568651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86628203626929344583045767 129942305440394016874568651)
        ·
          refine ⟨194913458160591025311852977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129942305440394016874568651 194913458160591025311852977)
          ·
            refine ⟨146185093620443268983889733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194913458160591025311852977 146185093620443268983889733)
            ·
              refine ⟨27409705053833112934479325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146185093620443268983889733 27409705053833112934479325)
              ·
                refine ⟨10278639395187417350429747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27409705053833112934479325 10278639395187417350429747)
                ·
                  refine ⟨15417959092781126025644621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10278639395187417350429747 15417959092781126025644621)
                  ·
                    refine ⟨5781734659792922259616733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15417959092781126025644621 5781734659792922259616733)
                    ·
                      refine ⟨2168150497422345847356275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781734659792922259616733 2168150497422345847356275)
                      ·
                        rfl

theorem cell23_4222458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_4222458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222458 prefixEnd_4222458 := by exact prefixLift 4222458
  have htrace : WordTrace (prefixWord ++ tailWord_4222458) baseStart_4222458 baseEnd_4222458 := by
    simpa [prefixWord, tailWord_4222458, baseEnd_4222458] using wordTrace_append hprefix tailTrace_4222458
  have hstable : (prefixWord ++ tailWord_4222458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222458).length < 2 ^ (prefixWord ++ tailWord_4222458).sum := by decide
  have hdescent : baseEnd_4222458 < baseStart_4222458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222475 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 3]
def baseStart_4222475 : Nat := 118140960795 + 4222475 * 2 ^ 59
def prefixEnd_4222475 : Nat := 4983230072969 + 3 ^ 40 * 4222475 * 2
def baseEnd_4222475 : Nat := 2168159226593472280843697

theorem tailTrace_4222475 : CollatzResearch.WordTrace tailWord_4222475 prefixEnd_4222475 2168159226593472280843697 := by
  unfold tailWord_4222475
  simp only [CollatzResearch.WordTrace]
  refine ⟨154006315377701691162116879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102670876918467794108077919 154006315377701691162116879)
  ·
    refine ⟨231009473066552536743175319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154006315377701691162116879 231009473066552536743175319)
    ·
      refine ⟨346514209599828805114762979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231009473066552536743175319 346514209599828805114762979)
      ·
        refine ⟨519771314399743207672144469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346514209599828805114762979 519771314399743207672144469)
        ·
          refine ⟨6091070090621990714907943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 519771314399743207672144469 6091070090621990714907943)
          ·
            refine ⟨9136605135932986072361915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091070090621990714907943 9136605135932986072361915)
            ·
              refine ⟨13704907703899479108542873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9136605135932986072361915 13704907703899479108542873)
              ·
                refine ⟨10278680777924609331407155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13704907703899479108542873 10278680777924609331407155)
                ·
                  refine ⟨15418021166886913997110733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10278680777924609331407155 15418021166886913997110733)
                  ·
                    refine ⟨5781757937582592748916525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15418021166886913997110733 5781757937582592748916525)
                    ·
                      refine ⟨2168159226593472280843697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781757937582592748916525 2168159226593472280843697)
                      ·
                        rfl

theorem cell23_4222475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 3].length) (baseStart_4222475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222475 prefixEnd_4222475 := by exact prefixLift 4222475
  have htrace : WordTrace (prefixWord ++ tailWord_4222475) baseStart_4222475 baseEnd_4222475 := by
    simpa [prefixWord, tailWord_4222475, baseEnd_4222475] using wordTrace_append hprefix tailTrace_4222475
  have hstable : (prefixWord ++ tailWord_4222475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222475).length < 2 ^ (prefixWord ++ tailWord_4222475).sum := by decide
  have hdescent : baseEnd_4222475 < baseStart_4222475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222492 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_4222492 : Nat := 118140960795 + 4222492 * 2 ^ 59
def prefixEnd_4222492 : Nat := 4983230072969 + 3 ^ 40 * 4222492 * 2
def baseEnd_4222492 : Nat := 2168167955764598714331119

theorem tailTrace_4222492 : CollatzResearch.WordTrace tailWord_4222492 prefixEnd_4222492 2168167955764598714331119 := by
  unfold tailWord_4222492
  simp only [CollatzResearch.WordTrace]
  refine ⟨77003467709320051532742865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102671290279093402043657153 77003467709320051532742865)
  ·
    refine ⟨57752600781990038649557149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77003467709320051532742865 57752600781990038649557149)
    ·
      refine ⟨21657225293246264493583931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57752600781990038649557149 21657225293246264493583931)
      ·
        refine ⟨32485837939869396740375897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21657225293246264493583931 32485837939869396740375897)
        ·
          refine ⟨24364378454902047555281923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32485837939869396740375897 24364378454902047555281923)
          ·
            refine ⟨36546567682353071332922885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24364378454902047555281923 36546567682353071332922885)
            ·
              refine ⟨6852481440441200874923041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36546567682353071332922885 6852481440441200874923041)
              ·
                refine ⟨5139361080330900656192281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6852481440441200874923041 5139361080330900656192281)
                ·
                  refine ⟨3854520810248175492144211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5139361080330900656192281 3854520810248175492144211)
                  ·
                    refine ⟨5781781215372263238216317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3854520810248175492144211 5781781215372263238216317)
                    ·
                      refine ⟨2168167955764598714331119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781781215372263238216317 2168167955764598714331119)
                      ·
                        rfl

theorem cell23_4222492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_4222492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222492 prefixEnd_4222492 := by exact prefixLift 4222492
  have htrace : WordTrace (prefixWord ++ tailWord_4222492) baseStart_4222492 baseEnd_4222492 := by
    simpa [prefixWord, tailWord_4222492, baseEnd_4222492] using wordTrace_append hprefix tailTrace_4222492
  have hstable : (prefixWord ++ tailWord_4222492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222492).length < 2 ^ (prefixWord ++ tailWord_4222492).sum := by decide
  have hdescent : baseEnd_4222492 < baseStart_4222492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222498 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_4222498 : Nat := 118140960795 + 4222498 * 2 ^ 59
def prefixEnd_4222498 : Nat := 4983230072969 + 3 ^ 40 * 4222498 * 2
def baseEnd_4222498 : Nat := 2168171036648525690856091

theorem tailTrace_4222498 : CollatzResearch.WordTrace tailWord_4222498 prefixEnd_4222498 2168171036648525690856091 := by
  unfold tailWord_4222498
  simp only [CollatzResearch.WordTrace]
  refine ⟨38501788564154591522551037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102671436171078910726802765 38501788564154591522551037)
  ·
    refine ⟨14438170711557971820956639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38501788564154591522551037 14438170711557971820956639)
    ·
      refine ⟨21657256067336957731434959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14438170711557971820956639 21657256067336957731434959)
      ·
        refine ⟨32485884101005436597152439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21657256067336957731434959 32485884101005436597152439)
        ·
          refine ⟨48728826151508154895728659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32485884101005436597152439 48728826151508154895728659)
          ·
            refine ⟨73093239227262232343592989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48728826151508154895728659 73093239227262232343592989)
            ·
              refine ⟨27409964710223337128847371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73093239227262232343592989 27409964710223337128847371)
              ·
                refine ⟨41114947065335005693271057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27409964710223337128847371 41114947065335005693271057)
                ·
                  refine ⟨30836210299001254269953293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41114947065335005693271057 30836210299001254269953293)
                  ·
                    refine ⟨11563578862125470351232485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30836210299001254269953293 11563578862125470351232485)
                    ·
                      refine ⟨2168171036648525690856091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11563578862125470351232485 2168171036648525690856091)
                      ·
                        rfl

theorem cell23_4222498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_4222498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222498 prefixEnd_4222498 := by exact prefixLift 4222498
  have htrace : WordTrace (prefixWord ++ tailWord_4222498) baseStart_4222498 baseEnd_4222498 := by
    simpa [prefixWord, tailWord_4222498, baseEnd_4222498] using wordTrace_append hprefix tailTrace_4222498
  have hstable : (prefixWord ++ tailWord_4222498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222498).length < 2 ^ (prefixWord ++ tailWord_4222498).sum := by decide
  have hdescent : baseEnd_4222498 < baseStart_4222498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222515 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 1, 4, 2]
def baseStart_4222515 : Nat := 118140960795 + 4222515 * 2 ^ 59
def prefixEnd_4222515 : Nat := 4983230072969 + 3 ^ 40 * 4222515 * 2
def baseEnd_4222515 : Nat := 2168179765819652124343513

theorem tailTrace_4222515 : CollatzResearch.WordTrace tailWord_4222515 prefixEnd_4222515 2168179765819652124343513 := by
  unfold tailWord_4222515
  simp only [CollatzResearch.WordTrace]
  refine ⟨154007774297556777993572999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102671849531704518662381999 154007774297556777993572999)
  ·
    refine ⟨231011661446335166990359499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154007774297556777993572999 231011661446335166990359499)
    ·
      refine ⟨346517492169502750485539249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231011661446335166990359499 346517492169502750485539249)
      ·
        refine ⟨259888119127127062864154437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346517492169502750485539249 259888119127127062864154437)
        ·
          refine ⟨48729022336336324287028957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259888119127127062864154437 48729022336336324287028957)
          ·
            refine ⟨18273383376126121607635859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48729022336336324287028957 18273383376126121607635859)
            ·
              refine ⟨27410075064189182411453789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18273383376126121607635859 27410075064189182411453789)
              ·
                refine ⟨10278778149070943404295171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27410075064189182411453789 10278778149070943404295171)
                ·
                  refine ⟨15418167223606415106442757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10278778149070943404295171 15418167223606415106442757)
                  ·
                    refine ⟨2890906354426202832458017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15418167223606415106442757 2890906354426202832458017)
                    ·
                      refine ⟨2168179765819652124343513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2890906354426202832458017 2168179765819652124343513)
                      ·
                        rfl

theorem cell23_4222515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4, 2].length) (baseStart_4222515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222515 prefixEnd_4222515 := by exact prefixLift 4222515
  have htrace : WordTrace (prefixWord ++ tailWord_4222515) baseStart_4222515 baseEnd_4222515 := by
    simpa [prefixWord, tailWord_4222515, baseEnd_4222515] using wordTrace_append hprefix tailTrace_4222515
  have hstable : (prefixWord ++ tailWord_4222515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222515).length < 2 ^ (prefixWord ++ tailWord_4222515).sum := by decide
  have hdescent : baseEnd_4222515 < baseStart_4222515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222531 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7]
def baseStart_4222531 : Nat := 118140960795 + 4222531 * 2 ^ 59
def prefixEnd_4222531 : Nat := 4983230072969 + 3 ^ 40 * 4222531 * 2
def baseEnd_4222531 : Nat := 2168187981510124061743439

theorem tailTrace_4222531 : CollatzResearch.WordTrace tailWord_4222531 prefixEnd_4222531 2168187981510124061743439 := by
  unfold tailWord_4222531
  simp only [CollatzResearch.WordTrace]
  refine ⟨154008357865498812726155447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102672238576999208484103631 154008357865498812726155447)
  ·
    refine ⟨231012536798248219089233171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154008357865498812726155447 231012536798248219089233171)
    ·
      refine ⟨346518805197372328633849757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231012536798248219089233171 346518805197372328633849757)
      ·
        refine ⟨129944551949014623237693659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346518805197372328633849757 129944551949014623237693659)
        ·
          refine ⟨194916827923521934856540489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129944551949014623237693659 194916827923521934856540489)
          ·
            refine ⟨146187620942641451142405367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194916827923521934856540489 146187620942641451142405367)
            ·
              refine ⟨219281431413962176713608051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146187620942641451142405367 219281431413962176713608051)
              ·
                refine ⟨328922147120943265070412077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219281431413962176713608051 328922147120943265070412077)
                ·
                  refine ⟨123345805170353724401404529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328922147120943265070412077 123345805170353724401404529)
                  ·
                    refine ⟨92509353877765293301053397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123345805170353724401404529 92509353877765293301053397)
                    ·
                      refine ⟨2168187981510124061743439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92509353877765293301053397 2168187981510124061743439)
                      ·
                        rfl

theorem cell23_4222531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_4222531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222531 prefixEnd_4222531 := by exact prefixLift 4222531
  have htrace : WordTrace (prefixWord ++ tailWord_4222531) baseStart_4222531 baseEnd_4222531 := by
    simpa [prefixWord, tailWord_4222531, baseEnd_4222531] using wordTrace_append hprefix tailTrace_4222531
  have hstable : (prefixWord ++ tailWord_4222531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222531).length < 2 ^ (prefixWord ++ tailWord_4222531).sum := by decide
  have hdescent : baseEnd_4222531 < baseStart_4222531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222565 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_4222565 : Nat := 118140960795 + 4222565 * 2 ^ 59
def prefixEnd_4222565 : Nat := 4983230072969 + 3 ^ 40 * 4222565 * 2
def baseEnd_4222565 : Nat := 2168205439852376928718283

theorem tailTrace_4222565 : CollatzResearch.WordTrace tailWord_4222565 prefixEnd_4222565 2168205439852376928718283 := by
  unfold tailWord_4222565
  simp only [CollatzResearch.WordTrace]
  refine ⟨154009597947375636532893149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102673065298250424355262099 154009597947375636532893149)
  ·
    refine ⟨57753599230265863699834931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154009597947375636532893149 57753599230265863699834931)
    ·
      refine ⟨86630398845398795549752397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57753599230265863699834931 86630398845398795549752397)
      ·
        refine ⟨32486399567024548331157149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86630398845398795549752397 32486399567024548331157149)
        ·
          refine ⟨12182399837634205624183931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32486399567024548331157149 12182399837634205624183931)
          ·
            refine ⟨18273599756451308436275897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12182399837634205624183931 18273599756451308436275897)
            ·
              refine ⟨13705199817338481327206923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18273599756451308436275897 13705199817338481327206923)
              ·
                refine ⟨20557799726007721990810385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13705199817338481327206923 20557799726007721990810385)
                ·
                  refine ⟨15418349794505791493107789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20557799726007721990810385 15418349794505791493107789)
                  ·
                    refine ⟨5781881172939671809915421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15418349794505791493107789 5781881172939671809915421)
                    ·
                      refine ⟨2168205439852376928718283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5781881172939671809915421 2168205439852376928718283)
                      ·
                        rfl

theorem cell23_4222565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_4222565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222565 prefixEnd_4222565 := by exact prefixLift 4222565
  have htrace : WordTrace (prefixWord ++ tailWord_4222565) baseStart_4222565 baseEnd_4222565 := by
    simpa [prefixWord, tailWord_4222565, baseEnd_4222565] using wordTrace_append hprefix tailTrace_4222565
  have hstable : (prefixWord ++ tailWord_4222565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222565).length < 2 ^ (prefixWord ++ tailWord_4222565).sum := by decide
  have hdescent : baseEnd_4222565 < baseStart_4222565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222612 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4222612 : Nat := 118140960795 + 4222612 * 2 ^ 59
def prefixEnd_4222612 : Nat := 4983230072969 + 3 ^ 40 * 4222612 * 2
def baseEnd_4222612 : Nat := 2168229573443138244830567

theorem tailTrace_4222612 : CollatzResearch.WordTrace tailWord_4222612 prefixEnd_4222612 2168229573443138244830567 := by
  unfold tailWord_4222612
  simp only [CollatzResearch.WordTrace]
  refine ⟨77005656089102681779927045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102674208118803575706569393 77005656089102681779927045)
  ·
    refine ⟨14438560516706752833736321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77005656089102681779927045 14438560516706752833736321)
    ·
      refine ⟨10828920387530064625302241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14438560516706752833736321 10828920387530064625302241)
      ·
        refine ⟨8121690290647548468976681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10828920387530064625302241 8121690290647548468976681)
        ·
          refine ⟨6091267717985661351732511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8121690290647548468976681 6091267717985661351732511)
          ·
            refine ⟨9136901576978492027598767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091267717985661351732511 9136901576978492027598767)
            ·
              refine ⟨13705352365467738041398151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9136901576978492027598767 13705352365467738041398151)
              ·
                refine ⟨20558028548201607062097227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13705352365467738041398151 20558028548201607062097227)
                ·
                  refine ⟨30837042822302410593145841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20558028548201607062097227 30837042822302410593145841)
                  ·
                    refine ⟨23127782116726807944859381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30837042822302410593145841 23127782116726807944859381)
                    ·
                      refine ⟨2168229573443138244830567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23127782116726807944859381 2168229573443138244830567)
                      ·
                        rfl

theorem cell23_4222612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4222612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222612 prefixEnd_4222612 := by exact prefixLift 4222612
  have htrace : WordTrace (prefixWord ++ tailWord_4222612) baseStart_4222612 baseEnd_4222612 := by
    simpa [prefixWord, tailWord_4222612, baseEnd_4222612] using wordTrace_append hprefix tailTrace_4222612
  have hstable : (prefixWord ++ tailWord_4222612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222612).length < 2 ^ (prefixWord ++ tailWord_4222612).sum := by decide
  have hdescent : baseEnd_4222612 < baseStart_4222612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222689 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_4222689 : Nat := 118140960795 + 4222689 * 2 ^ 59
def prefixEnd_4222689 : Nat := 4983230072969 + 3 ^ 40 * 4222689 * 2
def baseEnd_4222689 : Nat := 2168269111453534443567713

theorem tailTrace_4222689 : CollatzResearch.WordTrace tailWord_4222689 prefixEnd_4222689 2168269111453534443567713 := by
  unfold tailWord_4222689
  simp only [CollatzResearch.WordTrace]
  refine ⟨154014120598926405710407121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102676080399284270473604747 154014120598926405710407121)
  ·
    refine ⟨115510590449194804282805341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154014120598926405710407121 115510590449194804282805341)
    ·
      refine ⟨43316471418448051606052003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115510590449194804282805341 43316471418448051606052003)
      ·
        refine ⟨64974707127672077409078005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43316471418448051606052003 64974707127672077409078005)
        ·
          refine ⟨6091378793219257257101063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64974707127672077409078005 6091378793219257257101063)
          ·
            refine ⟨9137068189828885885651595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091378793219257257101063 9137068189828885885651595)
            ·
              refine ⟨13705602284743328828477393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9137068189828885885651595 13705602284743328828477393)
              ·
                refine ⟨10279201713557496621358045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13705602284743328828477393 10279201713557496621358045)
                ·
                  refine ⟨3854700642584061233009267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10279201713557496621358045 3854700642584061233009267)
                  ·
                    refine ⟨5782050963876091849513901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3854700642584061233009267 5782050963876091849513901)
                    ·
                      refine ⟨2168269111453534443567713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782050963876091849513901 2168269111453534443567713)
                      ·
                        rfl

theorem cell23_4222689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_4222689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222689 prefixEnd_4222689 := by exact prefixLift 4222689
  have htrace : WordTrace (prefixWord ++ tailWord_4222689) baseStart_4222689 baseEnd_4222689 := by
    simpa [prefixWord, tailWord_4222689, baseEnd_4222689] using wordTrace_append hprefix tailTrace_4222689
  have hstable : (prefixWord ++ tailWord_4222689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222689).length < 2 ^ (prefixWord ++ tailWord_4222689).sum := by decide
  have hdescent : baseEnd_4222689 < baseStart_4222689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222705 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 1, 6]
def baseStart_4222705 : Nat := 118140960795 + 4222705 * 2 ^ 59
def prefixEnd_4222705 : Nat := 4983230072969 + 3 ^ 40 * 4222705 * 2
def baseEnd_4222705 : Nat := 722759109048002126989213

theorem tailTrace_4222705 : CollatzResearch.WordTrace tailWord_4222705 prefixEnd_4222705 722759109048002126989213 := by
  unfold tailWord_4222705
  simp only [CollatzResearch.WordTrace]
  refine ⟨154014704166868440442989569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102676469444578960295326379 154014704166868440442989569)
  ·
    refine ⟨115511028125151330332242177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154014704166868440442989569 115511028125151330332242177)
    ·
      refine ⟨86633271093863497749181633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115511028125151330332242177 86633271093863497749181633)
      ·
        refine ⟨64974953320397623311886225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86633271093863497749181633 64974953320397623311886225)
        ·
          refine ⟨48731214990298217483914669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64974953320397623311886225 48731214990298217483914669)
          ·
            refine ⟨18274205621361831556468001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48731214990298217483914669 18274205621361831556468001)
            ·
              refine ⟨13705654216021373667351001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18274205621361831556468001 13705654216021373667351001)
              ·
                refine ⟨10279240662016030250513251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13705654216021373667351001 10279240662016030250513251)
                ·
                  refine ⟨15418860993024045375769877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10279240662016030250513251 15418860993024045375769877)
                  ·
                    refine ⟨722759109048002126989213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15418860993024045375769877 722759109048002126989213)
                    ·
                      rfl

theorem cell23_4222705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_4222705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222705 prefixEnd_4222705 := by exact prefixLift 4222705
  have htrace : WordTrace (prefixWord ++ tailWord_4222705) baseStart_4222705 baseEnd_4222705 := by
    simpa [prefixWord, tailWord_4222705, baseEnd_4222705] using wordTrace_append hprefix tailTrace_4222705
  have hstable : (prefixWord ++ tailWord_4222705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222705).length < 2 ^ (prefixWord ++ tailWord_4222705).sum := by decide
  have hdescent : baseEnd_4222705 < baseStart_4222705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222706 : List Nat := [3, 2, 1, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4222706 : Nat := 118140960795 + 4222706 * 2 ^ 59
def prefixEnd_4222706 : Nat := 4983230072969 + 3 ^ 40 * 4222706 * 2
def baseEnd_4222706 : Nat := 2168277840624660877055135

theorem tailTrace_4222706 : CollatzResearch.WordTrace tailWord_4222706 prefixEnd_4222706 2168277840624660877055135 := by
  unfold tailWord_4222706
  simp only [CollatzResearch.WordTrace]
  refine ⟨38503685159966204403443993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102676493759909878409183981 38503685159966204403443993)
  ·
    refine ⟨28877763869974653302582995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38503685159966204403443993 28877763869974653302582995)
    ·
      refine ⟨43316645804961979953874493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28877763869974653302582995 43316645804961979953874493)
      ·
        refine ⟨16243742176860742482702935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43316645804961979953874493 16243742176860742482702935)
        ·
          refine ⟨24365613265291113724054403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16243742176860742482702935 24365613265291113724054403)
          ·
            refine ⟨36548419897936670586081605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24365613265291113724054403 36548419897936670586081605)
            ·
              refine ⟨6852828730863125734890301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36548419897936670586081605 6852828730863125734890301)
              ·
                refine ⟨2569810774073672150583863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6852828730863125734890301 2569810774073672150583863)
                ·
                  refine ⟨3854716161110508225875795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2569810774073672150583863 3854716161110508225875795)
                  ·
                    refine ⟨5782074241665762338813693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3854716161110508225875795 5782074241665762338813693)
                    ·
                      refine ⟨2168277840624660877055135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782074241665762338813693 2168277840624660877055135)
                      ·
                        rfl

theorem cell23_4222706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4222706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222706 prefixEnd_4222706 := by exact prefixLift 4222706
  have htrace : WordTrace (prefixWord ++ tailWord_4222706) baseStart_4222706 baseEnd_4222706 := by
    simpa [prefixWord, tailWord_4222706, baseEnd_4222706] using wordTrace_append hprefix tailTrace_4222706
  have hstable : (prefixWord ++ tailWord_4222706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222706).length < 2 ^ (prefixWord ++ tailWord_4222706).sum := by decide
  have hdescent : baseEnd_4222706 < baseStart_4222706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222715 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 3]
def baseStart_4222715 : Nat := 118140960795 + 4222715 * 2 ^ 59
def prefixEnd_4222715 : Nat := 4983230072969 + 3 ^ 40 * 4222715 * 2
def baseEnd_4222715 : Nat := 2168282461950551341842593

theorem tailTrace_4222715 : CollatzResearch.WordTrace tailWord_4222715 prefixEnd_4222715 2168282461950551341842593 := by
  unfold tailWord_4222715
  simp only [CollatzResearch.WordTrace]
  refine ⟨154015068896832212150853599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102676712597888141433902399 154015068896832212150853599)
  ·
    refine ⟨231022603345248318226280399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154015068896832212150853599 231022603345248318226280399)
    ·
      refine ⟨346533905017872477339420599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231022603345248318226280399 346533905017872477339420599)
      ·
        refine ⟨519800857526808716009130899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346533905017872477339420599 519800857526808716009130899)
        ·
          refine ⟨779701286290213074013696349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519800857526808716009130899 779701286290213074013696349)
          ·
            refine ⟨292387982358829902755136131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 779701286290213074013696349 292387982358829902755136131)
            ·
              refine ⟨438581973538244854132704197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292387982358829902755136131 438581973538244854132704197)
              ·
                refine ⟨82234120038420910149882037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438581973538244854132704197 82234120038420910149882037)
                ·
                  refine ⟨7709448753601960326551441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82234120038420910149882037 7709448753601960326551441)
                  ·
                    refine ⟨5782086565201470244913581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7709448753601960326551441 5782086565201470244913581)
                    ·
                      refine ⟨2168282461950551341842593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782086565201470244913581 2168282461950551341842593)
                      ·
                        rfl

theorem cell23_4222715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 3].length) (baseStart_4222715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222715 prefixEnd_4222715 := by exact prefixLift 4222715
  have htrace : WordTrace (prefixWord ++ tailWord_4222715) baseStart_4222715 baseEnd_4222715 := by
    simpa [prefixWord, tailWord_4222715, baseEnd_4222715] using wordTrace_append hprefix tailTrace_4222715
  have hstable : (prefixWord ++ tailWord_4222715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222715).length < 2 ^ (prefixWord ++ tailWord_4222715).sum := by decide
  have hdescent : baseEnd_4222715 < baseStart_4222715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222790 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_4222790 : Nat := 118140960795 + 4222790 * 2 ^ 59
def prefixEnd_4222790 : Nat := 4983230072969 + 3 ^ 40 * 4222790 * 2
def baseEnd_4222790 : Nat := 722773657666546182801583

theorem tailTrace_4222790 : CollatzResearch.WordTrace tailWord_4222790 prefixEnd_4222790 722773657666546182801583 := by
  unfold tailWord_4222790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813056386611265623744807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102678536247706999973222549 4813056386611265623744807)
  ·
    refine ⟨7219584579916898435617211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4813056386611265623744807 7219584579916898435617211)
    ·
      refine ⟨10829376869875347653425817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7219584579916898435617211 10829376869875347653425817)
      ·
        refine ⟨8122032652406510740069363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10829376869875347653425817 8122032652406510740069363)
        ·
          refine ⟨12183048978609766110104045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8122032652406510740069363 12183048978609766110104045)
          ·
            refine ⟨4568643366978662291289017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12183048978609766110104045 4568643366978662291289017)
            ·
              refine ⟨3426482525233996718466763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4568643366978662291289017 3426482525233996718466763)
              ·
                refine ⟨5139723787850995077700145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3426482525233996718466763 5139723787850995077700145)
                ·
                  refine ⟨3854792840888246308275109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5139723787850995077700145 3854792840888246308275109)
                  ·
                    refine ⟨722773657666546182801583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3854792840888246308275109 722773657666546182801583)
                    ·
                      rfl

theorem cell23_4222790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_4222790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222790 prefixEnd_4222790 := by exact prefixLift 4222790
  have htrace : WordTrace (prefixWord ++ tailWord_4222790) baseStart_4222790 baseEnd_4222790 := by
    simpa [prefixWord, tailWord_4222790, baseEnd_4222790] using wordTrace_append hprefix tailTrace_4222790
  have hstable : (prefixWord ++ tailWord_4222790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222790).length < 2 ^ (prefixWord ++ tailWord_4222790).sum := by decide
  have hdescent : baseEnd_4222790 < baseStart_4222790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222796 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_4222796 : Nat := 118140960795 + 4222796 * 2 ^ 59
def prefixEnd_4222796 : Nat := 4983230072969 + 3 ^ 40 * 4222796 * 2
def baseEnd_4222796 : Nat := 2168324053883565524929721

theorem tailTrace_4222796 : CollatzResearch.WordTrace tailWord_4222796 prefixEnd_4222796 2168324053883565524929721 := by
  unfold tailWord_4222796
  simp only [CollatzResearch.WordTrace]
  refine ⟨77009011604769381492276121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102678682139692508656368161 77009011604769381492276121)
  ·
    refine ⟨57756758703577036119207091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77009011604769381492276121 57756758703577036119207091)
    ·
      refine ⟨86635138055365554178810637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57756758703577036119207091 86635138055365554178810637)
      ·
        refine ⟨32488176770762082817053989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86635138055365554178810637 32488176770762082817053989)
        ·
          refine ⟨6091533144517890528197623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32488176770762082817053989 6091533144517890528197623)
          ·
            refine ⟨9137299716776835792296435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091533144517890528197623 9137299716776835792296435)
            ·
              refine ⟨13705949575165253688444653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9137299716776835792296435 13705949575165253688444653)
              ·
                refine ⟨5139731090686970133166745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13705949575165253688444653 5139731090686970133166745)
                ·
                  refine ⟨3854798318015227599875059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5139731090686970133166745 3854798318015227599875059)
                  ·
                    refine ⟨5782197477022841399812589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3854798318015227599875059 5782197477022841399812589)
                    ·
                      refine ⟨2168324053883565524929721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782197477022841399812589 2168324053883565524929721)
                      ·
                        rfl

theorem cell23_4222796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_4222796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222796 prefixEnd_4222796 := by exact prefixLift 4222796
  have htrace : WordTrace (prefixWord ++ tailWord_4222796) baseStart_4222796 baseEnd_4222796 := by
    simpa [prefixWord, tailWord_4222796, baseEnd_4222796] using wordTrace_append hprefix tailTrace_4222796
  have hstable : (prefixWord ++ tailWord_4222796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222796).length < 2 ^ (prefixWord ++ tailWord_4222796).sum := by decide
  have hdescent : baseEnd_4222796 < baseStart_4222796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222845 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_4222845 : Nat := 118140960795 + 4222845 * 2 ^ 59
def prefixEnd_4222845 : Nat := 4983230072969 + 3 ^ 40 * 4222845 * 2
def baseEnd_4222845 : Nat := 2168349214435635833216995

theorem tailTrace_4222845 : CollatzResearch.WordTrace tailWord_4222845 prefixEnd_4222845 2168349214435635833216995 := by
  unfold tailWord_4222845
  simp only [CollatzResearch.WordTrace]
  refine ⟨154019810386361244353085989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102679873590907496235390659 154019810386361244353085989)
  ·
    refine ⟨28878714447442733316203623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154019810386361244353085989 28878714447442733316203623)
    ·
      refine ⟨43318071671164099974305435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28878714447442733316203623 43318071671164099974305435)
      ·
        refine ⟨64977107506746149961458153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43318071671164099974305435 64977107506746149961458153)
        ·
          refine ⟨48732830630059612471093615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64977107506746149961458153 48732830630059612471093615)
          ·
            refine ⟨73099245945089418706640423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48732830630059612471093615 73099245945089418706640423)
            ·
              refine ⟨109648868917634128059960635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73099245945089418706640423 109648868917634128059960635)
              ·
                refine ⟨164473303376451192089940953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109648868917634128059960635 164473303376451192089940953)
                ·
                  refine ⟨123354977532338394067455715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164473303376451192089940953 123354977532338394067455715)
                  ·
                    refine ⟨185032466298507591101183573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123354977532338394067455715 185032466298507591101183573)
                    ·
                      refine ⟨2168349214435635833216995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 185032466298507591101183573 2168349214435635833216995)
                      ·
                        rfl

theorem cell23_4222845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_4222845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222845 prefixEnd_4222845 := by exact prefixLift 4222845
  have htrace : WordTrace (prefixWord ++ tailWord_4222845) baseStart_4222845 baseEnd_4222845 := by
    simpa [prefixWord, tailWord_4222845, baseEnd_4222845] using wordTrace_append hprefix tailTrace_4222845
  have hstable : (prefixWord ++ tailWord_4222845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222845).length < 2 ^ (prefixWord ++ tailWord_4222845).sum := by decide
  have hdescent : baseEnd_4222845 < baseStart_4222845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222852 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_4222852 : Nat := 118140960795 + 4222852 * 2 ^ 59
def prefixEnd_4222852 : Nat := 4983230072969 + 3 ^ 40 * 4222852 * 2
def baseEnd_4222852 : Nat := 2168352808800217305829463

theorem tailTrace_4222852 : CollatzResearch.WordTrace tailWord_4222852 prefixEnd_4222852 2168352808800217305829463 := by
  unfold tailWord_4222852
  simp only [CollatzResearch.WordTrace]
  refine ⟨77010032848667942274295405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102680043798223923032393873 77010032848667942274295405)
  ·
    refine ⟨28878762318250478352860777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77010032848667942274295405 28878762318250478352860777)
    ·
      refine ⟨21659071738687858764645583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28878762318250478352860777 21659071738687858764645583)
      ·
        refine ⟨32488607608031788146968375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21659071738687858764645583 32488607608031788146968375)
        ·
          refine ⟨48732911412047682220452563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32488607608031788146968375 48732911412047682220452563)
          ·
            refine ⟨73099367118071523330678845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48732911412047682220452563 73099367118071523330678845)
            ·
              refine ⟨27412262669276821249004567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73099367118071523330678845 27412262669276821249004567)
              ·
                refine ⟨41118394003915231873506851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27412262669276821249004567 41118394003915231873506851)
                ·
                  refine ⟨61677591005872847810260277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41118394003915231873506851 61677591005872847810260277)
                  ·
                    refine ⟨5782274156800579482211901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61677591005872847810260277 5782274156800579482211901)
                    ·
                      refine ⟨2168352808800217305829463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782274156800579482211901 2168352808800217305829463)
                      ·
                        rfl

theorem cell23_4222852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_4222852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222852 prefixEnd_4222852 := by exact prefixLift 4222852
  have htrace : WordTrace (prefixWord ++ tailWord_4222852) baseStart_4222852 baseEnd_4222852 := by
    simpa [prefixWord, tailWord_4222852, baseEnd_4222852] using wordTrace_append hprefix tailTrace_4222852
  have hstable : (prefixWord ++ tailWord_4222852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222852).length < 2 ^ (prefixWord ++ tailWord_4222852).sum := by decide
  have hdescent : baseEnd_4222852 < baseStart_4222852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222865 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_4222865 : Nat := 118140960795 + 4222865 * 2 ^ 59
def prefixEnd_4222865 : Nat := 4983230072969 + 3 ^ 40 * 4222865 * 2
def baseEnd_4222865 : Nat := 2168359484048725754966903

theorem tailTrace_4222865 : CollatzResearch.WordTrace tailWord_4222865 prefixEnd_4222865 2168359484048725754966903 := by
  unfold tailWord_4222865
  simp only [CollatzResearch.WordTrace]
  refine ⟨154020539846288787768814049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102680359897525858512542699 154020539846288787768814049)
  ·
    refine ⟨115515404884716590826610537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154020539846288787768814049 115515404884716590826610537)
    ·
      refine ⟨86636553663537443119957903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115515404884716590826610537 86636553663537443119957903)
      ·
        refine ⟨129954830495306164679936855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86636553663537443119957903 129954830495306164679936855)
        ·
          refine ⟨194932245742959247019905283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129954830495306164679936855 194932245742959247019905283)
          ·
            refine ⟨292398368614438870529857925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194932245742959247019905283 292398368614438870529857925)
            ·
              refine ⟨54824694115207288224348361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 292398368614438870529857925 54824694115207288224348361)
              ·
                refine ⟨41118520586405466168261271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54824694115207288224348361 41118520586405466168261271)
                ·
                  refine ⟨61677780879608199252391907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41118520586405466168261271 61677780879608199252391907)
                  ·
                    refine ⟨92516671319412298878587861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61677780879608199252391907 92516671319412298878587861)
                    ·
                      refine ⟨2168359484048725754966903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92516671319412298878587861 2168359484048725754966903)
                      ·
                        rfl

theorem cell23_4222865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_4222865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222865 prefixEnd_4222865 := by exact prefixLift 4222865
  have htrace : WordTrace (prefixWord ++ tailWord_4222865) baseStart_4222865 baseEnd_4222865 := by
    simpa [prefixWord, tailWord_4222865, baseEnd_4222865] using wordTrace_append hprefix tailTrace_4222865
  have hstable : (prefixWord ++ tailWord_4222865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222865).length < 2 ^ (prefixWord ++ tailWord_4222865).sum := by decide
  have hdescent : baseEnd_4222865 < baseStart_4222865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222876 : List Nat := [2, 2, 3, 3, 1, 2, 2, 3, 5]
def baseStart_4222876 : Nat := 118140960795 + 4222876 * 2 ^ 59
def prefixEnd_4222876 : Nat := 4983230072969 + 3 ^ 40 * 4222876 * 2
def baseEnd_4222876 : Nat := 240929459148436134658817

theorem tailTrace_4222876 : CollatzResearch.WordTrace tailWord_4222876 prefixEnd_4222876 240929459148436134658817 := by
  unfold tailWord_4222876
  simp only [CollatzResearch.WordTrace]
  refine ⟨77010470524624468323732241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102680627366165957764976321 77010470524624468323732241)
  ·
    refine ⟨57757852893468351242799181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77010470524624468323732241 57757852893468351242799181)
    ·
      refine ⟨21659194835050631716049693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57757852893468351242799181 21659194835050631716049693)
      ·
        refine ⟨8122198063143986893518635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21659194835050631716049693 8122198063143986893518635)
        ·
          refine ⟨12183297094715980340277953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8122198063143986893518635 12183297094715980340277953)
          ·
            refine ⟨9137472821036985255208465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12183297094715980340277953 9137472821036985255208465)
            ·
              refine ⟨6853104615777738941406349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9137472821036985255208465 6853104615777738941406349)
              ·
                refine ⟨2569914230916652103027381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6853104615777738941406349 2569914230916652103027381)
                ·
                  refine ⟨240929459148436134658817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2569914230916652103027381 240929459148436134658817)
                  ·
                    rfl

theorem cell23_4222876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_4222876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222876 prefixEnd_4222876 := by exact prefixLift 4222876
  have htrace : WordTrace (prefixWord ++ tailWord_4222876) baseStart_4222876 baseEnd_4222876 := by
    simpa [prefixWord, tailWord_4222876, baseEnd_4222876] using wordTrace_append hprefix tailTrace_4222876
  have hstable : (prefixWord ++ tailWord_4222876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222876).length < 2 ^ (prefixWord ++ tailWord_4222876).sum := by decide
  have hdescent : baseEnd_4222876 < baseStart_4222876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222885 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_4222885 : Nat := 118140960795 + 4222885 * 2 ^ 59
def prefixEnd_4222885 : Nat := 4983230072969 + 3 ^ 40 * 4222885 * 2
def baseEnd_4222885 : Nat := 722789917887271892238937

theorem tailTrace_4222885 : CollatzResearch.WordTrace tailWord_4222885 prefixEnd_4222885 722789917887271892238937 := by
  unfold tailWord_4222885
  simp only [CollatzResearch.WordTrace]
  refine ⟨154021269306216331184542109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102680846204144220789694739 154021269306216331184542109)
  ·
    refine ⟨57757975989831124194203291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154021269306216331184542109 57757975989831124194203291)
    ·
      refine ⟨86636963984746686291304937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57757975989831124194203291 86636963984746686291304937)
      ·
        refine ⟨64977722988560014718478703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86636963984746686291304937 64977722988560014718478703)
        ·
          refine ⟨97466584482840022077718055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64977722988560014718478703 97466584482840022077718055)
          ·
            refine ⟨146199876724260033116577083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97466584482840022077718055 146199876724260033116577083)
            ·
              refine ⟨219299815086390049674865625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146199876724260033116577083 219299815086390049674865625)
              ·
                refine ⟨164474861314792537256149219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219299815086390049674865625 164474861314792537256149219)
                ·
                  refine ⟨246712291972188805884223829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164474861314792537256149219 246712291972188805884223829)
                  ·
                    refine ⟨722789917887271892238937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 246712291972188805884223829 722789917887271892238937)
                    ·
                      rfl

theorem cell23_4222885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_4222885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222885 prefixEnd_4222885 := by exact prefixLift 4222885
  have htrace : WordTrace (prefixWord ++ tailWord_4222885) baseStart_4222885 baseEnd_4222885 := by
    simpa [prefixWord, tailWord_4222885, baseEnd_4222885] using wordTrace_append hprefix tailTrace_4222885
  have hstable : (prefixWord ++ tailWord_4222885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222885).length < 2 ^ (prefixWord ++ tailWord_4222885).sum := by decide
  have hdescent : baseEnd_4222885 < baseStart_4222885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222912 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3]
def baseStart_4222912 : Nat := 118140960795 + 4222912 * 2 ^ 59
def prefixEnd_4222912 : Nat := 4983230072969 + 3 ^ 40 * 4222912 * 2
def baseEnd_4222912 : Nat := 2168383617639487071079187

theorem tailTrace_4222912 : CollatzResearch.WordTrace tailWord_4222912 prefixEnd_4222912 2168383617639487071079187 := by
  unfold tailWord_4222912
  simp only [CollatzResearch.WordTrace]
  refine ⟨77011127038559257397887495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102681502718079009863849993 77011127038559257397887495)
  ·
    refine ⟨115516690557838886096831243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77011127038559257397887495 115516690557838886096831243)
    ·
      refine ⟨173275035836758329145246865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115516690557838886096831243 173275035836758329145246865)
      ·
        refine ⟨129956276877568746858935149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173275035836758329145246865 129956276877568746858935149)
        ·
          refine ⟨48733603829088280072100681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129956276877568746858935149 48733603829088280072100681)
          ·
            refine ⟨36550202871816210054075511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48733603829088280072100681 36550202871816210054075511)
            ·
              refine ⟨54825304307724315081113267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36550202871816210054075511 54825304307724315081113267)
              ·
                refine ⟨82237956461586472621669901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54825304307724315081113267 82237956461586472621669901)
                ·
                  refine ⟨30839233673094927233126213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82237956461586472621669901 30839233673094927233126213)
                  ·
                    refine ⟨5782356313705298856211165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30839233673094927233126213 5782356313705298856211165)
                    ·
                      refine ⟨2168383617639487071079187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782356313705298856211165 2168383617639487071079187)
                      ·
                        rfl

theorem cell23_4222912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_4222912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222912 prefixEnd_4222912 := by exact prefixLift 4222912
  have htrace : WordTrace (prefixWord ++ tailWord_4222912) baseStart_4222912 baseEnd_4222912 := by
    simpa [prefixWord, tailWord_4222912, baseEnd_4222912] using wordTrace_append hprefix tailTrace_4222912
  have hstable : (prefixWord ++ tailWord_4222912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222912).length < 2 ^ (prefixWord ++ tailWord_4222912).sum := by decide
  have hdescent : baseEnd_4222912 < baseStart_4222912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222915 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 12]
def baseStart_4222915 : Nat := 118140960795 + 4222915 * 2 ^ 59
def prefixEnd_4222915 : Nat := 4983230072969 + 3 ^ 40 * 4222915 * 2
def baseEnd_4222915 : Nat := 240931684231272284371297

theorem tailTrace_4222915 : CollatzResearch.WordTrace tailWord_4222915 prefixEnd_4222915 240931684231272284371297 := by
  unfold tailWord_4222915
  simp only [CollatzResearch.WordTrace]
  refine ⟨154022363496107646308134199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102681575664071764205422799 154022363496107646308134199)
  ·
    refine ⟨231033545244161469462201299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154022363496107646308134199 231033545244161469462201299)
    ·
      refine ⟨346550317866242204193301949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231033545244161469462201299 346550317866242204193301949)
      ·
        refine ⟨129956369199840826572488231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346550317866242204193301949 129956369199840826572488231)
        ·
          refine ⟨194934553799761239858732347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129956369199840826572488231 194934553799761239858732347)
          ·
            refine ⟨292401830699641859788098521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194934553799761239858732347 292401830699641859788098521)
            ·
              refine ⟨219301373024731394841073891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292401830699641859788098521 219301373024731394841073891)
              ·
                refine ⟨328952059537097092261610837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219301373024731394841073891 328952059537097092261610837)
                ·
                  refine ⟨240931684231272284371297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 328952059537097092261610837 240931684231272284371297)
                  ·
                    rfl

theorem cell23_4222915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 12].length) (baseStart_4222915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222915 prefixEnd_4222915 := by exact prefixLift 4222915
  have htrace : WordTrace (prefixWord ++ tailWord_4222915) baseStart_4222915 baseEnd_4222915 := by
    simpa [prefixWord, tailWord_4222915, baseEnd_4222915] using wordTrace_append hprefix tailTrace_4222915
  have hstable : (prefixWord ++ tailWord_4222915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222915).length < 2 ^ (prefixWord ++ tailWord_4222915).sum := by decide
  have hdescent : baseEnd_4222915 < baseStart_4222915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222932 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 10]
def baseStart_4222932 : Nat := 118140960795 + 4222932 * 2 ^ 59
def prefixEnd_4222932 : Nat := 4983230072969 + 3 ^ 40 * 4222932 * 2
def baseEnd_4222932 : Nat := 240932654139175221425455

theorem tailTrace_4222932 : CollatzResearch.WordTrace tailWord_4222932 prefixEnd_4222932 240932654139175221425455 := by
  unfold tailWord_4222932
  simp only [CollatzResearch.WordTrace]
  refine ⟨77011491768523029105751525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102681989024697372141002033 77011491768523029105751525)
  ·
    refine ⟨14439654706598067957328411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77011491768523029105751525 14439654706598067957328411)
    ·
      refine ⟨21659482059897101935992617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14439654706598067957328411 21659482059897101935992617)
      ·
        refine ⟨16244611544922826451994463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21659482059897101935992617 16244611544922826451994463)
        ·
          refine ⟨24366917317384239677991695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16244611544922826451994463 24366917317384239677991695)
          ·
            refine ⟨36550375976076359516987543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24366917317384239677991695 36550375976076359516987543)
            ·
              refine ⟨54825563964114539275481315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36550375976076359516987543 54825563964114539275481315)
              ·
                refine ⟨82238345946171808913221973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54825563964114539275481315 82238345946171808913221973)
                ·
                  refine ⟨240932654139175221425455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 82238345946171808913221973 240932654139175221425455)
                  ·
                    rfl

theorem cell23_4222932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_4222932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222932 prefixEnd_4222932 := by exact prefixLift 4222932
  have htrace : WordTrace (prefixWord ++ tailWord_4222932) baseStart_4222932 baseEnd_4222932 := by
    simpa [prefixWord, tailWord_4222932, baseEnd_4222932] using wordTrace_append hprefix tailTrace_4222932
  have hstable : (prefixWord ++ tailWord_4222932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222932).length < 2 ^ (prefixWord ++ tailWord_4222932).sum := by decide
  have hdescent : baseEnd_4222932 < baseStart_4222932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222966 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_4222966 : Nat := 118140960795 + 4222966 * 2 ^ 59
def prefixEnd_4222966 : Nat := 4983230072969 + 3 ^ 40 * 4222966 * 2
def baseEnd_4222966 : Nat := 240934593954981095533771

theorem tailTrace_4222966 : CollatzResearch.WordTrace tailWord_4222966 prefixEnd_4222966 240934593954981095533771 := by
  unfold tailWord_4222966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9626513976182680126140047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102682815745948588012160501 9626513976182680126140047)
  ·
    refine ⟨14439770964274020189210071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9626513976182680126140047 14439770964274020189210071)
    ·
      refine ⟨21659656446411030283815107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14439770964274020189210071 21659656446411030283815107)
      ·
        refine ⟨32489484669616545425722661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21659656446411030283815107 32489484669616545425722661)
        ·
          refine ⟨6091778375553102267322999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32489484669616545425722661 6091778375553102267322999)
          ·
            refine ⟨9137667563329653400984499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091778375553102267322999 9137667563329653400984499)
            ·
              refine ⟨13706501344994480101476749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9137667563329653400984499 13706501344994480101476749)
              ·
                refine ⟨5139938004372930038053781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13706501344994480101476749 5139938004372930038053781)
                ·
                  refine ⟨240934593954981095533771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5139938004372930038053781 240934593954981095533771)
                  ·
                    rfl

theorem cell23_4222966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_4222966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222966 prefixEnd_4222966 := by exact prefixLift 4222966
  have htrace : WordTrace (prefixWord ++ tailWord_4222966) baseStart_4222966 baseEnd_4222966 := by
    simpa [prefixWord, tailWord_4222966, baseEnd_4222966] using wordTrace_append hprefix tailTrace_4222966
  have hstable : (prefixWord ++ tailWord_4222966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222966).length < 2 ^ (prefixWord ++ tailWord_4222966).sum := by decide
  have hdescent : baseEnd_4222966 < baseStart_4222966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4222992 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 1, 6]
def baseStart_4222992 : Nat := 118140960795 + 4222992 * 2 ^ 59
def prefixEnd_4222992 : Nat := 4983230072969 + 3 ^ 40 * 4222992 * 2
def baseEnd_4222992 : Nat := 722808232030615586026273

theorem tailTrace_4222992 : CollatzResearch.WordTrace tailWord_4222992 prefixEnd_4222992 722808232030615586026273 := by
  unfold tailWord_4222992
  simp only [CollatzResearch.WordTrace]
  refine ⟨77012585958414344229343615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102683447944552458972458153 77012585958414344229343615)
  ·
    refine ⟨115518878937621516344015423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77012585958414344229343615 115518878937621516344015423)
    ·
      refine ⟨173278318406432274516023135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115518878937621516344015423 173278318406432274516023135)
      ·
        refine ⟨259917477609648411774034703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173278318406432274516023135 259917477609648411774034703)
        ·
          refine ⟨389876216414472617661052055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259917477609648411774034703 389876216414472617661052055)
          ·
            refine ⟨584814324621708926491578083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389876216414472617661052055 584814324621708926491578083)
            ·
              refine ⟨877221486932563389737367125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584814324621708926491578083 877221486932563389737367125)
              ·
                refine ⟨10279939299990977223484771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 877221486932563389737367125 10279939299990977223484771)
                ·
                  refine ⟨15419908949986465835227157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10279939299990977223484771 15419908949986465835227157)
                  ·
                    refine ⟨722808232030615586026273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15419908949986465835227157 722808232030615586026273)
                    ·
                      rfl

theorem cell23_4222992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_4222992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4222992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4222992 prefixEnd_4222992 := by exact prefixLift 4222992
  have htrace : WordTrace (prefixWord ++ tailWord_4222992) baseStart_4222992 baseEnd_4222992 := by
    simpa [prefixWord, tailWord_4222992, baseEnd_4222992] using wordTrace_append hprefix tailTrace_4222992
  have hstable : (prefixWord ++ tailWord_4222992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4222992).length < 2 ^ (prefixWord ++ tailWord_4222992).sum := by decide
  have hdescent : baseEnd_4222992 < baseStart_4222992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4222992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223026 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_4223026 : Nat := 118140960795 + 4223026 * 2 ^ 59
def prefixEnd_4223026 : Nat := 4983230072969 + 3 ^ 40 * 4223026 * 2
def baseEnd_4223026 : Nat := 722814051478033208351221

theorem tailTrace_4223026 : CollatzResearch.WordTrace tailWord_4223026 prefixEnd_4223026 722814051478033208351221 := by
  unfold tailWord_4223026
  simp only [CollatzResearch.WordTrace]
  refine ⟨38506602999676378066356233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102684274665803674843616621 38506602999676378066356233)
  ·
    refine ⟨28879952249757283549767175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38506602999676378066356233 28879952249757283549767175)
    ·
      refine ⟨43319928374635925324650763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28879952249757283549767175 43319928374635925324650763)
      ·
        refine ⟨64979892561953887986976145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43319928374635925324650763 64979892561953887986976145)
        ·
          refine ⟨48734919421465415990232109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64979892561953887986976145 48734919421465415990232109)
          ·
            refine ⟨18275594783049530996337041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48734919421465415990232109 18275594783049530996337041)
            ·
              refine ⟨13706696087287148247252781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18275594783049530996337041 13706696087287148247252781)
              ·
                refine ⟨5140011032732680592719793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13706696087287148247252781 5140011032732680592719793)
                ·
                  refine ⟨3855008274549510444539845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5140011032732680592719793 3855008274549510444539845)
                  ·
                    refine ⟨722814051478033208351221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855008274549510444539845 722814051478033208351221)
                    ·
                      rfl

theorem cell23_4223026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_4223026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223026 prefixEnd_4223026 := by exact prefixLift 4223026
  have htrace : WordTrace (prefixWord ++ tailWord_4223026) baseStart_4223026 baseEnd_4223026 := by
    simpa [prefixWord, tailWord_4223026, baseEnd_4223026] using wordTrace_append hprefix tailTrace_4223026
  have hstable : (prefixWord ++ tailWord_4223026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223026).length < 2 ^ (prefixWord ++ tailWord_4223026).sum := by decide
  have hdescent : baseEnd_4223026 < baseStart_4223026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223029 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_4223029 : Nat := 118140960795 + 4223029 * 2 ^ 59
def prefixEnd_4223029 : Nat := 4983230072969 + 3 ^ 40 * 4223029 * 2
def baseEnd_4223029 : Nat := 2168443694876063113316149

theorem tailTrace_4223029 : CollatzResearch.WordTrace tailWord_4223029 prefixEnd_4223029 2168443694876063113316149 := by
  unfold tailWord_4223029
  simp only [CollatzResearch.WordTrace]
  refine ⟨154026521417694643777784141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102684347611796429185189427 154026521417694643777784141)
  ·
    refine ⟨57759945531635491416669053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154026521417694643777784141 57759945531635491416669053)
    ·
      refine ⟨21659979574363309281250895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57759945531635491416669053 21659979574363309281250895)
      ·
        refine ⟨32489969361544963921876343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21659979574363309281250895 32489969361544963921876343)
        ·
          refine ⟨48734954042317445882814515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32489969361544963921876343 48734954042317445882814515)
          ·
            refine ⟨73102431063476168824221773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48734954042317445882814515 73102431063476168824221773)
            ·
              refine ⟨27413411648803563309083165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73102431063476168824221773 27413411648803563309083165)
              ·
                refine ⟨10280029368301336240906187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27413411648803563309083165 10280029368301336240906187)
                ·
                  refine ⟨15420044052452004361359281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10280029368301336240906187 15420044052452004361359281)
                  ·
                    refine ⟨11565033039339003271019461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15420044052452004361359281 11565033039339003271019461)
                    ·
                      refine ⟨2168443694876063113316149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11565033039339003271019461 2168443694876063113316149)
                      ·
                        rfl

theorem cell23_4223029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_4223029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223029 prefixEnd_4223029 := by exact prefixLift 4223029
  have htrace : WordTrace (prefixWord ++ tailWord_4223029) baseStart_4223029 baseEnd_4223029 := by
    simpa [prefixWord, tailWord_4223029, baseEnd_4223029] using wordTrace_append hprefix tailTrace_4223029
  have hstable : (prefixWord ++ tailWord_4223029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223029).length < 2 ^ (prefixWord ++ tailWord_4223029).sum := by decide
  have hdescent : baseEnd_4223029 < baseStart_4223029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223036 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_4223036 : Nat := 118140960795 + 4223036 * 2 ^ 59
def prefixEnd_4223036 : Nat := 4983230072969 + 3 ^ 40 * 4223036 * 2
def baseEnd_4223036 : Nat := 2168447289240644585928617

theorem tailTrace_4223036 : CollatzResearch.WordTrace tailWord_4223036 prefixEnd_4223036 2168447289240644585928617 := by
  unfold tailWord_4223036
  simp only [CollatzResearch.WordTrace]
  refine ⟨77013388364334641986644481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102684517819112855982192641 77013388364334641986644481)
  ·
    refine ⟨57760041273250981489983361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77013388364334641986644481 57760041273250981489983361)
    ·
      refine ⟨43320030954938236117487521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57760041273250981489983361 43320030954938236117487521)
      ·
        refine ⟨32490023216203677088115641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43320030954938236117487521 32490023216203677088115641)
        ·
          refine ⟨24367517412152757816086731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32490023216203677088115641 24367517412152757816086731)
          ·
            refine ⟨36551276118229136724130097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24367517412152757816086731 36551276118229136724130097)
            ·
              refine ⟨27413457088671852543097573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36551276118229136724130097 27413457088671852543097573)
              ·
                refine ⟨5140023204125972351830795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27413457088671852543097573 5140023204125972351830795)
                ·
                  refine ⟨7710034806188958527746193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5140023204125972351830795 7710034806188958527746193)
                  ·
                    refine ⟨5782526104641718895809645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7710034806188958527746193 5782526104641718895809645)
                    ·
                      refine ⟨2168447289240644585928617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782526104641718895809645 2168447289240644585928617)
                      ·
                        rfl

theorem cell23_4223036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_4223036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223036 prefixEnd_4223036 := by exact prefixLift 4223036
  have htrace : WordTrace (prefixWord ++ tailWord_4223036) baseStart_4223036 baseEnd_4223036 := by
    simpa [prefixWord, tailWord_4223036, baseEnd_4223036] using wordTrace_append hprefix tailTrace_4223036
  have hstable : (prefixWord ++ tailWord_4223036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223036).length < 2 ^ (prefixWord ++ tailWord_4223036).sum := by decide
  have hdescent : baseEnd_4223036 < baseStart_4223036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223049 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 3]
def baseStart_4223049 : Nat := 118140960795 + 4223049 * 2 ^ 59
def prefixEnd_4223049 : Nat := 4983230072969 + 3 ^ 40 * 4223049 * 2
def baseEnd_4223049 : Nat := 2168453964489153035066057

theorem tailTrace_4223049 : CollatzResearch.WordTrace tailWord_4223049 prefixEnd_4223049 2168453964489153035066057 := by
  unfold tailWord_4223049
  simp only [CollatzResearch.WordTrace]
  refine ⟨154027250877622187193512201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102684833918414791462341467 154027250877622187193512201)
  ·
    refine ⟨115520438158216640395134151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154027250877622187193512201 115520438158216640395134151)
    ·
      refine ⟨173280657237324960592701227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115520438158216640395134151 173280657237324960592701227)
      ·
        refine ⟨259920985855987440889051841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173280657237324960592701227 259920985855987440889051841)
        ·
          refine ⟨194940739391990580666788881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259920985855987440889051841 194940739391990580666788881)
          ·
            refine ⟨146205554543992935500091661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194940739391990580666788881 146205554543992935500091661)
            ·
              refine ⟨54827082953997350812534373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146205554543992935500091661 54827082953997350812534373)
              ·
                refine ⟨10280078053874503277350195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54827082953997350812534373 10280078053874503277350195)
                ·
                  refine ⟨15420117080811754916025293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10280078053874503277350195 15420117080811754916025293)
                  ·
                    refine ⟨5782543905304408093509485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15420117080811754916025293 5782543905304408093509485)
                    ·
                      refine ⟨2168453964489153035066057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782543905304408093509485 2168453964489153035066057)
                      ·
                        rfl

theorem cell23_4223049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_4223049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223049 prefixEnd_4223049 := by exact prefixLift 4223049
  have htrace : WordTrace (prefixWord ++ tailWord_4223049) baseStart_4223049 baseEnd_4223049 := by
    simpa [prefixWord, tailWord_4223049, baseEnd_4223049] using wordTrace_append hprefix tailTrace_4223049
  have hstable : (prefixWord ++ tailWord_4223049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223049).length < 2 ^ (prefixWord ++ tailWord_4223049).sum := by decide
  have hdescent : baseEnd_4223049 < baseStart_4223049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223053 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_4223053 : Nat := 118140960795 + 4223053 * 2 ^ 59
def prefixEnd_4223053 : Nat := 4983230072969 + 3 ^ 40 * 4223053 * 2
def baseEnd_4223053 : Nat := 2168456018411771019416039

theorem tailTrace_4223053 : CollatzResearch.WordTrace tailWord_4223053 prefixEnd_4223053 2168456018411771019416039 := by
  unfold tailWord_4223053
  simp only [CollatzResearch.WordTrace]
  refine ⟨154027396769607695876657813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102684931179738463917771875 154027396769607695876657813)
  ·
    refine ⟨7220034223575360744218335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154027396769607695876657813 7220034223575360744218335)
    ·
      refine ⟨10830051335363041116327503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7220034223575360744218335 10830051335363041116327503)
      ·
        refine ⟨16245077003044561674491255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10830051335363041116327503 16245077003044561674491255)
        ·
          refine ⟨24367615504566842511736883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16245077003044561674491255 24367615504566842511736883)
          ·
            refine ⟨36551423256850263767605325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24367615504566842511736883 36551423256850263767605325)
            ·
              refine ⟨13706783721318848912851997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36551423256850263767605325 13706783721318848912851997)
              ·
                refine ⟨5140043895494568342319499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13706783721318848912851997 5140043895494568342319499)
                ·
                  refine ⟨7710065843241852513479249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5140043895494568342319499 7710065843241852513479249)
                  ·
                    refine ⟨5782549382431389385109437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7710065843241852513479249 5782549382431389385109437)
                    ·
                      refine ⟨2168456018411771019416039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782549382431389385109437 2168456018411771019416039)
                      ·
                        rfl

theorem cell23_4223053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_4223053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223053 prefixEnd_4223053 := by exact prefixLift 4223053
  have htrace : WordTrace (prefixWord ++ tailWord_4223053) baseStart_4223053 baseEnd_4223053 := by
    simpa [prefixWord, tailWord_4223053, baseEnd_4223053] using wordTrace_append hprefix tailTrace_4223053
  have hstable : (prefixWord ++ tailWord_4223053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223053).length < 2 ^ (prefixWord ++ tailWord_4223053).sum := by decide
  have hdescent : baseEnd_4223053 < baseStart_4223053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223059 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 9, 2]
def baseStart_4223059 : Nat := 118140960795 + 4223059 * 2 ^ 59
def prefixEnd_4223059 : Nat := 4983230072969 + 3 ^ 40 * 4223059 * 2
def baseEnd_4223059 : Nat := 2168459099295697995941011

theorem tailTrace_4223059 : CollatzResearch.WordTrace tailWord_4223059 prefixEnd_4223059 2168459099295697995941011 := by
  unfold tailWord_4223059
  simp only [CollatzResearch.WordTrace]
  refine ⟨154027615607585958901376231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102685077071723972600917487 154027615607585958901376231)
  ·
    refine ⟨231041423411378938352064347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154027615607585958901376231 231041423411378938352064347)
    ·
      refine ⟨346562135117068407528096521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231041423411378938352064347 346562135117068407528096521)
      ·
        refine ⟨259921601337801305646072391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346562135117068407528096521 259921601337801305646072391)
        ·
          refine ⟨389882402006701958469108587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259921601337801305646072391 389882402006701958469108587)
          ·
            refine ⟨584823603010052937703662881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389882402006701958469108587 584823603010052937703662881)
            ·
              refine ⟨438617702257539703277747161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584823603010052937703662881 438617702257539703277747161)
              ·
                refine ⟨328963276693154777458310371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438617702257539703277747161 328963276693154777458310371)
                ·
                  refine ⟨493444915039732166187465557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328963276693154777458310371 493444915039732166187465557)
                  ·
                    refine ⟨2891278799060930661254681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 493444915039732166187465557 2891278799060930661254681)
                    ·
                      refine ⟨2168459099295697995941011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891278799060930661254681 2168459099295697995941011)
                      ·
                        rfl

theorem cell23_4223059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9, 2].length) (baseStart_4223059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223059 prefixEnd_4223059 := by exact prefixLift 4223059
  have htrace : WordTrace (prefixWord ++ tailWord_4223059) baseStart_4223059 baseEnd_4223059 := by
    simpa [prefixWord, tailWord_4223059, baseEnd_4223059] using wordTrace_append hprefix tailTrace_4223059
  have hstable : (prefixWord ++ tailWord_4223059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223059).length < 2 ^ (prefixWord ++ tailWord_4223059).sum := by decide
  have hdescent : baseEnd_4223059 < baseStart_4223059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223066 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_4223066 : Nat := 118140960795 + 4223066 * 2 ^ 59
def prefixEnd_4223066 : Nat := 4983230072969 + 3 ^ 40 * 4223066 * 2
def baseEnd_4223066 : Nat := 2168462693660279468553479

theorem tailTrace_4223066 : CollatzResearch.WordTrace tailWord_4223066 prefixEnd_4223066 2168462693660279468553479 := by
  unfold tailWord_4223066
  simp only [CollatzResearch.WordTrace]
  refine ⟨38506967729640149774220263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102685247279040399397920701 38506967729640149774220263)
  ·
    refine ⟨57760451594460224661330395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38506967729640149774220263 57760451594460224661330395)
    ·
      refine ⟨86640677391690336991995593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57760451594460224661330395 86640677391690336991995593)
      ·
        refine ⟨64980508043767752743996695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86640677391690336991995593 64980508043767752743996695)
        ·
          refine ⟨97470762065651629115995043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64980508043767752743996695 97470762065651629115995043)
          ·
            refine ⟨146206143098477443673992565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97470762065651629115995043 146206143098477443673992565)
            ·
              refine ⟨13706825915482260344436803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146206143098477443673992565 13706825915482260344436803)
              ·
                refine ⟨20560238873223390516655205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13706825915482260344436803 20560238873223390516655205)
                ·
                  refine ⟨3855044788729385721872851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20560238873223390516655205 3855044788729385721872851)
                  ·
                    refine ⟨5782567183094078582809277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3855044788729385721872851 5782567183094078582809277)
                    ·
                      refine ⟨2168462693660279468553479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782567183094078582809277 2168462693660279468553479)
                      ·
                        rfl

theorem cell23_4223066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_4223066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223066 prefixEnd_4223066 := by exact prefixLift 4223066
  have htrace : WordTrace (prefixWord ++ tailWord_4223066) baseStart_4223066 baseEnd_4223066 := by
    simpa [prefixWord, tailWord_4223066, baseEnd_4223066] using wordTrace_append hprefix tailTrace_4223066
  have hstable : (prefixWord ++ tailWord_4223066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223066).length < 2 ^ (prefixWord ++ tailWord_4223066).sum := by decide
  have hdescent : baseEnd_4223066 < baseStart_4223066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223070 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4223070 : Nat := 118140960795 + 4223070 * 2 ^ 59
def prefixEnd_4223070 : Nat := 4983230072969 + 3 ^ 40 * 4223070 * 2
def baseEnd_4223070 : Nat := 2168464747582897452903461

theorem tailTrace_4223070 : CollatzResearch.WordTrace tailWord_4223070 prefixEnd_4223070 2168464747582897452903461 := by
  unfold tailWord_4223070
  simp only [CollatzResearch.WordTrace]
  refine ⟨19253502101318263472503333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102685344540364071853351109 19253502101318263472503333)
  ·
    refine ⟨3610031643997174401094375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19253502101318263472503333 3610031643997174401094375)
    ·
      refine ⟨5415047465995761601641563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610031643997174401094375 5415047465995761601641563)
      ·
        refine ⟨8122571198993642402462345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5415047465995761601641563 8122571198993642402462345)
        ·
          refine ⟨6091928399245231801846759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8122571198993642402462345 6091928399245231801846759)
          ·
            refine ⟨9137892598867847702770139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091928399245231801846759 9137892598867847702770139)
            ·
              refine ⟨13706838898301771554155209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9137892598867847702770139 13706838898301771554155209)
              ·
                refine ⟨10280129173726328665616407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13706838898301771554155209 10280129173726328665616407)
                ·
                  refine ⟨15420193760589492998424611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10280129173726328665616407 15420193760589492998424611)
                  ·
                    refine ⟨23130290640884239497636917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15420193760589492998424611 23130290640884239497636917)
                    ·
                      refine ⟨2168464747582897452903461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23130290640884239497636917 2168464747582897452903461)
                      ·
                        rfl

theorem cell23_4223070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4223070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223070 prefixEnd_4223070 := by exact prefixLift 4223070
  have htrace : WordTrace (prefixWord ++ tailWord_4223070) baseStart_4223070 baseEnd_4223070 := by
    simpa [prefixWord, tailWord_4223070, baseEnd_4223070] using wordTrace_append hprefix tailTrace_4223070
  have hstable : (prefixWord ++ tailWord_4223070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223070).length < 2 ^ (prefixWord ++ tailWord_4223070).sum := by decide
  have hdescent : baseEnd_4223070 < baseStart_4223070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223076 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_4223076 : Nat := 118140960795 + 4223076 * 2 ^ 59
def prefixEnd_4223076 : Nat := 4983230072969 + 3 ^ 40 * 4223076 * 2
def baseEnd_4223076 : Nat := 2168467828466824429428433

theorem tailTrace_4223076 : CollatzResearch.WordTrace tailWord_4223076 prefixEnd_4223076 2168467828466824429428433 := by
  unfold tailWord_4223076
  simp only [CollatzResearch.WordTrace]
  refine ⟨77014117824262185402372541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102685490432349580536496721 77014117824262185402372541)
  ·
    refine ⟨28880294184098319525889703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77014117824262185402372541 28880294184098319525889703)
    ·
      refine ⟨43320441276147479288834555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28880294184098319525889703 43320441276147479288834555)
      ·
        refine ⟨64980661914221218933251833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43320441276147479288834555 64980661914221218933251833)
        ·
          refine ⟨48735496435665914199938875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64980661914221218933251833 48735496435665914199938875)
          ·
            refine ⟨73103244653498871299908313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48735496435665914199938875 73103244653498871299908313)
            ·
              refine ⟨54827433490124153474931235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73103244653498871299908313 54827433490124153474931235)
              ·
                refine ⟨82241150235186230212396853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54827433490124153474931235 82241150235186230212396853)
                ·
                  refine ⟨7710107834548709082412205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82241150235186230212396853 7710107834548709082412205)
                  ·
                    refine ⟨2891290437955765905904577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7710107834548709082412205 2891290437955765905904577)
                    ·
                      refine ⟨2168467828466824429428433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891290437955765905904577 2168467828466824429428433)
                      ·
                        rfl

theorem cell23_4223076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_4223076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223076 prefixEnd_4223076 := by exact prefixLift 4223076
  have htrace : WordTrace (prefixWord ++ tailWord_4223076) baseStart_4223076 baseEnd_4223076 := by
    simpa [prefixWord, tailWord_4223076, baseEnd_4223076] using wordTrace_append hprefix tailTrace_4223076
  have hstable : (prefixWord ++ tailWord_4223076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223076).length < 2 ^ (prefixWord ++ tailWord_4223076).sum := by decide
  have hdescent : baseEnd_4223076 < baseStart_4223076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223109 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_4223109 : Nat := 118140960795 + 4223109 * 2 ^ 59
def prefixEnd_4223109 : Nat := 4983230072969 + 3 ^ 40 * 4223109 * 2
def baseEnd_4223109 : Nat := 2168484773328422800315781

theorem tailTrace_4223109 : CollatzResearch.WordTrace tailWord_4223109 prefixEnd_4223109 2168484773328422800315781 := by
  unfold tailWord_4223109
  simp only [CollatzResearch.WordTrace]
  refine ⟨154029439257404817440696381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102686292838269878293797587 154029439257404817440696381)
  ·
    refine ⟨57761039721526806540261143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154029439257404817440696381 57761039721526806540261143)
    ·
      refine ⟨86641559582290209810391715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57761039721526806540261143 86641559582290209810391715)
      ·
        refine ⟨129962339373435314715587573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86641559582290209810391715 129962339373435314715587573)
        ·
          refine ⟨12183969316259560754586335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129962339373435314715587573 12183969316259560754586335)
          ·
            refine ⟨18275953974389341131879503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12183969316259560754586335 18275953974389341131879503)
            ·
              refine ⟨27413930961584011697819255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18275953974389341131879503 27413930961584011697819255)
              ·
                refine ⟨41120896442376017546728883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27413930961584011697819255 41120896442376017546728883)
                ·
                  refine ⟨61681344663564026320093325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41120896442376017546728883 61681344663564026320093325)
                  ·
                    refine ⟨23130504248836509870034997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61681344663564026320093325 23130504248836509870034997)
                    ·
                      refine ⟨2168484773328422800315781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23130504248836509870034997 2168484773328422800315781)
                      ·
                        rfl

theorem cell23_4223109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_4223109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223109 prefixEnd_4223109 := by exact prefixLift 4223109
  have htrace : WordTrace (prefixWord ++ tailWord_4223109) baseStart_4223109 baseEnd_4223109 := by
    simpa [prefixWord, tailWord_4223109, baseEnd_4223109] using wordTrace_append hprefix tailTrace_4223109
  have hstable : (prefixWord ++ tailWord_4223109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223109).length < 2 ^ (prefixWord ++ tailWord_4223109).sum := by decide
  have hdescent : baseEnd_4223109 < baseStart_4223109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223123 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 2, 2, 2]
def baseStart_4223123 : Nat := 118140960795 + 4223123 * 2 ^ 59
def prefixEnd_4223123 : Nat := 4983230072969 + 3 ^ 40 * 4223123 * 2
def baseEnd_4223123 : Nat := 2168491962057585745540717

theorem tailTrace_4223123 : CollatzResearch.WordTrace tailWord_4223123 prefixEnd_4223123 2168491962057585745540717 := by
  unfold tailWord_4223123
  simp only [CollatzResearch.WordTrace]
  refine ⟨154029949879354097831706023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102686633252902731887804015 154029949879354097831706023)
  ·
    refine ⟨231044924819031146747559035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154029949879354097831706023 231044924819031146747559035)
    ·
      refine ⟨346567387228546720121338553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231044924819031146747559035 346567387228546720121338553)
      ·
        refine ⟨259925540421410040091003915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346567387228546720121338553 259925540421410040091003915)
        ·
          refine ⟨389888310632115060136505873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259925540421410040091003915 389888310632115060136505873)
          ·
            refine ⟨292416232974086295102379405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389888310632115060136505873 292416232974086295102379405)
            ·
              refine ⟨109656087365282360663392277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292416232974086295102379405 109656087365282360663392277)
              ·
                refine ⟨5140129095247610656096513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109656087365282360663392277 5140129095247610656096513)
                ·
                  refine ⟨3855096821435707992072385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5140129095247610656096513 3855096821435707992072385)
                  ·
                    refine ⟨2891322616076780994054289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3855096821435707992072385 2891322616076780994054289)
                    ·
                      refine ⟨2168491962057585745540717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891322616076780994054289 2168491962057585745540717)
                      ·
                        rfl

theorem cell23_4223123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 2, 2].length) (baseStart_4223123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223123 prefixEnd_4223123 := by exact prefixLift 4223123
  have htrace : WordTrace (prefixWord ++ tailWord_4223123) baseStart_4223123 baseEnd_4223123 := by
    simpa [prefixWord, tailWord_4223123, baseEnd_4223123] using wordTrace_append hprefix tailTrace_4223123
  have hstable : (prefixWord ++ tailWord_4223123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223123).length < 2 ^ (prefixWord ++ tailWord_4223123).sum := by decide
  have hdescent : baseEnd_4223123 < baseStart_4223123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223134 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_4223134 : Nat := 118140960795 + 4223134 * 2 ^ 59
def prefixEnd_4223134 : Nat := 4983230072969 + 3 ^ 40 * 4223134 * 2
def baseEnd_4223134 : Nat := 2168497610344785202503167

theorem tailTrace_4223134 : CollatzResearch.WordTrace tailWord_4223134 prefixEnd_4223134 2168497610344785202503167 := by
  unfold tailWord_4223134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19253793885289280838794557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102686900721542831140237637 19253793885289280838794557)
  ·
    refine ⟨7220172706983480314547959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19253793885289280838794557 7220172706983480314547959)
    ·
      refine ⟨10830259060475220471821939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7220172706983480314547959 10830259060475220471821939)
      ·
        refine ⟨16245388590712830707732909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10830259060475220471821939 16245388590712830707732909)
        ·
          refine ⟨6092020721517311515399841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16245388590712830707732909 6092020721517311515399841)
          ·
            refine ⟨4569015541137983636549881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6092020721517311515399841 4569015541137983636549881)
            ·
              refine ⟨3426761655853487727412411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4569015541137983636549881 3426761655853487727412411)
              ·
                refine ⟨5140142483780231591118617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3426761655853487727412411 5140142483780231591118617)
                ·
                  refine ⟨3855106862835173693338963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5140142483780231591118617 3855106862835173693338963)
                  ·
                    refine ⟨5782660294252760540008445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3855106862835173693338963 5782660294252760540008445)
                    ·
                      refine ⟨2168497610344785202503167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782660294252760540008445 2168497610344785202503167)
                      ·
                        rfl

theorem cell23_4223134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_4223134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223134 prefixEnd_4223134 := by exact prefixLift 4223134
  have htrace : WordTrace (prefixWord ++ tailWord_4223134) baseStart_4223134 baseEnd_4223134 := by
    simpa [prefixWord, tailWord_4223134, baseEnd_4223134] using wordTrace_append hprefix tailTrace_4223134
  have hstable : (prefixWord ++ tailWord_4223134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223134).length < 2 ^ (prefixWord ++ tailWord_4223134).sum := by decide
  have hdescent : baseEnd_4223134 < baseStart_4223134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223180 : List Nat := [2, 2, 1, 6, 1, 1, 1, 4, 5]
def baseStart_4223180 : Nat := 118140960795 + 4223180 * 2 ^ 59
def prefixEnd_4223180 : Nat := 4983230072969 + 3 ^ 40 * 4223180 * 2
def baseEnd_4223180 : Nat := 240946803383876891391995

theorem tailTrace_4223180 : CollatzResearch.WordTrace tailWord_4223180 prefixEnd_4223180 240946803383876891391995 := by
  unfold tailWord_4223180
  simp only [CollatzResearch.WordTrace]
  refine ⟨77016014420073798283265497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102688019226765064377687329 77016014420073798283265497)
  ·
    refine ⟨57762010815055348712449123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77016014420073798283265497 57762010815055348712449123)
    ·
      refine ⟨86643016222583023068673685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57762010815055348712449123 86643016222583023068673685)
      ·
        refine ⟨4061391385433579206344079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86643016222583023068673685 4061391385433579206344079)
        ·
          refine ⟨6092087078150368809516119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061391385433579206344079 6092087078150368809516119)
          ·
            refine ⟨9138130617225553214274179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092087078150368809516119 9138130617225553214274179)
            ·
              refine ⟨13707195925838329821411269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138130617225553214274179 13707195925838329821411269)
              ·
                refine ⟨2570099236094686841514613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13707195925838329821411269 2570099236094686841514613)
                ·
                  refine ⟨240946803383876891391995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2570099236094686841514613 240946803383876891391995)
                  ·
                    rfl

theorem cell23_4223180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_4223180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223180 prefixEnd_4223180 := by exact prefixLift 4223180
  have htrace : WordTrace (prefixWord ++ tailWord_4223180) baseStart_4223180 baseEnd_4223180 := by
    simpa [prefixWord, tailWord_4223180, baseEnd_4223180] using wordTrace_append hprefix tailTrace_4223180
  have hstable : (prefixWord ++ tailWord_4223180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223180).length < 2 ^ (prefixWord ++ tailWord_4223180).sum := by decide
  have hdescent : baseEnd_4223180 < baseStart_4223180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223186 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4223186 : Nat := 118140960795 + 4223186 * 2 ^ 59
def prefixEnd_4223186 : Nat := 4983230072969 + 3 ^ 40 * 4223186 * 2
def baseEnd_4223186 : Nat := 2168524311338818999052927

theorem tailTrace_4223186 : CollatzResearch.WordTrace tailWord_4223186 prefixEnd_4223186 2168524311338818999052927 := by
  unfold tailWord_4223186
  simp only [CollatzResearch.WordTrace]
  refine ⟨38508061919531464897812353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102688165118750573060832941 38508061919531464897812353)
  ·
    refine ⟨28881046439648598673359265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38508061919531464897812353 28881046439648598673359265)
    ·
      refine ⟨21660784829736449005019449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28881046439648598673359265 21660784829736449005019449)
      ·
        refine ⟨16245588622302336753764587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21660784829736449005019449 16245588622302336753764587)
        ·
          refine ⟨24368382933453505130646881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16245588622302336753764587 24368382933453505130646881)
          ·
            refine ⟨18276287200090128847985161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24368382933453505130646881 18276287200090128847985161)
            ·
              refine ⟨13707215400067596635988871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18276287200090128847985161 13707215400067596635988871)
              ·
                refine ⟨20560823100101394953983307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13707215400067596635988871 20560823100101394953983307)
                ·
                  refine ⟨30841234650152092430974961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20560823100101394953983307 30841234650152092430974961)
                  ·
                    refine ⟨23130925987614069323231221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30841234650152092430974961 23130925987614069323231221)
                    ·
                      refine ⟨2168524311338818999052927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23130925987614069323231221 2168524311338818999052927)
                      ·
                        rfl

theorem cell23_4223186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4223186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223186 prefixEnd_4223186 := by exact prefixLift 4223186
  have htrace : WordTrace (prefixWord ++ tailWord_4223186) baseStart_4223186 baseEnd_4223186 := by
    simpa [prefixWord, tailWord_4223186, baseEnd_4223186] using wordTrace_append hprefix tailTrace_4223186
  have hstable : (prefixWord ++ tailWord_4223186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223186).length < 2 ^ (prefixWord ++ tailWord_4223186).sum := by decide
  have hdescent : baseEnd_4223186 < baseStart_4223186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223190 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4223190 : Nat := 118140960795 + 4223190 * 2 ^ 59
def prefixEnd_4223190 : Nat := 4983230072969 + 3 ^ 40 * 4223190 * 2
def baseEnd_4223190 : Nat := 2168526365261436983402909

theorem tailTrace_4223190 : CollatzResearch.WordTrace tailWord_4223190 prefixEnd_4223190 2168526365261436983402909 := by
  unfold tailWord_4223190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9627024598131960517149689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102688262380074245516263349 9627024598131960517149689)
  ·
    refine ⟨7220268448598970387862267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9627024598131960517149689 7220268448598970387862267)
    ·
      refine ⟨10830402672898455581793401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7220268448598970387862267 10830402672898455581793401)
      ·
        refine ⟨8122802004673841686345051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10830402672898455581793401 8122802004673841686345051)
        ·
          refine ⟨12184203007010762529517577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8122802004673841686345051 12184203007010762529517577)
          ·
            refine ⟨9138152255258071897138183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12184203007010762529517577 9138152255258071897138183)
            ·
              refine ⟨13707228382887107845707275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138152255258071897138183 13707228382887107845707275)
              ·
                refine ⟨20560842574330661768560913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13707228382887107845707275 20560842574330661768560913)
                ·
                  refine ⟨15420631930747996326420685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20560842574330661768560913 15420631930747996326420685)
                  ·
                    refine ⟨5782736974030498622407757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15420631930747996326420685 5782736974030498622407757)
                    ·
                      refine ⟨2168526365261436983402909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782736974030498622407757 2168526365261436983402909)
                      ·
                        rfl

theorem cell23_4223190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4223190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223190 prefixEnd_4223190 := by exact prefixLift 4223190
  have htrace : WordTrace (prefixWord ++ tailWord_4223190) baseStart_4223190 baseEnd_4223190 := by
    simpa [prefixWord, tailWord_4223190, baseEnd_4223190] using wordTrace_append hprefix tailTrace_4223190
  have hstable : (prefixWord ++ tailWord_4223190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223190).length < 2 ^ (prefixWord ++ tailWord_4223190).sum := by decide
  have hdescent : baseEnd_4223190 < baseStart_4223190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223209 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_4223209 : Nat := 118140960795 + 4223209 * 2 ^ 59
def prefixEnd_4223209 : Nat := 4983230072969 + 3 ^ 40 * 4223209 * 2
def baseEnd_4223209 : Nat := 2168536121393872409065321

theorem tailTrace_4223209 : CollatzResearch.WordTrace tailWord_4223209 prefixEnd_4223209 2168536121393872409065321 := by
  unfold tailWord_4223209
  simp only [CollatzResearch.WordTrace]
  refine ⟨154033086557042534519336681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102688724371361689679557787 154033086557042534519336681)
  ·
    refine ⟨115524814917781900889502511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154033086557042534519336681 115524814917781900889502511)
    ·
      refine ⟨173287222376672851334253767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115524814917781900889502511 173287222376672851334253767)
      ·
        refine ⟨259930833565009277001380651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173287222376672851334253767 259930833565009277001380651)
        ·
          refine ⟨389896250347513915502070977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259930833565009277001380651 389896250347513915502070977)
          ·
            refine ⟨292422187760635436626553233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389896250347513915502070977 292422187760635436626553233)
            ·
              refine ⟨219316640820476577469914925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292422187760635436626553233 219316640820476577469914925)
              ·
                refine ⟨82243740307678716551218097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219316640820476577469914925 82243740307678716551218097)
                ·
                  refine ⟨61682805230759037413413573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82243740307678716551218097 61682805230759037413413573)
                  ·
                    refine ⟨11565525980767319515015045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61682805230759037413413573 11565525980767319515015045)
                    ·
                      refine ⟨2168536121393872409065321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11565525980767319515015045 2168536121393872409065321)
                      ·
                        rfl

theorem cell23_4223209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_4223209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223209 prefixEnd_4223209 := by exact prefixLift 4223209
  have htrace : WordTrace (prefixWord ++ tailWord_4223209) baseStart_4223209 baseEnd_4223209 := by
    simpa [prefixWord, tailWord_4223209, baseEnd_4223209] using wordTrace_append hprefix tailTrace_4223209
  have hstable : (prefixWord ++ tailWord_4223209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223209).length < 2 ^ (prefixWord ++ tailWord_4223209).sum := by decide
  have hdescent : baseEnd_4223209 < baseStart_4223209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223213 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4223213 : Nat := 118140960795 + 4223213 * 2 ^ 59
def prefixEnd_4223213 : Nat := 4983230072969 + 3 ^ 40 * 4223213 * 2
def baseEnd_4223213 : Nat := 2168538175316490393415303

theorem tailTrace_4223213 : CollatzResearch.WordTrace tailWord_4223213 prefixEnd_4223213 2168538175316490393415303 := by
  unfold tailWord_4223213
  simp only [CollatzResearch.WordTrace]
  refine ⟨154033232449028043202482293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102688821632685362134988195 154033232449028043202482293)
  ·
    refine ⟨14440615542096379050232715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154033232449028043202482293 14440615542096379050232715)
    ·
      refine ⟨21660923313144568575349073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14440615542096379050232715 21660923313144568575349073)
      ·
        refine ⟨16245692484858426431511805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21660923313144568575349073 16245692484858426431511805)
        ·
          refine ⟨6092134681821909911816927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16245692484858426431511805 6092134681821909911816927)
          ·
            refine ⟨9138202022732864867725391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092134681821909911816927 9138202022732864867725391)
            ·
              refine ⟨13707303034099297301588087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138202022732864867725391 13707303034099297301588087)
              ·
                refine ⟨20560954551148945952382131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13707303034099297301588087 20560954551148945952382131)
                ·
                  refine ⟨30841431826723418928573197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20560954551148945952382131 30841431826723418928573197)
                  ·
                    refine ⟨11565536935021282098214949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30841431826723418928573197 11565536935021282098214949)
                    ·
                      refine ⟨2168538175316490393415303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11565536935021282098214949 2168538175316490393415303)
                      ·
                        rfl

theorem cell23_4223213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4223213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223213 prefixEnd_4223213 := by exact prefixLift 4223213
  have htrace : WordTrace (prefixWord ++ tailWord_4223213) baseStart_4223213 baseEnd_4223213 := by
    simpa [prefixWord, tailWord_4223213, baseEnd_4223213] using wordTrace_append hprefix tailTrace_4223213
  have hstable : (prefixWord ++ tailWord_4223213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223213).length < 2 ^ (prefixWord ++ tailWord_4223213).sum := by decide
  have hdescent : baseEnd_4223213 < baseStart_4223213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223219 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 8]
def baseStart_4223219 : Nat := 118140960795 + 4223219 * 2 ^ 59
def prefixEnd_4223219 : Nat := 4983230072969 + 3 ^ 40 * 4223219 * 2
def baseEnd_4223219 : Nat := 240949028466713041104475

theorem tailTrace_4223219 : CollatzResearch.WordTrace tailWord_4223219 prefixEnd_4223219 240949028466713041104475 := by
  unfold tailWord_4223219
  simp only [CollatzResearch.WordTrace]
  refine ⟨154033451287006306227200711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102688967524670870818133807 154033451287006306227200711)
  ·
    refine ⟨231050176930509459340801067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154033451287006306227200711 231050176930509459340801067)
    ·
      refine ⟨346575265395764189011201601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231050176930509459340801067 346575265395764189011201601)
      ·
        refine ⟨259931449046823141758401201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346575265395764189011201601 259931449046823141758401201)
        ·
          refine ⟨194948586785117356318800901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259931449046823141758401201 194948586785117356318800901)
          ·
            refine ⟨36552860022209504309775169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194948586785117356318800901 36552860022209504309775169)
            ·
              refine ⟨27414645016657128232331377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36552860022209504309775169 27414645016657128232331377)
              ·
                refine ⟨20560983762492846174248533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27414645016657128232331377 20560983762492846174248533)
                ·
                  refine ⟨240949028466713041104475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20560983762492846174248533 240949028466713041104475)
                  ·
                    rfl

theorem cell23_4223219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 8].length) (baseStart_4223219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223219 prefixEnd_4223219 := by exact prefixLift 4223219
  have htrace : WordTrace (prefixWord ++ tailWord_4223219) baseStart_4223219 baseEnd_4223219 := by
    simpa [prefixWord, tailWord_4223219, baseEnd_4223219] using wordTrace_append hprefix tailTrace_4223219
  have hstable : (prefixWord ++ tailWord_4223219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223219).length < 2 ^ (prefixWord ++ tailWord_4223219).sum := by decide
  have hdescent : baseEnd_4223219 < baseStart_4223219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223240 : List Nat := [2, 1, 3, 2, 3, 1, 2, 4, 1, 4]
def baseStart_4223240 : Nat := 118140960795 + 4223240 * 2 ^ 59
def prefixEnd_4223240 : Nat := 4983230072969 + 3 ^ 40 * 4223240 * 2
def baseEnd_4223240 : Nat := 722850679764720595925893

theorem tailTrace_4223240 : CollatzResearch.WordTrace tailWord_4223240 prefixEnd_4223240 722850679764720595925893 := by
  unfold tailWord_4223240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77017108609965113406857587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102689478146620151209143449 77017108609965113406857587)
  ·
    refine ⟨115525662914947670110286381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77017108609965113406857587 115525662914947670110286381)
    ·
      refine ⟨43322123593105376291357393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115525662914947670110286381 43322123593105376291357393)
      ·
        refine ⟨32491592694829032218518045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43322123593105376291357393 32491592694829032218518045)
        ·
          refine ⟨12184347260560887081944267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32491592694829032218518045 12184347260560887081944267)
          ·
            refine ⟨18276520890841330622916401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12184347260560887081944267 18276520890841330622916401)
            ·
              refine ⟨13707390668130997967187301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18276520890841330622916401 13707390668130997967187301)
              ·
                refine ⟨2570135750274562118847619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13707390668130997967187301 2570135750274562118847619)
                ·
                  refine ⟨3855203625411843178271429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570135750274562118847619 3855203625411843178271429)
                  ·
                    refine ⟨722850679764720595925893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855203625411843178271429 722850679764720595925893)
                    ·
                      rfl

theorem cell23_4223240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_4223240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223240 prefixEnd_4223240 := by exact prefixLift 4223240
  have htrace : WordTrace (prefixWord ++ tailWord_4223240) baseStart_4223240 baseEnd_4223240 := by
    simpa [prefixWord, tailWord_4223240, baseEnd_4223240] using wordTrace_append hprefix tailTrace_4223240
  have hstable : (prefixWord ++ tailWord_4223240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223240).length < 2 ^ (prefixWord ++ tailWord_4223240).sum := by decide
  have hdescent : baseEnd_4223240 < baseStart_4223240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223259 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7]
def baseStart_4223259 : Nat := 118140960795 + 4223259 * 2 ^ 59
def prefixEnd_4223259 : Nat := 4983230072969 + 3 ^ 40 * 4223259 * 2
def baseEnd_4223259 : Nat := 2168561795426597213440091

theorem tailTrace_4223259 : CollatzResearch.WordTrace tailWord_4223259 prefixEnd_4223259 2168561795426597213440091 := by
  unfold tailWord_4223259
  simp only [CollatzResearch.WordTrace]
  refine ⟨154034910206861393058656831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102689940137907595372437887 154034910206861393058656831)
  ·
    refine ⟨231052365310292089587985247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154034910206861393058656831 231052365310292089587985247)
    ·
      refine ⟨346578547965438134381977871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231052365310292089587985247 346578547965438134381977871)
      ·
        refine ⟨519867821948157201572966807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346578547965438134381977871 519867821948157201572966807)
        ·
          refine ⟨779801732922235802359450211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519867821948157201572966807 779801732922235802359450211)
          ·
            refine ⟨1169702599383353703539175317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779801732922235802359450211 1169702599383353703539175317)
            ·
              refine ⟨54829809346094704853398843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1169702599383353703539175317 54829809346094704853398843)
              ·
                refine ⟨82244714019142057280098265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54829809346094704853398843 82244714019142057280098265)
                ·
                  refine ⟨61683535514356542960073699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82244714019142057280098265 61683535514356542960073699)
                  ·
                    refine ⟨92525303271534814440110549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61683535514356542960073699 92525303271534814440110549)
                    ·
                      refine ⟨2168561795426597213440091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92525303271534814440110549 2168561795426597213440091)
                      ·
                        rfl

theorem cell23_4223259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_4223259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223259 prefixEnd_4223259 := by exact prefixLift 4223259
  have htrace : WordTrace (prefixWord ++ tailWord_4223259) baseStart_4223259 baseEnd_4223259 := by
    simpa [prefixWord, tailWord_4223259, baseEnd_4223259] using wordTrace_append hprefix tailTrace_4223259
  have hstable : (prefixWord ++ tailWord_4223259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223259).length < 2 ^ (prefixWord ++ tailWord_4223259).sum := by decide
  have hdescent : baseEnd_4223259 < baseStart_4223259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223274 : List Nat := [3, 1, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_4223274 : Nat := 118140960795 + 4223274 * 2 ^ 59
def prefixEnd_4223274 : Nat := 4983230072969 + 3 ^ 40 * 4223274 * 2
def baseEnd_4223274 : Nat := 722856499212138218250841

theorem tailTrace_4223274 : CollatzResearch.WordTrace tailWord_4223274 prefixEnd_4223274 722856499212138218250841 := by
  unfold tailWord_4223274
  simp only [CollatzResearch.WordTrace]
  refine ⟨38508864325451762655113219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102690304867871367080301917 38508864325451762655113219)
  ·
    refine ⟨57763296488177643982669829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38508864325451762655113219 57763296488177643982669829)
    ·
      refine ⟨10830618091533308246750593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57763296488177643982669829 10830618091533308246750593)
      ·
        refine ⟨8122963568649981185062945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10830618091533308246750593 8122963568649981185062945)
        ·
          refine ⟨6092222676487485888797209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8122963568649981185062945 6092222676487485888797209)
          ·
            refine ⟨4569167007365614416597907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6092222676487485888797209 4569167007365614416597907)
            ·
              refine ⟨6853750511048421624896861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569167007365614416597907 6853750511048421624896861)
              ·
                refine ⟨2570156441643158109336323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6853750511048421624896861 2570156441643158109336323)
                ·
                  refine ⟨3855234662464737164004485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570156441643158109336323 3855234662464737164004485)
                  ·
                    refine ⟨722856499212138218250841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855234662464737164004485 722856499212138218250841)
                    ·
                      rfl

theorem cell23_4223274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_4223274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223274 prefixEnd_4223274 := by exact prefixLift 4223274
  have htrace : WordTrace (prefixWord ++ tailWord_4223274) baseStart_4223274 baseEnd_4223274 := by
    simpa [prefixWord, tailWord_4223274, baseEnd_4223274] using wordTrace_append hprefix tailTrace_4223274
  have hstable : (prefixWord ++ tailWord_4223274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223274).length < 2 ^ (prefixWord ++ tailWord_4223274).sum := by decide
  have hdescent : baseEnd_4223274 < baseStart_4223274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223280 : List Nat := [2, 1, 1, 1, 2, 2, 2, 7, 1, 1, 3]
def baseStart_4223280 : Nat := 118140960795 + 4223280 * 2 ^ 59
def prefixEnd_4223280 : Nat := 4983230072969 + 3 ^ 40 * 4223280 * 2
def baseEnd_4223280 : Nat := 2168572578520341631277495

theorem tailTrace_4223280 : CollatzResearch.WordTrace tailWord_4223280 prefixEnd_4223280 2168572578520341631277495 := by
  unfold tailWord_4223280
  simp only [CollatzResearch.WordTrace]
  refine ⟨77017838069892656822585647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102690450759856875763447529 77017838069892656822585647)
  ·
    refine ⟨115526757104838985233878471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77017838069892656822585647 115526757104838985233878471)
    ·
      refine ⟨173290135657258477850817707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115526757104838985233878471 173290135657258477850817707)
      ·
        refine ⟨259935203485887716776226561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173290135657258477850817707 259935203485887716776226561)
        ·
          refine ⟨194951402614415787582169921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259935203485887716776226561 194951402614415787582169921)
          ·
            refine ⟨146213551960811840686627441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194951402614415787582169921 146213551960811840686627441)
            ·
              refine ⟨109660163970608880514970581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146213551960811840686627441 109660163970608880514970581)
              ·
                refine ⟨2570160093061145637069623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109660163970608880514970581 2570160093061145637069623)
                ·
                  refine ⟨3855240139591718455604435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570160093061145637069623 3855240139591718455604435)
                  ·
                    refine ⟨5782860209387577683406653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3855240139591718455604435 5782860209387577683406653)
                    ·
                      refine ⟨2168572578520341631277495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782860209387577683406653 2168572578520341631277495)
                      ·
                        rfl

theorem cell23_4223280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 1, 3].length) (baseStart_4223280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223280 prefixEnd_4223280 := by exact prefixLift 4223280
  have htrace : WordTrace (prefixWord ++ tailWord_4223280) baseStart_4223280 baseEnd_4223280 := by
    simpa [prefixWord, tailWord_4223280, baseEnd_4223280] using wordTrace_append hprefix tailTrace_4223280
  have hstable : (prefixWord ++ tailWord_4223280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223280).length < 2 ^ (prefixWord ++ tailWord_4223280).sum := by decide
  have hdescent : baseEnd_4223280 < baseStart_4223280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223290 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2]
def baseStart_4223290 : Nat := 118140960795 + 4223290 * 2 ^ 59
def prefixEnd_4223290 : Nat := 4983230072969 + 3 ^ 40 * 4223290 * 2
def baseEnd_4223290 : Nat := 2168577713326886592152449

theorem tailTrace_4223290 : CollatzResearch.WordTrace tailWord_4223290 prefixEnd_4223290 2168577713326886592152449 := by
  unfold tailWord_4223290
  simp only [CollatzResearch.WordTrace]
  refine ⟨38509010217437271338258831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102690693913166056902023549 38509010217437271338258831)
  ·
    refine ⟨57763515326155907007388247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38509010217437271338258831 57763515326155907007388247)
    ·
      refine ⟨86645272989233860511082371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57763515326155907007388247 86645272989233860511082371)
      ·
        refine ⟨129967909483850790766623557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86645272989233860511082371 129967909483850790766623557)
        ·
          refine ⟨24368983028222023268741917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129967909483850790766623557 24368983028222023268741917)
          ·
            refine ⟨9138368635583258725778219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24368983028222023268741917 9138368635583258725778219)
            ·
              refine ⟨13707552953374888088667329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138368635583258725778219 13707552953374888088667329)
              ·
                refine ⟨10280664715031166066500497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13707552953374888088667329 10280664715031166066500497)
                ·
                  refine ⟨7710498536273374549875373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10280664715031166066500497 7710498536273374549875373)
                  ·
                    refine ⟨2891436951102515456203265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7710498536273374549875373 2891436951102515456203265)
                    ·
                      refine ⟨2168577713326886592152449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891436951102515456203265 2168577713326886592152449)
                      ·
                        rfl

theorem cell23_4223290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_4223290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223290 prefixEnd_4223290 := by exact prefixLift 4223290
  have htrace : WordTrace (prefixWord ++ tailWord_4223290) baseStart_4223290 baseEnd_4223290 := by
    simpa [prefixWord, tailWord_4223290, baseEnd_4223290] using wordTrace_append hprefix tailTrace_4223290
  have hstable : (prefixWord ++ tailWord_4223290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223290).length < 2 ^ (prefixWord ++ tailWord_4223290).sum := by decide
  have hdescent : baseEnd_4223290 < baseStart_4223290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223306 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_4223306 : Nat := 118140960795 + 4223306 * 2 ^ 59
def prefixEnd_4223306 : Nat := 4983230072969 + 3 ^ 40 * 4223306 * 2
def baseEnd_4223306 : Nat := 2168585929017358529552375

theorem tailTrace_4223306 : CollatzResearch.WordTrace tailWord_4223306 prefixEnd_4223306 2168585929017358529552375 := by
  unfold tailWord_4223306
  simp only [CollatzResearch.WordTrace]
  refine ⟨38509156109422780021404443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102691082958460746723745181 38509156109422780021404443)
  ·
    refine ⟨57763734164134170032106665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38509156109422780021404443 57763734164134170032106665)
    ·
      refine ⟨43322800623100627524079999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57763734164134170032106665 43322800623100627524079999)
      ·
        refine ⟨64984200934650941286119999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43322800623100627524079999 64984200934650941286119999)
        ·
          refine ⟨97476301401976411929179999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64984200934650941286119999 97476301401976411929179999)
          ·
            refine ⟨146214452102964617893769999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97476301401976411929179999 146214452102964617893769999)
            ·
              refine ⟨219321678154446926840654999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146214452102964617893769999 219321678154446926840654999)
              ·
                refine ⟨328982517231670390260982499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219321678154446926840654999 328982517231670390260982499)
                ·
                  refine ⟨493473775847505585391473749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328982517231670390260982499 493473775847505585391473749)
                  ·
                    refine ⟨5782895810712956078806333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 493473775847505585391473749 5782895810712956078806333)
                    ·
                      refine ⟨2168585929017358529552375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5782895810712956078806333 2168585929017358529552375)
                      ·
                        rfl

theorem cell23_4223306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_4223306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223306 prefixEnd_4223306 := by exact prefixLift 4223306
  have htrace : WordTrace (prefixWord ++ tailWord_4223306) baseStart_4223306 baseEnd_4223306 := by
    simpa [prefixWord, tailWord_4223306, baseEnd_4223306] using wordTrace_append hprefix tailTrace_4223306
  have hstable : (prefixWord ++ tailWord_4223306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223306).length < 2 ^ (prefixWord ++ tailWord_4223306).sum := by decide
  have hdescent : baseEnd_4223306 < baseStart_4223306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223317 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_4223317 : Nat := 118140960795 + 4223317 * 2 ^ 59
def prefixEnd_4223317 : Nat := 4983230072969 + 3 ^ 40 * 4223317 * 2
def baseEnd_4223317 : Nat := 722863859101519328838275

theorem tailTrace_4223317 : CollatzResearch.WordTrace tailWord_4223317 prefixEnd_4223317 722863859101519328838275 := by
  unfold tailWord_4223317
  simp only [CollatzResearch.WordTrace]
  refine ⟨154037025640651268964268205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102691350427100845976178803 154037025640651268964268205)
  ·
    refine ⟨57763884615244225861600577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154037025640651268964268205 57763884615244225861600577)
    ·
      refine ⟨43322913461433169396200433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57763884615244225861600577 43322913461433169396200433)
      ·
        refine ⟨32492185096074877047150325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43322913461433169396200433 32492185096074877047150325)
        ·
          refine ⟨3046142352757019723170343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32492185096074877047150325 3046142352757019723170343)
          ·
            refine ⟨4569213529135529584755515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046142352757019723170343 4569213529135529584755515)
            ·
              refine ⟨6853820293703294377133273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569213529135529584755515 6853820293703294377133273)
              ·
                refine ⟨5140365220277470782849955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6853820293703294377133273 5140365220277470782849955)
                ·
                  refine ⟨7710547830416206174274933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5140365220277470782849955 7710547830416206174274933)
                  ·
                    refine ⟨722863859101519328838275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7710547830416206174274933 722863859101519328838275)
                    ·
                      rfl

theorem cell23_4223317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_4223317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223317 prefixEnd_4223317 := by exact prefixLift 4223317
  have htrace : WordTrace (prefixWord ++ tailWord_4223317) baseStart_4223317 baseEnd_4223317 := by
    simpa [prefixWord, tailWord_4223317, baseEnd_4223317] using wordTrace_append hprefix tailTrace_4223317
  have hstable : (prefixWord ++ tailWord_4223317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223317).length < 2 ^ (prefixWord ++ tailWord_4223317).sum := by decide
  have hdescent : baseEnd_4223317 < baseStart_4223317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223324 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4223324 : Nat := 118140960795 + 4223324 * 2 ^ 59
def prefixEnd_4223324 : Nat := 4983230072969 + 3 ^ 40 * 4223324 * 2
def baseEnd_4223324 : Nat := 2168595171669139459127293

theorem tailTrace_4223324 : CollatzResearch.WordTrace tailWord_4223324 prefixEnd_4223324 2168595171669139459127293 := by
  unfold tailWord_4223324
  simp only [CollatzResearch.WordTrace]
  refine ⟨77018640475812954579886513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102691520634417272773182017 77018640475812954579886513)
  ·
    refine ⟨57763980356859715934914885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77018640475812954579886513 57763980356859715934914885)
    ·
      refine ⟨10830746316911196737796541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57763980356859715934914885 10830746316911196737796541)
      ·
        refine ⟨4061529868841698776673703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10830746316911196737796541 4061529868841698776673703)
        ·
          refine ⟨6092294803262548165010555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061529868841698776673703 6092294803262548165010555)
          ·
            refine ⟨9138442204893822247515833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092294803262548165010555 9138442204893822247515833)
            ·
              refine ⟨6853831653670366685636875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9138442204893822247515833 6853831653670366685636875)
              ·
                refine ⟨10280747480505550028455313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6853831653670366685636875 10280747480505550028455313)
                ·
                  refine ⟨7710560610379162521341485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10280747480505550028455313 7710560610379162521341485)
                  ·
                    refine ⟨2891460228892185945503057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7710560610379162521341485 2891460228892185945503057)
                    ·
                      refine ⟨2168595171669139459127293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891460228892185945503057 2168595171669139459127293)
                      ·
                        rfl

theorem cell23_4223324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4223324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223324 prefixEnd_4223324 := by exact prefixLift 4223324
  have htrace : WordTrace (prefixWord ++ tailWord_4223324) baseStart_4223324 baseEnd_4223324 := by
    simpa [prefixWord, tailWord_4223324, baseEnd_4223324] using wordTrace_append hprefix tailTrace_4223324
  have hstable : (prefixWord ++ tailWord_4223324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223324).length < 2 ^ (prefixWord ++ tailWord_4223324).sum := by decide
  have hdescent : baseEnd_4223324 < baseStart_4223324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223333 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4223333 : Nat := 118140960795 + 4223333 * 2 ^ 59
def prefixEnd_4223333 : Nat := 4983230072969 + 3 ^ 40 * 4223333 * 2
def baseEnd_4223333 : Nat := 2168599792995029923914751

theorem tailTrace_4223333 : CollatzResearch.WordTrace tailWord_4223333 prefixEnd_4223333 2168599792995029923914751 := by
  unfold tailWord_4223333
  simp only [CollatzResearch.WordTrace]
  refine ⟨154037609208593303696850653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102691739472395535797900435 154037609208593303696850653)
  ·
    refine ⟨57764103453222488886318995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154037609208593303696850653 57764103453222488886318995)
    ·
      refine ⟨86646155179833733329478493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57764103453222488886318995 86646155179833733329478493)
      ·
        refine ⟨32492308192437649998554435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86646155179833733329478493 32492308192437649998554435)
        ·
          refine ⟨48738462288656474997831653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32492308192437649998554435 48738462288656474997831653)
          ·
            refine ⟨9138461679123089062093435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48738462288656474997831653 9138461679123089062093435)
            ·
              refine ⟨13707692518684633593140153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138461679123089062093435 13707692518684633593140153)
              ·
                refine ⟨10280769389013475194855115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13707692518684633593140153 10280769389013475194855115)
                ·
                  refine ⟨15421154083520212792282673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10280769389013475194855115 15421154083520212792282673)
                  ·
                    refine ⟨11565865562640159594212005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15421154083520212792282673 11565865562640159594212005)
                    ·
                      refine ⟨2168599792995029923914751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11565865562640159594212005 2168599792995029923914751)
                      ·
                        rfl

theorem cell23_4223333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4223333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223333 prefixEnd_4223333 := by exact prefixLift 4223333
  have htrace : WordTrace (prefixWord ++ tailWord_4223333) baseStart_4223333 baseEnd_4223333 := by
    simpa [prefixWord, tailWord_4223333, baseEnd_4223333] using wordTrace_append hprefix tailTrace_4223333
  have hstable : (prefixWord ++ tailWord_4223333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223333).length < 2 ^ (prefixWord ++ tailWord_4223333).sum := by decide
  have hdescent : baseEnd_4223333 < baseStart_4223333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223337 : List Nat := [1, 2, 1, 1, 1, 3, 4, 5, 1, 2, 2]
def baseStart_4223337 : Nat := 118140960795 + 4223337 * 2 ^ 59
def prefixEnd_4223337 : Nat := 4983230072969 + 3 ^ 40 * 4223337 * 2
def baseEnd_4223337 : Nat := 2168601846917647908264733

theorem tailTrace_4223337 : CollatzResearch.WordTrace tailWord_4223337 prefixEnd_4223337 2168601846917647908264733 := by
  unfold tailWord_4223337
  simp only [CollatzResearch.WordTrace]
  refine ⟨154037755100578812379996265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102691836733719208253330843 154037755100578812379996265)
  ·
    refine ⟨115528316325434109284997199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154037755100578812379996265 115528316325434109284997199)
    ·
      refine ⟨173292474488151163927495799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115528316325434109284997199 173292474488151163927495799)
      ·
        refine ⟨259938711732226745891243699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173292474488151163927495799 259938711732226745891243699)
        ·
          refine ⟨389908067598340118836865549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259938711732226745891243699 389908067598340118836865549)
          ·
            refine ⟨146215525349377544563824581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389908067598340118836865549 146215525349377544563824581)
            ·
              refine ⟨27415411003008289605717109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146215525349377544563824581 27415411003008289605717109)
              ·
                refine ⟨2570194781532027150535979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27415411003008289605717109 2570194781532027150535979)
                ·
                  refine ⟨3855292172298040725803969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570194781532027150535979 3855292172298040725803969)
                  ·
                    refine ⟨2891469129223530544352977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3855292172298040725803969 2891469129223530544352977)
                    ·
                      refine ⟨2168601846917647908264733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891469129223530544352977 2168601846917647908264733)
                      ·
                        rfl

theorem cell23_4223337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 2, 2].length) (baseStart_4223337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223337 prefixEnd_4223337 := by exact prefixLift 4223337
  have htrace : WordTrace (prefixWord ++ tailWord_4223337) baseStart_4223337 baseEnd_4223337 := by
    simpa [prefixWord, tailWord_4223337, baseEnd_4223337] using wordTrace_append hprefix tailTrace_4223337
  have hstable : (prefixWord ++ tailWord_4223337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223337).length < 2 ^ (prefixWord ++ tailWord_4223337).sum := by decide
  have hdescent : baseEnd_4223337 < baseStart_4223337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223340 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_4223340 : Nat := 118140960795 + 4223340 * 2 ^ 59
def prefixEnd_4223340 : Nat := 4983230072969 + 3 ^ 40 * 4223340 * 2
def baseEnd_4223340 : Nat := 2168603387359611396527219

theorem tailTrace_4223340 : CollatzResearch.WordTrace tailWord_4223340 prefixEnd_4223340 2168603387359611396527219 := by
  unfold tailWord_4223340
  simp only [CollatzResearch.WordTrace]
  refine ⟨77018932259783971946177737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102691909679711962594903649 77018932259783971946177737)
  ·
    refine ⟨57764199194837978959633303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77018932259783971946177737 57764199194837978959633303)
    ·
      refine ⟨86646298792256968439449955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57764199194837978959633303 86646298792256968439449955)
      ·
        refine ⟨129969448188385452659174933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86646298792256968439449955 129969448188385452659174933)
        ·
          refine ⟨6092317883830568093398825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129969448188385452659174933 6092317883830568093398825)
          ·
            refine ⟨4569238412872926070049119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6092317883830568093398825 4569238412872926070049119)
            ·
              refine ⟨6853857619309389105073679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569238412872926070049119 6853857619309389105073679)
              ·
                refine ⟨10280786428964083657610519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6853857619309389105073679 10280786428964083657610519)
                ·
                  refine ⟨15421179643446125486415779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10280786428964083657610519 15421179643446125486415779)
                  ·
                    refine ⟨23131769465169188229623669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15421179643446125486415779 23131769465169188229623669)
                    ·
                      refine ⟨2168603387359611396527219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23131769465169188229623669 2168603387359611396527219)
                      ·
                        rfl

theorem cell23_4223340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_4223340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223340 prefixEnd_4223340 := by exact prefixLift 4223340
  have htrace : WordTrace (prefixWord ++ tailWord_4223340) baseStart_4223340 baseEnd_4223340 := by
    simpa [prefixWord, tailWord_4223340, baseEnd_4223340] using wordTrace_append hprefix tailTrace_4223340
  have hstable : (prefixWord ++ tailWord_4223340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223340).length < 2 ^ (prefixWord ++ tailWord_4223340).sum := by decide
  have hdescent : baseEnd_4223340 < baseStart_4223340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223473 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_4223473 : Nat := 118140960795 + 4223473 * 2 ^ 59
def prefixEnd_4223473 : Nat := 4983230072969 + 3 ^ 40 * 4223473 * 2
def baseEnd_4223473 : Nat := 2168671680286659376164107

theorem tailTrace_4223473 : CollatzResearch.WordTrace tailWord_4223473 prefixEnd_4223473 2168671680286659376164107 := by
  unfold tailWord_4223473
  simp only [CollatzResearch.WordTrace]
  refine ⟨154042715428086107606947073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102695143618724071737964715 154042715428086107606947073)
  ·
    refine ⟨115532036571064580705210305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154042715428086107606947073 115532036571064580705210305)
    ·
      refine ⟨86649027428298435528907729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115532036571064580705210305 86649027428298435528907729)
      ·
        refine ⟨64986770571223826646680797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86649027428298435528907729 64986770571223826646680797)
        ·
          refine ⟨24370038964208934992505299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64986770571223826646680797 24370038964208934992505299)
          ·
            refine ⟨36555058446313402488757949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24370038964208934992505299 36555058446313402488757949)
            ·
              refine ⟨13708146917367525933284231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36555058446313402488757949 13708146917367525933284231)
              ·
                refine ⟨20562220376051288899926347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13708146917367525933284231 20562220376051288899926347)
                ·
                  refine ⟨30843330564076933349889521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20562220376051288899926347 30843330564076933349889521)
                  ·
                    refine ⟨23132497923057700012417141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30843330564076933349889521 23132497923057700012417141)
                    ·
                      refine ⟨2168671680286659376164107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23132497923057700012417141 2168671680286659376164107)
                      ·
                        rfl

theorem cell23_4223473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_4223473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223473 prefixEnd_4223473 := by exact prefixLift 4223473
  have htrace : WordTrace (prefixWord ++ tailWord_4223473) baseStart_4223473 baseEnd_4223473 := by
    simpa [prefixWord, tailWord_4223473, baseEnd_4223473] using wordTrace_append hprefix tailTrace_4223473
  have hstable : (prefixWord ++ tailWord_4223473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223473).length < 2 ^ (prefixWord ++ tailWord_4223473).sum := by decide
  have hdescent : baseEnd_4223473 < baseStart_4223473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223500 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_4223500 : Nat := 118140960795 + 4223500 * 2 ^ 59
def prefixEnd_4223500 : Nat := 4983230072969 + 3 ^ 40 * 4223500 * 2
def baseEnd_4223500 : Nat := 2168685544264330770526483

theorem tailTrace_4223500 : CollatzResearch.WordTrace tailWord_4223500 prefixEnd_4223500 2168685544264330770526483 := by
  unfold tailWord_4223500
  simp only [CollatzResearch.WordTrace]
  refine ⟨77021850099494145609089977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102695800132658860812119969 77021850099494145609089977)
  ·
    refine ⟨57766387574620609206817483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77021850099494145609089977 57766387574620609206817483)
    ·
      refine ⟨86649581361930913810226225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57766387574620609206817483 86649581361930913810226225)
      ·
        refine ⟨64987186021448185357669669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86649581361930913810226225 64987186021448185357669669)
        ·
          refine ⟨12185097379021534754563063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64987186021448185357669669 12185097379021534754563063)
          ·
            refine ⟨18277646068532302131844595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12185097379021534754563063 18277646068532302131844595)
            ·
              refine ⟨27416469102798453197766893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18277646068532302131844595 27416469102798453197766893)
              ·
                refine ⟨10281175913549419949162585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27416469102798453197766893 10281175913549419949162585)
                ·
                  refine ⟨7710881935162064961871939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10281175913549419949162585 7710881935162064961871939)
                  ·
                    refine ⟨11566322902743097442807909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7710881935162064961871939 11566322902743097442807909)
                    ·
                      refine ⟨2168685544264330770526483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11566322902743097442807909 2168685544264330770526483)
                      ·
                        rfl

theorem cell23_4223500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_4223500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223500 prefixEnd_4223500 := by exact prefixLift 4223500
  have htrace : WordTrace (prefixWord ++ tailWord_4223500) baseStart_4223500 baseEnd_4223500 := by
    simpa [prefixWord, tailWord_4223500, baseEnd_4223500] using wordTrace_append hprefix tailTrace_4223500
  have hstable : (prefixWord ++ tailWord_4223500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223500).length < 2 ^ (prefixWord ++ tailWord_4223500).sum := by decide
  have hdescent : baseEnd_4223500 < baseStart_4223500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223534 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_4223534 : Nat := 118140960795 + 4223534 * 2 ^ 59
def prefixEnd_4223534 : Nat := 4983230072969 + 3 ^ 40 * 4223534 * 2
def baseEnd_4223534 : Nat := 2168703002606583637501327

theorem tailTrace_4223534 : CollatzResearch.WordTrace tailWord_4223534 prefixEnd_4223534 2168703002606583637501327 := by
  unfold tailWord_4223534
  simp only [CollatzResearch.WordTrace]
  refine ⟨19255617535108139378114707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102696626853910076683278437 19255617535108139378114707)
  ·
    refine ⟨28883426302662209067172061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19255617535108139378114707 28883426302662209067172061)
    ·
      refine ⟨10831284863498328400189523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28883426302662209067172061 10831284863498328400189523)
      ·
        refine ⟨16246927295247492600284285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10831284863498328400189523 16246927295247492600284285)
        ·
          refine ⟨6092597735717809725106607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16246927295247492600284285 6092597735717809725106607)
          ·
            refine ⟨9138896603576714587659911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092597735717809725106607 9138896603576714587659911)
            ·
              refine ⟨13708344905365071881489867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138896603576714587659911 13708344905365071881489867)
              ·
                refine ⟨20562517358047607822234801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13708344905365071881489867 20562517358047607822234801)
                ·
                  refine ⟨15421888018535705866676101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20562517358047607822234801 15421888018535705866676101)
                  ·
                    refine ⟨2891604003475444850001769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15421888018535705866676101 2891604003475444850001769)
                    ·
                      refine ⟨2168703002606583637501327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891604003475444850001769 2168703002606583637501327)
                      ·
                        rfl

theorem cell23_4223534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_4223534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223534 prefixEnd_4223534 := by exact prefixLift 4223534
  have htrace : WordTrace (prefixWord ++ tailWord_4223534) baseStart_4223534 baseEnd_4223534 := by
    simpa [prefixWord, tailWord_4223534, baseEnd_4223534] using wordTrace_append hprefix tailTrace_4223534
  have hstable : (prefixWord ++ tailWord_4223534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223534).length < 2 ^ (prefixWord ++ tailWord_4223534).sum := by decide
  have hdescent : baseEnd_4223534 < baseStart_4223534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223583 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 3, 6]
def baseStart_4223583 : Nat := 118140960795 + 4223583 * 2 ^ 59
def prefixEnd_4223583 : Nat := 4983230072969 + 3 ^ 40 * 4223583 * 2
def baseEnd_4223583 : Nat := 722909387719551315262867

theorem tailTrace_4223583 : CollatzResearch.WordTrace tailWord_4223583 prefixEnd_4223583 722909387719551315262867 := by
  unfold tailWord_4223583
  simp only [CollatzResearch.WordTrace]
  refine ⟨154046727457687596393451403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102697818305125064262300935 154046727457687596393451403)
  ·
    refine ⟨231070091186531394590177105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154046727457687596393451403 231070091186531394590177105)
    ·
      refine ⟨173302568389898545942632829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231070091186531394590177105 173302568389898545942632829)
      ·
        refine ⟨64988463146211954728487311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173302568389898545942632829 64988463146211954728487311)
        ·
          refine ⟨97482694719317932092730967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64988463146211954728487311 97482694719317932092730967)
          ·
            refine ⟨146224042078976898139096451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97482694719317932092730967 146224042078976898139096451)
            ·
              refine ⟨219336063118465347208644677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146224042078976898139096451 219336063118465347208644677)
              ·
                refine ⟨41125511834712252601620877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219336063118465347208644677 41125511834712252601620877)
                ·
                  refine ⟨15422066938017094725607829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41125511834712252601620877 15422066938017094725607829)
                  ·
                    refine ⟨722909387719551315262867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15422066938017094725607829 722909387719551315262867)
                    ·
                      rfl

theorem cell23_4223583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_4223583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223583 prefixEnd_4223583 := by exact prefixLift 4223583
  have htrace : WordTrace (prefixWord ++ tailWord_4223583) baseStart_4223583 baseEnd_4223583 := by
    simpa [prefixWord, tailWord_4223583, baseEnd_4223583] using wordTrace_append hprefix tailTrace_4223583
  have hstable : (prefixWord ++ tailWord_4223583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223583).length < 2 ^ (prefixWord ++ tailWord_4223583).sum := by decide
  have hdescent : baseEnd_4223583 < baseStart_4223583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223584 : List Nat := [2, 1, 1, 3, 2, 1, 4, 4, 1, 1, 3]
def baseStart_4223584 : Nat := 118140960795 + 4223584 * 2 ^ 59
def prefixEnd_4223584 : Nat := 4983230072969 + 3 ^ 40 * 4223584 * 2
def baseEnd_4223584 : Nat := 2168728676639308441876097

theorem tailTrace_4223584 : CollatzResearch.WordTrace tailWord_4223584 prefixEnd_4223584 2168728676639308441876097 := by
  unfold tailWord_4223584
  simp only [CollatzResearch.WordTrace]
  refine ⟨77023381965341986782118903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102697842620455982376158537 77023381965341986782118903)
  ·
    refine ⟨115535072948012980173178355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77023381965341986782118903 115535072948012980173178355)
    ·
      refine ⟨173302609422019470259767533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115535072948012980173178355 173302609422019470259767533)
      ·
        refine ⟨64988478533257301347412825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173302609422019470259767533 64988478533257301347412825)
        ·
          refine ⟨48741358899942976010559619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64988478533257301347412825 48741358899942976010559619)
          ·
            refine ⟨73112038349914464015839429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48741358899942976010559619 73112038349914464015839429)
            ·
              refine ⟨13708507190608962002969893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73112038349914464015839429 13708507190608962002969893)
              ·
                refine ⟨2570345098239180375556855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13708507190608962002969893 2570345098239180375556855)
                ·
                  refine ⟨3855517647358770563335283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570345098239180375556855 3855517647358770563335283)
                  ·
                    refine ⟨5783276471038155845002925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3855517647358770563335283 5783276471038155845002925)
                    ·
                      refine ⟨2168728676639308441876097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5783276471038155845002925 2168728676639308441876097)
                      ·
                        rfl

theorem cell23_4223584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_4223584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223584 prefixEnd_4223584 := by exact prefixLift 4223584
  have htrace : WordTrace (prefixWord ++ tailWord_4223584) baseStart_4223584 baseEnd_4223584 := by
    simpa [prefixWord, tailWord_4223584, baseEnd_4223584] using wordTrace_append hprefix tailTrace_4223584
  have hstable : (prefixWord ++ tailWord_4223584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223584).length < 2 ^ (prefixWord ++ tailWord_4223584).sum := by decide
  have hdescent : baseEnd_4223584 < baseStart_4223584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223610 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_4223610 : Nat := 118140960795 + 4223610 * 2 ^ 59
def prefixEnd_4223610 : Nat := 4983230072969 + 3 ^ 40 * 4223610 * 2
def baseEnd_4223610 : Nat := 2168742027136325340150977

theorem tailTrace_4223610 : CollatzResearch.WordTrace tailWord_4223610 prefixEnd_4223610 2168742027136325340150977 := by
  unfold tailWord_4223610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38511928057147445001171071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102698474819059853336456189 38511928057147445001171071)
  ·
    refine ⟨57767892085721167501756607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38511928057147445001171071 57767892085721167501756607)
    ·
      refine ⟨86651838128581751252634911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57767892085721167501756607 86651838128581751252634911)
      ·
        refine ⟨129977757192872626878952367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86651838128581751252634911 129977757192872626878952367)
        ·
          refine ⟨194966635789308940318428551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129977757192872626878952367 194966635789308940318428551)
          ·
            refine ⟨292449953683963410477642827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194966635789308940318428551 292449953683963410477642827)
            ·
              refine ⟨438674930525945115716464241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292449953683963410477642827 438674930525945115716464241)
              ·
                refine ⟨329006197894458836787348181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438674930525945115716464241 329006197894458836787348181)
                ·
                  refine ⟨7711082763151378987203473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 329006197894458836787348181 7711082763151378987203473)
                  ·
                    refine ⟨5783312072363534240402605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7711082763151378987203473 5783312072363534240402605)
                    ·
                      refine ⟨2168742027136325340150977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5783312072363534240402605 2168742027136325340150977)
                      ·
                        rfl

theorem cell23_4223610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_4223610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223610 prefixEnd_4223610 := by exact prefixLift 4223610
  have htrace : WordTrace (prefixWord ++ tailWord_4223610) baseStart_4223610 baseEnd_4223610 := by
    simpa [prefixWord, tailWord_4223610, baseEnd_4223610] using wordTrace_append hprefix tailTrace_4223610
  have hstable : (prefixWord ++ tailWord_4223610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223610).length < 2 ^ (prefixWord ++ tailWord_4223610).sum := by decide
  have hdescent : baseEnd_4223610 < baseStart_4223610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223643 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 6, 7]
def baseStart_4223643 : Nat := 118140960795 + 4223643 * 2 ^ 59
def prefixEnd_4223643 : Nat := 4983230072969 + 3 ^ 40 * 4223643 * 2
def baseEnd_4223643 : Nat := 722919657332641237012775

theorem tailTrace_4223643 : CollatzResearch.WordTrace tailWord_4223643 prefixEnd_4223643 722919657332641237012775 := by
  unfold tailWord_4223643
  simp only [CollatzResearch.WordTrace]
  refine ⟨154048915837470226640635583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102699277224980151093757055 154048915837470226640635583)
  ·
    refine ⟨231073373756205339960953375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154048915837470226640635583 231073373756205339960953375)
    ·
      refine ⟨346610060634308009941430063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231073373756205339960953375 346610060634308009941430063)
      ·
        refine ⟨519915090951462014912145095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346610060634308009941430063 519915090951462014912145095)
        ·
          refine ⟨779872636427193022368217643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519915090951462014912145095 779872636427193022368217643)
          ·
            refine ⟨1169808954640789533552326465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779872636427193022368217643 1169808954640789533552326465)
            ·
              refine ⟨877356715980592150164244849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169808954640789533552326465 877356715980592150164244849)
              ·
                refine ⟨658017536985444112623183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877356715980592150164244849 658017536985444112623183637)
                ·
                  refine ⟨30844572046192692779211733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 658017536985444112623183637 30844572046192692779211733)
                  ·
                    refine ⟨722919657332641237012775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30844572046192692779211733 722919657332641237012775)
                    ·
                      rfl

theorem cell23_4223643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_4223643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223643 prefixEnd_4223643 := by exact prefixLift 4223643
  have htrace : WordTrace (prefixWord ++ tailWord_4223643) baseStart_4223643 baseEnd_4223643 := by
    simpa [prefixWord, tailWord_4223643, baseEnd_4223643] using wordTrace_append hprefix tailTrace_4223643
  have hstable : (prefixWord ++ tailWord_4223643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223643).length < 2 ^ (prefixWord ++ tailWord_4223643).sum := by decide
  have hdescent : baseEnd_4223643 < baseStart_4223643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223658 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4223658 : Nat := 118140960795 + 4223658 * 2 ^ 59
def prefixEnd_4223658 : Nat := 4983230072969 + 3 ^ 40 * 4223658 * 2
def baseEnd_4223658 : Nat := 2168766674207741152350757

theorem tailTrace_4223658 : CollatzResearch.WordTrace tailWord_4223658 prefixEnd_4223658 2168766674207741152350757 := by
  unfold tailWord_4223658
  simp only [CollatzResearch.WordTrace]
  refine ⟨38512365733103971050607907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102699641954943922801621085 38512365733103971050607907)
  ·
    refine ⟨57768548599655956575911861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38512365733103971050607907 57768548599655956575911861)
    ·
      refine ⟨5415801431217745928991737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57768548599655956575911861 5415801431217745928991737)
      ·
        refine ⟨4061851073413309446743803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5415801431217745928991737 4061851073413309446743803)
        ·
          refine ⟨6092776610119964170115705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061851073413309446743803 6092776610119964170115705)
          ·
            refine ⟨4569582457589973127586779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6092776610119964170115705 4569582457589973127586779)
            ·
              refine ⟨6854373686384959691380169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569582457589973127586779 6854373686384959691380169)
              ·
                refine ⟨5140780264788719768535127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6854373686384959691380169 5140780264788719768535127)
                ·
                  refine ⟨7711170397183079652802691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5140780264788719768535127 7711170397183079652802691)
                  ·
                    refine ⟨11566755595774619479204037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7711170397183079652802691 11566755595774619479204037)
                    ·
                      refine ⟨2168766674207741152350757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11566755595774619479204037 2168766674207741152350757)
                      ·
                        rfl

theorem cell23_4223658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4223658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223658 prefixEnd_4223658 := by exact prefixLift 4223658
  have htrace : WordTrace (prefixWord ++ tailWord_4223658) baseStart_4223658 baseEnd_4223658 := by
    simpa [prefixWord, tailWord_4223658, baseEnd_4223658] using wordTrace_append hprefix tailTrace_4223658
  have hstable : (prefixWord ++ tailWord_4223658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223658).length < 2 ^ (prefixWord ++ tailWord_4223658).sum := by decide
  have hdescent : baseEnd_4223658 < baseStart_4223658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223661 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_4223661 : Nat := 118140960795 + 4223661 * 2 ^ 59
def prefixEnd_4223661 : Nat := 4983230072969 + 3 ^ 40 * 4223661 * 2
def baseEnd_4223661 : Nat := 2168768214649704640613243

theorem tailTrace_4223661 : CollatzResearch.WordTrace tailWord_4223661 prefixEnd_4223661 2168768214649704640613243 := by
  unfold tailWord_4223661
  simp only [CollatzResearch.WordTrace]
  refine ⟨154049572351405015714790837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102699714900936677143193891 154049572351405015714790837)
  ·
    refine ⟨14442147407944220223261641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154049572351405015714790837 14442147407944220223261641)
    ·
      refine ⟨10831610555958165167446231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14442147407944220223261641 10831610555958165167446231)
      ·
        refine ⟨16247415833937247751169347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10831610555958165167446231 16247415833937247751169347)
        ·
          refine ⟨24371123750905871626754021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16247415833937247751169347 24371123750905871626754021)
          ·
            refine ⟨4569585703294850930016379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24371123750905871626754021 4569585703294850930016379)
            ·
              refine ⟨6854378554942276395024569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569585703294850930016379 6854378554942276395024569)
              ·
                refine ⟨5140783916206707296268427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6854378554942276395024569 5140783916206707296268427)
                ·
                  refine ⟨7711175874310060944402641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5140783916206707296268427 7711175874310060944402641)
                  ·
                    refine ⟨5783381905732545708301981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7711175874310060944402641 5783381905732545708301981)
                    ·
                      refine ⟨2168768214649704640613243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5783381905732545708301981 2168768214649704640613243)
                      ·
                        rfl

theorem cell23_4223661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_4223661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223661 prefixEnd_4223661 := by exact prefixLift 4223661
  have htrace : WordTrace (prefixWord ++ tailWord_4223661) baseStart_4223661 baseEnd_4223661 := by
    simpa [prefixWord, tailWord_4223661, baseEnd_4223661] using wordTrace_append hprefix tailTrace_4223661
  have hstable : (prefixWord ++ tailWord_4223661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223661).length < 2 ^ (prefixWord ++ tailWord_4223661).sum := by decide
  have hdescent : baseEnd_4223661 < baseStart_4223661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223697 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 3, 4, 2]
def baseStart_4223697 : Nat := 118140960795 + 4223697 * 2 ^ 59
def prefixEnd_4223697 : Nat := 4983230072969 + 3 ^ 40 * 4223697 * 2
def baseEnd_4223697 : Nat := 2168786699953266499763077

theorem tailTrace_4223697 : CollatzResearch.WordTrace tailWord_4223697 prefixEnd_4223697 2168786699953266499763077 := by
  unfold tailWord_4223697
  simp only [CollatzResearch.WordTrace]
  refine ⟨154050885379274593863101345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102700590252849729242067563 154050885379274593863101345)
  ·
    refine ⟨115538164034455945397326009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154050885379274593863101345 115538164034455945397326009)
    ·
      refine ⟨86653623025841959047994507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115538164034455945397326009 86653623025841959047994507)
      ·
        refine ⟨129980434538762938571991761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86653623025841959047994507 129980434538762938571991761)
        ·
          refine ⟨97485325904072203928993821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129980434538762938571991761 97485325904072203928993821)
          ·
            refine ⟨36556997214027076473372683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97485325904072203928993821 36556997214027076473372683)
            ·
              refine ⟨54835495821040614710059025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36556997214027076473372683 54835495821040614710059025)
              ·
                refine ⟨41126621865780461032544269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54835495821040614710059025 41126621865780461032544269)
                ·
                  refine ⟨15422483199667672887204101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41126621865780461032544269 15422483199667672887204101)
                  ·
                    refine ⟨2891715599937688666350769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15422483199667672887204101 2891715599937688666350769)
                    ·
                      refine ⟨2168786699953266499763077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891715599937688666350769 2168786699953266499763077)
                      ·
                        rfl

theorem cell23_4223697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_4223697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223697 prefixEnd_4223697 := by exact prefixLift 4223697
  have htrace : WordTrace (prefixWord ++ tailWord_4223697) baseStart_4223697 baseEnd_4223697 := by
    simpa [prefixWord, tailWord_4223697, baseEnd_4223697] using wordTrace_append hprefix tailTrace_4223697
  have hstable : (prefixWord ++ tailWord_4223697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223697).length < 2 ^ (prefixWord ++ tailWord_4223697).sum := by decide
  have hdescent : baseEnd_4223697 < baseStart_4223697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223787 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 3, 6, 2]
def baseStart_4223787 : Nat := 118140960795 + 4223787 * 2 ^ 59
def prefixEnd_4223787 : Nat := 4983230072969 + 3 ^ 40 * 4223787 * 2
def baseEnd_4223787 : Nat := 2168832913212171147637663

theorem tailTrace_4223787 : CollatzResearch.WordTrace tailWord_4223787 prefixEnd_4223787 2168832913212171147637663 := by
  unfold tailWord_4223787
  simp only [CollatzResearch.WordTrace]
  refine ⟨154054167948948539233877615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102702778632632359489251743 154054167948948539233877615)
  ·
    refine ⟨231081251923422808850816423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154054167948948539233877615 231081251923422808850816423)
    ·
      refine ⟨346621877885134213276224635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231081251923422808850816423 346621877885134213276224635)
      ·
        refine ⟨519932816827701319914336953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346621877885134213276224635 519932816827701319914336953)
        ·
          refine ⟨389949612620775989935752715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519932816827701319914336953 389949612620775989935752715)
          ·
            refine ⟨584924418931163984903629073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389949612620775989935752715 584924418931163984903629073)
            ·
              refine ⟨438693314198372988677721805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584924418931163984903629073 438693314198372988677721805)
              ·
                refine ⟨164509992824389870754145677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 438693314198372988677721805 164509992824389870754145677)
                ·
                  refine ⟨61691247309146201532804629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164509992824389870754145677 61691247309146201532804629)
                  ·
                    refine ⟨2891777217616228196850217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61691247309146201532804629 2891777217616228196850217)
                    ·
                      refine ⟨2168832913212171147637663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891777217616228196850217 2168832913212171147637663)
                      ·
                        rfl

theorem cell23_4223787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6, 2].length) (baseStart_4223787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223787 prefixEnd_4223787 := by exact prefixLift 4223787
  have htrace : WordTrace (prefixWord ++ tailWord_4223787) baseStart_4223787 baseEnd_4223787 := by
    simpa [prefixWord, tailWord_4223787, baseEnd_4223787] using wordTrace_append hprefix tailTrace_4223787
  have hstable : (prefixWord ++ tailWord_4223787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223787).length < 2 ^ (prefixWord ++ tailWord_4223787).sum := by decide
  have hdescent : baseEnd_4223787 < baseStart_4223787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223864 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 4, 3, 2]
def baseStart_4223864 : Nat := 118140960795 + 4223864 * 2 ^ 59
def prefixEnd_4223864 : Nat := 4983230072969 + 3 ^ 40 * 4223864 * 2
def baseEnd_4223864 : Nat := 2168872451222567346374809

theorem tailTrace_4223864 : CollatzResearch.WordTrace tailWord_4223864 prefixEnd_4223864 2168872451222567346374809 := by
  unfold tailWord_4223864
  simp only [CollatzResearch.WordTrace]
  refine ⟨77028488184834790692215323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102704650913113054256287097 77028488184834790692215323)
  ·
    refine ⟨115542732277252186038322985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77028488184834790692215323 115542732277252186038322985)
    ·
      refine ⟨86657049207939139528742239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115542732277252186038322985 86657049207939139528742239)
      ·
        refine ⟨129985573811908709293113359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86657049207939139528742239 129985573811908709293113359)
        ·
          refine ⟨194978360717863063939670039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129985573811908709293113359 194978360717863063939670039)
          ·
            refine ⟨292467541076794595909505059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194978360717863063939670039 292467541076794595909505059)
            ·
              refine ⟨438701311615191893864257589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292467541076794595909505059 438701311615191893864257589)
              ·
                refine ⟨41128247963924240049774149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 438701311615191893864257589 41128247963924240049774149)
                ·
                  refine ⟨7711546493235795009332653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41128247963924240049774149 7711546493235795009332653)
                  ·
                    refine ⟨2891829934963423128499745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7711546493235795009332653 2891829934963423128499745)
                    ·
                      refine ⟨2168872451222567346374809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891829934963423128499745 2168872451222567346374809)
                      ·
                        rfl

theorem cell23_4223864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_4223864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223864 prefixEnd_4223864 := by exact prefixLift 4223864
  have htrace : WordTrace (prefixWord ++ tailWord_4223864) baseStart_4223864 baseEnd_4223864 := by
    simpa [prefixWord, tailWord_4223864, baseEnd_4223864] using wordTrace_append hprefix tailTrace_4223864
  have hstable : (prefixWord ++ tailWord_4223864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223864).length < 2 ^ (prefixWord ++ tailWord_4223864).sum := by decide
  have hdescent : baseEnd_4223864 < baseStart_4223864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223905 : List Nat := [1, 2, 3, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4223905 : Nat := 118140960795 + 4223905 * 2 ^ 59
def prefixEnd_4223905 : Nat := 4983230072969 + 3 ^ 40 * 4223905 * 2
def baseEnd_4223905 : Nat := 2168893503929401685962121

theorem tailTrace_4223905 : CollatzResearch.WordTrace tailWord_4223905 prefixEnd_4223905 2168893503929401685962121 := by
  unfold tailWord_4223905
  simp only [CollatzResearch.WordTrace]
  refine ⟨154058471762521045386673169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102705647841680696924448779 154058471762521045386673169)
  ·
    refine ⟨115543853821890784040004877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154058471762521045386673169 115543853821890784040004877)
    ·
      refine ⟨43328945183209044015001829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115543853821890784040004877 43328945183209044015001829)
      ·
        refine ⟨8124177221851695752812843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43328945183209044015001829 8124177221851695752812843)
        ·
          refine ⟨12186265832777543629219265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8124177221851695752812843 12186265832777543629219265)
          ·
            refine ⟨9139699374583157721914449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12186265832777543629219265 9139699374583157721914449)
            ·
              refine ⟨6854774530937368291435837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9139699374583157721914449 6854774530937368291435837)
              ·
                refine ⟨2570540449101513109288439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6854774530937368291435837 2570540449101513109288439)
                ·
                  refine ⟨3855810673652269663932659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570540449101513109288439 3855810673652269663932659)
                  ·
                    refine ⟨5783716010478404495898989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3855810673652269663932659 5783716010478404495898989)
                    ·
                      refine ⟨2168893503929401685962121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5783716010478404495898989 2168893503929401685962121)
                      ·
                        rfl

theorem cell23_4223905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4223905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223905 prefixEnd_4223905 := by exact prefixLift 4223905
  have htrace : WordTrace (prefixWord ++ tailWord_4223905) baseStart_4223905 baseEnd_4223905 := by
    simpa [prefixWord, tailWord_4223905, baseEnd_4223905] using wordTrace_append hprefix tailTrace_4223905
  have hstable : (prefixWord ++ tailWord_4223905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223905).length < 2 ^ (prefixWord ++ tailWord_4223905).sum := by decide
  have hdescent : baseEnd_4223905 < baseStart_4223905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223921 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 4, 4]
def baseStart_4223921 : Nat := 118140960795 + 4223921 * 2 ^ 59
def prefixEnd_4223921 : Nat := 4983230072969 + 3 ^ 40 * 4223921 * 2
def baseEnd_4223921 : Nat := 722967239873291207787349

theorem tailTrace_4223921 : CollatzResearch.WordTrace tailWord_4223921 prefixEnd_4223921 722967239873291207787349 := by
  unfold tailWord_4223921
  simp only [CollatzResearch.WordTrace]
  refine ⟨154059055330463080119255617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102706036886975386746170411 154059055330463080119255617)
  ·
    refine ⟨115544291497847310089441713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154059055330463080119255617 115544291497847310089441713)
    ·
      refine ⟨86658218623385482567081285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115544291497847310089441713 86658218623385482567081285)
      ·
        refine ⟨16248415991884777981327741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86658218623385482567081285 16248415991884777981327741)
        ·
          refine ⟨6093155996956791742997903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16248415991884777981327741 6093155996956791742997903)
          ·
            refine ⟨9139733995435187614496855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6093155996956791742997903 9139733995435187614496855)
            ·
              refine ⟨13709600993152781421745283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9139733995435187614496855 13709600993152781421745283)
              ·
                refine ⟨20564401489729172132617925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13709600993152781421745283 20564401489729172132617925)
                ·
                  refine ⟨3855825279324219774865861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20564401489729172132617925 3855825279324219774865861)
                  ·
                    refine ⟨722967239873291207787349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855825279324219774865861 722967239873291207787349)
                    ·
                      rfl

theorem cell23_4223921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_4223921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223921 prefixEnd_4223921 := by exact prefixLift 4223921
  have htrace : WordTrace (prefixWord ++ tailWord_4223921) baseStart_4223921 baseEnd_4223921 := by
    simpa [prefixWord, tailWord_4223921, baseEnd_4223921] using wordTrace_append hprefix tailTrace_4223921
  have hstable : (prefixWord ++ tailWord_4223921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223921).length < 2 ^ (prefixWord ++ tailWord_4223921).sum := by decide
  have hdescent : baseEnd_4223921 < baseStart_4223921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223928 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 3, 2, 2]
def baseStart_4223928 : Nat := 118140960795 + 4223928 * 2 ^ 59
def prefixEnd_4223928 : Nat := 4983230072969 + 3 ^ 40 * 4223928 * 2
def baseEnd_4223928 : Nat := 2168905313984455095974515

theorem tailTrace_4223928 : CollatzResearch.WordTrace tailWord_4223928 prefixEnd_4223928 2168905313984455095974515 := by
  unfold tailWord_4223928
  simp only [CollatzResearch.WordTrace]
  refine ⟨77029655320718860157380219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102706207094291813543173625 77029655320718860157380219)
  ·
    refine ⟨115544482981078290236070329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77029655320718860157380219 115544482981078290236070329)
    ·
      refine ⟨86658362235808717677052747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115544482981078290236070329 86658362235808717677052747)
      ·
        refine ⟨129987543353713076515579121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86658362235808717677052747 129987543353713076515579121)
        ·
          refine ⟨97490657515284807386684341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129987543353713076515579121 97490657515284807386684341)
          ·
            refine ⟨9139749142057950692501657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97490657515284807386684341 9139749142057950692501657)
            ·
              refine ⟨6854811856543463019376243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9139749142057950692501657 6854811856543463019376243)
              ·
                refine ⟨10282217784815194529064365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6854811856543463019376243 10282217784815194529064365)
                ·
                  refine ⟨3855831669305697948399137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10282217784815194529064365 3855831669305697948399137)
                  ·
                    refine ⟨2891873751979273461299353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3855831669305697948399137 2891873751979273461299353)
                    ·
                      refine ⟨2168905313984455095974515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891873751979273461299353 2168905313984455095974515)
                      ·
                        rfl

theorem cell23_4223928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_4223928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223928 prefixEnd_4223928 := by exact prefixLift 4223928
  have htrace : WordTrace (prefixWord ++ tailWord_4223928) baseStart_4223928 baseEnd_4223928 := by
    simpa [prefixWord, tailWord_4223928, baseEnd_4223928] using wordTrace_append hprefix tailTrace_4223928
  have hstable : (prefixWord ++ tailWord_4223928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223928).length < 2 ^ (prefixWord ++ tailWord_4223928).sum := by decide
  have hdescent : baseEnd_4223928 < baseStart_4223928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223961 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 3]
def baseStart_4223961 : Nat := 118140960795 + 4223961 * 2 ^ 59
def prefixEnd_4223961 : Nat := 4983230072969 + 3 ^ 40 * 4223961 * 2
def baseEnd_4223961 : Nat := 2168922258846053466861863

theorem tailTrace_4223961 : CollatzResearch.WordTrace tailWord_4223961 prefixEnd_4223961 2168922258846053466861863 := by
  unfold tailWord_4223961
  simp only [CollatzResearch.WordTrace]
  refine ⟨154060514250318166950711737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102707009500212111300474491 154060514250318166950711737)
  ·
    refine ⟨115545385687738625213033803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154060514250318166950711737 115545385687738625213033803)
    ·
      refine ⟨173318078531607937819550705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115545385687738625213033803 173318078531607937819550705)
      ·
        refine ⟨129988558898705953364663029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173318078531607937819550705 129988558898705953364663029)
        ·
          refine ⟨12186427396753683127937159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129988558898705953364663029 12186427396753683127937159)
          ·
            refine ⟨18279641095130524691905739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12186427396753683127937159 18279641095130524691905739)
            ·
              refine ⟨27419461642695787037858609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18279641095130524691905739 27419461642695787037858609)
              ·
                refine ⟨20564596232021840278393957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27419461642695787037858609 20564596232021840278393957)
                ·
                  refine ⟨3855861793504095052198867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20564596232021840278393957 3855861793504095052198867)
                  ·
                    refine ⟨5783792690256142578298301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3855861793504095052198867 5783792690256142578298301)
                    ·
                      refine ⟨2168922258846053466861863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5783792690256142578298301 2168922258846053466861863)
                      ·
                        rfl

theorem cell23_4223961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_4223961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223961 prefixEnd_4223961 := by exact prefixLift 4223961
  have htrace : WordTrace (prefixWord ++ tailWord_4223961) baseStart_4223961 baseEnd_4223961 := by
    simpa [prefixWord, tailWord_4223961, baseEnd_4223961] using wordTrace_append hprefix tailTrace_4223961
  have hstable : (prefixWord ++ tailWord_4223961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223961).length < 2 ^ (prefixWord ++ tailWord_4223961).sum := by decide
  have hdescent : baseEnd_4223961 < baseStart_4223961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223962 : List Nat := [3, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2]
def baseStart_4223962 : Nat := 118140960795 + 4223962 * 2 ^ 59
def prefixEnd_4223962 : Nat := 4983230072969 + 3 ^ 40 * 4223962 * 2
def baseEnd_4223962 : Nat := 2168922772326707962949359

theorem tailTrace_4223962 : CollatzResearch.WordTrace tailWord_4223962 prefixEnd_4223962 2168922772326707962949359 := by
  unfold tailWord_4223962
  simp only [CollatzResearch.WordTrace]
  refine ⟨38515137680828636030374535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102707033815543029414332093 38515137680828636030374535)
  ·
    refine ⟨57772706521242954045561803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38515137680828636030374535 57772706521242954045561803)
    ·
      refine ⟨86659059781864431068342705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57772706521242954045561803 86659059781864431068342705)
      ·
        refine ⟨64994294836398323301257029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86659059781864431068342705 64994294836398323301257029)
        ·
          refine ⟨12186430281824685618985693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64994294836398323301257029 12186430281824685618985693)
          ·
            refine ⟨4569911355684257107119635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12186430281824685618985693 4569911355684257107119635)
            ·
              refine ⟨6854867033526385660679453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569911355684257107119635 6854867033526385660679453)
              ·
                refine ⟨2570575137572394622754795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6854867033526385660679453 2570575137572394622754795)
                ·
                  refine ⟨3855862706358591934132193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570575137572394622754795 3855862706358591934132193)
                  ·
                    refine ⟨2891897029768943950599145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3855862706358591934132193 2891897029768943950599145)
                    ·
                      refine ⟨2168922772326707962949359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891897029768943950599145 2168922772326707962949359)
                      ·
                        rfl

theorem cell23_4223962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_4223962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223962 prefixEnd_4223962 := by exact prefixLift 4223962
  have htrace : WordTrace (prefixWord ++ tailWord_4223962) baseStart_4223962 baseEnd_4223962 := by
    simpa [prefixWord, tailWord_4223962, baseEnd_4223962] using wordTrace_append hprefix tailTrace_4223962
  have hstable : (prefixWord ++ tailWord_4223962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223962).length < 2 ^ (prefixWord ++ tailWord_4223962).sum := by decide
  have hdescent : baseEnd_4223962 < baseStart_4223962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4223989 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4223989 : Nat := 118140960795 + 4223989 * 2 ^ 59
def prefixEnd_4223989 : Nat := 4983230072969 + 3 ^ 40 * 4223989 * 2
def baseEnd_4223989 : Nat := 722978878768126452437245

theorem tailTrace_4223989 : CollatzResearch.WordTrace tailWord_4223989 prefixEnd_4223989 722978878768126452437245 := by
  unfold tailWord_4223989
  simp only [CollatzResearch.WordTrace]
  refine ⟨154061535494216727732731021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102707690329477818488487347 154061535494216727732731021)
  ·
    refine ⟨57773075810331272899774133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154061535494216727732731021 57773075810331272899774133)
    ·
      refine ⟨5416225857218556834353825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57773075810331272899774133 5416225857218556834353825)
      ·
        refine ⟨4062169392913917625765369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5416225857218556834353825 4062169392913917625765369)
        ·
          refine ⟨3046627044685438219324027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4062169392913917625765369 3046627044685438219324027)
          ·
            refine ⟨4569940567028157328986041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046627044685438219324027 4569940567028157328986041)
            ·
              refine ⟨3427455425271117996739531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4569940567028157328986041 3427455425271117996739531)
              ·
                refine ⟨5141183137906676995109297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427455425271117996739531 5141183137906676995109297)
                ·
                  refine ⟨3855887353430007746331973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5141183137906676995109297 3855887353430007746331973)
                  ·
                    refine ⟨722978878768126452437245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855887353430007746331973 722978878768126452437245)
                    ·
                      rfl

theorem cell23_4223989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4223989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4223989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4223989 prefixEnd_4223989 := by exact prefixLift 4223989
  have htrace : WordTrace (prefixWord ++ tailWord_4223989) baseStart_4223989 baseEnd_4223989 := by
    simpa [prefixWord, tailWord_4223989, baseEnd_4223989] using wordTrace_append hprefix tailTrace_4223989
  have hstable : (prefixWord ++ tailWord_4223989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4223989).length < 2 ^ (prefixWord ++ tailWord_4223989).sum := by decide
  have hdescent : baseEnd_4223989 < baseStart_4223989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4223989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224027 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8]
def baseStart_4224027 : Nat := 118140960795 + 4224027 * 2 ^ 59
def prefixEnd_4224027 : Nat := 4983230072969 + 3 ^ 40 * 4224027 * 2
def baseEnd_4224027 : Nat := 2168956148569250208636559

theorem tailTrace_4224027 : CollatzResearch.WordTrace tailWord_4224027 prefixEnd_4224027 2168956148569250208636559 := by
  unfold tailWord_4224027
  simp only [CollatzResearch.WordTrace]
  refine ⟨154062921468079060222614335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102708614312052706815076223 154062921468079060222614335)
  ·
    refine ⟨231094382202118590333921503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154062921468079060222614335 231094382202118590333921503)
    ·
      refine ⟨346641573303177885500882255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231094382202118590333921503 346641573303177885500882255)
      ·
        refine ⟨519962359954766828251323383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346641573303177885500882255 519962359954766828251323383)
        ·
          refine ⟨779943539932150242376985075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519962359954766828251323383 779943539932150242376985075)
          ·
            refine ⟨1169915309898225363565477613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779943539932150242376985075 1169915309898225363565477613)
            ·
              refine ⟨438718241211834511337054105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1169915309898225363565477613 438718241211834511337054105)
              ·
                refine ⟨329038680908875883502790579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438718241211834511337054105 329038680908875883502790579)
                ·
                  refine ⟨493558021363313825254185869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329038680908875883502790579 493558021363313825254185869)
                  ·
                    refine ⟨185084258011242684470319701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 493558021363313825254185869 185084258011242684470319701)
                    ·
                      refine ⟨2168956148569250208636559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 185084258011242684470319701 2168956148569250208636559)
                      ·
                        rfl

theorem cell23_4224027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_4224027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224027 prefixEnd_4224027 := by exact prefixLift 4224027
  have htrace : WordTrace (prefixWord ++ tailWord_4224027) baseStart_4224027 baseEnd_4224027 := by
    simpa [prefixWord, tailWord_4224027, baseEnd_4224027] using wordTrace_append hprefix tailTrace_4224027
  have hstable : (prefixWord ++ tailWord_4224027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224027).length < 2 ^ (prefixWord ++ tailWord_4224027).sum := by decide
  have hdescent : baseEnd_4224027 < baseStart_4224027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224035 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 2, 2, 2]
def baseStart_4224035 : Nat := 118140960795 + 4224035 * 2 ^ 59
def prefixEnd_4224035 : Nat := 4983230072969 + 3 ^ 40 * 4224035 * 2
def baseEnd_4224035 : Nat := 2168960256414486177336523

theorem tailTrace_4224035 : CollatzResearch.WordTrace tailWord_4224035 prefixEnd_4224035 2168960256414486177336523 := by
  unfold tailWord_4224035
  simp only [CollatzResearch.WordTrace]
  refine ⟨154063213252050077588905559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102708808834700051725937039 154063213252050077588905559)
  ·
    refine ⟨231094819878075116383358339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154063213252050077588905559 231094819878075116383358339)
    ·
      refine ⟨346642229817112674575037509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231094819878075116383358339 346642229817112674575037509)
      ·
        refine ⟨64995418090708626482819533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346642229817112674575037509 64995418090708626482819533)
        ·
          refine ⟨24373281784015734931057325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64995418090708626482819533 24373281784015734931057325)
          ·
            refine ⟨9139980669005900599146497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24373281784015734931057325 9139980669005900599146497)
            ·
              refine ⟨6854985501754425449359873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9139980669005900599146497 6854985501754425449359873)
              ·
                refine ⟨5141239126315819087019905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6854985501754425449359873 5141239126315819087019905)
                ·
                  refine ⟨3855929344736864315264929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5141239126315819087019905 3855929344736864315264929)
                  ·
                    refine ⟨2891947008552648236448697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3855929344736864315264929 2891947008552648236448697)
                    ·
                      refine ⟨2168960256414486177336523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891947008552648236448697 2168960256414486177336523)
                      ·
                        rfl

theorem cell23_4224035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_4224035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224035 prefixEnd_4224035 := by exact prefixLift 4224035
  have htrace : WordTrace (prefixWord ++ tailWord_4224035) baseStart_4224035 baseEnd_4224035 := by
    simpa [prefixWord, tailWord_4224035, baseEnd_4224035] using wordTrace_append hprefix tailTrace_4224035
  have hstable : (prefixWord ++ tailWord_4224035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224035).length < 2 ^ (prefixWord ++ tailWord_4224035).sum := by decide
  have hdescent : baseEnd_4224035 < baseStart_4224035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224052 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4224052 : Nat := 118140960795 + 4224052 * 2 ^ 59
def prefixEnd_4224052 : Nat := 4983230072969 + 3 ^ 40 * 4224052 * 2
def baseEnd_4224052 : Nat := 2168968985585612610823945

theorem tailTrace_4224052 : CollatzResearch.WordTrace tailWord_4224052 prefixEnd_4224052 2168968985585612610823945 := by
  unfold tailWord_4224052
  simp only [CollatzResearch.WordTrace]
  refine ⟨77031916646494244746137205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102709222195325659661516273 77031916646494244746137205)
  ·
    refine ⟨7221742185608835444950363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77031916646494244746137205 7221742185608835444950363)
    ·
      refine ⟨10832613278413253167425545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7221742185608835444950363 10832613278413253167425545)
      ·
        refine ⟨8124459958809939875569159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10832613278413253167425545 8124459958809939875569159)
        ·
          refine ⟨12186689938214909813353739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8124459958809939875569159 12186689938214909813353739)
          ·
            refine ⟨18280034907322364720030609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12186689938214909813353739 18280034907322364720030609)
            ·
              refine ⟨13710026180491773540022957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18280034907322364720030609 13710026180491773540022957)
              ·
                refine ⟨5141259817684415077508609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13710026180491773540022957 5141259817684415077508609)
                ·
                  refine ⟨3855944863263311308131457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5141259817684415077508609 3855944863263311308131457)
                  ·
                    refine ⟨2891958647447483481098593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3855944863263311308131457 2891958647447483481098593)
                    ·
                      refine ⟨2168968985585612610823945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891958647447483481098593 2168968985585612610823945)
                      ·
                        rfl

theorem cell23_4224052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4224052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224052 prefixEnd_4224052 := by exact prefixLift 4224052
  have htrace : WordTrace (prefixWord ++ tailWord_4224052) baseStart_4224052 baseEnd_4224052 := by
    simpa [prefixWord, tailWord_4224052, baseEnd_4224052] using wordTrace_append hprefix tailTrace_4224052
  have hstable : (prefixWord ++ tailWord_4224052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224052).length < 2 ^ (prefixWord ++ tailWord_4224052).sum := by decide
  have hdescent : baseEnd_4224052 < baseStart_4224052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224071 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 2, 5]
def baseStart_4224071 : Nat := 118140960795 + 4224071 * 2 ^ 59
def prefixEnd_4224071 : Nat := 4983230072969 + 3 ^ 40 * 4224071 * 2
def baseEnd_4224071 : Nat := 722992913906016012162119

theorem tailTrace_4224071 : CollatzResearch.WordTrace tailWord_4224071 prefixEnd_4224071 722992913906016012162119 := by
  unfold tailWord_4224071
  simp only [CollatzResearch.WordTrace]
  refine ⟨154064526279919655737216067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102709684186613103824810711 154064526279919655737216067)
  ·
    refine ⟨231096789419879483605824101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154064526279919655737216067 231096789419879483605824101)
    ·
      refine ⟨43330648016227403176092019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231096789419879483605824101 43330648016227403176092019)
      ·
        refine ⟨64995972024341104764138029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43330648016227403176092019 64995972024341104764138029)
        ·
          refine ⟨24373489509127914286551761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64995972024341104764138029 24373489509127914286551761)
          ·
            refine ⟨18280117131845935714913821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24373489509127914286551761 18280117131845935714913821)
            ·
              refine ⟨6855043924442225893092683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18280117131845935714913821 6855043924442225893092683)
              ·
                refine ⟨10282565886663338839639025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6855043924442225893092683 10282565886663338839639025)
                ·
                  refine ⟨7711924414997504129729269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10282565886663338839639025 7711924414997504129729269)
                  ·
                    refine ⟨722992913906016012162119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7711924414997504129729269 722992913906016012162119)
                    ·
                      rfl

theorem cell23_4224071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_4224071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224071 prefixEnd_4224071 := by exact prefixLift 4224071
  have htrace : WordTrace (prefixWord ++ tailWord_4224071) baseStart_4224071 baseEnd_4224071 := by
    simpa [prefixWord, tailWord_4224071, baseEnd_4224071] using wordTrace_append hprefix tailTrace_4224071
  have hstable : (prefixWord ++ tailWord_4224071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224071).length < 2 ^ (prefixWord ++ tailWord_4224071).sum := by decide
  have hdescent : baseEnd_4224071 < baseStart_4224071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224086 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4224086 : Nat := 118140960795 + 4224086 * 2 ^ 59
def prefixEnd_4224086 : Nat := 4983230072969 + 3 ^ 40 * 4224086 * 2
def baseEnd_4224086 : Nat := 2168986443927865477798789

theorem tailTrace_4224086 : CollatzResearch.WordTrace tailWord_4224086 prefixEnd_4224086 2168986443927865477798789 := by
  unfold tailWord_4224086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629067085929082081188257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102710048916576875532674741 9629067085929082081188257)
  ·
    refine ⟨7221800314446811560891193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9629067085929082081188257 7221800314446811560891193)
    ·
      refine ⟨5416350235835108670668395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7221800314446811560891193 5416350235835108670668395)
      ·
        refine ⟨8124525353752663006002593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416350235835108670668395 8124525353752663006002593)
        ·
          refine ⟨6093394015314497254501945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8124525353752663006002593 6093394015314497254501945)
          ·
            refine ⟨4570045511485872940876459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6093394015314497254501945 4570045511485872940876459)
            ·
              refine ⟨6855068267228809411314689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570045511485872940876459 6855068267228809411314689)
              ·
                refine ⟨5141301200421607058486017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855068267228809411314689 5141301200421607058486017)
                ·
                  refine ⟨3855975900316205293864513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5141301200421607058486017 3855975900316205293864513)
                  ·
                    refine ⟨2891981925237153970398385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3855975900316205293864513 2891981925237153970398385)
                    ·
                      refine ⟨2168986443927865477798789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2891981925237153970398385 2168986443927865477798789)
                      ·
                        rfl

theorem cell23_4224086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4224086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224086 prefixEnd_4224086 := by exact prefixLift 4224086
  have htrace : WordTrace (prefixWord ++ tailWord_4224086) baseStart_4224086 baseEnd_4224086 := by
    simpa [prefixWord, tailWord_4224086, baseEnd_4224086] using wordTrace_append hprefix tailTrace_4224086
  have hstable : (prefixWord ++ tailWord_4224086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224086).length < 2 ^ (prefixWord ++ tailWord_4224086).sum := by decide
  have hdescent : baseEnd_4224086 < baseStart_4224086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224118 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_4224118 : Nat := 118140960795 + 4224118 * 2 ^ 59
def prefixEnd_4224118 : Nat := 4983230072969 + 3 ^ 40 * 4224118 * 2
def baseEnd_4224118 : Nat := 723000958436269784199547

theorem tailTrace_4224118 : CollatzResearch.WordTrace tailWord_4224118 prefixEnd_4224118 723000958436269784199547 := by
  unfold tailWord_4224118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629140031921836422761063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102710827007166255176118005 9629140031921836422761063)
  ·
    refine ⟨14443710047882754634141595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9629140031921836422761063 14443710047882754634141595)
    ·
      refine ⟨21665565071824131951212393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14443710047882754634141595 21665565071824131951212393)
      ·
        refine ⟨16249173803868098963409295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21665565071824131951212393 16249173803868098963409295)
        ·
          refine ⟨24373760705802148445113943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16249173803868098963409295 24373760705802148445113943)
          ·
            refine ⟨36560641058703222667670915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24373760705802148445113943 36560641058703222667670915)
            ·
              refine ⟨54840961588054834001506373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36560641058703222667670915 54840961588054834001506373)
              ·
                refine ⟨10282680297760281375282445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54840961588054834001506373 10282680297760281375282445)
                ·
                  refine ⟨3856005111660105515730917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10282680297760281375282445 3856005111660105515730917)
                  ·
                    refine ⟨723000958436269784199547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856005111660105515730917 723000958436269784199547)
                    ·
                      rfl

theorem cell23_4224118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_4224118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224118 prefixEnd_4224118 := by exact prefixLift 4224118
  have htrace : WordTrace (prefixWord ++ tailWord_4224118) baseStart_4224118 baseEnd_4224118 := by
    simpa [prefixWord, tailWord_4224118, baseEnd_4224118] using wordTrace_append hprefix tailTrace_4224118
  have hstable : (prefixWord ++ tailWord_4224118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224118).length < 2 ^ (prefixWord ++ tailWord_4224118).sum := by decide
  have hdescent : baseEnd_4224118 < baseStart_4224118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224126 : List Nat := [4, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_4224126 : Nat := 118140960795 + 4224126 * 2 ^ 59
def prefixEnd_4224126 : Nat := 4983230072969 + 3 ^ 40 * 4224126 * 2
def baseEnd_4224126 : Nat := 241000775906005035699845

theorem tailTrace_4224126 : CollatzResearch.WordTrace tailWord_4224126 prefixEnd_4224126 241000775906005035699845 := by
  unfold tailWord_4224126
  simp only [CollatzResearch.WordTrace]
  refine ⟨19258316536840050016308529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102711021529813600086978821 19258316536840050016308529)
  ·
    refine ⟨14443737402630037512231397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19258316536840050016308529 14443737402630037512231397)
    ·
      refine ⟨2708200762993132033543387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14443737402630037512231397 2708200762993132033543387)
      ·
        refine ⟨4062301144489698050315081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708200762993132033543387 4062301144489698050315081)
        ·
          refine ⟨3046725858367273537736311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4062301144489698050315081 3046725858367273537736311)
          ·
            refine ⟨4570088787550910306604467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046725858367273537736311 4570088787550910306604467)
            ·
              refine ⟨6855133181326365459906701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570088787550910306604467 6855133181326365459906701)
              ·
                refine ⟨2570674942997387047465013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6855133181326365459906701 2570674942997387047465013)
                ·
                  refine ⟨241000775906005035699845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2570674942997387047465013 241000775906005035699845)
                  ·
                    rfl

theorem cell23_4224126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_4224126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224126 prefixEnd_4224126 := by exact prefixLift 4224126
  have htrace : WordTrace (prefixWord ++ tailWord_4224126) baseStart_4224126 baseEnd_4224126 := by
    simpa [prefixWord, tailWord_4224126, baseEnd_4224126] using wordTrace_append hprefix tailTrace_4224126
  have hstable : (prefixWord ++ tailWord_4224126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224126).length < 2 ^ (prefixWord ++ tailWord_4224126).sum := by decide
  have hdescent : baseEnd_4224126 < baseStart_4224126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224152 : List Nat := [2, 1, 2, 4, 2, 2, 3, 2, 1, 4]
def baseStart_4224152 : Nat := 118140960795 + 4224152 * 2 ^ 59
def prefixEnd_4224152 : Nat := 4983230072969 + 3 ^ 40 * 4224152 * 2
def baseEnd_4224152 : Nat := 723006777883687406524495

theorem tailTrace_4224152 : CollatzResearch.WordTrace tailWord_4224152 prefixEnd_4224152 723006777883687406524495 := by
  unfold tailWord_4224152
  simp only [CollatzResearch.WordTrace]
  refine ⟨77033740296313103285457355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102711653728417471047276473 77033740296313103285457355)
  ·
    refine ⟨115550610444469654928186033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77033740296313103285457355 115550610444469654928186033)
    ·
      refine ⟨86662957833352241196139525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115550610444469654928186033 86662957833352241196139525)
      ·
        refine ⟨16249304593753545224276161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86662957833352241196139525 16249304593753545224276161)
        ·
          refine ⟨12186978445315158918207121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16249304593753545224276161 12186978445315158918207121)
          ·
            refine ⟨9140233833986369188655341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12186978445315158918207121 9140233833986369188655341)
            ·
              refine ⟨3427587687744888445745753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9140233833986369188655341 3427587687744888445745753)
              ·
                refine ⟨2570690765808666334309315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3427587687744888445745753 2570690765808666334309315)
                ·
                  refine ⟨3856036148712999501463973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570690765808666334309315 3856036148712999501463973)
                  ·
                    refine ⟨723006777883687406524495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856036148712999501463973 723006777883687406524495)
                    ·
                      rfl

theorem cell23_4224152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_4224152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224152 prefixEnd_4224152 := by exact prefixLift 4224152
  have htrace : WordTrace (prefixWord ++ tailWord_4224152) baseStart_4224152 baseEnd_4224152 := by
    simpa [prefixWord, tailWord_4224152, baseEnd_4224152] using wordTrace_append hprefix tailTrace_4224152
  have hstable : (prefixWord ++ tailWord_4224152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224152).length < 2 ^ (prefixWord ++ tailWord_4224152).sum := by decide
  have hdescent : baseEnd_4224152 < baseStart_4224152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224161 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 3, 5]
def baseStart_4224161 : Nat := 118140960795 + 4224161 * 2 ^ 59
def prefixEnd_4224161 : Nat := 4983230072969 + 3 ^ 40 * 4224161 * 2
def baseEnd_4224161 : Nat := 723008318325650894786981

theorem tailTrace_4224161 : CollatzResearch.WordTrace tailWord_4224161 prefixEnd_4224161 723008318325650894786981 := by
  unfold tailWord_4224161
  simp only [CollatzResearch.WordTrace]
  refine ⟨154067808849593601107992337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102711872566395734071994891 154067808849593601107992337)
  ·
    refine ⟨115550856637195200830994253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154067808849593601107992337 115550856637195200830994253)
    ·
      refine ⟨43331571238948200311622845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115550856637195200830994253 43331571238948200311622845)
      ·
        refine ⟨16249339214605575116858567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43331571238948200311622845 16249339214605575116858567)
        ·
          refine ⟨24374008821908362675287851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16249339214605575116858567 24374008821908362675287851)
          ·
            refine ⟨36561013232862544012931777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24374008821908362675287851 36561013232862544012931777)
            ·
              refine ⟨27420759924646908009698833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36561013232862544012931777 27420759924646908009698833)
              ·
                refine ⟨20565569943485181007274125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27420759924646908009698833 20565569943485181007274125)
                ·
                  refine ⟨7712088728806942877727797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20565569943485181007274125 7712088728806942877727797)
                  ·
                    refine ⟨723008318325650894786981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7712088728806942877727797 723008318325650894786981)
                    ·
                      rfl

theorem cell23_4224161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_4224161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224161 prefixEnd_4224161 := by exact prefixLift 4224161
  have htrace : WordTrace (prefixWord ++ tailWord_4224161) baseStart_4224161 baseEnd_4224161 := by
    simpa [prefixWord, tailWord_4224161, baseEnd_4224161] using wordTrace_append hprefix tailTrace_4224161
  have hstable : (prefixWord ++ tailWord_4224161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224161).length < 2 ^ (prefixWord ++ tailWord_4224161).sum := by decide
  have hdescent : baseEnd_4224161 < baseStart_4224161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224178 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_4224178 : Nat := 118140960795 + 4224178 * 2 ^ 59
def prefixEnd_4224178 : Nat := 4983230072969 + 3 ^ 40 * 4224178 * 2
def baseEnd_4224178 : Nat := 723011228049359705949455

theorem tailTrace_4224178 : CollatzResearch.WordTrace tailWord_4224178 prefixEnd_4224178 723011228049359705949455 := by
  unfold tailWord_4224178
  simp only [CollatzResearch.WordTrace]
  refine ⟨38517107222633003252840297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102712285927021342007574125 38517107222633003252840297)
  ·
    refine ⟨28887830416974752439630223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38517107222633003252840297 28887830416974752439630223)
    ·
      refine ⟨43331745625462128659445335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28887830416974752439630223 43331745625462128659445335)
      ·
        refine ⟨64997618438193192989168003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43331745625462128659445335 64997618438193192989168003)
        ·
          refine ⟨97496427657289789483752005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64997618438193192989168003 97496427657289789483752005)
          ·
            refine ⟨18280580185741835528203501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97496427657289789483752005 18280580185741835528203501)
            ·
              refine ⟨6855217569653188323076313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18280580185741835528203501 6855217569653188323076313)
              ·
                refine ⟨5141413177239891242307235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855217569653188323076313 5141413177239891242307235)
                ·
                  refine ⟨7712119765859836863460853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5141413177239891242307235 7712119765859836863460853)
                  ·
                    refine ⟨723011228049359705949455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7712119765859836863460853 723011228049359705949455)
                    ·
                      rfl

theorem cell23_4224178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_4224178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224178 prefixEnd_4224178 := by exact prefixLift 4224178
  have htrace : WordTrace (prefixWord ++ tailWord_4224178) baseStart_4224178 baseEnd_4224178 := by
    simpa [prefixWord, tailWord_4224178, baseEnd_4224178] using wordTrace_append hprefix tailTrace_4224178
  have hstable : (prefixWord ++ tailWord_4224178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224178).length < 2 ^ (prefixWord ++ tailWord_4224178).sum := by decide
  have hdescent : baseEnd_4224178 < baseStart_4224178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224185 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 2, 3, 2]
def baseStart_4224185 : Nat := 118140960795 + 4224185 * 2 ^ 59
def prefixEnd_4224185 : Nat := 4983230072969 + 3 ^ 40 * 4224185 * 2
def baseEnd_4224185 : Nat := 2169037278512660590460833

theorem tailTrace_4224185 : CollatzResearch.WordTrace tailWord_4224185 prefixEnd_4224185 2169037278512660590460833 := by
  unfold tailWord_4224185
  simp only [CollatzResearch.WordTrace]
  refine ⟨154068684201506653206866009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102712456134337768804577339 154068684201506653206866009)
  ·
    refine ⟨115551513151129989905149507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154068684201506653206866009 115551513151129989905149507)
    ·
      refine ⟨173327269726694984857724261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115551513151129989905149507 173327269726694984857724261)
      ·
        refine ⟨32498863073755309660823299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173327269726694984857724261 32498863073755309660823299)
        ·
          refine ⟨48748294610632964491234949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32498863073755309660823299 48748294610632964491234949)
          ·
            refine ⟨9140305239493680842106553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48748294610632964491234949 9140305239493680842106553)
            ·
              refine ⟨6855228929620260631579915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9140305239493680842106553 6855228929620260631579915)
              ·
                refine ⟨10282843394430390947369873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6855228929620260631579915 10282843394430390947369873)
                ·
                  refine ⟨7712132545822793210527405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10282843394430390947369873 7712132545822793210527405)
                  ·
                    refine ⟨2892049704683547453947777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7712132545822793210527405 2892049704683547453947777)
                    ·
                      refine ⟨2169037278512660590460833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892049704683547453947777 2169037278512660590460833)
                      ·
                        rfl

theorem cell23_4224185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_4224185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224185 prefixEnd_4224185 := by exact prefixLift 4224185
  have htrace : WordTrace (prefixWord ++ tailWord_4224185) baseStart_4224185 baseEnd_4224185 := by
    simpa [prefixWord, tailWord_4224185, baseEnd_4224185] using wordTrace_append hprefix tailTrace_4224185
  have hstable : (prefixWord ++ tailWord_4224185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224185).length < 2 ^ (prefixWord ++ tailWord_4224185).sum := by decide
  have hdescent : baseEnd_4224185 < baseStart_4224185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224191 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 6, 4]
def baseStart_4224191 : Nat := 118140960795 + 4224191 * 2 ^ 59
def prefixEnd_4224191 : Nat := 4983230072969 + 3 ^ 40 * 4224191 * 2
def baseEnd_4224191 : Nat := 723013453132195855661935

theorem tailTrace_4224191 : CollatzResearch.WordTrace tailWord_4224191 prefixEnd_4224191 723013453132195855661935 := by
  unfold tailWord_4224191
  simp only [CollatzResearch.WordTrace]
  refine ⟨154068903039484916231584427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102712602026323277487722951 154068903039484916231584427)
  ·
    refine ⟨231103354559227374347376641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154068903039484916231584427 231103354559227374347376641)
    ·
      refine ⟨173327515919420530760532481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231103354559227374347376641 173327515919420530760532481)
      ·
        refine ⟨129995636939565398070399361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173327515919420530760532481 129995636939565398070399361)
        ·
          refine ⟨97496727704674048552799521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129995636939565398070399361 97496727704674048552799521)
          ·
            refine ⟨73122545778505536414599641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97496727704674048552799521 73122545778505536414599641)
            ·
              refine ⟨54841909333879152310949731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73122545778505536414599641 54841909333879152310949731)
              ·
                refine ⟨82262864000818728466424597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54841909333879152310949731 82262864000818728466424597)
                ·
                  refine ⟨3856071750038377896863653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82262864000818728466424597 3856071750038377896863653)
                  ·
                    refine ⟨723013453132195855661935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856071750038377896863653 723013453132195855661935)
                    ·
                      rfl

theorem cell23_4224191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_4224191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224191 prefixEnd_4224191 := by exact prefixLift 4224191
  have htrace : WordTrace (prefixWord ++ tailWord_4224191) baseStart_4224191 baseEnd_4224191 := by
    simpa [prefixWord, tailWord_4224191, baseEnd_4224191] using wordTrace_append hprefix tailTrace_4224191
  have hstable : (prefixWord ++ tailWord_4224191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224191).length < 2 ^ (prefixWord ++ tailWord_4224191).sum := by decide
  have hdescent : baseEnd_4224191 < baseStart_4224191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224204 : List Nat := [2, 2, 1, 18]
def baseStart_4224204 : Nat := 118140960795 + 4224204 * 2 ^ 59
def prefixEnd_4224204 : Nat := 4983230072969 + 3 ^ 40 * 4224204 * 2
def baseEnd_4224204 : Nat := 991791053792910844135

theorem tailTrace_4224204 : CollatzResearch.WordTrace tailWord_4224204 prefixEnd_4224204 991791053792910844135 := by
  unfold tailWord_4224204
  simp only [CollatzResearch.WordTrace]
  refine ⟨77034688594218909725903833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102712918125625212967871777 77034688594218909725903833)
  ·
    refine ⟨57776016445664182294427875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77034688594218909725903833 57776016445664182294427875)
    ·
      refine ⟨86664024668496273441641813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57776016445664182294427875 86664024668496273441641813)
      ·
        refine ⟨991791053792910844135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 86664024668496273441641813 991791053792910844135)
        ·
          rfl

theorem cell23_4224204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 18].length) (baseStart_4224204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224204 prefixEnd_4224204 := by exact prefixLift 4224204
  have htrace : WordTrace (prefixWord ++ tailWord_4224204) baseStart_4224204 baseEnd_4224204 := by
    simpa [prefixWord, tailWord_4224204, baseEnd_4224204] using wordTrace_append hprefix tailTrace_4224204
  have hstable : (prefixWord ++ tailWord_4224204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224204).length < 2 ^ (prefixWord ++ tailWord_4224204).sum := by decide
  have hdescent : baseEnd_4224204 < baseStart_4224204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224292 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_4224292 : Nat := 118140960795 + 4224292 * 2 ^ 59
def prefixEnd_4224292 : Nat := 4983230072969 + 3 ^ 40 * 4224292 * 2
def baseEnd_4224292 : Nat := 2169092220942691671822841

theorem tailTrace_4224292 : CollatzResearch.WordTrace tailWord_4224292 prefixEnd_4224292 2169092220942691671822841 := by
  unfold tailWord_4224292
  simp only [CollatzResearch.WordTrace]
  refine ⟨77036293406059505240505565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102715057874746006987340753 77036293406059505240505565)
  ·
    refine ⟨28888610027272314465189587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77036293406059505240505565 28888610027272314465189587)
    ·
      refine ⟨43332915040908471697784381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28888610027272314465189587 43332915040908471697784381)
      ·
        refine ⟨16249843140340676886669143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43332915040908471697784381 16249843140340676886669143)
        ·
          refine ⟨24374764710511015330003715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16249843140340676886669143 24374764710511015330003715)
          ·
            refine ⟨36562147065766522995005573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24374764710511015330003715 36562147065766522995005573)
            ·
              refine ⟨6855402574831223061563545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36562147065766522995005573 6855402574831223061563545)
              ·
                refine ⟨5141551931123417296172659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855402574831223061563545 5141551931123417296172659)
                ·
                  refine ⟨7712327896685125944258989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5141551931123417296172659 7712327896685125944258989)
                  ·
                    refine ⟨2892122961256922229097121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7712327896685125944258989 2892122961256922229097121)
                    ·
                      refine ⟨2169092220942691671822841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892122961256922229097121 2169092220942691671822841)
                      ·
                        rfl

theorem cell23_4224292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_4224292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224292 prefixEnd_4224292 := by exact prefixLift 4224292
  have htrace : WordTrace (prefixWord ++ tailWord_4224292) baseStart_4224292 baseEnd_4224292 := by
    simpa [prefixWord, tailWord_4224292, baseEnd_4224292] using wordTrace_append hprefix tailTrace_4224292
  have hstable : (prefixWord ++ tailWord_4224292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224292).length < 2 ^ (prefixWord ++ tailWord_4224292).sum := by decide
  have hdescent : baseEnd_4224292 < baseStart_4224292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224333 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4224333 : Nat := 118140960795 + 4224333 * 2 ^ 59
def prefixEnd_4224333 : Nat := 4983230072969 + 3 ^ 40 * 4224333 * 2
def baseEnd_4224333 : Nat := 2169113273649526011410153

theorem tailTrace_4224333 : CollatzResearch.WordTrace tailWord_4224333 prefixEnd_4224333 2169113273649526011410153 := by
  unfold tailWord_4224333
  simp only [CollatzResearch.WordTrace]
  refine ⟨154074082204970474483253653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102716054803313649655502435 154074082204970474483253653)
  ·
    refine ⟨7222222603357990991402515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154074082204970474483253653 7222222603357990991402515)
    ·
      refine ⟨10833333905036986487103773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7222222603357990991402515 10833333905036986487103773)
      ·
        refine ⟨4062500214388869932663915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10833333905036986487103773 4062500214388869932663915)
        ·
          refine ⟨6093750321583304898995873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4062500214388869932663915 6093750321583304898995873)
          ·
            refine ⟨4570312741187478674246905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6093750321583304898995873 4570312741187478674246905)
            ·
              refine ⟨3427734555890609005685179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4570312741187478674246905 3427734555890609005685179)
              ·
                refine ⟨5141601833835913508527769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427734555890609005685179 5141601833835913508527769)
                ·
                  refine ⟨3856201375376935131395827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5141601833835913508527769 3856201375376935131395827)
                  ·
                    refine ⟨5784302063065402697093741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856201375376935131395827 5784302063065402697093741)
                    ·
                      refine ⟨2169113273649526011410153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784302063065402697093741 2169113273649526011410153)
                      ·
                        rfl

theorem cell23_4224333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4224333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224333 prefixEnd_4224333 := by exact prefixLift 4224333
  have htrace : WordTrace (prefixWord ++ tailWord_4224333) baseStart_4224333 baseEnd_4224333 := by
    simpa [prefixWord, tailWord_4224333, baseEnd_4224333] using wordTrace_append hprefix tailTrace_4224333
  have hstable : (prefixWord ++ tailWord_4224333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224333).length < 2 ^ (prefixWord ++ tailWord_4224333).sum := by decide
  have hdescent : baseEnd_4224333 < baseStart_4224333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224338 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_4224338 : Nat := 118140960795 + 4224338 * 2 ^ 59
def prefixEnd_4224338 : Nat := 4983230072969 + 3 ^ 40 * 4224338 * 2
def baseEnd_4224338 : Nat := 2169115841052798491847629

theorem tailTrace_4224338 : CollatzResearch.WordTrace tailWord_4224338 prefixEnd_4224338 2169115841052798491847629 := by
  unfold tailWord_4224338
  simp only [CollatzResearch.WordTrace]
  refine ⟨38518566142488090084296417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102716176379968240224790445 38518566142488090084296417)
  ·
    refine ⟨28888924606866067563222313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38518566142488090084296417 28888924606866067563222313)
    ·
      refine ⟨21666693455149550672416735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28888924606866067563222313 21666693455149550672416735)
      ·
        refine ⟨32500040182724326008625103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21666693455149550672416735 32500040182724326008625103)
        ·
          refine ⟨48750060274086489012937655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32500040182724326008625103 48750060274086489012937655)
          ·
            refine ⟨73125090411129733519406483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48750060274086489012937655 73125090411129733519406483)
            ·
              refine ⟨109687635616694600279109725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73125090411129733519406483 109687635616694600279109725)
              ·
                refine ⟨41132863356260475104666147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109687635616694600279109725 41132863356260475104666147)
                ·
                  refine ⟨61699295034390712656999221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41132863356260475104666147 61699295034390712656999221)
                  ·
                    refine ⟨5784308909474129311593677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61699295034390712656999221 5784308909474129311593677)
                    ·
                      refine ⟨2169115841052798491847629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784308909474129311593677 2169115841052798491847629)
                      ·
                        rfl

theorem cell23_4224338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_4224338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224338 prefixEnd_4224338 := by exact prefixLift 4224338
  have htrace : WordTrace (prefixWord ++ tailWord_4224338) baseStart_4224338 baseEnd_4224338 := by
    simpa [prefixWord, tailWord_4224338, baseEnd_4224338] using wordTrace_append hprefix tailTrace_4224338
  have hstable : (prefixWord ++ tailWord_4224338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224338).length < 2 ^ (prefixWord ++ tailWord_4224338).sum := by decide
  have hdescent : baseEnd_4224338 < baseStart_4224338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224351 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_4224351 : Nat := 118140960795 + 4224351 * 2 ^ 59
def prefixEnd_4224351 : Nat := 4983230072969 + 3 ^ 40 * 4224351 * 2
def baseEnd_4224351 : Nat := 2169122516301306940985069

theorem tailTrace_4224351 : CollatzResearch.WordTrace tailWord_4224351 prefixEnd_4224351 2169122516301306940985069 := by
  unfold tailWord_4224351
  simp only [CollatzResearch.WordTrace]
  refine ⟨154074738718905263557408907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102716492479270175704939271 154074738718905263557408907)
  ·
    refine ⟨231112108078357895336113361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154074738718905263557408907 231112108078357895336113361)
    ·
      refine ⟨173334081058768421502085021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231112108078357895336113361 173334081058768421502085021)
      ·
        refine ⟨65000280397038158063281883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173334081058768421502085021 65000280397038158063281883)
        ·
          refine ⟨97500420595557237094922825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65000280397038158063281883 97500420595557237094922825)
          ·
            refine ⟨73125315446667927821192119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97500420595557237094922825 73125315446667927821192119)
            ·
              refine ⟨109687973170001891731788179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73125315446667927821192119 109687973170001891731788179)
              ·
                refine ⟨164531959755002837597682269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109687973170001891731788179 164531959755002837597682269)
                ·
                  refine ⟨61699484908126064099130851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164531959755002837597682269 61699484908126064099130851)
                  ·
                    refine ⟨92549227362189096148696277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61699484908126064099130851 92549227362189096148696277)
                    ·
                      refine ⟨2169122516301306940985069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92549227362189096148696277 2169122516301306940985069)
                      ·
                        rfl

theorem cell23_4224351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_4224351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224351 prefixEnd_4224351 := by exact prefixLift 4224351
  have htrace : WordTrace (prefixWord ++ tailWord_4224351) baseStart_4224351 baseEnd_4224351 := by
    simpa [prefixWord, tailWord_4224351, baseEnd_4224351] using wordTrace_append hprefix tailTrace_4224351
  have hstable : (prefixWord ++ tailWord_4224351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224351).length < 2 ^ (prefixWord ++ tailWord_4224351).sum := by decide
  have hdescent : baseEnd_4224351 < baseStart_4224351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224395 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 2, 4, 2]
def baseStart_4224395 : Nat := 118140960795 + 4224395 * 2 ^ 59
def prefixEnd_4224395 : Nat := 4983230072969 + 3 ^ 40 * 4224395 * 2
def baseEnd_4224395 : Nat := 2169145109450104768834867

theorem tailTrace_4224395 : CollatzResearch.WordTrace tailWord_4224395 prefixEnd_4224395 2169145109450104768834867 := by
  unfold tailWord_4224395
  simp only [CollatzResearch.WordTrace]
  refine ⟨154076343530745859072010639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102717562353830572714673759 154076343530745859072010639)
  ·
    refine ⟨231114515296118788608015959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154076343530745859072010639 231114515296118788608015959)
    ·
      refine ⟨346671772944178182912023939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231114515296118788608015959 346671772944178182912023939)
      ·
        refine ⟨520007659416267274368035909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346671772944178182912023939 520007659416267274368035909)
        ·
          refine ⟨97501436140550113944006733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 520007659416267274368035909 97501436140550113944006733)
          ·
            refine ⟨36563038552706292729002525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97501436140550113944006733 36563038552706292729002525)
            ·
              refine ⟨13711139457264859773375947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36563038552706292729002525 13711139457264859773375947)
              ·
                refine ⟨20566709185897289660063921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13711139457264859773375947 20566709185897289660063921)
                ·
                  refine ⟨15425031889422967245047941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20566709185897289660063921 15425031889422967245047941)
                  ·
                    refine ⟨2892193479266806358446489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15425031889422967245047941 2892193479266806358446489)
                    ·
                      refine ⟨2169145109450104768834867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892193479266806358446489 2169145109450104768834867)
                      ·
                        rfl

theorem cell23_4224395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4, 2].length) (baseStart_4224395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224395 prefixEnd_4224395 := by exact prefixLift 4224395
  have htrace : WordTrace (prefixWord ++ tailWord_4224395) baseStart_4224395 baseEnd_4224395 := by
    simpa [prefixWord, tailWord_4224395, baseEnd_4224395] using wordTrace_append hprefix tailTrace_4224395
  have hstable : (prefixWord ++ tailWord_4224395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224395).length < 2 ^ (prefixWord ++ tailWord_4224395).sum := by decide
  have hdescent : baseEnd_4224395 < baseStart_4224395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224412 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4224412 : Nat := 118140960795 + 4224412 * 2 ^ 59
def prefixEnd_4224412 : Nat := 4983230072969 + 3 ^ 40 * 4224412 * 2
def baseEnd_4224412 : Nat := 2169153838621231202322289

theorem tailTrace_4224412 : CollatzResearch.WordTrace tailWord_4224412 prefixEnd_4224412 2169153838621231202322289 := by
  unfold tailWord_4224412
  simp only [CollatzResearch.WordTrace]
  refine ⟨77038481785842135487689745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102717975714456180650252993 77038481785842135487689745)
  ·
    refine ⟨57778861339381601615767309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77038481785842135487689745 57778861339381601615767309)
    ·
      refine ⟨21667073002268100605912741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57778861339381601615767309 21667073002268100605912741)
      ·
        refine ⟨4062576187925268863608639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21667073002268100605912741 4062576187925268863608639)
        ·
          refine ⟨6093864281887903295412959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4062576187925268863608639 6093864281887903295412959)
          ·
            refine ⟨9140796422831854943119439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6093864281887903295412959 9140796422831854943119439)
            ·
              refine ⟨13711194634247782414679159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9140796422831854943119439 13711194634247782414679159)
              ·
                refine ⟨20566791951371673622018739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13711194634247782414679159 20566791951371673622018739)
                ·
                  refine ⟨30850187927057510433028109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20566791951371673622018739 30850187927057510433028109)
                  ·
                    refine ⟨11568820472646566412385541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30850187927057510433028109 11568820472646566412385541)
                    ·
                      refine ⟨2169153838621231202322289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11568820472646566412385541 2169153838621231202322289)
                      ·
                        rfl

theorem cell23_4224412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4224412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224412 prefixEnd_4224412 := by exact prefixLift 4224412
  have htrace : WordTrace (prefixWord ++ tailWord_4224412) baseStart_4224412 baseEnd_4224412 := by
    simpa [prefixWord, tailWord_4224412, baseEnd_4224412] using wordTrace_append hprefix tailTrace_4224412
  have hstable : (prefixWord ++ tailWord_4224412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224412).length < 2 ^ (prefixWord ++ tailWord_4224412).sum := by decide
  have hdescent : baseEnd_4224412 < baseStart_4224412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224415 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 3]
def baseStart_4224415 : Nat := 118140960795 + 4224415 * 2 ^ 59
def prefixEnd_4224415 : Nat := 4983230072969 + 3 ^ 40 * 4224415 * 2
def baseEnd_4224415 : Nat := 2169155379063194690584775

theorem tailTrace_4224415 : CollatzResearch.WordTrace tailWord_4224415 prefixEnd_4224415 2169155379063194690584775 := by
  unfold tailWord_4224415
  simp only [CollatzResearch.WordTrace]
  refine ⟨154077072990673402487738699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102718048660448934991825799 154077072990673402487738699)
  ·
    refine ⟨231115609486010103731608049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154077072990673402487738699 231115609486010103731608049)
    ·
      refine ⟨173336707114507577798706037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231115609486010103731608049 173336707114507577798706037)
      ·
        refine ⟨16250316291985085418628691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173336707114507577798706037 16250316291985085418628691)
        ·
          refine ⟨24375474437977628127943037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16250316291985085418628691 24375474437977628127943037)
          ·
            refine ⟨9140802914241610547978639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24375474437977628127943037 9140802914241610547978639)
            ·
              refine ⟨13711204371362415821967959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9140802914241610547978639 13711204371362415821967959)
              ·
                refine ⟨20566806557043623732951939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13711204371362415821967959 20566806557043623732951939)
                ·
                  refine ⟨30850209835565435599427909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20566806557043623732951939 30850209835565435599427909)
                  ·
                    refine ⟨5784414344168519174892733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30850209835565435599427909 5784414344168519174892733)
                    ·
                      refine ⟨2169155379063194690584775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784414344168519174892733 2169155379063194690584775)
                      ·
                        rfl

theorem cell23_4224415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_4224415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224415 prefixEnd_4224415 := by exact prefixLift 4224415
  have htrace : WordTrace (prefixWord ++ tailWord_4224415) baseStart_4224415 baseEnd_4224415 := by
    simpa [prefixWord, tailWord_4224415, baseEnd_4224415] using wordTrace_append hprefix tailTrace_4224415
  have hstable : (prefixWord ++ tailWord_4224415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224415).length < 2 ^ (prefixWord ++ tailWord_4224415).sum := by decide
  have hdescent : baseEnd_4224415 < baseStart_4224415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224448 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 5, 5]
def baseStart_4224448 : Nat := 118140960795 + 4224448 * 2 ^ 59
def prefixEnd_4224448 : Nat := 4983230072969 + 3 ^ 40 * 4224448 * 2
def baseEnd_4224448 : Nat := 723057441308264353824041

theorem tailTrace_4224448 : CollatzResearch.WordTrace tailWord_4224448 prefixEnd_4224448 723057441308264353824041 := by
  unfold tailWord_4224448
  simp only [CollatzResearch.WordTrace]
  refine ⟨77039138299776924561844999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102718851066369232749126665 77039138299776924561844999)
  ·
    refine ⟨115558707449665386842767499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77039138299776924561844999 115558707449665386842767499)
    ·
      refine ⟨173338061174498080264151249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115558707449665386842767499 173338061174498080264151249)
      ·
        refine ⟨130003545880873560198113437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173338061174498080264151249 130003545880873560198113437)
        ·
          refine ⟨48751329705327585074292539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130003545880873560198113437 48751329705327585074292539)
          ·
            refine ⟨73126994557991377611438809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48751329705327585074292539 73126994557991377611438809)
            ·
              refine ⟨54845245918493533208579107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73126994557991377611438809 54845245918493533208579107)
              ·
                refine ⟨82267868877740299812868661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54845245918493533208579107 82267868877740299812868661)
                ·
                  refine ⟨7712612707288153107456437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82267868877740299812868661 7712612707288153107456437)
                  ·
                    refine ⟨723057441308264353824041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7712612707288153107456437 723057441308264353824041)
                    ·
                      rfl

theorem cell23_4224448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_4224448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224448 prefixEnd_4224448 := by exact prefixLift 4224448
  have htrace : WordTrace (prefixWord ++ tailWord_4224448) baseStart_4224448 baseEnd_4224448 := by
    simpa [prefixWord, tailWord_4224448, baseEnd_4224448] using wordTrace_append hprefix tailTrace_4224448
  have hstable : (prefixWord ++ tailWord_4224448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224448).length < 2 ^ (prefixWord ++ tailWord_4224448).sum := by decide
  have hdescent : baseEnd_4224448 < baseStart_4224448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224455 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_4224455 : Nat := 118140960795 + 4224455 * 2 ^ 59
def prefixEnd_4224455 : Nat := 4983230072969 + 3 ^ 40 * 4224455 * 2
def baseEnd_4224455 : Nat := 2169175918289374534084591

theorem tailTrace_4224455 : CollatzResearch.WordTrace tailWord_4224455 prefixEnd_4224455 2169175918289374534084591 := by
  unfold tailWord_4224455
  simp only [CollatzResearch.WordTrace]
  refine ⟨154078531910528489319194819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102719021273685659546129879 154078531910528489319194819)
  ·
    refine ⟨231117797865792733978792229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154078531910528489319194819 231117797865792733978792229)
    ·
      refine ⟨43334587099836137621023543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231117797865792733978792229 43334587099836137621023543)
      ·
        refine ⟨65001880649754206431535315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43334587099836137621023543 65001880649754206431535315)
        ·
          refine ⟨97502820974631309647302973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65001880649754206431535315 97502820974631309647302973)
          ·
            refine ⟨36563557865486741117738615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97502820974631309647302973 36563557865486741117738615)
            ·
              refine ⟨54845336798230111676607923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36563557865486741117738615 54845336798230111676607923)
              ·
                refine ⟨82268005197345167514911885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54845336798230111676607923 82268005197345167514911885)
                ·
                  refine ⟨30850501949004437818091957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82268005197345167514911885 30850501949004437818091957)
                  ·
                    refine ⟨2892234557719166045446121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30850501949004437818091957 2892234557719166045446121)
                    ·
                      refine ⟨2169175918289374534084591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892234557719166045446121 2169175918289374534084591)
                      ·
                        rfl

theorem cell23_4224455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_4224455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224455 prefixEnd_4224455 := by exact prefixLift 4224455
  have htrace : WordTrace (prefixWord ++ tailWord_4224455) baseStart_4224455 baseEnd_4224455 := by
    simpa [prefixWord, tailWord_4224455, baseEnd_4224455] using wordTrace_append hprefix tailTrace_4224455
  have hstable : (prefixWord ++ tailWord_4224455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224455).length < 2 ^ (prefixWord ++ tailWord_4224455).sum := by decide
  have hdescent : baseEnd_4224455 < baseStart_4224455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224462 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_4224462 : Nat := 118140960795 + 4224462 * 2 ^ 59
def prefixEnd_4224462 : Nat := 4983230072969 + 3 ^ 40 * 4224462 * 2
def baseEnd_4224462 : Nat := 2169179512653956006697059

theorem tailTrace_4224462 : CollatzResearch.WordTrace tailWord_4224462 prefixEnd_4224462 2169179512653956006697059 := by
  unfold tailWord_4224462
  simp only [CollatzResearch.WordTrace]
  refine ⟨19259848402687891189337455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102719191481002086343133093 19259848402687891189337455)
  ·
    refine ⟨28889772604031836784006183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19259848402687891189337455 28889772604031836784006183)
    ·
      refine ⟨43334658906047755176009275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28889772604031836784006183 43334658906047755176009275)
      ·
        refine ⟨65001988359071632764013913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43334658906047755176009275 65001988359071632764013913)
        ·
          refine ⟨48751491269303724573010435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65001988359071632764013913 48751491269303724573010435)
          ·
            refine ⟨73127236903955586859515653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48751491269303724573010435 73127236903955586859515653)
            ·
              refine ⟨13711356919491672536159185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73127236903955586859515653 13711356919491672536159185)
              ·
                refine ⟨10283517689618754402119389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13711356919491672536159185 10283517689618754402119389)
                ·
                  refine ⟨3856319133607032900794771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10283517689618754402119389 3856319133607032900794771)
                  ·
                    refine ⟨5784478700410549351192157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856319133607032900794771 5784478700410549351192157)
                    ·
                      refine ⟨2169179512653956006697059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784478700410549351192157 2169179512653956006697059)
                      ·
                        rfl

theorem cell23_4224462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_4224462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224462 prefixEnd_4224462 := by exact prefixLift 4224462
  have htrace : WordTrace (prefixWord ++ tailWord_4224462) baseStart_4224462 baseEnd_4224462 := by
    simpa [prefixWord, tailWord_4224462, baseEnd_4224462] using wordTrace_append hprefix tailTrace_4224462
  have hstable : (prefixWord ++ tailWord_4224462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224462).length < 2 ^ (prefixWord ++ tailWord_4224462).sum := by decide
  have hdescent : baseEnd_4224462 < baseStart_4224462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224495 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 4, 4]
def baseStart_4224495 : Nat := 118140960795 + 4224495 * 2 ^ 59
def prefixEnd_4224495 : Nat := 4983230072969 + 3 ^ 40 * 4224495 * 2
def baseEnd_4224495 : Nat := 723065485838518125861469

theorem tailTrace_4224495 : CollatzResearch.WordTrace tailWord_4224495 prefixEnd_4224495 723065485838518125861469 := by
  unfold tailWord_4224495
  simp only [CollatzResearch.WordTrace]
  refine ⟨154079990830383576150650939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102719993886922384100433959 154079990830383576150650939)
  ·
    refine ⟨231119986245575364225976409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154079990830383576150650939 231119986245575364225976409)
    ·
      refine ⟨173339989684181523169482307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231119986245575364225976409 173339989684181523169482307)
      ·
        refine ⟨260009984526272284754223461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173339989684181523169482307 260009984526272284754223461)
        ·
          refine ⟨48751872098676053391416899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260009984526272284754223461 48751872098676053391416899)
          ·
            refine ⟨73127808148014080087125349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48751872098676053391416899 73127808148014080087125349)
            ·
              refine ⟨13711464027752640016336003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73127808148014080087125349 13711464027752640016336003)
              ·
                refine ⟨20567196041628960024504005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13711464027752640016336003 20567196041628960024504005)
                ·
                  refine ⟨3856349257805430004594501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20567196041628960024504005 3856349257805430004594501)
                  ·
                    refine ⟨723065485838518125861469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856349257805430004594501 723065485838518125861469)
                    ·
                      rfl

theorem cell23_4224495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_4224495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224495 prefixEnd_4224495 := by exact prefixLift 4224495
  have htrace : WordTrace (prefixWord ++ tailWord_4224495) baseStart_4224495 baseEnd_4224495 := by
    simpa [prefixWord, tailWord_4224495, baseEnd_4224495] using wordTrace_append hprefix tailTrace_4224495
  have hstable : (prefixWord ++ tailWord_4224495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224495).length < 2 ^ (prefixWord ++ tailWord_4224495).sum := by decide
  have hdescent : baseEnd_4224495 < baseStart_4224495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224496 : List Nat := [2, 1, 1, 1, 3, 5, 3, 2, 1, 1, 3]
def baseStart_4224496 : Nat := 118140960795 + 4224496 * 2 ^ 59
def prefixEnd_4224496 : Nat := 4983230072969 + 3 ^ 40 * 4224496 * 2
def baseEnd_4224496 : Nat := 2169196970996208873671903

theorem tailTrace_4224496 : CollatzResearch.WordTrace tailWord_4224496 prefixEnd_4224496 2169196970996208873671903 := by
  unfold tailWord_4224496
  simp only [CollatzResearch.WordTrace]
  refine ⟨77040013651689976660718671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102720018202253302214291561 77040013651689976660718671)
  ·
    refine ⟨115560020477534964991078007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77040013651689976660718671 115560020477534964991078007)
    ·
      refine ⟨173340030716302447486617011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115560020477534964991078007 173340030716302447486617011)
      ·
        refine ⟨260010046074453671229925517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173340030716302447486617011 260010046074453671229925517)
        ·
          refine ⟨97503767277920126711222069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260010046074453671229925517 97503767277920126711222069)
          ·
            refine ⟨9140978182305011879177069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97503767277920126711222069 9140978182305011879177069)
            ·
              refine ⟨3427866818364379454691401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9140978182305011879177069 3427866818364379454691401)
              ·
                refine ⟨2570900113773284591018551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3427866818364379454691401 2570900113773284591018551)
                ·
                  refine ⟨3856350170659926886527827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570900113773284591018551 3856350170659926886527827)
                  ·
                    refine ⟨5784525255989890329791741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856350170659926886527827 5784525255989890329791741)
                    ·
                      refine ⟨2169196970996208873671903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784525255989890329791741 2169196970996208873671903)
                      ·
                        rfl

theorem cell23_4224496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 1, 3].length) (baseStart_4224496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224496 prefixEnd_4224496 := by exact prefixLift 4224496
  have htrace : WordTrace (prefixWord ++ tailWord_4224496) baseStart_4224496 baseEnd_4224496 := by
    simpa [prefixWord, tailWord_4224496, baseEnd_4224496] using wordTrace_append hprefix tailTrace_4224496
  have hstable : (prefixWord ++ tailWord_4224496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224496).length < 2 ^ (prefixWord ++ tailWord_4224496).sum := by decide
  have hdescent : baseEnd_4224496 < baseStart_4224496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224505 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 3]
def baseStart_4224505 : Nat := 118140960795 + 4224505 * 2 ^ 59
def prefixEnd_4224505 : Nat := 4983230072969 + 3 ^ 40 * 4224505 * 2
def baseEnd_4224505 : Nat := 2169201592322099338459361

theorem tailTrace_4224505 : CollatzResearch.WordTrace tailWord_4224505 prefixEnd_4224505 2169201592322099338459361 := by
  unfold tailWord_4224505
  simp only [CollatzResearch.WordTrace]
  refine ⟨154080355560347347858514969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102720237040231565239009979 154080355560347347858514969)
  ·
    refine ⟨115560266670260510893886227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154080355560347347858514969 115560266670260510893886227)
    ·
      refine ⟨173340400005390766340829341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115560266670260510893886227 173340400005390766340829341)
      ·
        refine ⟨65002650002021537377811003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173340400005390766340829341 65002650002021537377811003)
        ·
          refine ⟨97503975003032306066716505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65002650002021537377811003 97503975003032306066716505)
          ·
            refine ⟨73127981252274229550037379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97503975003032306066716505 73127981252274229550037379)
            ·
              refine ⟨109691971878411344325056069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73127981252274229550037379 109691971878411344325056069)
              ·
                refine ⟨20567244727202127060948013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109691971878411344325056069 20567244727202127060948013)
                ·
                  refine ⟨7712716772700797647855505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20567244727202127060948013 7712716772700797647855505)
                  ·
                    refine ⟨5784537579525598235891629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7712716772700797647855505 5784537579525598235891629)
                    ·
                      refine ⟨2169201592322099338459361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784537579525598235891629 2169201592322099338459361)
                      ·
                        rfl

theorem cell23_4224505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_4224505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224505 prefixEnd_4224505 := by exact prefixLift 4224505
  have htrace : WordTrace (prefixWord ++ tailWord_4224505) baseStart_4224505 baseEnd_4224505 := by
    simpa [prefixWord, tailWord_4224505, baseEnd_4224505] using wordTrace_append hprefix tailTrace_4224505
  have hstable : (prefixWord ++ tailWord_4224505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224505).length < 2 ^ (prefixWord ++ tailWord_4224505).sum := by decide
  have hdescent : baseEnd_4224505 < baseStart_4224505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224508 : List Nat := [2, 2, 2, 1, 2, 1, 3, 10]
def baseStart_4224508 : Nat := 118140960795 + 4224508 * 2 ^ 59
def prefixEnd_4224508 : Nat := 4983230072969 + 3 ^ 40 * 4224508 * 2
def baseEnd_4224508 : Nat := 80340856769039363952661

theorem tailTrace_4224508 : CollatzResearch.WordTrace tailWord_4224508 prefixEnd_4224508 80340856769039363952661 := by
  unfold tailWord_4224508
  simp only [CollatzResearch.WordTrace]
  refine ⟨77040232489668239685437089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102720309986224319580582785 77040232489668239685437089)
  ·
    refine ⟨57780174367251179764077817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77040232489668239685437089 57780174367251179764077817)
    ·
      refine ⟨43335130775438384823058363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57780174367251179764077817 43335130775438384823058363)
      ·
        refine ⟨65002696163157577234587545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43335130775438384823058363 65002696163157577234587545)
        ·
          refine ⟨48752022122368182925940659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65002696163157577234587545 48752022122368182925940659)
          ·
            refine ⟨73128033183552274388910989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48752022122368182925940659 73128033183552274388910989)
            ·
              refine ⟨27423012443832102895841621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73128033183552274388910989 27423012443832102895841621)
              ·
                refine ⟨80340856769039363952661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27423012443832102895841621 80340856769039363952661)
                ·
                  rfl

theorem cell23_4224508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 10].length) (baseStart_4224508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224508 prefixEnd_4224508 := by exact prefixLift 4224508
  have htrace : WordTrace (prefixWord ++ tailWord_4224508) baseStart_4224508 baseEnd_4224508 := by
    simpa [prefixWord, tailWord_4224508, baseEnd_4224508] using wordTrace_append hprefix tailTrace_4224508
  have hstable : (prefixWord ++ tailWord_4224508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224508).length < 2 ^ (prefixWord ++ tailWord_4224508).sum := by decide
  have hdescent : baseEnd_4224508 < baseStart_4224508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224516 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_4224516 : Nat := 118140960795 + 4224516 * 2 ^ 59
def prefixEnd_4224516 : Nat := 4983230072969 + 3 ^ 40 * 4224516 * 2
def baseEnd_4224516 : Nat := 723069080203099598473937

theorem tailTrace_4224516 : CollatzResearch.WordTrace tailWord_4224516 prefixEnd_4224516 723069080203099598473937 := by
  unfold tailWord_4224516
  simp only [CollatzResearch.WordTrace]
  refine ⟨77040378381653748368582701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102720504508871664491443601 77040378381653748368582701)
  ·
    refine ⟨28890141893120155638218513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77040378381653748368582701 28890141893120155638218513)
    ·
      refine ⟨21667606419840116728663885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28890141893120155638218513 21667606419840116728663885)
      ·
        refine ⟨8125352407440043773248957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21667606419840116728663885 8125352407440043773248957)
        ·
          refine ⟨3047007152790016414968359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8125352407440043773248957 3047007152790016414968359)
          ·
            refine ⟨4570510729185024622452539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047007152790016414968359 4570510729185024622452539)
            ·
              refine ⟨6855766093777536933678809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570510729185024622452539 6855766093777536933678809)
              ·
                refine ⟨5141824570333152700259107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855766093777536933678809 5141824570333152700259107)
                ·
                  refine ⟨7712736855499729050388661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5141824570333152700259107 7712736855499729050388661)
                  ·
                    refine ⟨723069080203099598473937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7712736855499729050388661 723069080203099598473937)
                    ·
                      rfl

theorem cell23_4224516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_4224516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224516 prefixEnd_4224516 := by exact prefixLift 4224516
  have htrace : WordTrace (prefixWord ++ tailWord_4224516) baseStart_4224516 baseEnd_4224516 := by
    simpa [prefixWord, tailWord_4224516, baseEnd_4224516] using wordTrace_append hprefix tailTrace_4224516
  have hstable : (prefixWord ++ tailWord_4224516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224516).length < 2 ^ (prefixWord ++ tailWord_4224516).sum := by decide
  have hdescent : baseEnd_4224516 < baseStart_4224516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224519 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_4224519 : Nat := 118140960795 + 4224519 * 2 ^ 59
def prefixEnd_4224519 : Nat := 4983230072969 + 3 ^ 40 * 4224519 * 2
def baseEnd_4224519 : Nat := 2169208781051262283684297

theorem tailTrace_4224519 : CollatzResearch.WordTrace tailWord_4224519 prefixEnd_4224519 2169208781051262283684297 := by
  unfold tailWord_4224519
  simp only [CollatzResearch.WordTrace]
  refine ⟨154080866182296628249524611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102720577454864418833016407 154080866182296628249524611)
  ·
    refine ⟨231121299273444942374286917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154080866182296628249524611 231121299273444942374286917)
    ·
      refine ⟨43335243613770926695178797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231121299273444942374286917 43335243613770926695178797)
      ·
        refine ⟨16250716355164097510692049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43335243613770926695178797 16250716355164097510692049)
        ·
          refine ⟨12188037266373073133019037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16250716355164097510692049 12188037266373073133019037)
          ·
            refine ⟨4570513974889902424882139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12188037266373073133019037 4570513974889902424882139)
            ·
              refine ⟨6855770962334853637323209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570513974889902424882139 6855770962334853637323209)
              ·
                refine ⟨5141828221751140227992407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855770962334853637323209 5141828221751140227992407)
                ·
                  refine ⟨7712742332626710341988611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5141828221751140227992407 7712742332626710341988611)
                  ·
                    refine ⟨11569113498940065512982917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7712742332626710341988611 11569113498940065512982917)
                    ·
                      refine ⟨2169208781051262283684297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11569113498940065512982917 2169208781051262283684297)
                      ·
                        rfl

theorem cell23_4224519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_4224519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224519 prefixEnd_4224519 := by exact prefixLift 4224519
  have htrace : WordTrace (prefixWord ++ tailWord_4224519) baseStart_4224519 baseEnd_4224519 := by
    simpa [prefixWord, tailWord_4224519, baseEnd_4224519] using wordTrace_append hprefix tailTrace_4224519
  have hstable : (prefixWord ++ tailWord_4224519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224519).length < 2 ^ (prefixWord ++ tailWord_4224519).sum := by decide
  have hdescent : baseEnd_4224519 < baseStart_4224519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224522 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_4224522 : Nat := 118140960795 + 4224522 * 2 ^ 59
def prefixEnd_4224522 : Nat := 4983230072969 + 3 ^ 40 * 4224522 * 2
def baseEnd_4224522 : Nat := 2169210321493225771946783

theorem tailTrace_4224522 : CollatzResearch.WordTrace tailWord_4224522 prefixEnd_4224522 2169210321493225771946783 := by
  unfold tailWord_4224522
  simp only [CollatzResearch.WordTrace]
  refine ⟨38520243900321439940470955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102720650400857173174589213 38520243900321439940470955)
  ·
    refine ⟨57780365850482159910706433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38520243900321439940470955 57780365850482159910706433)
    ·
      refine ⟨43335274387861619933029825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57780365850482159910706433 43335274387861619933029825)
      ·
        refine ⟨32501455790896214949772369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43335274387861619933029825 32501455790896214949772369)
        ·
          refine ⟨24376091843172161212329277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32501455790896214949772369 24376091843172161212329277)
          ·
            refine ⟨9141034441189560454623479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24376091843172161212329277 9141034441189560454623479)
            ·
              refine ⟨13711551661784340681935219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9141034441189560454623479 13711551661784340681935219)
              ·
                refine ⟨20567327492676511022902829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13711551661784340681935219 20567327492676511022902829)
                ·
                  refine ⟨7712747809753691633588561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20567327492676511022902829 7712747809753691633588561)
                  ·
                    refine ⟨5784560857315268725191421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7712747809753691633588561 5784560857315268725191421)
                    ·
                      refine ⟨2169210321493225771946783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784560857315268725191421 2169210321493225771946783)
                      ·
                        rfl

theorem cell23_4224522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_4224522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224522 prefixEnd_4224522 := by exact prefixLift 4224522
  have htrace : WordTrace (prefixWord ++ tailWord_4224522) baseStart_4224522 baseEnd_4224522 := by
    simpa [prefixWord, tailWord_4224522, baseEnd_4224522] using wordTrace_append hprefix tailTrace_4224522
  have hstable : (prefixWord ++ tailWord_4224522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224522).length < 2 ^ (prefixWord ++ tailWord_4224522).sum := by decide
  have hdescent : baseEnd_4224522 < baseStart_4224522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224569 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4224569 : Nat := 118140960795 + 4224569 * 2 ^ 59
def prefixEnd_4224569 : Nat := 4983230072969 + 3 ^ 40 * 4224569 * 2
def baseEnd_4224569 : Nat := 2169234455083987088059067

theorem tailTrace_4224569 : CollatzResearch.WordTrace tailWord_4224569 prefixEnd_4224569 2169234455083987088059067 := by
  unfold tailWord_4224569
  simp only [CollatzResearch.WordTrace]
  refine ⟨154082689832115486788844761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102721793221410324525896507 154082689832115486788844761)
  ·
    refine ⟨115562017374086615091633571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154082689832115486788844761 115562017374086615091633571)
    ·
      refine ⟨173343026061129922637450357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115562017374086615091633571 173343026061129922637450357)
      ·
        refine ⟨16250908693230930247260971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173343026061129922637450357 16250908693230930247260971)
        ·
          refine ⟨24376363039846395370891457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16250908693230930247260971 24376363039846395370891457)
          ·
            refine ⟨18282272279884796528168593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24376363039846395370891457 18282272279884796528168593)
            ·
              refine ⟨13711704209913597396126445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18282272279884796528168593 13711704209913597396126445)
              ·
                refine ⟨5141889078717599023547417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13711704209913597396126445 5141889078717599023547417)
                ·
                  refine ⟨3856416809038199267660563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5141889078717599023547417 3856416809038199267660563)
                  ·
                    refine ⟨5784625213557298901490845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856416809038199267660563 5784625213557298901490845)
                    ·
                      refine ⟨2169234455083987088059067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784625213557298901490845 2169234455083987088059067)
                      ·
                        rfl

theorem cell23_4224569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4224569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224569 prefixEnd_4224569 := by exact prefixLift 4224569
  have htrace : WordTrace (prefixWord ++ tailWord_4224569) baseStart_4224569 baseEnd_4224569 := by
    simpa [prefixWord, tailWord_4224569, baseEnd_4224569] using wordTrace_append hprefix tailTrace_4224569
  have hstable : (prefixWord ++ tailWord_4224569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224569).length < 2 ^ (prefixWord ++ tailWord_4224569).sum := by decide
  have hdescent : baseEnd_4224569 < baseStart_4224569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224592 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 1, 4, 2]
def baseStart_4224592 : Nat := 118140960795 + 4224592 * 2 ^ 59
def prefixEnd_4224592 : Nat := 4983230072969 + 3 ^ 40 * 4224592 * 2
def baseEnd_4224592 : Nat := 2169246265139040498071461

theorem tailTrace_4224592 : CollatzResearch.WordTrace tailWord_4224592 prefixEnd_4224592 2169246265139040498071461 := by
  unfold tailWord_4224592
  simp only [CollatzResearch.WordTrace]
  refine ⟨77041764355516080858466015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102722352474021441144621353 77041764355516080858466015)
  ·
    refine ⟨115562646533274121287699023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77041764355516080858466015 115562646533274121287699023)
    ·
      refine ⟨173343969799911181931548535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115562646533274121287699023 173343969799911181931548535)
      ·
        refine ⟨260015954699866772897322803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173343969799911181931548535 260015954699866772897322803)
        ·
          refine ⟨390023932049800159345984205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260015954699866772897322803 390023932049800159345984205)
          ·
            refine ⟨146258974518675059754744077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 390023932049800159345984205 146258974518675059754744077)
            ·
              refine ⟨54847115444503147408029029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146258974518675059754744077 54847115444503147408029029)
              ·
                refine ⟨10283834145844340139005443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54847115444503147408029029 10283834145844340139005443)
                ·
                  refine ⟨15425751218766510208508165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10283834145844340139005443 15425751218766510208508165)
                  ·
                    refine ⟨2892328353518720664095281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15425751218766510208508165 2892328353518720664095281)
                    ·
                      refine ⟨2169246265139040498071461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892328353518720664095281 2169246265139040498071461)
                      ·
                        rfl

theorem cell23_4224592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 4, 2].length) (baseStart_4224592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224592 prefixEnd_4224592 := by exact prefixLift 4224592
  have htrace : WordTrace (prefixWord ++ tailWord_4224592) baseStart_4224592 baseEnd_4224592 := by
    simpa [prefixWord, tailWord_4224592, baseEnd_4224592] using wordTrace_append hprefix tailTrace_4224592
  have hstable : (prefixWord ++ tailWord_4224592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224592).length < 2 ^ (prefixWord ++ tailWord_4224592).sum := by decide
  have hdescent : baseEnd_4224592 < baseStart_4224592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224609 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_4224609 : Nat := 118140960795 + 4224609 * 2 ^ 59
def prefixEnd_4224609 : Nat := 4983230072969 + 3 ^ 40 * 4224609 * 2
def baseEnd_4224609 : Nat := 2169254994310166931558883

theorem tailTrace_4224609 : CollatzResearch.WordTrace tailWord_4224609 prefixEnd_4224609 2169254994310166931558883 := by
  unfold tailWord_4224609
  simp only [CollatzResearch.WordTrace]
  refine ⟨154084148751970573620300881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102722765834647049080200587 154084148751970573620300881)
  ·
    refine ⟨115563111563977930215225661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154084148751970573620300881 115563111563977930215225661)
    ·
      refine ⟨43336166836491723830709623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115563111563977930215225661 43336166836491723830709623)
      ·
        refine ⟨65004250254737585746064435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43336166836491723830709623 65004250254737585746064435)
        ·
          refine ⟨97506375382106378619096653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65004250254737585746064435 97506375382106378619096653)
          ·
            refine ⟨36564890768289891982161245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97506375382106378619096653 36564890768289891982161245)
            ·
              refine ⟨13711834038108709493310467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36564890768289891982161245 13711834038108709493310467)
              ·
                refine ⟨20567751057163064239965701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13711834038108709493310467 20567751057163064239965701)
                ·
                  refine ⟨3856453323218074544993569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20567751057163064239965701 3856453323218074544993569)
                  ·
                    refine ⟨2892339992413555908745177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3856453323218074544993569 2892339992413555908745177)
                    ·
                      refine ⟨2169254994310166931558883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892339992413555908745177 2169254994310166931558883)
                      ·
                        rfl

theorem cell23_4224609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_4224609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224609 prefixEnd_4224609 := by exact prefixLift 4224609
  have htrace : WordTrace (prefixWord ++ tailWord_4224609) baseStart_4224609 baseEnd_4224609 := by
    simpa [prefixWord, tailWord_4224609, baseEnd_4224609] using wordTrace_append hprefix tailTrace_4224609
  have hstable : (prefixWord ++ tailWord_4224609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224609).length < 2 ^ (prefixWord ++ tailWord_4224609).sum := by decide
  have hdescent : baseEnd_4224609 < baseStart_4224609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224615 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 7]
def baseStart_4224615 : Nat := 118140960795 + 4224615 * 2 ^ 59
def prefixEnd_4224615 : Nat := 4983230072969 + 3 ^ 40 * 4224615 * 2
def baseEnd_4224615 : Nat := 241028675021565989787095

theorem tailTrace_4224615 : CollatzResearch.WordTrace tailWord_4224615 prefixEnd_4224615 241028675021565989787095 := by
  unfold tailWord_4224615
  simp only [CollatzResearch.WordTrace]
  refine ⟨154084367589948836645019299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102722911726632557763346199 154084367589948836645019299)
  ·
    refine ⟨231126551384923254967528949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154084367589948836645019299 231126551384923254967528949)
    ·
      refine ⟨21668114192336555153205839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 231126551384923254967528949 21668114192336555153205839)
      ·
        refine ⟨32502171288504832729808759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21668114192336555153205839 32502171288504832729808759)
        ·
          refine ⟨48753256932757249094713139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32502171288504832729808759 48753256932757249094713139)
          ·
            refine ⟨73129885399135873642069709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48753256932757249094713139 73129885399135873642069709)
            ·
              refine ⟨27423707024675952615776141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73129885399135873642069709 27423707024675952615776141)
              ·
                refine ⟨10283890134253482230916053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27423707024675952615776141 10283890134253482230916053)
                ·
                  refine ⟨241028675021565989787095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10283890134253482230916053 241028675021565989787095)
                  ·
                    rfl

theorem cell23_4224615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 7].length) (baseStart_4224615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224615 prefixEnd_4224615 := by exact prefixLift 4224615
  have htrace : WordTrace (prefixWord ++ tailWord_4224615) baseStart_4224615 baseEnd_4224615 := by
    simpa [prefixWord, tailWord_4224615, baseEnd_4224615] using wordTrace_append hprefix tailTrace_4224615
  have hstable : (prefixWord ++ tailWord_4224615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224615).length < 2 ^ (prefixWord ++ tailWord_4224615).sum := by decide
  have hdescent : baseEnd_4224615 < baseStart_4224615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224626 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_4224626 : Nat := 118140960795 + 4224626 * 2 ^ 59
def prefixEnd_4224626 : Nat := 4983230072969 + 3 ^ 40 * 4224626 * 2
def baseEnd_4224626 : Nat := 2169263723481293365046305

theorem tailTrace_4224626 : CollatzResearch.WordTrace tailWord_4224626 prefixEnd_4224626 2169263723481293365046305 := by
  unfold tailWord_4224626
  simp only [CollatzResearch.WordTrace]
  refine ⟨38521192198227246380917433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102723179195272657015779821 38521192198227246380917433)
  ·
    refine ⟨28890894148670434785688075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38521192198227246380917433 28890894148670434785688075)
    ·
      refine ⟨43336341223005652178532113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28890894148670434785688075 43336341223005652178532113)
      ·
        refine ⟨32502255917254239133899085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43336341223005652178532113 32502255917254239133899085)
        ·
          refine ⟨12188345968970339675212157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32502255917254239133899085 12188345968970339675212157)
          ·
            refine ⟨4570629738363877378204559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12188345968970339675212157 4570629738363877378204559)
            ·
              refine ⟨6855944607545816067306839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570629738363877378204559 6855944607545816067306839)
              ·
                refine ⟨10283916911318724100960259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6855944607545816067306839 10283916911318724100960259)
                ·
                  refine ⟨15425875366978086151440389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10283916911318724100960259 15425875366978086151440389)
                  ·
                    refine ⟨2892351631308391153395073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15425875366978086151440389 2892351631308391153395073)
                    ·
                      refine ⟨2169263723481293365046305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892351631308391153395073 2169263723481293365046305)
                      ·
                        rfl

theorem cell23_4224626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_4224626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224626 prefixEnd_4224626 := by exact prefixLift 4224626
  have htrace : WordTrace (prefixWord ++ tailWord_4224626) baseStart_4224626 baseEnd_4224626 := by
    simpa [prefixWord, tailWord_4224626, baseEnd_4224626] using wordTrace_append hprefix tailTrace_4224626
  have hstable : (prefixWord ++ tailWord_4224626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224626).length < 2 ^ (prefixWord ++ tailWord_4224626).sum := by decide
  have hdescent : baseEnd_4224626 < baseStart_4224626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224645 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_4224645 : Nat := 118140960795 + 4224645 * 2 ^ 59
def prefixEnd_4224645 : Nat := 4983230072969 + 3 ^ 40 * 4224645 * 2
def baseEnd_4224645 : Nat := 723091159871242930236239

theorem tailTrace_4224645 : CollatzResearch.WordTrace tailWord_4224645 prefixEnd_4224645 723091159871242930236239 := by
  unfold tailWord_4224645
  simp only [CollatzResearch.WordTrace]
  refine ⟨154085461779840151768611389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102723641186560101179074259 154085461779840151768611389)
  ·
    refine ⟨57782048167440056913229271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154085461779840151768611389 57782048167440056913229271)
    ·
      refine ⟨86673072251160085369843907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57782048167440056913229271 86673072251160085369843907)
      ·
        refine ⟨130009608376740128054765861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86673072251160085369843907 130009608376740128054765861)
        ·
          refine ⟨24376801570638774010268599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130009608376740128054765861 24376801570638774010268599)
          ·
            refine ⟨36565202355958161015402899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24376801570638774010268599 36565202355958161015402899)
            ·
              refine ⟨54847803533937241523104349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36565202355958161015402899 54847803533937241523104349)
              ·
                refine ⟨20567926325226465571164131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54847803533937241523104349 20567926325226465571164131)
                ·
                  refine ⟨30851889487839698356746197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20567926325226465571164131 30851889487839698356746197)
                  ·
                    refine ⟨723091159871242930236239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30851889487839698356746197 723091159871242930236239)
                    ·
                      rfl

theorem cell23_4224645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_4224645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224645 prefixEnd_4224645 := by exact prefixLift 4224645
  have htrace : WordTrace (prefixWord ++ tailWord_4224645) baseStart_4224645 baseEnd_4224645 := by
    simpa [prefixWord, tailWord_4224645, baseEnd_4224645] using wordTrace_append hprefix tailTrace_4224645
  have hstable : (prefixWord ++ tailWord_4224645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224645).length < 2 ^ (prefixWord ++ tailWord_4224645).sum := by decide
  have hdescent : baseEnd_4224645 < baseStart_4224645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224665 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_4224665 : Nat := 118140960795 + 4224665 * 2 ^ 59
def prefixEnd_4224665 : Nat := 4983230072969 + 3 ^ 40 * 4224665 * 2
def baseEnd_4224665 : Nat := 2169283749226818712458625

theorem tailTrace_4224665 : CollatzResearch.WordTrace tailWord_4224665 prefixEnd_4224665 2169283749226818712458625 := by
  unfold tailWord_4224665
  simp only [CollatzResearch.WordTrace]
  refine ⟨154086191239767695184339449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102724127493178463456226299 154086191239767695184339449)
  ·
    refine ⟨115564643429825771388254587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154086191239767695184339449 115564643429825771388254587)
    ·
      refine ⟨173346965144738657082381881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115564643429825771388254587 173346965144738657082381881)
      ·
        refine ⟨130010223858553992811786411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173346965144738657082381881 130010223858553992811786411)
        ·
          refine ⟨195015335787830989217679617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130010223858553992811786411 195015335787830989217679617)
          ·
            refine ⟨146261501840873241913259713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195015335787830989217679617 146261501840873241913259713)
            ·
              refine ⟨109696126380654931434944785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146261501840873241913259713 109696126380654931434944785)
              ·
                refine ⟨82272094785491198576208589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109696126380654931434944785 82272094785491198576208589)
                ·
                  refine ⟨30852035544559199466078221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82272094785491198576208589 30852035544559199466078221)
                  ·
                    refine ⟨11569513329209699799779333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30852035544559199466078221 11569513329209699799779333)
                    ·
                      refine ⟨2169283749226818712458625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11569513329209699799779333 2169283749226818712458625)
                      ·
                        rfl

theorem cell23_4224665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_4224665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224665 prefixEnd_4224665 := by exact prefixLift 4224665
  have htrace : WordTrace (prefixWord ++ tailWord_4224665) baseStart_4224665 baseEnd_4224665 := by
    simpa [prefixWord, tailWord_4224665, baseEnd_4224665] using wordTrace_append hprefix tailTrace_4224665
  have hstable : (prefixWord ++ tailWord_4224665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224665).length < 2 ^ (prefixWord ++ tailWord_4224665).sum := by decide
  have hdescent : baseEnd_4224665 < baseStart_4224665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224672 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_4224672 : Nat := 118140960795 + 4224672 * 2 ^ 59
def prefixEnd_4224672 : Nat := 4983230072969 + 3 ^ 40 * 4224672 * 2
def baseEnd_4224672 : Nat := 2169287343591400185071093

theorem tailTrace_4224672 : CollatzResearch.WordTrace tailWord_4224672 prefixEnd_4224672 2169287343591400185071093 := by
  unfold tailWord_4224672
  simp only [CollatzResearch.WordTrace]
  refine ⟨77043223275371167689922135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102724297700494890253229513 77043223275371167689922135)
  ·
    refine ⟨115564834913056751534883203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77043223275371167689922135 115564834913056751534883203)
    ·
      refine ⟨173347252369585127302324805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115564834913056751534883203 173347252369585127302324805)
      ·
        refine ⟨32502609819297211369185901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173347252369585127302324805 32502609819297211369185901)
        ·
          refine ⟨12188478682236454263444713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32502609819297211369185901 12188478682236454263444713)
          ·
            refine ⟨9141359011677340697583535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12188478682236454263444713 9141359011677340697583535)
            ·
              refine ⟨13712038517516011046375303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9141359011677340697583535 13712038517516011046375303)
              ·
                refine ⟨20568057776274016569562955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13712038517516011046375303 20568057776274016569562955)
                ·
                  refine ⟨30852086664411024854344433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20568057776274016569562955 30852086664411024854344433)
                  ·
                    refine ⟨23139064998308268640758325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30852086664411024854344433 23139064998308268640758325)
                    ·
                      refine ⟨2169287343591400185071093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23139064998308268640758325 2169287343591400185071093)
                      ·
                        rfl

theorem cell23_4224672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_4224672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224672 prefixEnd_4224672 := by exact prefixLift 4224672
  have htrace : WordTrace (prefixWord ++ tailWord_4224672) baseStart_4224672 baseEnd_4224672 := by
    simpa [prefixWord, tailWord_4224672, baseEnd_4224672] using wordTrace_append hprefix tailTrace_4224672
  have hstable : (prefixWord ++ tailWord_4224672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224672).length < 2 ^ (prefixWord ++ tailWord_4224672).sum := by decide
  have hdescent : baseEnd_4224672 < baseStart_4224672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224733 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4224733 : Nat := 118140960795 + 4224733 * 2 ^ 59
def prefixEnd_4224733 : Nat := 4983230072969 + 3 ^ 40 * 4224733 * 2
def baseEnd_4224733 : Nat := 2169318665911324446408313

theorem tailTrace_4224733 : CollatzResearch.WordTrace tailWord_4224733 prefixEnd_4224733 2169318665911324446408313 := by
  unfold tailWord_4224733
  simp only [CollatzResearch.WordTrace]
  refine ⟨154088671403521342797814853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102725780935680895198543235 154088671403521342797814853)
  ·
    refine ⟨28891625888160251774590285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154088671403521342797814853 28891625888160251774590285)
    ·
      refine ⟨10834359708060094415471357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28891625888160251774590285 10834359708060094415471357)
      ·
        refine ⟨4062884890522535405801759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10834359708060094415471357 4062884890522535405801759)
        ·
          refine ⟨6094327335783803108702639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4062884890522535405801759 6094327335783803108702639)
          ·
            refine ⟨9141491003675704663053959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094327335783803108702639 9141491003675704663053959)
            ·
              refine ⟨13712236505513556994580939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9141491003675704663053959 13712236505513556994580939)
              ·
                refine ⟨20568354758270335491871409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13712236505513556994580939 20568354758270335491871409)
                ·
                  refine ⟨15426266068702751618903557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20568354758270335491871409 15426266068702751618903557)
                  ·
                    refine ⟨2892424887881765928544417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15426266068702751618903557 2892424887881765928544417)
                    ·
                      refine ⟨2169318665911324446408313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892424887881765928544417 2169318665911324446408313)
                      ·
                        rfl

theorem cell23_4224733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4224733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224733 prefixEnd_4224733 := by exact prefixLift 4224733
  have htrace : WordTrace (prefixWord ++ tailWord_4224733) baseStart_4224733 baseEnd_4224733 := by
    simpa [prefixWord, tailWord_4224733, baseEnd_4224733] using wordTrace_append hprefix tailTrace_4224733
  have hstable : (prefixWord ++ tailWord_4224733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224733).length < 2 ^ (prefixWord ++ tailWord_4224733).sum := by decide
  have hdescent : baseEnd_4224733 < baseStart_4224733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224745 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_4224745 : Nat := 118140960795 + 4224745 * 2 ^ 59
def prefixEnd_4224745 : Nat := 4983230072969 + 3 ^ 40 * 4224745 * 2
def baseEnd_4224745 : Nat := 2169324827679178399458257

theorem tailTrace_4224745 : CollatzResearch.WordTrace tailWord_4224745 prefixEnd_4224745 2169324827679178399458257 := by
  unfold tailWord_4224745
  simp only [CollatzResearch.WordTrace]
  refine ⟨154089109079477868847251689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102726072719651912564834459 154089109079477868847251689)
  ·
    refine ⟨115566831809608401635438767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154089109079477868847251689 115566831809608401635438767)
    ·
      refine ⟨173350247714412602453158151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115566831809608401635438767 173350247714412602453158151)
      ·
        refine ⟨260025371571618903679737227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173350247714412602453158151 260025371571618903679737227)
        ·
          refine ⟨390038057357428355519605841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260025371571618903679737227 390038057357428355519605841)
          ·
            refine ⟨292528543018071266639704381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390038057357428355519605841 292528543018071266639704381)
            ·
              refine ⟨109698203631776724989889143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292528543018071266639704381 109698203631776724989889143)
              ·
                refine ⟨164547305447665087484833715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109698203631776724989889143 164547305447665087484833715)
                ·
                  refine ⟨246820958171497631227250573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164547305447665087484833715 246820958171497631227250573)
                  ·
                    refine ⟨92557859314311611710218965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246820958171497631227250573 92557859314311611710218965)
                    ·
                      refine ⟨2169324827679178399458257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92557859314311611710218965 2169324827679178399458257)
                      ·
                        rfl

theorem cell23_4224745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_4224745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224745 prefixEnd_4224745 := by exact prefixLift 4224745
  have htrace : WordTrace (prefixWord ++ tailWord_4224745) baseStart_4224745 baseEnd_4224745 := by
    simpa [prefixWord, tailWord_4224745, baseEnd_4224745] using wordTrace_append hprefix tailTrace_4224745
  have hstable : (prefixWord ++ tailWord_4224745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224745).length < 2 ^ (prefixWord ++ tailWord_4224745).sum := by decide
  have hdescent : baseEnd_4224745 < baseStart_4224745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224782 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_4224782 : Nat := 118140960795 + 4224782 * 2 ^ 59
def prefixEnd_4224782 : Nat := 4983230072969 + 3 ^ 40 * 4224782 * 2
def baseEnd_4224782 : Nat := 723114608821131584898529

theorem tailTrace_4224782 : CollatzResearch.WordTrace tailWord_4224782 prefixEnd_4224782 723114608821131584898529 := by
  unfold tailWord_4224782
  simp only [CollatzResearch.WordTrace]
  refine ⟨19261307322542978020793575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102726972386895882777565733 19261307322542978020793575)
  ·
    refine ⟨28891960983814467031190363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19261307322542978020793575 28891960983814467031190363)
    ·
      refine ⟨43337941475721700546785545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28891960983814467031190363 43337941475721700546785545)
      ·
        refine ⟨32503456106791275410089159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43337941475721700546785545 32503456106791275410089159)
        ·
          refine ⟨48755184160186913115133739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32503456106791275410089159 48755184160186913115133739)
          ·
            refine ⟨73132776240280369672700609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48755184160186913115133739 73132776240280369672700609)
            ·
              refine ⟨54849582180210277254525457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73132776240280369672700609 54849582180210277254525457)
              ·
                refine ⟨41137186635157707940894093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54849582180210277254525457 41137186635157707940894093)
                ·
                  refine ⟨15426444988184140477835285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41137186635157707940894093 15426444988184140477835285)
                  ·
                    refine ⟨723114608821131584898529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15426444988184140477835285 723114608821131584898529)
                    ·
                      rfl

theorem cell23_4224782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_4224782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224782 prefixEnd_4224782 := by exact prefixLift 4224782
  have htrace : WordTrace (prefixWord ++ tailWord_4224782) baseStart_4224782 baseEnd_4224782 := by
    simpa [prefixWord, tailWord_4224782, baseEnd_4224782] using wordTrace_append hprefix tailTrace_4224782
  have hstable : (prefixWord ++ tailWord_4224782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224782).length < 2 ^ (prefixWord ++ tailWord_4224782).sum := by decide
  have hdescent : baseEnd_4224782 < baseStart_4224782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224792 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4224792 : Nat := 118140960795 + 4224792 * 2 ^ 59
def prefixEnd_4224792 : Nat := 4983230072969 + 3 ^ 40 * 4224792 * 2
def baseEnd_4224792 : Nat := 2169348961269939715570541

theorem tailTrace_4224792 : CollatzResearch.WordTrace tailWord_4224792 prefixEnd_4224792 2169348961269939715570541 := by
  unfold tailWord_4224792
  simp only [CollatzResearch.WordTrace]
  refine ⟨77045411655153797937106315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102727215540205063916141753 77045411655153797937106315)
  ·
    refine ⟨115568117482730696905659473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77045411655153797937106315 115568117482730696905659473)
    ·
      refine ⟨86676088112048022679244605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115568117482730696905659473 86676088112048022679244605)
      ·
        refine ⟨32503533042018008504716727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86676088112048022679244605 32503533042018008504716727)
        ·
          refine ⟨48755299563027012757075091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32503533042018008504716727 48755299563027012757075091)
          ·
            refine ⟨73132949344540519135612637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48755299563027012757075091 73132949344540519135612637)
            ·
              refine ⟨27424856004202694675854739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73132949344540519135612637 27424856004202694675854739)
              ·
                refine ⟨41137284006304042013782109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27424856004202694675854739 41137284006304042013782109)
                ·
                  refine ⟨15426481502364015755168291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41137284006304042013782109 15426481502364015755168291)
                  ·
                    refine ⟨23139722253546023632752437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15426481502364015755168291 23139722253546023632752437)
                    ·
                      refine ⟨2169348961269939715570541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23139722253546023632752437 2169348961269939715570541)
                      ·
                        rfl

theorem cell23_4224792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4224792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224792 prefixEnd_4224792 := by exact prefixLift 4224792
  have htrace : WordTrace (prefixWord ++ tailWord_4224792) baseStart_4224792 baseEnd_4224792 := by
    simpa [prefixWord, tailWord_4224792, baseEnd_4224792] using wordTrace_append hprefix tailTrace_4224792
  have hstable : (prefixWord ++ tailWord_4224792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224792).length < 2 ^ (prefixWord ++ tailWord_4224792).sum := by decide
  have hdescent : baseEnd_4224792 < baseStart_4224792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224812 : List Nat := [2, 2, 1, 1, 1, 6, 1, 9]
def baseStart_4224812 : Nat := 118140960795 + 4224812 * 2 ^ 59
def prefixEnd_4224812 : Nat := 4983230072969 + 3 ^ 40 * 4224812 * 2
def baseEnd_4224812 : Nat := 80346638180852949530387

theorem tailTrace_4224812 : CollatzResearch.WordTrace tailWord_4224812 prefixEnd_4224812 80346638180852949530387 := by
  unfold tailWord_4224812
  simp only [CollatzResearch.WordTrace]
  refine ⟨77045776385117569644970345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102727701846823426193293793 77045776385117569644970345)
  ·
    refine ⟨57784332288838177233727759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77045776385117569644970345 57784332288838177233727759)
    ·
      refine ⟨86676498433257265850591639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57784332288838177233727759 86676498433257265850591639)
      ·
        refine ⟨130014747649885898775887459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86676498433257265850591639 130014747649885898775887459)
        ·
          refine ⟨195022121474828848163831189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130014747649885898775887459 195022121474828848163831189)
          ·
            refine ⟨9141661944132602257679587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 195022121474828848163831189 9141661944132602257679587)
            ·
              refine ⟨13712492916198903386519381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9141661944132602257679587 13712492916198903386519381)
              ·
                refine ⟨80346638180852949530387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13712492916198903386519381 80346638180852949530387)
                ·
                  rfl

theorem cell23_4224812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 9].length) (baseStart_4224812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224812 prefixEnd_4224812 := by exact prefixLift 4224812
  have htrace : WordTrace (prefixWord ++ tailWord_4224812) baseStart_4224812 baseEnd_4224812 := by
    simpa [prefixWord, tailWord_4224812, baseEnd_4224812] using wordTrace_append hprefix tailTrace_4224812
  have hstable : (prefixWord ++ tailWord_4224812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224812).length < 2 ^ (prefixWord ++ tailWord_4224812).sum := by decide
  have hdescent : baseEnd_4224812 < baseStart_4224812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224823 : List Nat := [1, 1, 3, 1, 2, 1, 2, 7, 1, 2, 2]
def baseStart_4224823 : Nat := 118140960795 + 4224823 * 2 ^ 59
def prefixEnd_4224823 : Nat := 4983230072969 + 3 ^ 40 * 4224823 * 2
def baseEnd_4224823 : Nat := 2169364879170229094282899

theorem tailTrace_4224823 : CollatzResearch.WordTrace tailWord_4224823 prefixEnd_4224823 2169364879170229094282899 := by
  unfold tailWord_4224823
  simp only [CollatzResearch.WordTrace]
  refine ⟨154091953973195288168591123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102727969315463525445727415 154091953973195288168591123)
  ·
    refine ⟨231137930959792932252886685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154091953973195288168591123 231137930959792932252886685)
    ·
      refine ⟨86676724109922349594832507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231137930959792932252886685 86676724109922349594832507)
      ·
        refine ⟨130015086164883524392248761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86676724109922349594832507 130015086164883524392248761)
        ·
          refine ⟨97511314623662643294186571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130015086164883524392248761 97511314623662643294186571)
          ·
            refine ⟨146266971935493964941279857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97511314623662643294186571 146266971935493964941279857)
            ·
              refine ⟨109700228951620473705959893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146266971935493964941279857 109700228951620473705959893)
              ·
                refine ⟨2571099116053604852483435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109700228951620473705959893 2571099116053604852483435)
                ·
                  refine ⟨3856648674080407278725153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571099116053604852483435 3856648674080407278725153)
                  ·
                    refine ⟨2892486505560305459043865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3856648674080407278725153 2892486505560305459043865)
                    ·
                      refine ⟨2169364879170229094282899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892486505560305459043865 2169364879170229094282899)
                      ·
                        rfl

theorem cell23_4224823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_4224823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224823 prefixEnd_4224823 := by exact prefixLift 4224823
  have htrace : WordTrace (prefixWord ++ tailWord_4224823) baseStart_4224823 baseEnd_4224823 := by
    simpa [prefixWord, tailWord_4224823, baseEnd_4224823] using wordTrace_append hprefix tailTrace_4224823
  have hstable : (prefixWord ++ tailWord_4224823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224823).length < 2 ^ (prefixWord ++ tailWord_4224823).sum := by decide
  have hdescent : baseEnd_4224823 < baseStart_4224823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224826 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_4224826 : Nat := 118140960795 + 4224826 * 2 ^ 59
def prefixEnd_4224826 : Nat := 4983230072969 + 3 ^ 40 * 4224826 * 2
def baseEnd_4224826 : Nat := 2169366419612192582545385

theorem tailTrace_4224826 : CollatzResearch.WordTrace tailWord_4224826 prefixEnd_4224826 2169366419612192582545385 := by
  unfold tailWord_4224826
  simp only [CollatzResearch.WordTrace]
  refine ⟨38523015848046104920237583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102728042261456279787300221 38523015848046104920237583)
  ·
    refine ⟨57784523772069157380356375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38523015848046104920237583 57784523772069157380356375)
    ·
      refine ⟨86676785658103736070534563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57784523772069157380356375 86676785658103736070534563)
      ·
        refine ⟨130015178487155604105801845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86676785658103736070534563 130015178487155604105801845)
        ·
          refine ⟨12188922983170837884918923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130015178487155604105801845 12188922983170837884918923)
          ·
            refine ⟨18283384474756256827378385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12188922983170837884918923 18283384474756256827378385)
            ·
              refine ⟨13712538356067192620533789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18283384474756256827378385 13712538356067192620533789)
              ·
                refine ⟨5142201883525197232700171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13712538356067192620533789 5142201883525197232700171)
                ·
                  refine ⟨7713302825287795849050257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5142201883525197232700171 7713302825287795849050257)
                  ·
                    refine ⟨5784977118965846886787693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7713302825287795849050257 5784977118965846886787693)
                    ·
                      refine ⟨2169366419612192582545385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5784977118965846886787693 2169366419612192582545385)
                      ·
                        rfl

theorem cell23_4224826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_4224826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224826 prefixEnd_4224826 := by exact prefixLift 4224826
  have htrace : WordTrace (prefixWord ++ tailWord_4224826) baseStart_4224826 baseEnd_4224826 := by
    simpa [prefixWord, tailWord_4224826, baseEnd_4224826] using wordTrace_append hprefix tailTrace_4224826
  have hstable : (prefixWord ++ tailWord_4224826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224826).length < 2 ^ (prefixWord ++ tailWord_4224826).sum := by decide
  have hdescent : baseEnd_4224826 < baseStart_4224826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224829 : List Nat := [1, 4, 1, 4, 1, 3, 9]
def baseStart_4224829 : Nat := 118140960795 + 4224829 * 2 ^ 59
def prefixEnd_4224829 : Nat := 4983230072969 + 3 ^ 40 * 4224829 * 2
def baseEnd_4224829 : Nat := 26782320494495753960591

theorem tailTrace_4224829 : CollatzResearch.WordTrace tailWord_4224829 prefixEnd_4224829 26782320494495753960591 := by
  unfold tailWord_4224829
  simp only [CollatzResearch.WordTrace]
  refine ⟨154092172811173551193309541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102728115207449034128873027 154092172811173551193309541)
  ·
    refine ⟨28892282402095040848745539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154092172811173551193309541 28892282402095040848745539)
    ·
      refine ⟨43338423603142561273118309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28892282402095040848745539 43338423603142561273118309)
      ·
        refine ⟨8125954425589230238709683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43338423603142561273118309 8125954425589230238709683)
        ·
          refine ⟨12188931638383845358064525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8125954425589230238709683 12188931638383845358064525)
          ·
            refine ⟨4570849364393942009274197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12188931638383845358064525 4570849364393942009274197)
            ·
              refine ⟨26782320494495753960591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4570849364393942009274197 26782320494495753960591)
              ·
                rfl

theorem cell23_4224829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 9].length) (baseStart_4224829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224829 prefixEnd_4224829 := by exact prefixLift 4224829
  have htrace : WordTrace (prefixWord ++ tailWord_4224829) baseStart_4224829 baseEnd_4224829 := by
    simpa [prefixWord, tailWord_4224829, baseEnd_4224829] using wordTrace_append hprefix tailTrace_4224829
  have hstable : (prefixWord ++ tailWord_4224829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224829).length < 2 ^ (prefixWord ++ tailWord_4224829).sum := by decide
  have hdescent : baseEnd_4224829 < baseStart_4224829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224842 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_4224842 : Nat := 118140960795 + 4224842 * 2 ^ 59
def prefixEnd_4224842 : Nat := 4983230072969 + 3 ^ 40 * 4224842 * 2
def baseEnd_4224842 : Nat := 723124878434221506648437

theorem tailTrace_4224842 : CollatzResearch.WordTrace tailWord_4224842 prefixEnd_4224842 723124878434221506648437 := by
  unfold tailWord_4224842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38523161740031613603383195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102728431306750969609021853 38523161740031613603383195)
  ·
    refine ⟨57784742610047420405074793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38523161740031613603383195 57784742610047420405074793)
    ·
      refine ⟨43338556957535565303806095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57784742610047420405074793 43338556957535565303806095)
      ·
        refine ⟨65007835436303347955709143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43338556957535565303806095 65007835436303347955709143)
        ·
          refine ⟨97511753154455021933563715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65007835436303347955709143 97511753154455021933563715)
          ·
            refine ⟨146267629731682532900345573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97511753154455021933563715 146267629731682532900345573)
            ·
              refine ⟨27425180574690474918814795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146267629731682532900345573 27425180574690474918814795)
              ·
                refine ⟨41137770862035712378222193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27425180574690474918814795 41137770862035712378222193)
                ·
                  refine ⟨30853328146526784283666645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41137770862035712378222193 30853328146526784283666645)
                  ·
                    refine ⟨723124878434221506648437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30853328146526784283666645 723124878434221506648437)
                    ·
                      rfl

theorem cell23_4224842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_4224842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224842 prefixEnd_4224842 := by exact prefixLift 4224842
  have htrace : WordTrace (prefixWord ++ tailWord_4224842) baseStart_4224842 baseEnd_4224842 := by
    simpa [prefixWord, tailWord_4224842, baseEnd_4224842] using wordTrace_append hprefix tailTrace_4224842
  have hstable : (prefixWord ++ tailWord_4224842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224842).length < 2 ^ (prefixWord ++ tailWord_4224842).sum := by decide
  have hdescent : baseEnd_4224842 < baseStart_4224842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224860 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4224860 : Nat := 118140960795 + 4224860 * 2 ^ 59
def prefixEnd_4224860 : Nat := 4983230072969 + 3 ^ 40 * 4224860 * 2
def baseEnd_4224860 : Nat := 2169383877954445449520229

theorem tailTrace_4224860 : CollatzResearch.WordTrace tailWord_4224860 prefixEnd_4224860 2169383877954445449520229 := by
  unfold tailWord_4224860
  simp only [CollatzResearch.WordTrace]
  refine ⟨77046651737030621743844017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102728868982707495658458689 77046651737030621743844017)
  ·
    refine ⟨57784988802772966307883013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77046651737030621743844017 57784988802772966307883013)
    ·
      refine ⟨10834685400519931182728065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57784988802772966307883013 10834685400519931182728065)
      ·
        refine ⟨8126014050389948387046049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10834685400519931182728065 8126014050389948387046049)
        ·
          refine ⟨6094510537792461290284537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126014050389948387046049 6094510537792461290284537)
          ·
            refine ⟨4570882903344345967713403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6094510537792461290284537 4570882903344345967713403)
            ·
              refine ⟨6856324355016518951570105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570882903344345967713403 6856324355016518951570105)
              ·
                refine ⟨5142243266262389213677579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6856324355016518951570105 5142243266262389213677579)
                ·
                  refine ⟨7713364899393583820516369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5142243266262389213677579 7713364899393583820516369)
                  ·
                    refine ⟨5785023674545187865387277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7713364899393583820516369 5785023674545187865387277)
                    ·
                      refine ⟨2169383877954445449520229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5785023674545187865387277 2169383877954445449520229)
                      ·
                        rfl

theorem cell23_4224860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4224860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224860 prefixEnd_4224860 := by exact prefixLift 4224860
  have htrace : WordTrace (prefixWord ++ tailWord_4224860) baseStart_4224860 baseEnd_4224860 := by
    simpa [prefixWord, tailWord_4224860, baseEnd_4224860] using wordTrace_append hprefix tailTrace_4224860
  have hstable : (prefixWord ++ tailWord_4224860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224860).length < 2 ^ (prefixWord ++ tailWord_4224860).sum := by decide
  have hdescent : baseEnd_4224860 < baseStart_4224860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224892 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_4224892 : Nat := 118140960795 + 4224892 * 2 ^ 59
def prefixEnd_4224892 : Nat := 4983230072969 + 3 ^ 40 * 4224892 * 2
def baseEnd_4224892 : Nat := 2169400309335389324320081

theorem tailTrace_4224892 : CollatzResearch.WordTrace tailWord_4224892 prefixEnd_4224892 2169400309335389324320081 := by
  unfold tailWord_4224892
  simp only [CollatzResearch.WordTrace]
  refine ⟨77047235304972656476426465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102729647073296875301901953 77047235304972656476426465)
  ·
    refine ⟨57785426478729492357319849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77047235304972656476426465 57785426478729492357319849)
    ·
      refine ⟨43339069859047119267989887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57785426478729492357319849 43339069859047119267989887)
      ·
        refine ⟨65008604788570678901984831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43339069859047119267989887 65008604788570678901984831)
        ·
          refine ⟨97512907182856018352977247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65008604788570678901984831 97512907182856018352977247)
          ·
            refine ⟨146269360774284027529465871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97512907182856018352977247 146269360774284027529465871)
            ·
              refine ⟨219404041161426041294198807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146269360774284027529465871 219404041161426041294198807)
              ·
                refine ⟨329106061742139061941298211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219404041161426041294198807 329106061742139061941298211)
                ·
                  refine ⟨493659092613208592911947317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329106061742139061941298211 493659092613208592911947317)
                  ·
                    refine ⟨46280539932488305585495061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 493659092613208592911947317 46280539932488305585495061)
                    ·
                      refine ⟨2169400309335389324320081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46280539932488305585495061 2169400309335389324320081)
                      ·
                        rfl

theorem cell23_4224892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_4224892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224892 prefixEnd_4224892 := by exact prefixLift 4224892
  have htrace : WordTrace (prefixWord ++ tailWord_4224892) baseStart_4224892 baseEnd_4224892 := by
    simpa [prefixWord, tailWord_4224892, baseEnd_4224892] using wordTrace_append hprefix tailTrace_4224892
  have hstable : (prefixWord ++ tailWord_4224892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224892).length < 2 ^ (prefixWord ++ tailWord_4224892).sum := by decide
  have hdescent : baseEnd_4224892 < baseStart_4224892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224899 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 3]
def baseStart_4224899 : Nat := 118140960795 + 4224899 * 2 ^ 59
def prefixEnd_4224899 : Nat := 4983230072969 + 3 ^ 40 * 4224899 * 2
def baseEnd_4224899 : Nat := 2169403903699970796932549

theorem tailTrace_4224899 : CollatzResearch.WordTrace tailWord_4224899 prefixEnd_4224899 2169403903699970796932549 := by
  unfold tailWord_4224899
  simp only [CollatzResearch.WordTrace]
  refine ⟨154094725920919953148357751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102729817280613302098905167 154094725920919953148357751)
  ·
    refine ⟨231142088881379929722536627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154094725920919953148357751 231142088881379929722536627)
    ·
      refine ⟨346713133322069894583804941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231142088881379929722536627 346713133322069894583804941)
      ·
        refine ⟨130017424995776210468926853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346713133322069894583804941 130017424995776210468926853)
        ·
          refine ⟨24378267186708039462923785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130017424995776210468926853 24378267186708039462923785)
          ·
            refine ⟨18283700390031029597192839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24378267186708039462923785 18283700390031029597192839)
            ·
              refine ⟨27425550585046544395789259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18283700390031029597192839 27425550585046544395789259)
              ·
                refine ⟨41138325877569816593683889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27425550585046544395789259 41138325877569816593683889)
                ·
                  refine ⟨30853744408177362445262917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41138325877569816593683889 30853744408177362445262917)
                  ·
                    refine ⟨5785077076533255458486797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30853744408177362445262917 5785077076533255458486797)
                    ·
                      refine ⟨2169403903699970796932549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5785077076533255458486797 2169403903699970796932549)
                      ·
                        rfl

theorem cell23_4224899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_4224899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224899 prefixEnd_4224899 := by exact prefixLift 4224899
  have htrace : WordTrace (prefixWord ++ tailWord_4224899) baseStart_4224899 baseEnd_4224899 := by
    simpa [prefixWord, tailWord_4224899, baseEnd_4224899] using wordTrace_append hprefix tailTrace_4224899
  have hstable : (prefixWord ++ tailWord_4224899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224899).length < 2 ^ (prefixWord ++ tailWord_4224899).sum := by decide
  have hdescent : baseEnd_4224899 < baseStart_4224899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224906 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_4224906 : Nat := 118140960795 + 4224906 * 2 ^ 59
def prefixEnd_4224906 : Nat := 4983230072969 + 3 ^ 40 * 4224906 * 2
def baseEnd_4224906 : Nat := 723135832688184089848339

theorem tailTrace_4224906 : CollatzResearch.WordTrace tailWord_4224906 prefixEnd_4224906 723135832688184089848339 := by
  unfold tailWord_4224906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38523745307973648335965643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102729987487929728895908381 38523745307973648335965643)
  ·
    refine ⟨57785617961960472503948465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38523745307973648335965643 57785617961960472503948465)
    ·
      refine ⟨43339213471470354377961349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57785617961960472503948465 43339213471470354377961349)
      ·
        refine ⟨8126102525900691445867753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43339213471470354377961349 8126102525900691445867753)
        ·
          refine ⟨6094576894425518584400815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126102525900691445867753 6094576894425518584400815)
          ·
            refine ⟨9141865341638277876601223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094576894425518584400815 9141865341638277876601223)
            ·
              refine ⟨13712798012457416814901835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9141865341638277876601223 13712798012457416814901835)
              ·
                refine ⟨20569197018686125222352753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13712798012457416814901835 20569197018686125222352753)
                ·
                  refine ⟨15426897764014593916764565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20569197018686125222352753 15426897764014593916764565)
                  ·
                    refine ⟨723135832688184089848339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15426897764014593916764565 723135832688184089848339)
                    ·
                      rfl

theorem cell23_4224906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_4224906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224906 prefixEnd_4224906 := by exact prefixLift 4224906
  have htrace : WordTrace (prefixWord ++ tailWord_4224906) baseStart_4224906 baseEnd_4224906 := by
    simpa [prefixWord, tailWord_4224906, baseEnd_4224906] using wordTrace_append hprefix tailTrace_4224906
  have hstable : (prefixWord ++ tailWord_4224906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224906).length < 2 ^ (prefixWord ++ tailWord_4224906).sum := by decide
  have hdescent : baseEnd_4224906 < baseStart_4224906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224913 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 2, 2, 2]
def baseStart_4224913 : Nat := 118140960795 + 4224913 * 2 ^ 59
def prefixEnd_4224913 : Nat := 4983230072969 + 3 ^ 40 * 4224913 * 2
def baseEnd_4224913 : Nat := 2169411092429133742157485

theorem tailTrace_4224913 : CollatzResearch.WordTrace tailWord_4224913 prefixEnd_4224913 2169411092429133742157485 := by
  unfold tailWord_4224913
  simp only [CollatzResearch.WordTrace]
  refine ⟨154095236542869233539367393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102730157695246155692911595 154095236542869233539367393)
  ·
    refine ⟨115571427407151925154525545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154095236542869233539367393 115571427407151925154525545)
    ·
      refine ⟨86678570555363943865894159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115571427407151925154525545 86678570555363943865894159)
      ·
        refine ⟨130017855833045915798841239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86678570555363943865894159 130017855833045915798841239)
        ·
          refine ⟨195026783749568873698261859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130017855833045915798841239 195026783749568873698261859)
          ·
            refine ⟨292540175624353310547392789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195026783749568873698261859 292540175624353310547392789)
            ·
              refine ⟨13712820732391561431909037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 292540175624353310547392789 13712820732391561431909037)
              ·
                refine ⟨5142307774646835536965889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13712820732391561431909037 5142307774646835536965889)
                ·
                  refine ⟨3856730830985126652724417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142307774646835536965889 3856730830985126652724417)
                  ·
                    refine ⟨2892548123238844989543313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3856730830985126652724417 2892548123238844989543313)
                    ·
                      refine ⟨2169411092429133742157485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892548123238844989543313 2169411092429133742157485)
                      ·
                        rfl

theorem cell23_4224913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_4224913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224913 prefixEnd_4224913 := by exact prefixLift 4224913
  have htrace : WordTrace (prefixWord ++ tailWord_4224913) baseStart_4224913 baseEnd_4224913 := by
    simpa [prefixWord, tailWord_4224913, baseEnd_4224913] using wordTrace_append hprefix tailTrace_4224913
  have hstable : (prefixWord ++ tailWord_4224913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224913).length < 2 ^ (prefixWord ++ tailWord_4224913).sum := by decide
  have hdescent : baseEnd_4224913 < baseStart_4224913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224919 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 7]
def baseStart_4224919 : Nat := 118140960795 + 4224919 * 2 ^ 59
def prefixEnd_4224919 : Nat := 4983230072969 + 3 ^ 40 * 4224919 * 2
def baseEnd_4224919 : Nat := 241046019257006746520273

theorem tailTrace_4224919 : CollatzResearch.WordTrace tailWord_4224919 prefixEnd_4224919 241046019257006746520273 := by
  unfold tailWord_4224919
  simp only [CollatzResearch.WordTrace]
  refine ⟨154095455380847496564085811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102730303587231664376057207 154095455380847496564085811)
  ·
    refine ⟨231143183071271244846128717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154095455380847496564085811 231143183071271244846128717)
    ·
      refine ⟨86678693651726716817298269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231143183071271244846128717 86678693651726716817298269)
      ·
        refine ⟨32504510119397518806486851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86678693651726716817298269 32504510119397518806486851)
        ·
          refine ⟨48756765179096278209730277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32504510119397518806486851 48756765179096278209730277)
          ·
            refine ⟨9141893471080552164324427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48756765179096278209730277 9141893471080552164324427)
            ·
              refine ⟨13712840206620828246486641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9141893471080552164324427 13712840206620828246486641)
              ·
                refine ⟨10284630154965621184864981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13712840206620828246486641 10284630154965621184864981)
                ·
                  refine ⟨241046019257006746520273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10284630154965621184864981 241046019257006746520273)
                  ·
                    rfl

theorem cell23_4224919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 7].length) (baseStart_4224919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224919 prefixEnd_4224919 := by exact prefixLift 4224919
  have htrace : WordTrace (prefixWord ++ tailWord_4224919) baseStart_4224919 baseEnd_4224919 := by
    simpa [prefixWord, tailWord_4224919, baseEnd_4224919] using wordTrace_append hprefix tailTrace_4224919
  have hstable : (prefixWord ++ tailWord_4224919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224919).length < 2 ^ (prefixWord ++ tailWord_4224919).sum := by decide
  have hdescent : baseEnd_4224919 < baseStart_4224919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4224969 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_4224969 : Nat := 118140960795 + 4224969 * 2 ^ 59
def prefixEnd_4224969 : Nat := 4983230072969 + 3 ^ 40 * 4224969 * 2
def baseEnd_4224969 : Nat := 2169439847345785523057227

theorem tailTrace_4224969 : CollatzResearch.WordTrace tailWord_4224969 prefixEnd_4224969 2169439847345785523057227 := by
  unfold tailWord_4224969
  simp only [CollatzResearch.WordTrace]
  refine ⟨154097279030666355103405961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102731519353777570068937307 154097279030666355103405961)
  ·
    refine ⟨115572959272999766327554471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154097279030666355103405961 115572959272999766327554471)
    ·
      refine ⟨173359438909499649491331707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115572959272999766327554471 173359438909499649491331707)
      ·
        refine ⟨260039158364249474236997561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173359438909499649491331707 260039158364249474236997561)
        ·
          refine ⟨195029368773187105677748171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260039158364249474236997561 195029368773187105677748171)
          ·
            refine ⟨292544053159780658516622257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195029368773187105677748171 292544053159780658516622257)
            ·
              refine ⟨219408039869835493887466693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292544053159780658516622257 219408039869835493887466693)
              ·
                refine ⟨41139007475594155103900005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219408039869835493887466693 41139007475594155103900005)
                ·
                  refine ⟨7713563901673904081981251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41139007475594155103900005 7713563901673904081981251)
                  ·
                    refine ⟨11570345852510856122971877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7713563901673904081981251 11570345852510856122971877)
                    ·
                      refine ⟨2169439847345785523057227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11570345852510856122971877 2169439847345785523057227)
                      ·
                        rfl

theorem cell23_4224969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_4224969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4224969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4224969 prefixEnd_4224969 := by exact prefixLift 4224969
  have htrace : WordTrace (prefixWord ++ tailWord_4224969) baseStart_4224969 baseEnd_4224969 := by
    simpa [prefixWord, tailWord_4224969, baseEnd_4224969] using wordTrace_append hprefix tailTrace_4224969
  have hstable : (prefixWord ++ tailWord_4224969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4224969).length < 2 ^ (prefixWord ++ tailWord_4224969).sum := by decide
  have hdescent : baseEnd_4224969 < baseStart_4224969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4224969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225113 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 3]
def baseStart_4225113 : Nat := 118140960795 + 4225113 * 2 ^ 59
def prefixEnd_4225113 : Nat := 4983230072969 + 3 ^ 40 * 4225113 * 2
def baseEnd_4225113 : Nat := 2169513788560032959656565

theorem tailTrace_4225113 : CollatzResearch.WordTrace tailWord_4225113 prefixEnd_4225113 2169513788560032959656565 := by
  unfold tailWord_4225113
  simp only [CollatzResearch.WordTrace]
  refine ⟨154102531142144667696647993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102735020761429778464431995 154102531142144667696647993)
  ·
    refine ⟨115576898356608500772485995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154102531142144667696647993 115576898356608500772485995)
    ·
      refine ⟨173365347534912751158728993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115576898356608500772485995 173365347534912751158728993)
      ·
        refine ⟨130024010651184563369046745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173365347534912751158728993 130024010651184563369046745)
        ·
          refine ⟨97518007988388422526785059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130024010651184563369046745 97518007988388422526785059)
          ·
            refine ⟨146277011982582633790177589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97518007988388422526785059 146277011982582633790177589)
            ·
              refine ⟨13713469873367121917829149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146277011982582633790177589 13713469873367121917829149)
              ·
                refine ⟨5142551202512670719185931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13713469873367121917829149 5142551202512670719185931)
                ·
                  refine ⟨7713826803769006078778897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5142551202512670719185931 7713826803769006078778897)
                  ·
                    refine ⟨5785370102826754559084173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7713826803769006078778897 5785370102826754559084173)
                    ·
                      refine ⟨2169513788560032959656565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5785370102826754559084173 2169513788560032959656565)
                      ·
                        rfl

theorem cell23_4225113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_4225113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225113 prefixEnd_4225113 := by exact prefixLift 4225113
  have htrace : WordTrace (prefixWord ++ tailWord_4225113) baseStart_4225113 baseEnd_4225113 := by
    simpa [prefixWord, tailWord_4225113, baseEnd_4225113] using wordTrace_append hprefix tailTrace_4225113
  have hstable : (prefixWord ++ tailWord_4225113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225113).length < 2 ^ (prefixWord ++ tailWord_4225113).sum := by decide
  have hdescent : baseEnd_4225113 < baseStart_4225113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225116 : List Nat := [2, 2, 4, 1, 1, 3, 10]
def baseStart_4225116 : Nat := 118140960795 + 4225116 * 2 ^ 59
def prefixEnd_4225116 : Nat := 4983230072969 + 3 ^ 40 * 4225116 * 2
def baseEnd_4225116 : Nat := 26784139864222178369371

theorem tailTrace_4225116 : CollatzResearch.WordTrace tailWord_4225116 prefixEnd_4225116 26784139864222178369371 := by
  unfold tailWord_4225116
  simp only [CollatzResearch.WordTrace]
  refine ⟨77051320280566899604503601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102735093707422532806004801 77051320280566899604503601)
  ·
    refine ⟨57788490210425174703377701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77051320280566899604503601 57788490210425174703377701)
    ·
      refine ⟨10835341914454720256883319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57788490210425174703377701 10835341914454720256883319)
      ·
        refine ⟨16253012871682080385324979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10835341914454720256883319 16253012871682080385324979)
        ·
          refine ⟨24379519307523120577987469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16253012871682080385324979 24379519307523120577987469)
          ·
            refine ⟨9142319740321170216745301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24379519307523120577987469 9142319740321170216745301)
            ·
              refine ⟨26784139864222178369371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9142319740321170216745301 26784139864222178369371)
              ·
                rfl

theorem cell23_4225116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 10].length) (baseStart_4225116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225116 prefixEnd_4225116 := by exact prefixLift 4225116
  have htrace : WordTrace (prefixWord ++ tailWord_4225116) baseStart_4225116 baseEnd_4225116 := by
    simpa [prefixWord, tailWord_4225116, baseEnd_4225116] using wordTrace_append hprefix tailTrace_4225116
  have hstable : (prefixWord ++ tailWord_4225116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225116).length < 2 ^ (prefixWord ++ tailWord_4225116).sum := by decide
  have hdescent : baseEnd_4225116 < baseStart_4225116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225120 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 2, 4]
def baseStart_4225120 : Nat := 118140960795 + 4225120 * 2 ^ 59
def prefixEnd_4225120 : Nat := 4983230072969 + 3 ^ 40 * 4225120 * 2
def baseEnd_4225120 : Nat := 723172460974871477423011

theorem tailTrace_4225120 : CollatzResearch.WordTrace tailWord_4225120 prefixEnd_4225120 723172460974871477423011 := by
  unfold tailWord_4225120
  simp only [CollatzResearch.WordTrace]
  refine ⟨77051393226559653946076407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102735190968746205261435209 77051393226559653946076407)
  ·
    refine ⟨115577089839839480919114611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77051393226559653946076407 115577089839839480919114611)
    ·
      refine ⟨173365634759759221378671917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115577089839839480919114611 173365634759759221378671917)
      ·
        refine ⟨65012113034909708017001969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173365634759759221378671917 65012113034909708017001969)
        ·
          refine ⟨48759084776182281012751477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65012113034909708017001969 48759084776182281012751477)
          ·
            refine ⟨4571164197767088844945451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48759084776182281012751477 4571164197767088844945451)
            ·
              refine ⟨6856746296650633267418177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571164197767088844945451 6856746296650633267418177)
              ·
                refine ⟨5142559722487974950563633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6856746296650633267418177 5142559722487974950563633)
                ·
                  refine ⟨3856919791865981212922725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142559722487974950563633 3856919791865981212922725)
                  ·
                    refine ⟨723172460974871477423011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856919791865981212922725 723172460974871477423011)
                    ·
                      rfl

theorem cell23_4225120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_4225120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225120 prefixEnd_4225120 := by exact prefixLift 4225120
  have htrace : WordTrace (prefixWord ++ tailWord_4225120) baseStart_4225120 baseEnd_4225120 := by
    simpa [prefixWord, tailWord_4225120, baseEnd_4225120] using wordTrace_append hprefix tailTrace_4225120
  have hstable : (prefixWord ++ tailWord_4225120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225120).length < 2 ^ (prefixWord ++ tailWord_4225120).sum := by decide
  have hdescent : baseEnd_4225120 < baseStart_4225120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225127 : List Nat := [1, 1, 5, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_4225127 : Nat := 118140960795 + 4225127 * 2 ^ 59
def prefixEnd_4225127 : Nat := 4983230072969 + 3 ^ 40 * 4225127 * 2
def baseEnd_4225127 : Nat := 2169520977289195904881501

theorem tailTrace_4225127 : CollatzResearch.WordTrace tailWord_4225127 prefixEnd_4225127 2169520977289195904881501 := by
  unfold tailWord_4225127
  simp only [CollatzResearch.WordTrace]
  refine ⟨154103041764093948087657635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102735361176062632058438423 154103041764093948087657635)
  ·
    refine ⟨231154562646140922131486453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154103041764093948087657635 231154562646140922131486453)
    ·
      refine ⟨21670740248075711449826855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 231154562646140922131486453 21670740248075711449826855)
      ·
        refine ⟨32506110372113567174740283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21670740248075711449826855 32506110372113567174740283)
        ·
          refine ⟨48759165558170350762110425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32506110372113567174740283 48759165558170350762110425)
          ·
            refine ⟨36569374168627763071582819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48759165558170350762110425 36569374168627763071582819)
            ·
              refine ⟨54854061252941644607374229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36569374168627763071582819 54854061252941644607374229)
              ·
                refine ⟨2571284121231639590970667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54854061252941644607374229 2571284121231639590970667)
                ·
                  refine ⟨3856926181847459386456001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571284121231639590970667 3856926181847459386456001)
                  ·
                    refine ⟨2892694636385594539842001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3856926181847459386456001 2892694636385594539842001)
                    ·
                      refine ⟨2169520977289195904881501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892694636385594539842001 2169520977289195904881501)
                      ·
                        rfl

theorem cell23_4225127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_4225127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225127 prefixEnd_4225127 := by exact prefixLift 4225127
  have htrace : WordTrace (prefixWord ++ tailWord_4225127) baseStart_4225127 baseEnd_4225127 := by
    simpa [prefixWord, tailWord_4225127, baseEnd_4225127] using wordTrace_append hprefix tailTrace_4225127
  have hstable : (prefixWord ++ tailWord_4225127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225127).length < 2 ^ (prefixWord ++ tailWord_4225127).sum := by decide
  have hdescent : baseEnd_4225127 < baseStart_4225127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225143 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_4225143 : Nat := 118140960795 + 4225143 * 2 ^ 59
def prefixEnd_4225143 : Nat := 4983230072969 + 3 ^ 40 * 4225143 * 2
def baseEnd_4225143 : Nat := 2169529192979667842281427

theorem tailTrace_4225143 : CollatzResearch.WordTrace tailWord_4225143 prefixEnd_4225143 2169529192979667842281427 := by
  unfold tailWord_4225143
  simp only [CollatzResearch.WordTrace]
  refine ⟨154103625332035982820240083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102735750221357321880160055 154103625332035982820240083)
  ·
    refine ⟨231155437998053974230360125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154103625332035982820240083 231155437998053974230360125)
    ·
      refine ⟨86683289249270240336385047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231155437998053974230360125 86683289249270240336385047)
      ·
        refine ⟨130024933873905360504577571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86683289249270240336385047 130024933873905360504577571)
        ·
          refine ⟨195037400810858040756866357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130024933873905360504577571 195037400810858040756866357)
          ·
            refine ⟨18284756326017941320956221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 195037400810858040756866357 18284756326017941320956221)
            ·
              refine ⟨6856783622256727995358583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18284756326017941320956221 6856783622256727995358583)
              ·
                refine ⟨10285175433385091993037875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6856783622256727995358583 10285175433385091993037875)
                ·
                  refine ⟨15427763150077637989556813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10285175433385091993037875 15427763150077637989556813)
                  ·
                    refine ⟨5785411181279114246083805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15427763150077637989556813 5785411181279114246083805)
                    ·
                      refine ⟨2169529192979667842281427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5785411181279114246083805 2169529192979667842281427)
                      ·
                        rfl

theorem cell23_4225143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_4225143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225143 prefixEnd_4225143 := by exact prefixLift 4225143
  have htrace : WordTrace (prefixWord ++ tailWord_4225143) baseStart_4225143 baseEnd_4225143 := by
    simpa [prefixWord, tailWord_4225143, baseEnd_4225143] using wordTrace_append hprefix tailTrace_4225143
  have hstable : (prefixWord ++ tailWord_4225143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225143).length < 2 ^ (prefixWord ++ tailWord_4225143).sum := by decide
  have hdescent : baseEnd_4225143 < baseStart_4225143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225156 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_4225156 : Nat := 118140960795 + 4225156 * 2 ^ 59
def prefixEnd_4225156 : Nat := 4983230072969 + 3 ^ 40 * 4225156 * 2
def baseEnd_4225156 : Nat := 2169535868228176291418867

theorem tailTrace_4225156 : CollatzResearch.WordTrace tailWord_4225156 prefixEnd_4225156 2169535868228176291418867 := by
  unfold tailWord_4225156
  simp only [CollatzResearch.WordTrace]
  refine ⟨77052049740494443020231661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102736066320659257360308881 77052049740494443020231661)
  ·
    refine ⟨28894518652685416132586873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77052049740494443020231661 28894518652685416132586873)
    ·
      refine ⟨21670888989514062099440155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28894518652685416132586873 21670888989514062099440155)
      ·
        refine ⟨32506333484271093149160233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21670888989514062099440155 32506333484271093149160233)
        ·
          refine ⟨24379750113203319861870175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32506333484271093149160233 24379750113203319861870175)
          ·
            refine ⟨36569625169804979792805263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24379750113203319861870175 36569625169804979792805263)
            ·
              refine ⟨54854437754707469689207895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36569625169804979792805263 54854437754707469689207895)
              ·
                refine ⟨82281656632061204533811843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54854437754707469689207895 82281656632061204533811843)
                ·
                  refine ⟨123422484948091806800717765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82281656632061204533811843 123422484948091806800717765)
                  ·
                    refine ⟨23141715927767213775134581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123422484948091806800717765 23141715927767213775134581)
                    ·
                      refine ⟨2169535868228176291418867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23141715927767213775134581 2169535868228176291418867)
                      ·
                        rfl

theorem cell23_4225156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_4225156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225156 prefixEnd_4225156 := by exact prefixLift 4225156
  have htrace : WordTrace (prefixWord ++ tailWord_4225156) baseStart_4225156 baseEnd_4225156 := by
    simpa [prefixWord, tailWord_4225156, baseEnd_4225156] using wordTrace_append hprefix tailTrace_4225156
  have hstable : (prefixWord ++ tailWord_4225156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225156).length < 2 ^ (prefixWord ++ tailWord_4225156).sum := by decide
  have hdescent : baseEnd_4225156 < baseStart_4225156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225160 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_4225160 : Nat := 118140960795 + 4225160 * 2 ^ 59
def prefixEnd_4225160 : Nat := 4983230072969 + 3 ^ 40 * 4225160 * 2
def baseEnd_4225160 : Nat := 2169537922150794275768849

theorem tailTrace_4225160 : CollatzResearch.WordTrace tailWord_4225160 prefixEnd_4225160 2169537922150794275768849 := by
  unfold tailWord_4225160
  simp only [CollatzResearch.WordTrace]
  refine ⟨77052122686487197361804467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102736163581982929815739289 77052122686487197361804467)
  ·
    refine ⟨115578184029730796042706701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77052122686487197361804467 115578184029730796042706701)
    ·
      refine ⟨43341819011149048516015013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115578184029730796042706701 43341819011149048516015013)
      ·
        refine ⟨8126591064590446596752815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43341819011149048516015013 8126591064590446596752815)
        ·
          refine ⟨12189886596885669895129223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8126591064590446596752815 12189886596885669895129223)
          ·
            refine ⟨18284829895328504842693835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12189886596885669895129223 18284829895328504842693835)
            ·
              refine ⟨27427244842992757264040753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18284829895328504842693835 27427244842992757264040753)
              ·
                refine ⟨20570433632244567948030565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27427244842992757264040753 20570433632244567948030565)
                ·
                  refine ⟨3856956306045856490255731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20570433632244567948030565 3856956306045856490255731)
                  ·
                    refine ⟨5785434459068784735383597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856956306045856490255731 5785434459068784735383597)
                    ·
                      refine ⟨2169537922150794275768849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5785434459068784735383597 2169537922150794275768849)
                      ·
                        rfl

theorem cell23_4225160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_4225160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225160 prefixEnd_4225160 := by exact prefixLift 4225160
  have htrace : WordTrace (prefixWord ++ tailWord_4225160) baseStart_4225160 baseEnd_4225160 := by
    simpa [prefixWord, tailWord_4225160, baseEnd_4225160] using wordTrace_append hprefix tailTrace_4225160
  have hstable : (prefixWord ++ tailWord_4225160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225160).length < 2 ^ (prefixWord ++ tailWord_4225160).sum := by decide
  have hdescent : baseEnd_4225160 < baseStart_4225160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225194 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4225194 : Nat := 118140960795 + 4225194 * 2 ^ 59
def prefixEnd_4225194 : Nat := 4983230072969 + 3 ^ 40 * 4225194 * 2
def baseEnd_4225194 : Nat := 2169555380493047142743693

theorem tailTrace_4225194 : CollatzResearch.WordTrace tailWord_4225194 prefixEnd_4225194 2169555380493047142743693 := by
  unfold tailWord_4225194
  simp only [CollatzResearch.WordTrace]
  refine ⟨38526371363712804632586659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102736990303234145686897757 38526371363712804632586659)
  ·
    refine ⟨57789557045569206948879989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38526371363712804632586659 57789557045569206948879989)
    ·
      refine ⟨5417770973022113151457499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57789557045569206948879989 5417770973022113151457499)
      ·
        refine ⟨8126656459533169727186249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5417770973022113151457499 8126656459533169727186249)
        ·
          refine ⟨6094992344649877295389687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126656459533169727186249 6094992344649877295389687)
          ·
            refine ⟨9142488516974815943084531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094992344649877295389687 9142488516974815943084531)
            ·
              refine ⟨13713732775462223914626797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9142488516974815943084531 13713732775462223914626797)
              ·
                refine ⟨5142649790798333967985049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13713732775462223914626797 5142649790798333967985049)
                ·
                  refine ⟨3856987343098750475988787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142649790798333967985049 3856987343098750475988787)
                  ·
                    refine ⟨5785481014648125713983181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856987343098750475988787 5785481014648125713983181)
                    ·
                      refine ⟨2169555380493047142743693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5785481014648125713983181 2169555380493047142743693)
                      ·
                        rfl

theorem cell23_4225194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4225194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225194 prefixEnd_4225194 := by exact prefixLift 4225194
  have htrace : WordTrace (prefixWord ++ tailWord_4225194) baseStart_4225194 baseEnd_4225194 := by
    simpa [prefixWord, tailWord_4225194, baseEnd_4225194] using wordTrace_append hprefix tailTrace_4225194
  have hstable : (prefixWord ++ tailWord_4225194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225194).length < 2 ^ (prefixWord ++ tailWord_4225194).sum := by decide
  have hdescent : baseEnd_4225194 < baseStart_4225194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225196 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_4225196 : Nat := 118140960795 + 4225196 * 2 ^ 59
def prefixEnd_4225196 : Nat := 4983230072969 + 3 ^ 40 * 4225196 * 2
def baseEnd_4225196 : Nat := 2169556407454356134918683

theorem tailTrace_4225196 : CollatzResearch.WordTrace tailWord_4225196 prefixEnd_4225196 2169556407454356134918683 := by
  unfold tailWord_4225196
  simp only [CollatzResearch.WordTrace]
  refine ⟨77052779200421986435959721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102737038933895981914612961 77052779200421986435959721)
  ·
    refine ⟨57789584400316489826969791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77052779200421986435959721 57789584400316489826969791)
    ·
      refine ⟨86684376600474734740454687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57789584400316489826969791 86684376600474734740454687)
      ·
        refine ⟨130026564900712102110682031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86684376600474734740454687 130026564900712102110682031)
        ·
          refine ⟨195039847351068153166023047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130026564900712102110682031 195039847351068153166023047)
          ·
            refine ⟨292559771026602229749034571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195039847351068153166023047 292559771026602229749034571)
            ·
              refine ⟨438839656539903344623551857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292559771026602229749034571 438839656539903344623551857)
              ·
                refine ⟨329129742404927508467663893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438839656539903344623551857 329129742404927508467663893)
                ·
                  refine ⟨15427956675230976959421745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 329129742404927508467663893 15427956675230976959421745)
                  ·
                    refine ⟨11570967506423232719566309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15427956675230976959421745 11570967506423232719566309)
                    ·
                      refine ⟨2169556407454356134918683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11570967506423232719566309 2169556407454356134918683)
                      ·
                        rfl

theorem cell23_4225196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_4225196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225196 prefixEnd_4225196 := by exact prefixLift 4225196
  have htrace : WordTrace (prefixWord ++ tailWord_4225196) baseStart_4225196 baseEnd_4225196 := by
    simpa [prefixWord, tailWord_4225196, baseEnd_4225196] using wordTrace_append hprefix tailTrace_4225196
  have hstable : (prefixWord ++ tailWord_4225196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225196).length < 2 ^ (prefixWord ++ tailWord_4225196).sum := by decide
  have hdescent : baseEnd_4225196 < baseStart_4225196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225234 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_4225234 : Nat := 118140960795 + 4225234 * 2 ^ 59
def prefixEnd_4225234 : Nat := 4983230072969 + 3 ^ 40 * 4225234 * 2
def baseEnd_4225234 : Nat := 2169575919719226986243509

theorem tailTrace_4225234 : CollatzResearch.WordTrace tailWord_4225234 prefixEnd_4225234 2169575919719226986243509 := by
  unfold tailWord_4225234
  simp only [CollatzResearch.WordTrace]
  refine ⟨38526736093676576340450689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102737962916470870241201837 38526736093676576340450689)
  ·
    refine ⟨28895052070257432255338017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38526736093676576340450689 28895052070257432255338017)
    ·
      refine ⟨21671289052693074191503513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28895052070257432255338017 21671289052693074191503513)
      ·
        refine ⟨16253466789519805643627635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21671289052693074191503513 16253466789519805643627635)
        ·
          refine ⟨24380200184279708465441453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16253466789519805643627635 24380200184279708465441453)
          ·
            refine ⟨9142575069104890674540545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24380200184279708465441453 9142575069104890674540545)
            ·
              refine ⟨6856931301828668005905409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9142575069104890674540545 6856931301828668005905409)
              ·
                refine ⟨5142698476371501004429057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6856931301828668005905409 5142698476371501004429057)
                ·
                  refine ⟨3857023857278625753321793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142698476371501004429057 3857023857278625753321793)
                  ·
                    refine ⟨2892767892958969314991345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3857023857278625753321793 2892767892958969314991345)
                    ·
                      refine ⟨2169575919719226986243509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892767892958969314991345 2169575919719226986243509)
                      ·
                        rfl

theorem cell23_4225234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_4225234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225234 prefixEnd_4225234 := by exact prefixLift 4225234
  have htrace : WordTrace (prefixWord ++ tailWord_4225234) baseStart_4225234 baseEnd_4225234 := by
    simpa [prefixWord, tailWord_4225234, baseEnd_4225234] using wordTrace_append hprefix tailTrace_4225234
  have hstable : (prefixWord ++ tailWord_4225234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225234).length < 2 ^ (prefixWord ++ tailWord_4225234).sum := by decide
  have hdescent : baseEnd_4225234 < baseStart_4225234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225240 : List Nat := [2, 1, 2, 2, 4, 2, 1, 4, 5]
def baseStart_4225240 : Nat := 118140960795 + 4225240 * 2 ^ 59
def prefixEnd_4225240 : Nat := 4983230072969 + 3 ^ 40 * 4225240 * 2
def baseEnd_4225240 : Nat := 241064333400350440307609

theorem tailTrace_4225240 : CollatzResearch.WordTrace tailWord_4225240 prefixEnd_4225240 241064333400350440307609 := by
  unfold tailWord_4225240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77053581606342284193260587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102738108808456378924347449 77053581606342284193260587)
  ·
    refine ⟨115580372409513426289890881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77053581606342284193260587 115580372409513426289890881)
    ·
      refine ⟨86685279307135069717418161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115580372409513426289890881 86685279307135069717418161)
      ·
        refine ⟨65013959480351302288063621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86685279307135069717418161 65013959480351302288063621)
        ·
          refine ⟨12190117402565869179011929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65013959480351302288063621 12190117402565869179011929)
          ·
            refine ⟨9142588051924401884258947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12190117402565869179011929 9142588051924401884258947)
            ·
              refine ⟨13713882077886602826388421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9142588051924401884258947 13713882077886602826388421)
              ·
                refine ⟨2571352889603738029947829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13713882077886602826388421 2571352889603738029947829)
                ·
                  refine ⟨241064333400350440307609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2571352889603738029947829 241064333400350440307609)
                  ·
                    rfl

theorem cell23_4225240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 5].length) (baseStart_4225240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225240 prefixEnd_4225240 := by exact prefixLift 4225240
  have htrace : WordTrace (prefixWord ++ tailWord_4225240) baseStart_4225240 baseEnd_4225240 := by
    simpa [prefixWord, tailWord_4225240, baseEnd_4225240] using wordTrace_append hprefix tailTrace_4225240
  have hstable : (prefixWord ++ tailWord_4225240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225240).length < 2 ^ (prefixWord ++ tailWord_4225240).sum := by decide
  have hdescent : baseEnd_4225240 < baseStart_4225240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225243 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 2, 5, 2]
def baseStart_4225243 : Nat := 118140960795 + 4225243 * 2 ^ 59
def prefixEnd_4225243 : Nat := 4983230072969 + 3 ^ 40 * 4225243 * 2
def baseEnd_4225243 : Nat := 2169580541045117451030967

theorem tailTrace_4225243 : CollatzResearch.WordTrace tailWord_4225243 prefixEnd_4225243 2169580541045117451030967 := by
  unfold tailWord_4225243
  simp only [CollatzResearch.WordTrace]
  refine ⟨154107272631673699898880383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102738181754449133265920255 154107272631673699898880383)
  ·
    refine ⟨231160908947510549848320575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154107272631673699898880383 231160908947510549848320575)
    ·
      refine ⟨346741363421265824772480863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231160908947510549848320575 346741363421265824772480863)
      ·
        refine ⟨520112045131898737158721295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346741363421265824772480863 520112045131898737158721295)
        ·
          refine ⟨780168067697848105738081943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520112045131898737158721295 780168067697848105738081943)
          ·
            refine ⟨1170252101546772158607122915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780168067697848105738081943 1170252101546772158607122915)
            ·
              refine ⟨1755378152320158237910684373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170252101546772158607122915 1755378152320158237910684373)
              ·
                refine ⟨41141675445003708701031665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1755378152320158237910684373 41141675445003708701031665)
                ·
                  refine ⟨30856256583752781525773749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41141675445003708701031665 30856256583752781525773749)
                  ·
                    refine ⟨2892774054726823268041289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30856256583752781525773749 2892774054726823268041289)
                    ·
                      refine ⟨2169580541045117451030967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892774054726823268041289 2169580541045117451030967)
                      ·
                        rfl

theorem cell23_4225243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5, 2].length) (baseStart_4225243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225243 prefixEnd_4225243 := by exact prefixLift 4225243
  have htrace : WordTrace (prefixWord ++ tailWord_4225243) baseStart_4225243 baseEnd_4225243 := by
    simpa [prefixWord, tailWord_4225243, baseEnd_4225243] using wordTrace_append hprefix tailTrace_4225243
  have hstable : (prefixWord ++ tailWord_4225243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225243).length < 2 ^ (prefixWord ++ tailWord_4225243).sum := by decide
  have hdescent : baseEnd_4225243 < baseStart_4225243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225270 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_4225270 : Nat := 118140960795 + 4225270 * 2 ^ 59
def prefixEnd_4225270 : Nat := 4983230072969 + 3 ^ 40 * 4225270 * 2
def baseEnd_4225270 : Nat := 723198135007596281797781

theorem tailTrace_4225270 : CollatzResearch.WordTrace tailWord_4225270 prefixEnd_4225270 723198135007596281797781 := by
  unfold tailWord_4225270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631766087660992719382079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102738838268383922340075509 9631766087660992719382079)
  ·
    refine ⟨14447649131491489079073119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9631766087660992719382079 14447649131491489079073119)
    ·
      refine ⟨21671473697237233618609679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14447649131491489079073119 21671473697237233618609679)
      ·
        refine ⟨32507210545855850427914519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21671473697237233618609679 32507210545855850427914519)
        ·
          refine ⟨48760815818783775641871779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32507210545855850427914519 48760815818783775641871779)
          ·
            refine ⟨73141223728175663462807669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48760815818783775641871779 73141223728175663462807669)
            ·
              refine ⟨6856989724516468449638219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73141223728175663462807669 6856989724516468449638219)
              ·
                refine ⟨10285484586774702674457329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6856989724516468449638219 10285484586774702674457329)
                ·
                  refine ⟨7714113440081027005842997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10285484586774702674457329 7714113440081027005842997)
                  ·
                    refine ⟨723198135007596281797781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7714113440081027005842997 723198135007596281797781)
                    ·
                      rfl

theorem cell23_4225270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_4225270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225270 prefixEnd_4225270 := by exact prefixLift 4225270
  have htrace : WordTrace (prefixWord ++ tailWord_4225270) baseStart_4225270 baseEnd_4225270 := by
    simpa [prefixWord, tailWord_4225270, baseEnd_4225270] using wordTrace_append hprefix tailTrace_4225270
  have hstable : (prefixWord ++ tailWord_4225270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225270).length < 2 ^ (prefixWord ++ tailWord_4225270).sum := by decide
  have hdescent : baseEnd_4225270 < baseStart_4225270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225273 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_4225273 : Nat := 118140960795 + 4225273 * 2 ^ 59
def prefixEnd_4225273 : Nat := 4983230072969 + 3 ^ 40 * 4225273 * 2
def baseEnd_4225273 : Nat := 2169595945464752333655829

theorem tailTrace_4225273 : CollatzResearch.WordTrace tailWord_4225273 prefixEnd_4225273 2169595945464752333655829 := by
  unfold tailWord_4225273
  simp only [CollatzResearch.WordTrace]
  refine ⟨154108366821565015022472473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102738911214376676681648315 154108366821565015022472473)
  ·
    refine ⟨115581275116173761266854355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154108366821565015022472473 115581275116173761266854355)
    ·
      refine ⟨173371912674260641900281533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115581275116173761266854355 173371912674260641900281533)
      ·
        refine ⟨65014467252847740712605575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173371912674260641900281533 65014467252847740712605575)
        ·
          refine ⟨97521700879271611068908363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65014467252847740712605575 97521700879271611068908363)
          ·
            refine ⟨146282551318907416603362545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97521700879271611068908363 146282551318907416603362545)
            ·
              refine ⟨109711913489180562452521909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146282551318907416603362545 109711913489180562452521909)
              ·
                refine ⟨10285491889610677729923929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109711913489180562452521909 10285491889610677729923929)
                ·
                  refine ⟨7714118917208008297442947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10285491889610677729923929 7714118917208008297442947)
                  ·
                    refine ⟨11571178375812012446164421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7714118917208008297442947 11571178375812012446164421)
                    ·
                      refine ⟨2169595945464752333655829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11571178375812012446164421 2169595945464752333655829)
                      ·
                        rfl

theorem cell23_4225273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_4225273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225273 prefixEnd_4225273 := by exact prefixLift 4225273
  have htrace : WordTrace (prefixWord ++ tailWord_4225273) baseStart_4225273 baseEnd_4225273 := by
    simpa [prefixWord, tailWord_4225273, baseEnd_4225273] using wordTrace_append hprefix tailTrace_4225273
  have hstable : (prefixWord ++ tailWord_4225273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225273).length < 2 ^ (prefixWord ++ tailWord_4225273).sum := by decide
  have hdescent : baseEnd_4225273 < baseStart_4225273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225283 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 5, 4]
def baseStart_4225283 : Nat := 118140960795 + 4225283 * 2 ^ 59
def prefixEnd_4225283 : Nat := 4983230072969 + 3 ^ 40 * 4225283 * 2
def baseEnd_4225283 : Nat := 723200360090432431510261

theorem tailTrace_4225283 : CollatzResearch.WordTrace tailWord_4225283 prefixEnd_4225283 723200360090432431510261 := by
  unfold tailWord_4225283
  simp only [CollatzResearch.WordTrace]
  refine ⟨154108731551528786730336503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102739154367685857820224335 154108731551528786730336503)
  ·
    refine ⟨231163097327293180095504755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154108731551528786730336503 231163097327293180095504755)
    ·
      refine ⟨346744645990939770143257133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231163097327293180095504755 346744645990939770143257133)
      ·
        refine ⟨130029242246602413803721425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346744645990939770143257133 130029242246602413803721425)
        ·
          refine ⟨97521931684951810352791069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130029242246602413803721425 97521931684951810352791069)
          ·
            refine ⟨36570724381856928882296651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97521931684951810352791069 36570724381856928882296651)
            ·
              refine ⟨54856086572785393323444977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36570724381856928882296651 54856086572785393323444977)
              ·
                refine ⟨41142064929589044992583733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54856086572785393323444977 41142064929589044992583733)
                ·
                  refine ⟨3857068587148972968054725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41142064929589044992583733 3857068587148972968054725)
                  ·
                    refine ⟨723200360090432431510261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857068587148972968054725 723200360090432431510261)
                    ·
                      rfl

theorem cell23_4225283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 4].length) (baseStart_4225283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225283 prefixEnd_4225283 := by exact prefixLift 4225283
  have htrace : WordTrace (prefixWord ++ tailWord_4225283) baseStart_4225283 baseEnd_4225283 := by
    simpa [prefixWord, tailWord_4225283, baseEnd_4225283] using wordTrace_append hprefix tailTrace_4225283
  have hstable : (prefixWord ++ tailWord_4225283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225283).length < 2 ^ (prefixWord ++ tailWord_4225283).sum := by decide
  have hdescent : baseEnd_4225283 < baseStart_4225283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225290 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_4225290 : Nat := 118140960795 + 4225290 * 2 ^ 59
def prefixEnd_4225290 : Nat := 4983230072969 + 3 ^ 40 * 4225290 * 2
def baseEnd_4225290 : Nat := 2169604674635878767143251

theorem tailTrace_4225290 : CollatzResearch.WordTrace tailWord_4225290 prefixEnd_4225290 2169604674635878767143251 := by
  unfold tailWord_4225290
  simp only [CollatzResearch.WordTrace]
  refine ⟨38527246715625856731460331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102739324575002284617227549 38527246715625856731460331)
  ·
    refine ⟨57790870073438785097190497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38527246715625856731460331 57790870073438785097190497)
    ·
      refine ⟨43343152555079088822892873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57790870073438785097190497 43343152555079088822892873)
      ·
        refine ⟨32507364416309316617169655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43343152555079088822892873 32507364416309316617169655)
        ·
          refine ⟨48761046624463974925754483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32507364416309316617169655 48761046624463974925754483)
          ·
            refine ⟨73141569936695962388631725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48761046624463974925754483 73141569936695962388631725)
            ·
              refine ⟨27428088726260985895736897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73141569936695962388631725 27428088726260985895736897)
              ·
                refine ⟨20571066544695739421802673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27428088726260985895736897 20571066544695739421802673)
                ·
                  refine ⟨15428299908521804566352005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20571066544695739421802673 15428299908521804566352005)
                  ·
                    refine ⟨2892806232847838356191001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15428299908521804566352005 2892806232847838356191001)
                    ·
                      refine ⟨2169604674635878767143251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892806232847838356191001 2169604674635878767143251)
                      ·
                        rfl

theorem cell23_4225290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_4225290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225290 prefixEnd_4225290 := by exact prefixLift 4225290
  have htrace : WordTrace (prefixWord ++ tailWord_4225290) baseStart_4225290 baseEnd_4225290 := by
    simpa [prefixWord, tailWord_4225290, baseEnd_4225290] using wordTrace_append hprefix tailTrace_4225290
  have hstable : (prefixWord ++ tailWord_4225290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225290).length < 2 ^ (prefixWord ++ tailWord_4225290).sum := by decide
  have hdescent : baseEnd_4225290 < baseStart_4225290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225313 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 6]
def baseStart_4225313 : Nat := 118140960795 + 4225313 * 2 ^ 59
def prefixEnd_4225313 : Nat := 4983230072969 + 3 ^ 40 * 4225313 * 2
def baseEnd_4225313 : Nat := 241068498298992464128405

theorem tailTrace_4225313 : CollatzResearch.WordTrace tailWord_4225313 prefixEnd_4225313 241068498298992464128405 := by
  unfold tailWord_4225313
  simp only [CollatzResearch.WordTrace]
  refine ⟨154109825741420101853928593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102739883827613401235952395 154109825741420101853928593)
  ·
    refine ⟨115582369306065076390446445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154109825741420101853928593 115582369306065076390446445)
    ·
      refine ⟨43343388489774403646417417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115582369306065076390446445 43343388489774403646417417)
      ·
        refine ⟨32507541367330802734813063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43343388489774403646417417 32507541367330802734813063)
        ·
          refine ⟨48761312050996204102219595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32507541367330802734813063 48761312050996204102219595)
          ·
            refine ⟨73141968076494306153329393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48761312050996204102219595 73141968076494306153329393)
            ·
              refine ⟨54856476057370729614997045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73141968076494306153329393 54856476057370729614997045)
              ·
                refine ⟨5142794630378505901405973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54856476057370729614997045 5142794630378505901405973)
                ·
                  refine ⟨241068498298992464128405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5142794630378505901405973 241068498298992464128405)
                  ·
                    rfl

theorem cell23_4225313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 6].length) (baseStart_4225313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225313 prefixEnd_4225313 := by exact prefixLift 4225313
  have htrace : WordTrace (prefixWord ++ tailWord_4225313) baseStart_4225313 baseEnd_4225313 := by
    simpa [prefixWord, tailWord_4225313, baseEnd_4225313] using wordTrace_append hprefix tailTrace_4225313
  have hstable : (prefixWord ++ tailWord_4225313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225313).length < 2 ^ (prefixWord ++ tailWord_4225313).sum := by decide
  have hdescent : baseEnd_4225313 < baseStart_4225313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225380 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_4225380 : Nat := 118140960795 + 4225380 * 2 ^ 59
def prefixEnd_4225380 : Nat := 4983230072969 + 3 ^ 40 * 4225380 * 2
def baseEnd_4225380 : Nat := 2169650887894783415017837

theorem tailTrace_4225380 : CollatzResearch.WordTrace tailWord_4225380 prefixEnd_4225380 2169650887894783415017837 := by
  unfold tailWord_4225380
  simp only [CollatzResearch.WordTrace]
  refine ⟨77056134716088686148308797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102741512954784914864411729 77056134716088686148308797)
  ·
    refine ⟨28896050518533257305615799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77056134716088686148308797 28896050518533257305615799)
    ·
      refine ⟨43344075777799885958423699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28896050518533257305615799 43344075777799885958423699)
      ·
        refine ⟨65016113666699828937635549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43344075777799885958423699 65016113666699828937635549)
        ·
          refine ⟨24381042625012435851613331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65016113666699828937635549 24381042625012435851613331)
          ·
            refine ⟨36571563937518653777419997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24381042625012435851613331 36571563937518653777419997)
            ·
              refine ⟨13714336476569495166532499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36571563937518653777419997 13714336476569495166532499)
              ·
                refine ⟨20571504714854242749798749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13714336476569495166532499 20571504714854242749798749)
                ·
                  refine ⟨7714314268070341031174531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20571504714854242749798749 7714314268070341031174531)
                  ·
                    refine ⟨11571471402105511546761797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7714314268070341031174531 11571471402105511546761797)
                    ·
                      refine ⟨2169650887894783415017837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11571471402105511546761797 2169650887894783415017837)
                      ·
                        rfl

theorem cell23_4225380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_4225380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225380 prefixEnd_4225380 := by exact prefixLift 4225380
  have htrace : WordTrace (prefixWord ++ tailWord_4225380) baseStart_4225380 baseEnd_4225380 := by
    simpa [prefixWord, tailWord_4225380, baseEnd_4225380] using wordTrace_append hprefix tailTrace_4225380
  have hstable : (prefixWord ++ tailWord_4225380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225380).length < 2 ^ (prefixWord ++ tailWord_4225380).sum := by decide
  have hdescent : baseEnd_4225380 < baseStart_4225380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225384 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4225384 : Nat := 118140960795 + 4225384 * 2 ^ 59
def prefixEnd_4225384 : Nat := 4983230072969 + 3 ^ 40 * 4225384 * 2
def baseEnd_4225384 : Nat := 2169652941817401399367819

theorem tailTrace_4225384 : CollatzResearch.WordTrace tailWord_4225384 prefixEnd_4225384 2169652941817401399367819 := by
  unfold tailWord_4225384
  simp only [CollatzResearch.WordTrace]
  refine ⟨77056207662081440489881603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102741610216108587319842137 77056207662081440489881603)
  ·
    refine ⟨115584311493122160734822405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77056207662081440489881603 115584311493122160734822405)
    ·
      refine ⟨21672058404960405137779201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115584311493122160734822405 21672058404960405137779201)
      ·
        refine ⟨16254043803720303853334401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21672058404960405137779201 16254043803720303853334401)
        ·
          refine ⟨12190532852790227890000801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16254043803720303853334401 12190532852790227890000801)
          ·
            refine ⟨9142899639592670917500601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12190532852790227890000801 9142899639592670917500601)
            ·
              refine ⟨6857174729694503188125451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9142899639592670917500601 6857174729694503188125451)
              ·
                refine ⟨10285762094541754782188177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6857174729694503188125451 10285762094541754782188177)
                ·
                  refine ⟨7714321570906316086641133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10285762094541754782188177 7714321570906316086641133)
                  ·
                    refine ⟨2892870589089868532490425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7714321570906316086641133 2892870589089868532490425)
                    ·
                      refine ⟨2169652941817401399367819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892870589089868532490425 2169652941817401399367819)
                      ·
                        rfl

theorem cell23_4225384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4225384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225384 prefixEnd_4225384 := by exact prefixLift 4225384
  have htrace : WordTrace (prefixWord ++ tailWord_4225384) baseStart_4225384 baseEnd_4225384 := by
    simpa [prefixWord, tailWord_4225384, baseEnd_4225384] using wordTrace_append hprefix tailTrace_4225384
  have hstable : (prefixWord ++ tailWord_4225384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225384).length < 2 ^ (prefixWord ++ tailWord_4225384).sum := by decide
  have hdescent : baseEnd_4225384 < baseStart_4225384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225420 : List Nat := [2, 2, 1, 2, 1, 6, 1, 8]
def baseStart_4225420 : Nat := 118140960795 + 4225420 * 2 ^ 59
def prefixEnd_4225420 : Nat := 4983230072969 + 3 ^ 40 * 4225420 * 2
def baseEnd_4225420 : Nat := 80358201004480120685839

theorem tailTrace_4225420 : CollatzResearch.WordTrace tailWord_4225420 prefixEnd_4225420 80358201004480120685839 := by
  unfold tailWord_4225420
  simp only [CollatzResearch.WordTrace]
  refine ⟨77056864176016229564036857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102742485568021639418715809 77056864176016229564036857)
  ·
    refine ⟨57792648132012172173027643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77056864176016229564036857 57792648132012172173027643)
    ·
      refine ⟨86688972198018258259541465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57792648132012172173027643 86688972198018258259541465)
      ·
        refine ⟨65016729148513693694656099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86688972198018258259541465 65016729148513693694656099)
        ·
          refine ⟨97525093722770540541984149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65016729148513693694656099 97525093722770540541984149)
          ·
            refine ⟨4571488768254869087905507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97525093722770540541984149 4571488768254869087905507)
            ·
              refine ⟨6857233152382303631858261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571488768254869087905507 6857233152382303631858261)
              ·
                refine ⟨80358201004480120685839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6857233152382303631858261 80358201004480120685839)
                ·
                  rfl

theorem cell23_4225420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 8].length) (baseStart_4225420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225420 prefixEnd_4225420 := by exact prefixLift 4225420
  have htrace : WordTrace (prefixWord ++ tailWord_4225420) baseStart_4225420 baseEnd_4225420 := by
    simpa [prefixWord, tailWord_4225420, baseEnd_4225420] using wordTrace_append hprefix tailTrace_4225420
  have hstable : (prefixWord ++ tailWord_4225420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225420).length < 2 ^ (prefixWord ++ tailWord_4225420).sum := by decide
  have hdescent : baseEnd_4225420 < baseStart_4225420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225433 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 2, 7]
def baseStart_4225433 : Nat := 118140960795 + 4225433 * 2 ^ 59
def prefixEnd_4225433 : Nat := 4983230072969 + 3 ^ 40 * 4225433 * 2
def baseEnd_4225433 : Nat := 723226034123157235885031

theorem tailTrace_4225433 : CollatzResearch.WordTrace tailWord_4225433 prefixEnd_4225433 723226034123157235885031 := by
  unfold tailWord_4225433
  simp only [CollatzResearch.WordTrace]
  refine ⟨154114202500985362348296953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102742801667323574898864635 154114202500985362348296953)
  ·
    refine ⟨115585651875739021761222715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154114202500985362348296953 115585651875739021761222715)
    ·
      refine ⟨173378477813608532641834073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115585651875739021761222715 173378477813608532641834073)
      ·
        refine ⟨130033858360206399481375555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173378477813608532641834073 130033858360206399481375555)
        ·
          refine ⟨195050787540309599222063333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130033858360206399481375555 195050787540309599222063333)
          ·
            refine ⟨36572022663808049854136875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195050787540309599222063333 36572022663808049854136875)
            ·
              refine ⟨54858033995712074781205313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36572022663808049854136875 54858033995712074781205313)
              ·
                refine ⟨41143525496784056085903985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54858033995712074781205313 41143525496784056085903985)
                ·
                  refine ⟨30857644122588042064427989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41143525496784056085903985 30857644122588042064427989)
                  ·
                    refine ⟨723226034123157235885031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30857644122588042064427989 723226034123157235885031)
                    ·
                      rfl

theorem cell23_4225433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_4225433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225433 prefixEnd_4225433 := by exact prefixLift 4225433
  have htrace : WordTrace (prefixWord ++ tailWord_4225433) baseStart_4225433 baseEnd_4225433 := by
    simpa [prefixWord, tailWord_4225433, baseEnd_4225433] using wordTrace_append hprefix tailTrace_4225433
  have hstable : (prefixWord ++ tailWord_4225433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225433).length < 2 ^ (prefixWord ++ tailWord_4225433).sum := by decide
  have hdescent : baseEnd_4225433 < baseStart_4225433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225437 : List Nat := [1, 4, 2, 1, 4, 1, 3, 7]
def baseStart_4225437 : Nat := 118140960795 + 4225437 * 2 ^ 59
def prefixEnd_4225437 : Nat := 4983230072969 + 3 ^ 40 * 4225437 * 2
def baseEnd_4225437 : Nat := 80358524307114433037225

theorem tailTrace_4225437 : CollatzResearch.WordTrace tailWord_4225437 prefixEnd_4225437 80358524307114433037225 := by
  unfold tailWord_4225437
  simp only [CollatzResearch.WordTrace]
  refine ⟨154114348392970871031442565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102742898928647247354295043 154114348392970871031442565)
  ·
    refine ⟨28896440323682038318395481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154114348392970871031442565 28896440323682038318395481)
    ·
      refine ⟨21672330242761528738796611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28896440323682038318395481 21672330242761528738796611)
      ·
        refine ⟨32508495364142293108194917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21672330242761528738796611 32508495364142293108194917)
        ·
          refine ⟨6095342880776679957786547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32508495364142293108194917 6095342880776679957786547)
          ·
            refine ⟨9143014321165019936679821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6095342880776679957786547 9143014321165019936679821)
            ·
              refine ⟨3428630370436882476254933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9143014321165019936679821 3428630370436882476254933)
              ·
                refine ⟨80358524307114433037225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3428630370436882476254933 80358524307114433037225)
                ·
                  rfl

theorem cell23_4225437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 7].length) (baseStart_4225437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225437 prefixEnd_4225437 := by exact prefixLift 4225437
  have htrace : WordTrace (prefixWord ++ tailWord_4225437) baseStart_4225437 baseEnd_4225437 := by
    simpa [prefixWord, tailWord_4225437, baseEnd_4225437] using wordTrace_append hprefix tailTrace_4225437
  have hstable : (prefixWord ++ tailWord_4225437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225437).length < 2 ^ (prefixWord ++ tailWord_4225437).sum := by decide
  have hdescent : baseEnd_4225437 < baseStart_4225437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225447 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_4225447 : Nat := 118140960795 + 4225447 * 2 ^ 59
def prefixEnd_4225447 : Nat := 4983230072969 + 3 ^ 40 * 4225447 * 2
def baseEnd_4225447 : Nat := 2169685291098634652880029

theorem tailTrace_4225447 : CollatzResearch.WordTrace tailWord_4225447 prefixEnd_4225447 2169685291098634652880029 := by
  unfold tailWord_4225447
  simp only [CollatzResearch.WordTrace]
  refine ⟨154114713122934642739306595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102743142081956428492871063 154114713122934642739306595)
  ·
    refine ⟨231172069684401964108959893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154114713122934642739306595 231172069684401964108959893)
    ·
      refine ⟨10836190766456342067607495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 231172069684401964108959893 10836190766456342067607495)
      ·
        refine ⟨16254286149684513101411243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10836190766456342067607495 16254286149684513101411243)
        ·
          refine ⟨24381429224526769652116865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16254286149684513101411243 24381429224526769652116865)
          ·
            refine ⟨18286071918395077239087649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24381429224526769652116865 18286071918395077239087649)
            ·
              refine ⟨13714553938796307929315737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18286071918395077239087649 13714553938796307929315737)
              ·
                refine ⟨10285915454097230946986803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13714553938796307929315737 10285915454097230946986803)
                ·
                  refine ⟨15428873181145846420480205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10285915454097230946986803 15428873181145846420480205)
                  ·
                    refine ⟨5785827442929692407680077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15428873181145846420480205 5785827442929692407680077)
                    ·
                      refine ⟨2169685291098634652880029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5785827442929692407680077 2169685291098634652880029)
                      ·
                        rfl

theorem cell23_4225447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_4225447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225447 prefixEnd_4225447 := by exact prefixLift 4225447
  have htrace : WordTrace (prefixWord ++ tailWord_4225447) baseStart_4225447 baseEnd_4225447 := by
    simpa [prefixWord, tailWord_4225447, baseEnd_4225447] using wordTrace_append hprefix tailTrace_4225447
  have hstable : (prefixWord ++ tailWord_4225447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225447).length < 2 ^ (prefixWord ++ tailWord_4225447).sum := by decide
  have hdescent : baseEnd_4225447 < baseStart_4225447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225448 : List Nat := [2, 1, 6, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4225448 : Nat := 118140960795 + 4225448 * 2 ^ 59
def prefixEnd_4225448 : Nat := 4983230072969 + 3 ^ 40 * 4225448 * 2
def baseEnd_4225448 : Nat := 2169685804579289148967525

theorem tailTrace_4225448 : CollatzResearch.WordTrace tailWord_4225448 prefixEnd_4225448 2169685804579289148967525 := by
  unfold tailWord_4225448
  simp only [CollatzResearch.WordTrace]
  refine ⟨77057374797965509955046499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102743166397287346606728665 77057374797965509955046499)
  ·
    refine ⟨115586062196948264932569749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77057374797965509955046499 115586062196948264932569749)
    ·
      refine ⟨5418096665481949918714207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 115586062196948264932569749 5418096665481949918714207)
      ·
        refine ⟨8127144998222924878071311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418096665481949918714207 8127144998222924878071311)
        ·
          refine ⟨12190717497334387317106967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8127144998222924878071311 12190717497334387317106967)
          ·
            refine ⟨18286076246001580975660451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12190717497334387317106967 18286076246001580975660451)
            ·
              refine ⟨27429114369002371463490677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18286076246001580975660451 27429114369002371463490677)
              ·
                refine ⟨2571479472093972324702251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27429114369002371463490677 2571479472093972324702251)
                ·
                  refine ⟨3857219208140958487053377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571479472093972324702251 3857219208140958487053377)
                  ·
                    refine ⟨2892914406105718865290033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3857219208140958487053377 2892914406105718865290033)
                    ·
                      refine ⟨2169685804579289148967525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892914406105718865290033 2169685804579289148967525)
                      ·
                        rfl

theorem cell23_4225448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4225448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225448 prefixEnd_4225448 := by exact prefixLift 4225448
  have htrace : WordTrace (prefixWord ++ tailWord_4225448) baseStart_4225448 baseEnd_4225448 := by
    simpa [prefixWord, tailWord_4225448, baseEnd_4225448] using wordTrace_append hprefix tailTrace_4225448
  have hstable : (prefixWord ++ tailWord_4225448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225448).length < 2 ^ (prefixWord ++ tailWord_4225448).sum := by decide
  have hdescent : baseEnd_4225448 < baseStart_4225448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225470 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4225470 : Nat := 118140960795 + 4225470 * 2 ^ 59
def prefixEnd_4225470 : Nat := 4983230072969 + 3 ^ 40 * 4225470 * 2
def baseEnd_4225470 : Nat := 2169697101153688062892423

theorem tailTrace_4225470 : CollatzResearch.WordTrace tailWord_4225470 prefixEnd_4225470 2169697101153688062892423 := by
  unfold tailWord_4225470
  simp only [CollatzResearch.WordTrace]
  refine ⟨19264444000231414708424233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102743701334567545111595909 19264444000231414708424233)
  ·
    refine ⟨14448333000173561031318175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19264444000231414708424233 14448333000173561031318175)
    ·
      refine ⟨21672499500260341546977263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14448333000173561031318175 21672499500260341546977263)
      ·
        refine ⟨32508749250390512320465895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21672499500260341546977263 32508749250390512320465895)
        ·
          refine ⟨48763123875585768480698843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32508749250390512320465895 48763123875585768480698843)
          ·
            refine ⟨73144685813378652721048265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48763123875585768480698843 73144685813378652721048265)
            ·
              refine ⟨54858514360033989540786199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73144685813378652721048265 54858514360033989540786199)
              ·
                refine ⟨82287771540050984311179299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54858514360033989540786199 82287771540050984311179299)
                ·
                  refine ⟨123431657310076476466768949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82287771540050984311179299 123431657310076476466768949)
                  ·
                    refine ⟨11571717872819669668759589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123431657310076476466768949 11571717872819669668759589)
                    ·
                      refine ⟨2169697101153688062892423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11571717872819669668759589 2169697101153688062892423)
                      ·
                        rfl

theorem cell23_4225470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4225470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225470 prefixEnd_4225470 := by exact prefixLift 4225470
  have htrace : WordTrace (prefixWord ++ tailWord_4225470) baseStart_4225470 baseEnd_4225470 := by
    simpa [prefixWord, tailWord_4225470, baseEnd_4225470] using wordTrace_append hprefix tailTrace_4225470
  have hstable : (prefixWord ++ tailWord_4225470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225470).length < 2 ^ (prefixWord ++ tailWord_4225470).sum := by decide
  have hdescent : baseEnd_4225470 < baseStart_4225470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225480 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 2, 6]
def baseStart_4225480 : Nat := 118140960795 + 4225480 * 2 ^ 59
def prefixEnd_4225480 : Nat := 4983230072969 + 3 ^ 40 * 4225480 * 2
def baseEnd_4225480 : Nat := 723234078653411007922459

theorem tailTrace_4225480 : CollatzResearch.WordTrace tailWord_4225480 prefixEnd_4225480 723234078653411007922459 := by
  unfold tailWord_4225480
  simp only [CollatzResearch.WordTrace]
  refine ⟨77057958365907544687628947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102743944487876726250171929 77057958365907544687628947)
  ·
    refine ⟨115586937548861317031443421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77057958365907544687628947 115586937548861317031443421)
    ·
      refine ⟨43345101580822993886791283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115586937548861317031443421 43345101580822993886791283)
      ·
        refine ⟨65017652371234490830186925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43345101580822993886791283 65017652371234490830186925)
        ·
          refine ⟨24381619639212934061320097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65017652371234490830186925 24381619639212934061320097)
          ·
            refine ⟨18286214729409700545990073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24381619639212934061320097 18286214729409700545990073)
            ·
              refine ⟨13714661047057275409492555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18286214729409700545990073 13714661047057275409492555)
              ·
                refine ⟨20571991570585913114238833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13714661047057275409492555 20571991570585913114238833)
                ·
                  refine ⟨15428993677939434835679125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20571991570585913114238833 15428993677939434835679125)
                  ·
                    refine ⟨723234078653411007922459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15428993677939434835679125 723234078653411007922459)
                    ·
                      rfl

theorem cell23_4225480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_4225480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225480 prefixEnd_4225480 := by exact prefixLift 4225480
  have htrace : WordTrace (prefixWord ++ tailWord_4225480) baseStart_4225480 baseEnd_4225480 := by
    simpa [prefixWord, tailWord_4225480, baseEnd_4225480] using wordTrace_append hprefix tailTrace_4225480
  have hstable : (prefixWord ++ tailWord_4225480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225480).length < 2 ^ (prefixWord ++ tailWord_4225480).sum := by decide
  have hdescent : baseEnd_4225480 < baseStart_4225480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225507 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 5]
def baseStart_4225507 : Nat := 118140960795 + 4225507 * 2 ^ 59
def prefixEnd_4225507 : Nat := 4983230072969 + 3 ^ 40 * 4225507 * 2
def baseEnd_4225507 : Nat := 2169716099937904418129753

theorem tailTrace_4225507 : CollatzResearch.WordTrace tailWord_4225507 prefixEnd_4225507 2169716099937904418129753 := by
  unfold tailWord_4225507
  simp only [CollatzResearch.WordTrace]
  refine ⟨154116901502717272986490775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102744601001811515324327183 154116901502717272986490775)
  ·
    refine ⟨231175352254075909479736163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154116901502717272986490775 231175352254075909479736163)
    ·
      refine ⟨346763028381113864219604245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231175352254075909479736163 346763028381113864219604245)
      ·
        refine ⟨16254516955364712385293949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 346763028381113864219604245 16254516955364712385293949)
        ·
          refine ⟨6095443858261767144485231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16254516955364712385293949 6095443858261767144485231)
          ·
            refine ⟨9143165787392650716727847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6095443858261767144485231 9143165787392650716727847)
            ·
              refine ⟨13714748681088976075091771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9143165787392650716727847 13714748681088976075091771)
              ·
                refine ⟨20572123021633464112637657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13714748681088976075091771 20572123021633464112637657)
                ·
                  refine ⟨15429092266225098084478243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20572123021633464112637657 15429092266225098084478243)
                  ·
                    refine ⟨23143638399337647126717365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15429092266225098084478243 23143638399337647126717365)
                    ·
                      refine ⟨2169716099937904418129753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23143638399337647126717365 2169716099937904418129753)
                      ·
                        rfl

theorem cell23_4225507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_4225507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225507 prefixEnd_4225507 := by exact prefixLift 4225507
  have htrace : WordTrace (prefixWord ++ tailWord_4225507) baseStart_4225507 baseEnd_4225507 := by
    simpa [prefixWord, tailWord_4225507, baseEnd_4225507] using wordTrace_append hprefix tailTrace_4225507
  have hstable : (prefixWord ++ tailWord_4225507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225507).length < 2 ^ (prefixWord ++ tailWord_4225507).sum := by decide
  have hdescent : baseEnd_4225507 < baseStart_4225507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225542 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_4225542 : Nat := 118140960795 + 4225542 * 2 ^ 59
def prefixEnd_4225542 : Nat := 4983230072969 + 3 ^ 40 * 4225542 * 2
def baseEnd_4225542 : Nat := 2169734071760811781192093

theorem tailTrace_4225542 : CollatzResearch.WordTrace tailWord_4225542 prefixEnd_4225542 2169734071760811781192093 := by
  unfold tailWord_4225542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816193064299702311375465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102745452038393649309343253 4816193064299702311375465)
  ·
    refine ⟨3612144798224776733531599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4816193064299702311375465 3612144798224776733531599)
    ·
      refine ⟨5418217197337165100297399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3612144798224776733531599 5418217197337165100297399)
      ·
        refine ⟨8127325796005747650446099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418217197337165100297399 8127325796005747650446099)
        ·
          refine ⟨12190988694008621475669149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8127325796005747650446099 12190988694008621475669149)
          ·
            refine ⟨4571620760253233053375931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12190988694008621475669149 4571620760253233053375931)
            ·
              refine ⟨6857431140379849580063897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571620760253233053375931 6857431140379849580063897)
              ·
                refine ⟨5143073355284887185047923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6857431140379849580063897 5143073355284887185047923)
                ·
                  refine ⟨7714610032927330777571885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5143073355284887185047923 7714610032927330777571885)
                  ·
                    refine ⟨2892978762347749041589457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7714610032927330777571885 2892978762347749041589457)
                    ·
                      refine ⟨2169734071760811781192093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2892978762347749041589457 2169734071760811781192093)
                      ·
                        rfl

theorem cell23_4225542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_4225542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225542 prefixEnd_4225542 := by exact prefixLift 4225542
  have htrace : WordTrace (prefixWord ++ tailWord_4225542) baseStart_4225542 baseEnd_4225542 := by
    simpa [prefixWord, tailWord_4225542, baseEnd_4225542] using wordTrace_append hprefix tailTrace_4225542
  have hstable : (prefixWord ++ tailWord_4225542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225542).length < 2 ^ (prefixWord ++ tailWord_4225542).sum := by decide
  have hdescent : baseEnd_4225542 < baseStart_4225542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225557 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_4225557 : Nat := 118140960795 + 4225557 * 2 ^ 59
def prefixEnd_4225557 : Nat := 4983230072969 + 3 ^ 40 * 4225557 * 2
def baseEnd_4225557 : Nat := 723247257990209740834841

theorem tailTrace_4225557 : CollatzResearch.WordTrace tailWord_4225557 prefixEnd_4225557 723247257990209740834841 := by
  unfold tailWord_4225557
  simp only [CollatzResearch.WordTrace]
  refine ⟨154118725152536131525810925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102745816768357421017207283 154118725152536131525810925)
  ·
    refine ⟨57794521932201049322179097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154118725152536131525810925 57794521932201049322179097)
    ·
      refine ⟨43345891449150786991634323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57794521932201049322179097 43345891449150786991634323)
      ·
        refine ⟨65018837173726180487451485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43345891449150786991634323 65018837173726180487451485)
        ·
          refine ⟨24382063940147317682794307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65018837173726180487451485 24382063940147317682794307)
          ·
            refine ⟨36573095910220976524191461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24382063940147317682794307 36573095910220976524191461)
            ·
              refine ⟨6857455483166433098285899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36573095910220976524191461 6857455483166433098285899)
              ·
                refine ⟨10286183224749649647428849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6857455483166433098285899 10286183224749649647428849)
                ·
                  refine ⟨7714637418562237235571637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10286183224749649647428849 7714637418562237235571637)
                  ·
                    refine ⟨723247257990209740834841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7714637418562237235571637 723247257990209740834841)
                    ·
                      rfl

theorem cell23_4225557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_4225557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225557 prefixEnd_4225557 := by exact prefixLift 4225557
  have htrace : WordTrace (prefixWord ++ tailWord_4225557) baseStart_4225557 baseEnd_4225557 := by
    simpa [prefixWord, tailWord_4225557, baseEnd_4225557] using wordTrace_append hprefix tailTrace_4225557
  have hstable : (prefixWord ++ tailWord_4225557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225557).length < 2 ^ (prefixWord ++ tailWord_4225557).sum := by decide
  have hdescent : baseEnd_4225557 < baseStart_4225557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225587 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 3, 4]
def baseStart_4225587 : Nat := 118140960795 + 4225587 * 2 ^ 59
def prefixEnd_4225587 : Nat := 4983230072969 + 3 ^ 40 * 4225587 * 2
def baseEnd_4225587 : Nat := 723252392796754701709795

theorem tailTrace_4225587 : CollatzResearch.WordTrace tailWord_4225587 prefixEnd_4225587 723252392796754701709795 := by
  unfold tailWord_4225587
  simp only [CollatzResearch.WordTrace]
  refine ⟨154119819342427446649403015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102746546228284964432935343 154119819342427446649403015)
  ·
    refine ⟨231179729013641169974104523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154119819342427446649403015 231179729013641169974104523)
    ·
      refine ⟨346769593520461754961156785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231179729013641169974104523 346769593520461754961156785)
      ·
        refine ⟨260077195140346316220867589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346769593520461754961156785 260077195140346316220867589)
        ·
          refine ⟨48764474088814934291412673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260077195140346316220867589 48764474088814934291412673)
          ·
            refine ⟨36573355566611200718559505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48764474088814934291412673 36573355566611200718559505)
            ·
              refine ⟨27430016674958400538919629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36573355566611200718559505 27430016674958400538919629)
              ·
                refine ⟨10286256253109400202094861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27430016674958400538919629 10286256253109400202094861)
                ·
                  refine ⟨3857346094916025075785573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10286256253109400202094861 3857346094916025075785573)
                  ·
                    refine ⟨723252392796754701709795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857346094916025075785573 723252392796754701709795)
                    ·
                      rfl

theorem cell23_4225587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 4].length) (baseStart_4225587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225587 prefixEnd_4225587 := by exact prefixLift 4225587
  have htrace : WordTrace (prefixWord ++ tailWord_4225587) baseStart_4225587 baseEnd_4225587 := by
    simpa [prefixWord, tailWord_4225587, baseEnd_4225587] using wordTrace_append hprefix tailTrace_4225587
  have hstable : (prefixWord ++ tailWord_4225587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225587).length < 2 ^ (prefixWord ++ tailWord_4225587).sum := by decide
  have hdescent : baseEnd_4225587 < baseStart_4225587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225594 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2]
def baseStart_4225594 : Nat := 118140960795 + 4225594 * 2 ^ 59
def prefixEnd_4225594 : Nat := 4983230072969 + 3 ^ 40 * 4225594 * 2
def baseEnd_4225594 : Nat := 2169760772754845577741853

theorem tailTrace_4225594 : CollatzResearch.WordTrace tailWord_4225594 prefixEnd_4225594 2169760772754845577741853 := by
  unfold tailWord_4225594
  simp only [CollatzResearch.WordTrace]
  refine ⟨38530018663350521711226959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102746716435601391229938557 38530018663350521711226959)
  ·
    refine ⟨57795027995025782566840439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38530018663350521711226959 57795027995025782566840439)
    ·
      refine ⟨86692541992538673850260659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57795027995025782566840439 86692541992538673850260659)
      ·
        refine ⟨130038812988808010775390989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86692541992538673850260659 130038812988808010775390989)
        ·
          refine ⟨48764554870803004040771621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130038812988808010775390989 48764554870803004040771621)
          ·
            refine ⟨9143354038275563257644679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48764554870803004040771621 9143354038275563257644679)
            ·
              refine ⟨13715031057413344886467019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9143354038275563257644679 13715031057413344886467019)
              ·
                refine ⟨20572546586120017329700529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13715031057413344886467019 20572546586120017329700529)
                ·
                  refine ⟨15429409939590012997275397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20572546586120017329700529 15429409939590012997275397)
                  ·
                    refine ⟨2893014363673127436989137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15429409939590012997275397 2893014363673127436989137)
                    ·
                      refine ⟨2169760772754845577741853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893014363673127436989137 2169760772754845577741853)
                      ·
                        rfl

theorem cell23_4225594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_4225594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225594 prefixEnd_4225594 := by exact prefixLift 4225594
  have htrace : WordTrace (prefixWord ++ tailWord_4225594) baseStart_4225594 baseEnd_4225594 := by
    simpa [prefixWord, tailWord_4225594, baseEnd_4225594] using wordTrace_append hprefix tailTrace_4225594
  have hstable : (prefixWord ++ tailWord_4225594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225594).length < 2 ^ (prefixWord ++ tailWord_4225594).sum := by decide
  have hdescent : baseEnd_4225594 < baseStart_4225594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225614 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_4225614 : Nat := 118140960795 + 4225614 * 2 ^ 59
def prefixEnd_4225614 : Nat := 4983230072969 + 3 ^ 40 * 4225614 * 2
def baseEnd_4225614 : Nat := 2169771042367935499491761

theorem tailTrace_4225614 : CollatzResearch.WordTrace tailWord_4225614 prefixEnd_4225614 2169771042367935499491761 := by
  unfold tailWord_4225614
  simp only [CollatzResearch.WordTrace]
  refine ⟨19265100514166203782579487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102747202742219753507090597 19265100514166203782579487)
  ·
    refine ⟨28897650771249305673869231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19265100514166203782579487 28897650771249305673869231)
    ·
      refine ⟨43346476156873958510803847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28897650771249305673869231 43346476156873958510803847)
      ·
        refine ⟨65019714235310937766205771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43346476156873958510803847 65019714235310937766205771)
        ·
          refine ⟨97529571352966406649308657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65019714235310937766205771 97529571352966406649308657)
          ·
            refine ⟨73147178514724804986981493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97529571352966406649308657 73147178514724804986981493)
            ·
              refine ⟨6857547985755450467529515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73147178514724804986981493 6857547985755450467529515)
              ·
                refine ⟨10286321978633175701294273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6857547985755450467529515 10286321978633175701294273)
                ·
                  refine ⟨7714741483974881775970705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10286321978633175701294273 7714741483974881775970705)
                  ·
                    refine ⟨5786056112981161331978029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7714741483974881775970705 5786056112981161331978029)
                    ·
                      refine ⟨2169771042367935499491761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786056112981161331978029 2169771042367935499491761)
                      ·
                        rfl

theorem cell23_4225614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_4225614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225614 prefixEnd_4225614 := by exact prefixLift 4225614
  have htrace : WordTrace (prefixWord ++ tailWord_4225614) baseStart_4225614 baseEnd_4225614 := by
    simpa [prefixWord, tailWord_4225614, baseEnd_4225614] using wordTrace_append hprefix tailTrace_4225614
  have hstable : (prefixWord ++ tailWord_4225614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225614).length < 2 ^ (prefixWord ++ tailWord_4225614).sum := by decide
  have hdescent : baseEnd_4225614 < baseStart_4225614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225644 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_4225644 : Nat := 118140960795 + 4225644 * 2 ^ 59
def prefixEnd_4225644 : Nat := 4983230072969 + 3 ^ 40 * 4225644 * 2
def baseEnd_4225644 : Nat := 2169786446787570382116623

theorem tailTrace_4225644 : CollatzResearch.WordTrace tailWord_4225644 prefixEnd_4225644 2169786446787570382116623 := by
  unfold tailWord_4225644
  simp only [CollatzResearch.WordTrace]
  refine ⟨77060949151610472692113993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102747932202147296922818657 77060949151610472692113993)
  ·
    refine ⟨57795711863707854519085495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77060949151610472692113993 57795711863707854519085495)
    ·
      refine ⟨86693567795561781778628243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57795711863707854519085495 86693567795561781778628243)
      ·
        refine ⟨130040351693342672667942365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86693567795561781778628243 130040351693342672667942365)
        ·
          refine ⟨48765131885003502250478387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130040351693342672667942365 48765131885003502250478387)
          ·
            refine ⟨73147697827505253375717581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48765131885003502250478387 73147697827505253375717581)
            ·
              refine ⟨27430386685314470015894093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73147697827505253375717581 27430386685314470015894093)
              ·
                refine ⟨10286395006992926255960285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27430386685314470015894093 10286395006992926255960285)
                ·
                  refine ⟨3857398127622347345985107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10286395006992926255960285 3857398127622347345985107)
                  ·
                    refine ⟨5786097191433521018977661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3857398127622347345985107 5786097191433521018977661)
                    ·
                      refine ⟨2169786446787570382116623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786097191433521018977661 2169786446787570382116623)
                      ·
                        rfl

theorem cell23_4225644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_4225644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225644 prefixEnd_4225644 := by exact prefixLift 4225644
  have htrace : WordTrace (prefixWord ++ tailWord_4225644) baseStart_4225644 baseEnd_4225644 := by
    simpa [prefixWord, tailWord_4225644, baseEnd_4225644] using wordTrace_append hprefix tailTrace_4225644
  have hstable : (prefixWord ++ tailWord_4225644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225644).length < 2 ^ (prefixWord ++ tailWord_4225644).sum := by decide
  have hdescent : baseEnd_4225644 < baseStart_4225644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225664 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 1, 5]
def baseStart_4225664 : Nat := 118140960795 + 4225664 * 2 ^ 59
def prefixEnd_4225664 : Nat := 4983230072969 + 3 ^ 40 * 4225664 * 2
def baseEnd_4225664 : Nat := 723265572133553434622177

theorem tailTrace_4225664 : CollatzResearch.WordTrace tailWord_4225664 prefixEnd_4225664 723265572133553434622177 := by
  unfold tailWord_4225664
  simp only [CollatzResearch.WordTrace]
  refine ⟨77061313881574244399978023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102748418508765659199970697 77061313881574244399978023)
  ·
    refine ⟨115591970822361366599967035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77061313881574244399978023 115591970822361366599967035)
    ·
      refine ⟨173387956233542049899950553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115591970822361366599967035 173387956233542049899950553)
      ·
        refine ⟨130040967175156537424962915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173387956233542049899950553 130040967175156537424962915)
        ·
          refine ⟨195061450762734806137444373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130040967175156537424962915 195061450762734806137444373)
          ·
            refine ⟨9143505504503194037692705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 195061450762734806137444373 9143505504503194037692705)
            ·
              refine ⟨6857629128377395528269529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9143505504503194037692705 6857629128377395528269529)
              ·
                refine ⟨5143221846283046646202147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6857629128377395528269529 5143221846283046646202147)
                ·
                  refine ⟨7714832769424569969303221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5143221846283046646202147 7714832769424569969303221)
                  ·
                    refine ⟨723265572133553434622177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7714832769424569969303221 723265572133553434622177)
                    ·
                      rfl

theorem cell23_4225664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_4225664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225664 prefixEnd_4225664 := by exact prefixLift 4225664
  have htrace : WordTrace (prefixWord ++ tailWord_4225664) baseStart_4225664 baseEnd_4225664 := by
    simpa [prefixWord, tailWord_4225664, baseEnd_4225664] using wordTrace_append hprefix tailTrace_4225664
  have hstable : (prefixWord ++ tailWord_4225664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225664).length < 2 ^ (prefixWord ++ tailWord_4225664).sum := by decide
  have hdescent : baseEnd_4225664 < baseStart_4225664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225667 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 4]
def baseStart_4225667 : Nat := 118140960795 + 4225667 * 2 ^ 59
def prefixEnd_4225667 : Nat := 4983230072969 + 3 ^ 40 * 4225667 * 2
def baseEnd_4225667 : Nat := 2169798256842623792129017

theorem tailTrace_4225667 : CollatzResearch.WordTrace tailWord_4225667 prefixEnd_4225667 2169798256842623792129017 := by
  unfold tailWord_4225667
  simp only [CollatzResearch.WordTrace]
  refine ⟨154122737182137620312315255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102748491454758413541543503 154122737182137620312315255)
  ·
    refine ⟨231184105773206430468472883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154122737182137620312315255 231184105773206430468472883)
    ·
      refine ⟨346776158659809645702709325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231184105773206430468472883 346776158659809645702709325)
      ·
        refine ⟨130041059497428617138515997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346776158659809645702709325 130041059497428617138515997)
        ·
          refine ⟨48765397311535731426943499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130041059497428617138515997 48765397311535731426943499)
          ·
            refine ⟨73148095967303597140415249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48765397311535731426943499 73148095967303597140415249)
            ·
              refine ⟨54861071975477697855311437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73148095967303597140415249 54861071975477697855311437)
              ·
                refine ⟨20572901990804136695741789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54861071975477697855311437 20572901990804136695741789)
                ·
                  refine ⟨7714838246551551260903171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20572901990804136695741789 7714838246551551260903171)
                  ·
                    refine ⟨11572257369827326891354757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7714838246551551260903171 11572257369827326891354757)
                    ·
                      refine ⟨2169798256842623792129017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11572257369827326891354757 2169798256842623792129017)
                      ·
                        rfl

theorem cell23_4225667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_4225667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225667 prefixEnd_4225667 := by exact prefixLift 4225667
  have htrace : WordTrace (prefixWord ++ tailWord_4225667) baseStart_4225667 baseEnd_4225667 := by
    simpa [prefixWord, tailWord_4225667, baseEnd_4225667] using wordTrace_append hprefix tailTrace_4225667
  have hstable : (prefixWord ++ tailWord_4225667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225667).length < 2 ^ (prefixWord ++ tailWord_4225667).sum := by decide
  have hdescent : baseEnd_4225667 < baseStart_4225667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225711 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 2, 4]
def baseStart_4225711 : Nat := 118140960795 + 4225711 * 2 ^ 59
def prefixEnd_4225711 : Nat := 4983230072969 + 3 ^ 40 * 4225711 * 2
def baseEnd_4225711 : Nat := 723273616663807206659605

theorem tailTrace_4225711 : CollatzResearch.WordTrace tailWord_4225711 prefixEnd_4225711 723273616663807206659605 := by
  unfold tailWord_4225711
  simp only [CollatzResearch.WordTrace]
  refine ⟨154124341993978215826916987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102749561329318810551277991 154124341993978215826916987)
  ·
    refine ⟨231186512990967323740375481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154124341993978215826916987 231186512990967323740375481)
    ·
      refine ⟨173389884743225492805281611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231186512990967323740375481 173389884743225492805281611)
      ·
        refine ⟨260084827114838239207922417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173389884743225492805281611 260084827114838239207922417)
        ·
          refine ⟨195063620336128679405941813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260084827114838239207922417 195063620336128679405941813)
          ·
            refine ⟨18287214406512063694307045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 195063620336128679405941813 18287214406512063694307045)
            ·
              refine ⟨3428852701221011942682571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18287214406512063694307045 3428852701221011942682571)
              ·
                refine ⟨5143279051831517914023857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428852701221011942682571 5143279051831517914023857)
                ·
                  refine ⟨3857459288873638435517893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5143279051831517914023857 3857459288873638435517893)
                  ·
                    refine ⟨723273616663807206659605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857459288873638435517893 723273616663807206659605)
                    ·
                      rfl

theorem cell23_4225711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 4].length) (baseStart_4225711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225711 prefixEnd_4225711 := by exact prefixLift 4225711
  have htrace : WordTrace (prefixWord ++ tailWord_4225711) baseStart_4225711 baseEnd_4225711 := by
    simpa [prefixWord, tailWord_4225711, baseEnd_4225711] using wordTrace_append hprefix tailTrace_4225711
  have hstable : (prefixWord ++ tailWord_4225711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225711).length < 2 ^ (prefixWord ++ tailWord_4225711).sum := by decide
  have hdescent : baseEnd_4225711 < baseStart_4225711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225718 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4225718 : Nat := 118140960795 + 4225718 * 2 ^ 59
def prefixEnd_4225718 : Nat := 4983230072969 + 3 ^ 40 * 4225718 * 2
def baseEnd_4225718 : Nat := 2169824444356003092591283

theorem tailTrace_4225718 : CollatzResearch.WordTrace tailWord_4225718 prefixEnd_4225718 2169824444356003092591283 := by
  unfold tailWord_4225718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632787331559553501401363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102749731536635237348281205 9632787331559553501401363)
  ·
    refine ⟨14449180997339330252102045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9632787331559553501401363 14449180997339330252102045)
    ·
      refine ⟨5418442874002248844538267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14449180997339330252102045 5418442874002248844538267)
      ·
        refine ⟨8127664311003373266807401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418442874002248844538267 8127664311003373266807401)
        ·
          refine ⟨6095748233252529950105551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8127664311003373266807401 6095748233252529950105551)
          ·
            refine ⟨9143622349878794925158327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6095748233252529950105551 9143622349878794925158327)
            ·
              refine ⟨13715433524818192387737491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9143622349878794925158327 13715433524818192387737491)
              ·
                refine ⟨20573150287227288581606237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13715433524818192387737491 20573150287227288581606237)
                ·
                  refine ⟨7714931357710233218102339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20573150287227288581606237 7714931357710233218102339)
                  ·
                    refine ⟨11572397036565349827153509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7714931357710233218102339 11572397036565349827153509)
                    ·
                      refine ⟨2169824444356003092591283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11572397036565349827153509 2169824444356003092591283)
                      ·
                        rfl

theorem cell23_4225718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4225718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225718 prefixEnd_4225718 := by exact prefixLift 4225718
  have htrace : WordTrace (prefixWord ++ tailWord_4225718) baseStart_4225718 baseEnd_4225718 := by
    simpa [prefixWord, tailWord_4225718, baseEnd_4225718] using wordTrace_append hprefix tailTrace_4225718
  have hstable : (prefixWord ++ tailWord_4225718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225718).length < 2 ^ (prefixWord ++ tailWord_4225718).sum := by decide
  have hdescent : baseEnd_4225718 < baseStart_4225718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225738 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_4225738 : Nat := 118140960795 + 4225738 * 2 ^ 59
def prefixEnd_4225738 : Nat := 4983230072969 + 3 ^ 40 * 4225738 * 2
def baseEnd_4225738 : Nat := 2169834713969093014341191

theorem tailTrace_4225738 : CollatzResearch.WordTrace tailWord_4225738 prefixEnd_4225738 2169834713969093014341191 := by
  unfold tailWord_4225738
  simp only [CollatzResearch.WordTrace]
  refine ⟨38531331691220099859537467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102750217843253599625433245 38531331691220099859537467)
  ·
    refine ⟨57796997536830149789306201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38531331691220099859537467 57796997536830149789306201)
    ·
      refine ⟨43347748152622612341979651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57796997536830149789306201 43347748152622612341979651)
      ·
        refine ⟨65021622228933918512969477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43347748152622612341979651 65021622228933918512969477)
        ·
          refine ⟨12191554167925109721181777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65021622228933918512969477 12191554167925109721181777)
          ·
            refine ⟨9143665625943832290886333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12191554167925109721181777 9143665625943832290886333)
            ·
              refine ⟨3428874609728937109082375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9143665625943832290886333 3428874609728937109082375)
              ·
                refine ⟨5143311914593405663623563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428874609728937109082375 5143311914593405663623563)
                ·
                  refine ⟨7714967871890108495435345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5143311914593405663623563 7714967871890108495435345)
                  ·
                    refine ⟨5786225903917581371576509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7714967871890108495435345 5786225903917581371576509)
                    ·
                      refine ⟨2169834713969093014341191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786225903917581371576509 2169834713969093014341191)
                      ·
                        rfl

theorem cell23_4225738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_4225738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225738 prefixEnd_4225738 := by exact prefixLift 4225738
  have htrace : WordTrace (prefixWord ++ tailWord_4225738) baseStart_4225738 baseEnd_4225738 := by
    simpa [prefixWord, tailWord_4225738, baseEnd_4225738] using wordTrace_append hprefix tailTrace_4225738
  have hstable : (prefixWord ++ tailWord_4225738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225738).length < 2 ^ (prefixWord ++ tailWord_4225738).sum := by decide
  have hdescent : baseEnd_4225738 < baseStart_4225738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225741 : List Nat := [1, 6, 2, 1, 3, 10]
def baseStart_4225741 : Nat := 118140960795 + 4225741 * 2 ^ 59
def prefixEnd_4225741 : Nat := 4983230072969 + 3 ^ 40 * 4225741 * 2
def baseEnd_4225741 : Nat := 8929367302103113179439

theorem tailTrace_4225741 : CollatzResearch.WordTrace tailWord_4225741 prefixEnd_4225741 8929367302103113179439 := by
  unfold tailWord_4225741
  simp only [CollatzResearch.WordTrace]
  refine ⟨154125436183869530950509077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102750290789246353967006051 154125436183869530950509077)
  ·
    refine ⟨7224629821118884263305113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154125436183869530950509077 7224629821118884263305113)
    ·
      refine ⟨5418472365839163197478835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7224629821118884263305113 5418472365839163197478835)
      ·
        refine ⟨8127708548758744796218253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418472365839163197478835 8127708548758744796218253)
        ·
          refine ⟨3047890705784529298581845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8127708548758744796218253 3047890705784529298581845)
          ·
            refine ⟨8929367302103113179439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3047890705784529298581845 8929367302103113179439)
            ·
              rfl

theorem cell23_4225741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 10].length) (baseStart_4225741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225741 prefixEnd_4225741 := by exact prefixLift 4225741
  have htrace : WordTrace (prefixWord ++ tailWord_4225741) baseStart_4225741 baseEnd_4225741 := by
    simpa [prefixWord, tailWord_4225741, baseEnd_4225741] using wordTrace_append hprefix tailTrace_4225741
  have hstable : (prefixWord ++ tailWord_4225741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225741).length < 2 ^ (prefixWord ++ tailWord_4225741).sum := by decide
  have hdescent : baseEnd_4225741 < baseStart_4225741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225751 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_4225751 : Nat := 118140960795 + 4225751 * 2 ^ 59
def prefixEnd_4225751 : Nat := 4983230072969 + 3 ^ 40 * 4225751 * 2
def baseEnd_4225751 : Nat := 2169841389217601463478631

theorem tailTrace_4225751 : CollatzResearch.WordTrace tailWord_4225751 prefixEnd_4225751 2169841389217601463478631 := by
  unfold tailWord_4225751
  simp only [CollatzResearch.WordTrace]
  refine ⟨154125800913833302658373107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102750533942555535105582071 154125800913833302658373107)
  ·
    refine ⟨231188701370749953987559661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154125800913833302658373107 231188701370749953987559661)
    ·
      refine ⟨86695763014031232745334873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231188701370749953987559661 86695763014031232745334873)
      ·
        refine ⟨65021822260523424559001155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86695763014031232745334873 65021822260523424559001155)
        ·
          refine ⟨97532733390785136838501733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65021822260523424559001155 97532733390785136838501733)
          ·
            refine ⟨18287387510772213157219075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97532733390785136838501733 18287387510772213157219075)
            ·
              refine ⟨27431081266158319735828613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18287387510772213157219075 27431081266158319735828613)
              ·
                refine ⟨5143327737404684950467865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27431081266158319735828613 5143327737404684950467865)
                ·
                  refine ⟨3857495803053513712850899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5143327737404684950467865 3857495803053513712850899)
                  ·
                    refine ⟨5786243704580270569276349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3857495803053513712850899 5786243704580270569276349)
                    ·
                      refine ⟨2169841389217601463478631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786243704580270569276349 2169841389217601463478631)
                      ·
                        rfl

theorem cell23_4225751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_4225751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225751 prefixEnd_4225751 := by exact prefixLift 4225751
  have htrace : WordTrace (prefixWord ++ tailWord_4225751) baseStart_4225751 baseEnd_4225751 := by
    simpa [prefixWord, tailWord_4225751, baseEnd_4225751] using wordTrace_append hprefix tailTrace_4225751
  have hstable : (prefixWord ++ tailWord_4225751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225751).length < 2 ^ (prefixWord ++ tailWord_4225751).sum := by decide
  have hdescent : baseEnd_4225751 < baseStart_4225751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225752 : List Nat := [2, 1, 2, 2, 3, 4, 2, 2, 1, 2, 2]
def baseStart_4225752 : Nat := 118140960795 + 4225752 * 2 ^ 59
def prefixEnd_4225752 : Nat := 4983230072969 + 3 ^ 40 * 4225752 * 2
def baseEnd_4225752 : Nat := 2169841902698255959566127

theorem tailTrace_4225752 : CollatzResearch.WordTrace tailWord_4225752 prefixEnd_4225752 2169841902698255959566127 := by
  unfold tailWord_4225752
  simp only [CollatzResearch.WordTrace]
  refine ⟨77062918693414839914579755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102750558257886453219439673 77062918693414839914579755)
  ·
    refine ⟨115594378040122259871869633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77062918693414839914579755 115594378040122259871869633)
    ·
      refine ⟨86695783530091694903902225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115594378040122259871869633 86695783530091694903902225)
      ·
        refine ⟨65021837647568771177926669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86695783530091694903902225 65021837647568771177926669)
        ·
          refine ⟨24383189117838289191722501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65021837647568771177926669 24383189117838289191722501)
          ·
            refine ⟨4571847959594679223447969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24383189117838289191722501 4571847959594679223447969)
            ·
              refine ⟨3428885969696009417585977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4571847959594679223447969 3428885969696009417585977)
              ·
                refine ⟨2571664477272007063189483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3428885969696009417585977 2571664477272007063189483)
                ·
                  refine ⟨3857496715908010594784225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571664477272007063189483 3857496715908010594784225)
                  ·
                    refine ⟨2893122536931007946088169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3857496715908010594784225 2893122536931007946088169)
                    ·
                      refine ⟨2169841902698255959566127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893122536931007946088169 2169841902698255959566127)
                      ·
                        rfl

theorem cell23_4225752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_4225752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225752 prefixEnd_4225752 := by exact prefixLift 4225752
  have htrace : WordTrace (prefixWord ++ tailWord_4225752) baseStart_4225752 baseEnd_4225752 := by
    simpa [prefixWord, tailWord_4225752, baseEnd_4225752] using wordTrace_append hprefix tailTrace_4225752
  have hstable : (prefixWord ++ tailWord_4225752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225752).length < 2 ^ (prefixWord ++ tailWord_4225752).sum := by decide
  have hdescent : baseEnd_4225752 < baseStart_4225752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225761 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_4225761 : Nat := 118140960795 + 4225761 * 2 ^ 59
def prefixEnd_4225761 : Nat := 4983230072969 + 3 ^ 40 * 4225761 * 2
def baseEnd_4225761 : Nat := 2169846524024146424353585

theorem tailTrace_4225761 : CollatzResearch.WordTrace tailWord_4225761 prefixEnd_4225761 2169846524024146424353585 := by
  unfold tailWord_4225761
  simp only [CollatzResearch.WordTrace]
  refine ⟨154126165643797074366237137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102750777095864716244158091 154126165643797074366237137)
  ·
    refine ⟨115594624232847805774677853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154126165643797074366237137 115594624232847805774677853)
    ·
      refine ⟨43347984087317927165504195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115594624232847805774677853 43347984087317927165504195)
      ·
        refine ⟨65021976130976890748256293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43347984087317927165504195 65021976130976890748256293)
        ·
          refine ⟨12191620524558167015298055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65021976130976890748256293 12191620524558167015298055)
          ·
            refine ⟨18287430786837250522947083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12191620524558167015298055 18287430786837250522947083)
            ·
              refine ⟨27431146180255875784420625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18287430786837250522947083 27431146180255875784420625)
              ·
                refine ⟨20573359635191906838315469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27431146180255875784420625 20573359635191906838315469)
                ·
                  refine ⟨7715009863196965064368301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20573359635191906838315469 7715009863196965064368301)
                  ·
                    refine ⟨2893128698698861899138113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7715009863196965064368301 2893128698698861899138113)
                    ·
                      refine ⟨2169846524024146424353585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893128698698861899138113 2169846524024146424353585)
                      ·
                        rfl

theorem cell23_4225761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_4225761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225761 prefixEnd_4225761 := by exact prefixLift 4225761
  have htrace : WordTrace (prefixWord ++ tailWord_4225761) baseStart_4225761 baseEnd_4225761 := by
    simpa [prefixWord, tailWord_4225761, baseEnd_4225761] using wordTrace_append hprefix tailTrace_4225761
  have hstable : (prefixWord ++ tailWord_4225761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225761).length < 2 ^ (prefixWord ++ tailWord_4225761).sum := by decide
  have hdescent : baseEnd_4225761 < baseStart_4225761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225791 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 4, 2, 2]
def baseStart_4225791 : Nat := 118140960795 + 4225791 * 2 ^ 59
def prefixEnd_4225791 : Nat := 4983230072969 + 3 ^ 40 * 4225791 * 2
def baseEnd_4225791 : Nat := 2169861928443781306978447

theorem tailTrace_4225791 : CollatzResearch.WordTrace tailWord_4225791 prefixEnd_4225791 2169861928443781306978447 := by
  unfold tailWord_4225791
  simp only [CollatzResearch.WordTrace]
  refine ⟨154127259833688389489829227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102751506555792259659886151 154127259833688389489829227)
  ·
    refine ⟨231190889750532584234743841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154127259833688389489829227 231190889750532584234743841)
    ·
      refine ⟨173393167312899438176057881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231190889750532584234743841 173393167312899438176057881)
      ·
        refine ⟨130044875484674578632043411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173393167312899438176057881 130044875484674578632043411)
        ·
          refine ⟨195067313227011867948065117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130044875484674578632043411 195067313227011867948065117)
          ·
            refine ⟨73150242460129450480524419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195067313227011867948065117 73150242460129450480524419)
            ·
              refine ⟨109725363690194175720786629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73150242460129450480524419 109725363690194175720786629)
              ·
                refine ⟨20573505691911407947647493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109725363690194175720786629 20573505691911407947647493)
                ·
                  refine ⟨3857532317233388990183905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20573505691911407947647493 3857532317233388990183905)
                  ·
                    refine ⟨2893149237925041742637929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3857532317233388990183905 2893149237925041742637929)
                    ·
                      refine ⟨2169861928443781306978447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893149237925041742637929 2169861928443781306978447)
                      ·
                        rfl

theorem cell23_4225791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_4225791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225791 prefixEnd_4225791 := by exact prefixLift 4225791
  have htrace : WordTrace (prefixWord ++ tailWord_4225791) baseStart_4225791 baseEnd_4225791 := by
    simpa [prefixWord, tailWord_4225791, baseEnd_4225791] using wordTrace_append hprefix tailTrace_4225791
  have hstable : (prefixWord ++ tailWord_4225791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225791).length < 2 ^ (prefixWord ++ tailWord_4225791).sum := by decide
  have hdescent : baseEnd_4225791 < baseStart_4225791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225825 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_4225825 : Nat := 118140960795 + 4225825 * 2 ^ 59
def prefixEnd_4225825 : Nat := 4983230072969 + 3 ^ 40 * 4225825 * 2
def baseEnd_4225825 : Nat := 2169879386786034173953291

theorem tailTrace_4225825 : CollatzResearch.WordTrace tailWord_4225825 prefixEnd_4225825 2169879386786034173953291 := by
  unfold tailWord_4225825
  simp only [CollatzResearch.WordTrace]
  refine ⟨154128499915565213296566929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102752333277043475531044619 154128499915565213296566929)
  ·
    refine ⟨115596374936673909972425197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154128499915565213296566929 115596374936673909972425197)
    ·
      refine ⟨43348640601252716239659449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115596374936673909972425197 43348640601252716239659449)
      ·
        refine ⟨32511480450939537179744587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43348640601252716239659449 32511480450939537179744587)
        ·
          refine ⟨48767220676409305769616881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32511480450939537179744587 48767220676409305769616881)
          ·
            refine ⟨36575415507306979327212661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48767220676409305769616881 36575415507306979327212661)
            ·
              refine ⟨3428945203810029311926187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36575415507306979327212661 3428945203810029311926187)
              ·
                refine ⟨5143417805715043967889281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428945203810029311926187 5143417805715043967889281)
                ·
                  refine ⟨3857563354286282975916961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5143417805715043967889281 3857563354286282975916961)
                  ·
                    refine ⟨2893172515714712231937721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3857563354286282975916961 2893172515714712231937721)
                    ·
                      refine ⟨2169879386786034173953291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893172515714712231937721 2169879386786034173953291)
                      ·
                        rfl

theorem cell23_4225825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_4225825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225825 prefixEnd_4225825 := by exact prefixLift 4225825
  have htrace : WordTrace (prefixWord ++ tailWord_4225825) baseStart_4225825 baseEnd_4225825 := by
    simpa [prefixWord, tailWord_4225825, baseEnd_4225825] using wordTrace_append hprefix tailTrace_4225825
  have hstable : (prefixWord ++ tailWord_4225825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225825).length < 2 ^ (prefixWord ++ tailWord_4225825).sum := by decide
  have hdescent : baseEnd_4225825 < baseStart_4225825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225924 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_4225924 : Nat := 118140960795 + 4225924 * 2 ^ 59
def prefixEnd_4225924 : Nat := 4983230072969 + 3 ^ 40 * 4225924 * 2
def baseEnd_4225924 : Nat := 2169930221370829286615335

theorem tailTrace_4225924 : CollatzResearch.WordTrace tailWord_4225924 prefixEnd_4225924 2169930221370829286615335 := by
  unfold tailWord_4225924
  simp only [CollatzResearch.WordTrace]
  refine ⟨77066055371103276602210413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102754740494804368802947217 77066055371103276602210413)
  ·
    refine ⟨28899770764163728725828905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77066055371103276602210413 28899770764163728725828905)
    ·
      refine ⟨21674828073122796544371679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28899770764163728725828905 21674828073122796544371679)
      ·
        refine ⟨32512242109684194816557519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21674828073122796544371679 32512242109684194816557519)
        ·
          refine ⟨48768363164526292224836279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32512242109684194816557519 48768363164526292224836279)
          ·
            refine ⟨73152544746789438337254419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48768363164526292224836279 73152544746789438337254419)
            ·
              refine ⟨109728817120184157505881629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73152544746789438337254419 109728817120184157505881629)
              ·
                refine ⟨41148306420069059064705611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109728817120184157505881629 41148306420069059064705611)
                ·
                  refine ⟨61722459630103588597058417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41148306420069059064705611 61722459630103588597058417)
                  ·
                    refine ⟨46291844722577691447793813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61722459630103588597058417 46291844722577691447793813)
                    ·
                      refine ⟨2169930221370829286615335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46291844722577691447793813 2169930221370829286615335)
                      ·
                        rfl

theorem cell23_4225924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_4225924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225924 prefixEnd_4225924 := by exact prefixLift 4225924
  have htrace : WordTrace (prefixWord ++ tailWord_4225924) baseStart_4225924 baseEnd_4225924 := by
    simpa [prefixWord, tailWord_4225924, baseEnd_4225924] using wordTrace_append hprefix tailTrace_4225924
  have hstable : (prefixWord ++ tailWord_4225924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225924).length < 2 ^ (prefixWord ++ tailWord_4225924).sum := by decide
  have hdescent : baseEnd_4225924 < baseStart_4225924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225925 : List Nat := [1, 3, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_4225925 : Nat := 118140960795 + 4225925 * 2 ^ 59
def prefixEnd_4225925 : Nat := 4983230072969 + 3 ^ 40 * 4225925 * 2
def baseEnd_4225925 : Nat := 723310244950494594234277

theorem tailTrace_4225925 : CollatzResearch.WordTrace tailWord_4225925 prefixEnd_4225925 723310244950494594234277 := by
  unfold tailWord_4225925
  simp only [CollatzResearch.WordTrace]
  refine ⟨154132147215202930375207229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102754764810135286916804819 154132147215202930375207229)
  ·
    refine ⟨57799555205701098890702711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154132147215202930375207229 57799555205701098890702711)
    ·
      refine ⟨86699332808551648336054067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57799555205701098890702711 86699332808551648336054067)
      ·
        refine ⟨130048999212827472504081101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86699332808551648336054067 130048999212827472504081101)
        ·
          refine ⟨48768374704810302189030413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130048999212827472504081101 48768374704810302189030413)
          ·
            refine ⟨18288140514303863320886405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48768374704810302189030413 18288140514303863320886405)
            ·
              refine ⟨3429026346431974372666201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18288140514303863320886405 3429026346431974372666201)
              ·
                refine ⟨2571769759823980779499651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3429026346431974372666201 2571769759823980779499651)
                ·
                  refine ⟨3857654639735971169249477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571769759823980779499651 3857654639735971169249477)
                  ·
                    refine ⟨723310244950494594234277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857654639735971169249477 723310244950494594234277)
                    ·
                      rfl

theorem cell23_4225925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_4225925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225925 prefixEnd_4225925 := by exact prefixLift 4225925
  have htrace : WordTrace (prefixWord ++ tailWord_4225925) baseStart_4225925 baseEnd_4225925 := by
    simpa [prefixWord, tailWord_4225925, baseEnd_4225925] using wordTrace_append hprefix tailTrace_4225925
  have hstable : (prefixWord ++ tailWord_4225925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225925).length < 2 ^ (prefixWord ++ tailWord_4225925).sum := by decide
  have hdescent : baseEnd_4225925 < baseStart_4225925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225942 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4225942 : Nat := 118140960795 + 4225942 * 2 ^ 59
def prefixEnd_4225942 : Nat := 4983230072969 + 3 ^ 40 * 4225942 * 2
def baseEnd_4225942 : Nat := 723313154674203405396751

theorem tailTrace_4225942 : CollatzResearch.WordTrace tailWord_4225942 prefixEnd_4225942 723313154674203405396751 := by
  unfold tailWord_4225942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9633297953508833892411005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102755178170760894852384053 9633297953508833892411005)
  ·
    refine ⟨3612486732565812709654127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9633297953508833892411005 3612486732565812709654127)
    ·
      refine ⟨5418730098848719064481191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3612486732565812709654127 5418730098848719064481191)
      ·
        refine ⟨8128095148273078596721787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418730098848719064481191 8128095148273078596721787)
        ·
          refine ⟨12192142722409617895082681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128095148273078596721787 12192142722409617895082681)
          ·
            refine ⟨9144107041807213421312011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12192142722409617895082681 9144107041807213421312011)
            ·
              refine ⟨13716160562710820131968017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9144107041807213421312011 13716160562710820131968017)
              ·
                refine ⟨10287120422033115098976013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13716160562710820131968017 10287120422033115098976013)
                ·
                  refine ⟨3857670158262418162116005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10287120422033115098976013 3857670158262418162116005)
                  ·
                    refine ⟨723313154674203405396751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857670158262418162116005 723313154674203405396751)
                    ·
                      rfl

theorem cell23_4225942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4225942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225942 prefixEnd_4225942 := by exact prefixLift 4225942
  have htrace : WordTrace (prefixWord ++ tailWord_4225942) baseStart_4225942 baseEnd_4225942 := by
    simpa [prefixWord, tailWord_4225942, baseEnd_4225942] using wordTrace_append hprefix tailTrace_4225942
  have hstable : (prefixWord ++ tailWord_4225942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225942).length < 2 ^ (prefixWord ++ tailWord_4225942).sum := by decide
  have hdescent : baseEnd_4225942 < baseStart_4225942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225951 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 3, 5]
def baseStart_4225951 : Nat := 118140960795 + 4225951 * 2 ^ 59
def prefixEnd_4225951 : Nat := 4983230072969 + 3 ^ 40 * 4225951 * 2
def baseEnd_4225951 : Nat := 723314695116166893659237

theorem tailTrace_4225951 : CollatzResearch.WordTrace tailWord_4225951 prefixEnd_4225951 723314695116166893659237 := by
  unfold tailWord_4225951
  simp only [CollatzResearch.WordTrace]
  refine ⟨154133095513108736815653707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102755397008739157877102471 154133095513108736815653707)
  ·
    refine ⟨231199643269663105223480561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154133095513108736815653707 231199643269663105223480561)
    ·
      refine ⟨173399732452247328917610421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231199643269663105223480561 173399732452247328917610421)
      ·
        refine ⟨16256224917398187086025977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173399732452247328917610421 16256224917398187086025977)
        ·
          refine ⟨12192168688048640314519483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16256224917398187086025977 12192168688048640314519483)
          ·
            refine ⟨18288253032072960471779225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12192168688048640314519483 18288253032072960471779225)
            ·
              refine ⟨13716189774054720353834419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18288253032072960471779225 13716189774054720353834419)
              ·
                refine ⟨20574284661082080530751629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13716189774054720353834419 20574284661082080530751629)
                ·
                  refine ⟨7715356747905780199031861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20574284661082080530751629 7715356747905780199031861)
                  ·
                    refine ⟨723314695116166893659237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7715356747905780199031861 723314695116166893659237)
                    ·
                      rfl

theorem cell23_4225951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_4225951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225951 prefixEnd_4225951 := by exact prefixLift 4225951
  have htrace : WordTrace (prefixWord ++ tailWord_4225951) baseStart_4225951 baseEnd_4225951 := by
    simpa [prefixWord, tailWord_4225951, baseEnd_4225951] using wordTrace_append hprefix tailTrace_4225951
  have hstable : (prefixWord ++ tailWord_4225951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225951).length < 2 ^ (prefixWord ++ tailWord_4225951).sum := by decide
  have hdescent : baseEnd_4225951 < baseStart_4225951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225991 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_4225991 : Nat := 118140960795 + 4225991 * 2 ^ 59
def prefixEnd_4225991 : Nat := 4983230072969 + 3 ^ 40 * 4225991 * 2
def baseEnd_4225991 : Nat := 2169964624574680524477527

theorem tailTrace_4225991 : CollatzResearch.WordTrace tailWord_4225991 prefixEnd_4225991 2169964624574680524477527 := by
  unfold tailWord_4225991
  simp only [CollatzResearch.WordTrace]
  refine ⟨154134554432963823647109827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102756369621975882431406551 154134554432963823647109827)
  ·
    refine ⟨231201831649445735470664741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154134554432963823647109827 231201831649445735470664741)
    ·
      refine ⟨43350343434271075400749639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231201831649445735470664741 43350343434271075400749639)
      ·
        refine ⟨65025515151406613101124459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43350343434271075400749639 65025515151406613101124459)
        ·
          refine ⟨97538272727109919651686689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65025515151406613101124459 97538272727109919651686689)
          ·
            refine ⟨73153704545332439738765017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97538272727109919651686689 73153704545332439738765017)
            ·
              refine ⟨54865278408999329804073763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73153704545332439738765017 54865278408999329804073763)
              ·
                refine ⟨82297917613498994706110645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54865278408999329804073763 82297917613498994706110645)
                ·
                  refine ⟨7715429776265530753697873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82297917613498994706110645 7715429776265530753697873)
                  ·
                    refine ⟨5786572332199148065273405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7715429776265530753697873 5786572332199148065273405)
                    ·
                      refine ⟨2169964624574680524477527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786572332199148065273405 2169964624574680524477527)
                      ·
                        rfl

theorem cell23_4225991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_4225991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225991 prefixEnd_4225991 := by exact prefixLift 4225991
  have htrace : WordTrace (prefixWord ++ tailWord_4225991) baseStart_4225991 baseEnd_4225991 := by
    simpa [prefixWord, tailWord_4225991, baseEnd_4225991] using wordTrace_append hprefix tailTrace_4225991
  have hstable : (prefixWord ++ tailWord_4225991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225991).length < 2 ^ (prefixWord ++ tailWord_4225991).sum := by decide
  have hdescent : baseEnd_4225991 < baseStart_4225991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225994 : List Nat := [3, 1, 2, 1, 2, 1, 1, 12]
def baseStart_4225994 : Nat := 118140960795 + 4225994 * 2 ^ 59
def prefixEnd_4225994 : Nat := 4983230072969 + 3 ^ 40 * 4225994 * 2
def baseEnd_4225994 : Nat := 80369117222838667138519

theorem tailTrace_4225994 : CollatzResearch.WordTrace tailWord_4225994 prefixEnd_4225994 80369117222838667138519 := by
  unfold tailWord_4225994
  simp only [CollatzResearch.WordTrace]
  refine ⟨38533665962988238789867259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102756442567968636772979357 38533665962988238789867259)
  ·
    refine ⟨57800498944482358184800889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38533665962988238789867259 57800498944482358184800889)
    ·
      refine ⟨43350374208361768638600667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57800498944482358184800889 43350374208361768638600667)
      ·
        refine ⟨65025561312542652957901001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43350374208361768638600667 65025561312542652957901001)
        ·
          refine ⟨48769170984406989718425751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65025561312542652957901001 48769170984406989718425751)
          ·
            refine ⟨73153756476610484577638627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48769170984406989718425751 73153756476610484577638627)
            ·
              refine ⟨109730634714915726866457941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73153756476610484577638627 109730634714915726866457941)
              ·
                refine ⟨80369117222838667138519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 109730634714915726866457941 80369117222838667138519)
                ·
                  rfl

theorem cell23_4225994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_4225994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225994 prefixEnd_4225994 := by exact prefixLift 4225994
  have htrace : WordTrace (prefixWord ++ tailWord_4225994) baseStart_4225994 baseEnd_4225994 := by
    simpa [prefixWord, tailWord_4225994, baseEnd_4225994] using wordTrace_append hprefix tailTrace_4225994
  have hstable : (prefixWord ++ tailWord_4225994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225994).length < 2 ^ (prefixWord ++ tailWord_4225994).sum := by decide
  have hdescent : baseEnd_4225994 < baseStart_4225994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4225998 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_4225998 : Nat := 118140960795 + 4225998 * 2 ^ 59
def prefixEnd_4225998 : Nat := 4983230072969 + 3 ^ 40 * 4225998 * 2
def baseEnd_4225998 : Nat := 723322739646420665696665

theorem tailTrace_4225998 : CollatzResearch.WordTrace tailWord_4225998 prefixEnd_4225998 723322739646420665696665 := by
  unfold tailWord_4225998
  simp only [CollatzResearch.WordTrace]
  refine ⟨19266851217992307980326831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102756539829292309228409765 19266851217992307980326831)
  ·
    refine ⟨28900276826988461970490247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19266851217992307980326831 28900276826988461970490247)
    ·
      refine ⟨43350415240482692955735371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28900276826988461970490247 43350415240482692955735371)
      ·
        refine ⟨65025622860724039433603057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43350415240482692955735371 65025622860724039433603057)
        ·
          refine ⟨48769217145543029575202293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65025622860724039433603057 48769217145543029575202293)
          ·
            refine ⟨4572114107394659022675215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48769217145543029575202293 4572114107394659022675215)
            ·
              refine ⟨6858171161091988534012823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572114107394659022675215 6858171161091988534012823)
              ·
                refine ⟨10287256741637982801019235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6858171161091988534012823 10287256741637982801019235)
                ·
                  refine ⟨15430885112456974201528853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10287256741637982801019235 15430885112456974201528853)
                  ·
                    refine ⟨723322739646420665696665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15430885112456974201528853 723322739646420665696665)
                    ·
                      rfl

theorem cell23_4225998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_4225998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4225998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4225998 prefixEnd_4225998 := by exact prefixLift 4225998
  have htrace : WordTrace (prefixWord ++ tailWord_4225998) baseStart_4225998 baseEnd_4225998 := by
    simpa [prefixWord, tailWord_4225998, baseEnd_4225998] using wordTrace_append hprefix tailTrace_4225998
  have hstable : (prefixWord ++ tailWord_4225998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4225998).length < 2 ^ (prefixWord ++ tailWord_4225998).sum := by decide
  have hdescent : baseEnd_4225998 < baseStart_4225998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4225998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226005 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4226005 : Nat := 118140960795 + 4226005 * 2 ^ 59
def prefixEnd_4226005 : Nat := 4983230072969 + 3 ^ 40 * 4226005 * 2
def baseEnd_4226005 : Nat := 2169971813303843469702463

theorem tailTrace_4226005 : CollatzResearch.WordTrace tailWord_4226005 prefixEnd_4226005 2169971813303843469702463 := by
  unfold tailWord_4226005
  simp only [CollatzResearch.WordTrace]
  refine ⟨154135065054913104038119469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102756710036608736025412979 154135065054913104038119469)
  ·
    refine ⟨57800649395592414014294801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154135065054913104038119469 57800649395592414014294801)
    ·
      refine ⟨43350487046694310510721101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57800649395592414014294801 43350487046694310510721101)
      ·
        refine ⟨16256432642510366441520413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43350487046694310510721101 16256432642510366441520413)
        ·
          refine ⟨6096162240941387415570155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16256432642510366441520413 6096162240941387415570155)
          ·
            refine ⟨9144243361412081123355233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6096162240941387415570155 9144243361412081123355233)
            ·
              refine ⟨6858182521059060842516425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9144243361412081123355233 6858182521059060842516425)
              ·
                refine ⟨5143636890794295631887319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6858182521059060842516425 5143636890794295631887319)
                ·
                  refine ⟨7715455336191443447830979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5143636890794295631887319 7715455336191443447830979)
                  ·
                    refine ⟨11573183004287165171746469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7715455336191443447830979 11573183004287165171746469)
                    ·
                      refine ⟨2169971813303843469702463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11573183004287165171746469 2169971813303843469702463)
                      ·
                        rfl

theorem cell23_4226005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4226005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226005 prefixEnd_4226005 := by exact prefixLift 4226005
  have htrace : WordTrace (prefixWord ++ tailWord_4226005) baseStart_4226005 baseEnd_4226005 := by
    simpa [prefixWord, tailWord_4226005, baseEnd_4226005] using wordTrace_append hprefix tailTrace_4226005
  have hstable : (prefixWord ++ tailWord_4226005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226005).length < 2 ^ (prefixWord ++ tailWord_4226005).sum := by decide
  have hdescent : baseEnd_4226005 < baseStart_4226005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226008 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_4226008 : Nat := 118140960795 + 4226008 * 2 ^ 59
def prefixEnd_4226008 : Nat := 4983230072969 + 3 ^ 40 * 4226008 * 2
def baseEnd_4226008 : Nat := 2169973353745806957964949

theorem tailTrace_4226008 : CollatzResearch.WordTrace tailWord_4226008 prefixEnd_4226008 2169973353745806957964949 := by
  unfold tailWord_4226008
  simp only [CollatzResearch.WordTrace]
  refine ⟨77067587236951117775239339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102756782982601490366985785 77067587236951117775239339)
  ·
    refine ⟨115601380855426676662859009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77067587236951117775239339 115601380855426676662859009)
    ·
      refine ⟨86701035641570007497144257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115601380855426676662859009 86701035641570007497144257)
      ·
        refine ⟨65025776731177505622858193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86701035641570007497144257 65025776731177505622858193)
        ·
          refine ⟨48769332548383129217143645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65025776731177505622858193 48769332548383129217143645)
          ·
            refine ⟨18288499705643673456428867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48769332548383129217143645 18288499705643673456428867)
            ·
              refine ⟨27432749558465510184643301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18288499705643673456428867 27432749558465510184643301)
              ·
                refine ⟨5143640542212283159620619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27432749558465510184643301 5143640542212283159620619)
                ·
                  refine ⟨7715460813318424739430929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5143640542212283159620619 7715460813318424739430929)
                  ·
                    refine ⟨5786595609988818554573197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7715460813318424739430929 5786595609988818554573197)
                    ·
                      refine ⟨2169973353745806957964949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786595609988818554573197 2169973353745806957964949)
                      ·
                        rfl

theorem cell23_4226008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_4226008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226008 prefixEnd_4226008 := by exact prefixLift 4226008
  have htrace : WordTrace (prefixWord ++ tailWord_4226008) baseStart_4226008 baseEnd_4226008 := by
    simpa [prefixWord, tailWord_4226008, baseEnd_4226008] using wordTrace_append hprefix tailTrace_4226008
  have hstable : (prefixWord ++ tailWord_4226008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226008).length < 2 ^ (prefixWord ++ tailWord_4226008).sum := by decide
  have hdescent : baseEnd_4226008 < baseStart_4226008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226055 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_4226055 : Nat := 118140960795 + 4226055 * 2 ^ 59
def prefixEnd_4226055 : Nat := 4983230072969 + 3 ^ 40 * 4226055 * 2
def baseEnd_4226055 : Nat := 2169997487336568274077233

theorem tailTrace_4226055 : CollatzResearch.WordTrace tailWord_4226055 prefixEnd_4226055 2169997487336568274077233 := by
  unfold tailWord_4226055
  simp only [CollatzResearch.WordTrace]
  refine ⟨154136888704731962577439619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102757925803154641718293079 154136888704731962577439619)
  ·
    refine ⟨231205333057097943866159429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154136888704731962577439619 231205333057097943866159429)
    ·
      refine ⟨43350999948205864474904893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231205333057097943866159429 43350999948205864474904893)
      ·
        refine ⟨16256624980577199178089335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43350999948205864474904893 16256624980577199178089335)
        ·
          refine ⟨24384937470865798767134003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16256624980577199178089335 24384937470865798767134003)
          ·
            refine ⟨36577406206298698150701005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24384937470865798767134003 36577406206298698150701005)
            ·
              refine ⟨13716527327362011806512877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36577406206298698150701005 13716527327362011806512877)
              ·
                refine ⟨5143697747760754427442329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13716527327362011806512877 5143697747760754427442329)
                ·
                  refine ⟨3857773310820565820581747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5143697747760754427442329 3857773310820565820581747)
                  ·
                    refine ⟨5786659966230848730872621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3857773310820565820581747 5786659966230848730872621)
                    ·
                      refine ⟨2169997487336568274077233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786659966230848730872621 2169997487336568274077233)
                      ·
                        rfl

theorem cell23_4226055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_4226055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226055 prefixEnd_4226055 := by exact prefixLift 4226055
  have htrace : WordTrace (prefixWord ++ tailWord_4226055) baseStart_4226055 baseEnd_4226055 := by
    simpa [prefixWord, tailWord_4226055, baseEnd_4226055] using wordTrace_append hprefix tailTrace_4226055
  have hstable : (prefixWord ++ tailWord_4226055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226055).length < 2 ^ (prefixWord ++ tailWord_4226055).sum := by decide
  have hdescent : baseEnd_4226055 < baseStart_4226055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226091 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4]
def baseStart_4226091 : Nat := 118140960795 + 4226091 * 2 ^ 59
def prefixEnd_4226091 : Nat := 4983230072969 + 3 ^ 40 * 4226091 * 2
def baseEnd_4226091 : Nat := 2170015972640130133227067

theorem tailTrace_4226091 : CollatzResearch.WordTrace tailWord_4226091 prefixEnd_4226091 2170015972640130133227067 := by
  unfold tailWord_4226091
  simp only [CollatzResearch.WordTrace]
  refine ⟨154138201732601540725750127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102758801155067693817166751 154138201732601540725750127)
  ·
    refine ⟨231207302598902311088625191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154138201732601540725750127 231207302598902311088625191)
    ·
      refine ⟨346810953898353466632937787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231207302598902311088625191 346810953898353466632937787)
      ·
        refine ⟨520216430847530199949406681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346810953898353466632937787 520216430847530199949406681)
        ·
          refine ⟨390162323135647649962055011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520216430847530199949406681 390162323135647649962055011)
          ·
            refine ⟨585243484703471474943082517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390162323135647649962055011 585243484703471474943082517)
            ·
              refine ⟨27433288345475225387956993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 585243484703471474943082517 27433288345475225387956993)
              ·
                refine ⟨20574966259106419040967745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27433288345475225387956993 20574966259106419040967745)
                ·
                  refine ⟨15431224694329814280725809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20574966259106419040967745 15431224694329814280725809)
                  ·
                    refine ⟨11573418520747360710544357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15431224694329814280725809 11573418520747360710544357)
                    ·
                      refine ⟨2170015972640130133227067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11573418520747360710544357 2170015972640130133227067)
                      ·
                        rfl

theorem cell23_4226091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_4226091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226091 prefixEnd_4226091 := by exact prefixLift 4226091
  have htrace : WordTrace (prefixWord ++ tailWord_4226091) baseStart_4226091 baseEnd_4226091 := by
    simpa [prefixWord, tailWord_4226091, baseEnd_4226091] using wordTrace_append hprefix tailTrace_4226091
  have hstable : (prefixWord ++ tailWord_4226091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226091).length < 2 ^ (prefixWord ++ tailWord_4226091).sum := by decide
  have hdescent : baseEnd_4226091 < baseStart_4226091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226101 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 7]
def baseStart_4226101 : Nat := 118140960795 + 4226101 * 2 ^ 59
def prefixEnd_4226101 : Nat := 4983230072969 + 3 ^ 40 * 4226101 * 2
def baseEnd_4226101 : Nat := 241113456382963899344669

theorem tailTrace_4226101 : CollatzResearch.WordTrace tailWord_4226101 prefixEnd_4226101 241113456382963899344669 := by
  unfold tailWord_4226101
  simp only [CollatzResearch.WordTrace]
  refine ⟨154138566462565312433614157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102759044308376874955742771 154138566462565312433614157)
  ·
    refine ⟨57801962423461992162605309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154138566462565312433614157 57801962423461992162605309)
    ·
      refine ⟨21675735908798247060976991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57801962423461992162605309 21675735908798247060976991)
      ·
        refine ⟨32513603863197370591465487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21675735908798247060976991 32513603863197370591465487)
        ·
          refine ⟨48770405794796055887198231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32513603863197370591465487 48770405794796055887198231)
          ·
            refine ⟨73155608692194083830797347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48770405794796055887198231 73155608692194083830797347)
            ·
              refine ⟨109733413038291125746196021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73155608692194083830797347 109733413038291125746196021)
              ·
                refine ⟨10287507472339793038705877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109733413038291125746196021 10287507472339793038705877)
                ·
                  refine ⟨241113456382963899344669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10287507472339793038705877 241113456382963899344669)
                  ·
                    rfl

theorem cell23_4226101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_4226101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226101 prefixEnd_4226101 := by exact prefixLift 4226101
  have htrace : WordTrace (prefixWord ++ tailWord_4226101) baseStart_4226101 baseEnd_4226101 := by
    simpa [prefixWord, tailWord_4226101, baseEnd_4226101] using wordTrace_append hprefix tailTrace_4226101
  have hstable : (prefixWord ++ tailWord_4226101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226101).length < 2 ^ (prefixWord ++ tailWord_4226101).sum := by decide
  have hdescent : baseEnd_4226101 < baseStart_4226101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226108 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_4226108 : Nat := 118140960795 + 4226108 * 2 ^ 59
def prefixEnd_4226108 : Nat := 4983230072969 + 3 ^ 40 * 4226108 * 2
def baseEnd_4226108 : Nat := 2170024701811256566714489

theorem tailTrace_4226108 : CollatzResearch.WordTrace tailWord_4226108 prefixEnd_4226108 2170024701811256566714489 := by
  unfold tailWord_4226108
  simp only [CollatzResearch.WordTrace]
  refine ⟨77069410886769976314559489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102759214515693301752745985 77069410886769976314559489)
  ·
    refine ⟨57802058165077482235919617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77069410886769976314559489 57802058165077482235919617)
    ·
      refine ⟨43351543623808111676939713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57802058165077482235919617 43351543623808111676939713)
      ·
        refine ⟨32513657717856083757704785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43351543623808111676939713 32513657717856083757704785)
        ·
          refine ⟨24385243288392062818278589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32513657717856083757704785 24385243288392062818278589)
          ·
            refine ⟨9144466233147023556854471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24385243288392062818278589 9144466233147023556854471)
            ·
              refine ⟨13716699349720535335281707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9144466233147023556854471 13716699349720535335281707)
              ·
                refine ⟨20575049024580803002922561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13716699349720535335281707 20575049024580803002922561)
                ·
                  refine ⟨15431286768435602252191921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20575049024580803002922561 15431286768435602252191921)
                  ·
                    refine ⟨11573465076326701689143941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15431286768435602252191921 11573465076326701689143941)
                    ·
                      refine ⟨2170024701811256566714489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11573465076326701689143941 2170024701811256566714489)
                      ·
                        rfl

theorem cell23_4226108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_4226108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226108 prefixEnd_4226108 := by exact prefixLift 4226108
  have htrace : WordTrace (prefixWord ++ tailWord_4226108) baseStart_4226108 baseEnd_4226108 := by
    simpa [prefixWord, tailWord_4226108, baseEnd_4226108] using wordTrace_append hprefix tailTrace_4226108
  have hstable : (prefixWord ++ tailWord_4226108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226108).length < 2 ^ (prefixWord ++ tailWord_4226108).sum := by decide
  have hdescent : baseEnd_4226108 < baseStart_4226108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226138 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2]
def baseStart_4226138 : Nat := 118140960795 + 4226138 * 2 ^ 59
def prefixEnd_4226138 : Nat := 4983230072969 + 3 ^ 40 * 4226138 * 2
def baseEnd_4226138 : Nat := 2170040106230891449339351

theorem tailTrace_4226138 : CollatzResearch.WordTrace tailWord_4226138 prefixEnd_4226138 2170040106230891449339351 := by
  unfold tailWord_4226138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38534978990857816938177767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102759943975620845168474045 38534978990857816938177767)
  ·
    refine ⟨57802468486286725407266651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38534978990857816938177767 57802468486286725407266651)
    ·
      refine ⟨86703702729430088110899977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57802468486286725407266651 86703702729430088110899977)
      ·
        refine ⟨65027777047072566083174983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86703702729430088110899977 65027777047072566083174983)
        ·
          refine ⟨97541665570608849124762475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65027777047072566083174983 97541665570608849124762475)
          ·
            refine ⟨146312498355913273687143713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97541665570608849124762475 146312498355913273687143713)
            ·
              refine ⟨109734373766934955265357785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146312498355913273687143713 109734373766934955265357785)
              ·
                refine ⟨82300780325201216449018339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109734373766934955265357785 82300780325201216449018339)
                ·
                  refine ⟨123451170487801824673527509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82300780325201216449018339 123451170487801824673527509)
                  ·
                    refine ⟨2893386808307855265785801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 123451170487801824673527509 2893386808307855265785801)
                    ·
                      refine ⟨2170040106230891449339351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893386808307855265785801 2170040106230891449339351)
                      ·
                        rfl

theorem cell23_4226138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_4226138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226138 prefixEnd_4226138 := by exact prefixLift 4226138
  have htrace : WordTrace (prefixWord ++ tailWord_4226138) baseStart_4226138 baseEnd_4226138 := by
    simpa [prefixWord, tailWord_4226138, baseEnd_4226138] using wordTrace_append hprefix tailTrace_4226138
  have hstable : (prefixWord ++ tailWord_4226138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226138).length < 2 ^ (prefixWord ++ tailWord_4226138).sum := by decide
  have hdescent : baseEnd_4226138 < baseStart_4226138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226142 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4226142 : Nat := 118140960795 + 4226142 * 2 ^ 59
def prefixEnd_4226142 : Nat := 4983230072969 + 3 ^ 40 * 4226142 * 2
def baseEnd_4226142 : Nat := 2170042160153509433689333

theorem tailTrace_4226142 : CollatzResearch.WordTrace tailWord_4226142 prefixEnd_4226142 2170042160153509433689333 := by
  unfold tailWord_4226142
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267507731927097054482085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102760041236944517623904453 19267507731927097054482085)
  ·
    refine ⟨3612657699736330697715391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19267507731927097054482085 3612657699736330697715391)
    ·
      refine ⟨5418986549604496046573087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3612657699736330697715391 5418986549604496046573087)
      ·
        refine ⟨8128479824406744069859631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418986549604496046573087 8128479824406744069859631)
        ·
          refine ⟨12192719736610116104789447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128479824406744069859631 12192719736610116104789447)
          ·
            refine ⟨18289079604915174157184171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12192719736610116104789447 18289079604915174157184171)
            ·
              refine ⟨27433619407372761235776257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18289079604915174157184171 27433619407372761235776257)
              ·
                refine ⟨20575214555529570926832193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27433619407372761235776257 20575214555529570926832193)
                ·
                  refine ⟨15431410916647178195124145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20575214555529570926832193 15431410916647178195124145)
                  ·
                    refine ⟨11573558187485383646343109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15431410916647178195124145 11573558187485383646343109)
                    ·
                      refine ⟨2170042160153509433689333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11573558187485383646343109 2170042160153509433689333)
                      ·
                        rfl

theorem cell23_4226142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4226142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226142 prefixEnd_4226142 := by exact prefixLift 4226142
  have htrace : WordTrace (prefixWord ++ tailWord_4226142) baseStart_4226142 baseEnd_4226142 := by
    simpa [prefixWord, tailWord_4226142, baseEnd_4226142] using wordTrace_append hprefix tailTrace_4226142
  have hstable : (prefixWord ++ tailWord_4226142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226142).length < 2 ^ (prefixWord ++ tailWord_4226142).sum := by decide
  have hdescent : baseEnd_4226142 < baseStart_4226142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226146 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4226146 : Nat := 118140960795 + 4226146 * 2 ^ 59
def prefixEnd_4226146 : Nat := 4983230072969 + 3 ^ 40 * 4226146 * 2
def baseEnd_4226146 : Nat := 2170044214076127418039315

theorem tailTrace_4226146 : CollatzResearch.WordTrace tailWord_4226146 prefixEnd_4226146 2170044214076127418039315 := by
  unfold tailWord_4226146
  simp only [CollatzResearch.WordTrace]
  refine ⟨38535051936850571279750573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102760138498268190079334861 38535051936850571279750573)
  ·
    refine ⟨14450644476318964229906465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38535051936850571279750573 14450644476318964229906465)
    ·
      refine ⟨10837983357239223172429849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14450644476318964229906465 10837983357239223172429849)
      ·
        refine ⟨8128487517929417379322387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10837983357239223172429849 8128487517929417379322387)
        ·
          refine ⟨12192731276894126068983581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128487517929417379322387 12192731276894126068983581)
          ·
            refine ⟨4572274228835297275868843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12192731276894126068983581 4572274228835297275868843)
            ·
              refine ⟨6858411343252945913803265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572274228835297275868843 6858411343252945913803265)
              ·
                refine ⟨5143808507439709435352449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6858411343252945913803265 5143808507439709435352449)
                ·
                  refine ⟨3857856380579782076514337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5143808507439709435352449 3857856380579782076514337)
                  ·
                    refine ⟨2893392285434836557385753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3857856380579782076514337 2893392285434836557385753)
                    ·
                      refine ⟨2170044214076127418039315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893392285434836557385753 2170044214076127418039315)
                      ·
                        rfl

theorem cell23_4226146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4226146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226146 prefixEnd_4226146 := by exact prefixLift 4226146
  have htrace : WordTrace (prefixWord ++ tailWord_4226146) baseStart_4226146 baseEnd_4226146 := by
    simpa [prefixWord, tailWord_4226146, baseEnd_4226146] using wordTrace_append hprefix tailTrace_4226146
  have hstable : (prefixWord ++ tailWord_4226146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226146).length < 2 ^ (prefixWord ++ tailWord_4226146).sum := by decide
  have hdescent : baseEnd_4226146 < baseStart_4226146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226188 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_4226188 : Nat := 118140960795 + 4226188 * 2 ^ 59
def prefixEnd_4226188 : Nat := 4983230072969 + 3 ^ 40 * 4226188 * 2
def baseEnd_4226188 : Nat := 2170065780263616253714121

theorem tailTrace_4226188 : CollatzResearch.WordTrace tailWord_4226188 prefixEnd_4226188 2170065780263616253714121 := by
  unfold tailWord_4226188
  simp only [CollatzResearch.WordTrace]
  refine ⟨77070869806625063146015609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102761159742166750861354145 77070869806625063146015609)
  ·
    refine ⟨57803152354968797359511707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77070869806625063146015609 57803152354968797359511707)
    ·
      refine ⟨86704728532453196039267561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57803152354968797359511707 86704728532453196039267561)
      ·
        refine ⟨65028546399339897029450671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86704728532453196039267561 65028546399339897029450671)
        ·
          refine ⟨97542819599009845544176007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65028546399339897029450671 97542819599009845544176007)
          ·
            refine ⟨146314229398514768316264011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97542819599009845544176007 146314229398514768316264011)
            ·
              refine ⟨219471344097772152474396017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146314229398514768316264011 219471344097772152474396017)
              ·
                refine ⟨164603508073329114355797013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219471344097772152474396017 164603508073329114355797013)
                ·
                  refine ⟨7715789440937302235427985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 164603508073329114355797013 7715789440937302235427985)
                  ·
                    refine ⟨5786842080702976676570989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7715789440937302235427985 5786842080702976676570989)
                    ·
                      refine ⟨2170065780263616253714121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786842080702976676570989 2170065780263616253714121)
                      ·
                        rfl

theorem cell23_4226188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_4226188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226188 prefixEnd_4226188 := by exact prefixLift 4226188
  have htrace : WordTrace (prefixWord ++ tailWord_4226188) baseStart_4226188 baseEnd_4226188 := by
    simpa [prefixWord, tailWord_4226188, baseEnd_4226188] using wordTrace_append hprefix tailTrace_4226188
  have hstable : (prefixWord ++ tailWord_4226188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226188).length < 2 ^ (prefixWord ++ tailWord_4226188).sum := by decide
  have hdescent : baseEnd_4226188 < baseStart_4226188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226205 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_4226205 : Nat := 118140960795 + 4226205 * 2 ^ 59
def prefixEnd_4226205 : Nat := 4983230072969 + 3 ^ 40 * 4226205 * 2
def baseEnd_4226205 : Nat := 2170074509434742687201543

theorem tailTrace_4226205 : CollatzResearch.WordTrace tailWord_4226205 prefixEnd_4226205 2170074509434742687201543 := by
  unfold tailWord_4226205
  simp only [CollatzResearch.WordTrace]
  refine ⟨154142359654188538195400069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102761573102792358796933379 154142359654188538195400069)
  ·
    refine ⟨28901692435160350911637513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154142359654188538195400069 28901692435160350911637513)
    ·
      refine ⟨21676269326370263183728135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28901692435160350911637513 21676269326370263183728135)
      ·
        refine ⟨32514403989555394775592203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21676269326370263183728135 32514403989555394775592203)
        ·
          refine ⟨48771605984333092163388305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32514403989555394775592203 48771605984333092163388305)
          ·
            refine ⟨36578704488249819122541229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48771605984333092163388305 36578704488249819122541229)
            ·
              refine ⟨13717014183093682170952961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36578704488249819122541229 13717014183093682170952961)
              ·
                refine ⟨10287760637320261628214721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13717014183093682170952961 10287760637320261628214721)
                ·
                  refine ⟨7715820477990196221161041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10287760637320261628214721 7715820477990196221161041)
                  ·
                    refine ⟨5786865358492647165870781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7715820477990196221161041 5786865358492647165870781)
                    ·
                      refine ⟨2170074509434742687201543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5786865358492647165870781 2170074509434742687201543)
                      ·
                        rfl

theorem cell23_4226205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_4226205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226205 prefixEnd_4226205 := by exact prefixLift 4226205
  have htrace : WordTrace (prefixWord ++ tailWord_4226205) baseStart_4226205 baseEnd_4226205 := by
    simpa [prefixWord, tailWord_4226205, baseEnd_4226205] using wordTrace_append hprefix tailTrace_4226205
  have hstable : (prefixWord ++ tailWord_4226205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226205).length < 2 ^ (prefixWord ++ tailWord_4226205).sum := by decide
  have hdescent : baseEnd_4226205 < baseStart_4226205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226208 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 6]
def baseStart_4226208 : Nat := 118140960795 + 4226208 * 2 ^ 59
def prefixEnd_4226208 : Nat := 4983230072969 + 3 ^ 40 * 4226208 * 2
def baseEnd_4226208 : Nat := 241119561097411797273781

theorem tailTrace_4226208 : CollatzResearch.WordTrace tailWord_4226208 prefixEnd_4226208 241119561097411797273781 := by
  unfold tailWord_4226208
  simp only [CollatzResearch.WordTrace]
  refine ⟨77071234536588834853879639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102761646048785113138506185 77071234536588834853879639)
  ·
    refine ⟨115606851804883252280819459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77071234536588834853879639 115606851804883252280819459)
    ·
      refine ⟨173410277707324878421229189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115606851804883252280819459 173410277707324878421229189)
      ·
        refine ⟨32514427070123414703980473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173410277707324878421229189 32514427070123414703980473)
        ·
          refine ⟨24385820302592561027985355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32514427070123414703980473 24385820302592561027985355)
          ·
            refine ⟨36578730453888841541978033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24385820302592561027985355 36578730453888841541978033)
            ·
              refine ⟨27434047840416631156483525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36578730453888841541978033 27434047840416631156483525)
              ·
                refine ⟨5143883970078118341840661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27434047840416631156483525 5143883970078118341840661)
                ·
                  refine ⟨241119561097411797273781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5143883970078118341840661 241119561097411797273781)
                  ·
                    rfl

theorem cell23_4226208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 6].length) (baseStart_4226208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226208 prefixEnd_4226208 := by exact prefixLift 4226208
  have htrace : WordTrace (prefixWord ++ tailWord_4226208) baseStart_4226208 baseEnd_4226208 := by
    simpa [prefixWord, tailWord_4226208, baseEnd_4226208] using wordTrace_append hprefix tailTrace_4226208
  have hstable : (prefixWord ++ tailWord_4226208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226208).length < 2 ^ (prefixWord ++ tailWord_4226208).sum := by decide
  have hdescent : baseEnd_4226208 < baseStart_4226208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226211 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8]
def baseStart_4226211 : Nat := 118140960795 + 4226211 * 2 ^ 59
def prefixEnd_4226211 : Nat := 4983230072969 + 3 ^ 40 * 4226211 * 2
def baseEnd_4226211 : Nat := 2170077590318669663726515

theorem tailTrace_4226211 : CollatzResearch.WordTrace tailWord_4226211 prefixEnd_4226211 2170077590318669663726515 := by
  unfold tailWord_4226211
  simp only [CollatzResearch.WordTrace]
  refine ⟨154142578492166801220118487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102761718994777867480078991 154142578492166801220118487)
  ·
    refine ⟨231213867738250201830177731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154142578492166801220118487 231213867738250201830177731)
    ·
      refine ⟨346820801607375302745266597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231213867738250201830177731 346820801607375302745266597)
      ·
        refine ⟨65028900301382869264737487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346820801607375302745266597 65028900301382869264737487)
        ·
          refine ⟨97543350452074303897106231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65028900301382869264737487 97543350452074303897106231)
          ·
            refine ⟨146315025678111455845659347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97543350452074303897106231 146315025678111455845659347)
            ·
              refine ⟨219472538517167183768489021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146315025678111455845659347 219472538517167183768489021)
              ·
                refine ⟨82302201943937693913183383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219472538517167183768489021 82302201943937693913183383)
                ·
                  refine ⟨123453302915906540869775075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82302201943937693913183383 123453302915906540869775075)
                  ·
                    refine ⟨185179954373859811304662613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123453302915906540869775075 185179954373859811304662613)
                    ·
                      refine ⟨2170077590318669663726515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 185179954373859811304662613 2170077590318669663726515)
                      ·
                        rfl

theorem cell23_4226211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_4226211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226211 prefixEnd_4226211 := by exact prefixLift 4226211
  have htrace : WordTrace (prefixWord ++ tailWord_4226211) baseStart_4226211 baseEnd_4226211 := by
    simpa [prefixWord, tailWord_4226211, baseEnd_4226211] using wordTrace_append hprefix tailTrace_4226211
  have hstable : (prefixWord ++ tailWord_4226211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226211).length < 2 ^ (prefixWord ++ tailWord_4226211).sum := by decide
  have hdescent : baseEnd_4226211 < baseStart_4226211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226212 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_4226212 : Nat := 118140960795 + 4226212 * 2 ^ 59
def prefixEnd_4226212 : Nat := 4983230072969 + 3 ^ 40 * 4226212 * 2
def baseEnd_4226212 : Nat := 723359367933108053271337

theorem tailTrace_4226212 : CollatzResearch.WordTrace tailWord_4226212 prefixEnd_4226212 723359367933108053271337 := by
  unfold tailWord_4226212
  simp only [CollatzResearch.WordTrace]
  refine ⟨77071307482581589195452445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102761743310108785593936593 77071307482581589195452445)
  ·
    refine ⟨28901740305968095948294667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77071307482581589195452445 28901740305968095948294667)
    ·
      refine ⟨43352610458952143922442001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28901740305968095948294667 43352610458952143922442001)
      ·
        refine ⟨32514457844214107941831501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43352610458952143922442001 32514457844214107941831501)
        ·
          refine ⟨12192921691580290478186813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32514457844214107941831501 12192921691580290478186813)
          ·
            refine ⟨4572345634342608929320055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12192921691580290478186813 4572345634342608929320055)
            ·
              refine ⟨6858518451513913393980083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572345634342608929320055 6858518451513913393980083)
              ·
                refine ⟨10287777677270870090970125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6858518451513913393980083 10287777677270870090970125)
                ·
                  refine ⟨3857916628976576284113797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10287777677270870090970125 3857916628976576284113797)
                  ·
                    refine ⟨723359367933108053271337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857916628976576284113797 723359367933108053271337)
                    ·
                      rfl

theorem cell23_4226212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_4226212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226212 prefixEnd_4226212 := by exact prefixLift 4226212
  have htrace : WordTrace (prefixWord ++ tailWord_4226212) baseStart_4226212 baseEnd_4226212 := by
    simpa [prefixWord, tailWord_4226212, baseEnd_4226212] using wordTrace_append hprefix tailTrace_4226212
  have hstable : (prefixWord ++ tailWord_4226212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226212).length < 2 ^ (prefixWord ++ tailWord_4226212).sum := by decide
  have hdescent : baseEnd_4226212 < baseStart_4226212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226225 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 6]
def baseStart_4226225 : Nat := 118140960795 + 4226225 * 2 ^ 59
def prefixEnd_4226225 : Nat := 4983230072969 + 3 ^ 40 * 4226225 * 2
def baseEnd_4226225 : Nat := 241120531005314734327939

theorem tailTrace_4226225 : CollatzResearch.WordTrace tailWord_4226225 prefixEnd_4226225 241120531005314734327939 := by
  unfold tailWord_4226225
  simp only [CollatzResearch.WordTrace]
  refine ⟨154143089114116081611128129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102762059409410721074085419 154143089114116081611128129)
  ·
    refine ⟨115607316835587061208346097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154143089114116081611128129 115607316835587061208346097)
    ·
      refine ⟨86705487626690295906259573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115607316835587061208346097 86705487626690295906259573)
      ·
        refine ⟨8128639465002215241211835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86705487626690295906259573 8128639465002215241211835)
        ·
          refine ⟨12192959197503322861817753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128639465002215241211835 12192959197503322861817753)
          ·
            refine ⟨9144719398127492146363315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12192959197503322861817753 9144719398127492146363315)
            ·
              refine ⟨13717079097191238219544973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9144719398127492146363315 13717079097191238219544973)
              ·
                refine ⟨5143904661446714332329365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13717079097191238219544973 5143904661446714332329365)
                ·
                  refine ⟨241120531005314734327939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5143904661446714332329365 241120531005314734327939)
                  ·
                    rfl

theorem cell23_4226225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 6].length) (baseStart_4226225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226225 prefixEnd_4226225 := by exact prefixLift 4226225
  have htrace : WordTrace (prefixWord ++ tailWord_4226225) baseStart_4226225 baseEnd_4226225 := by
    simpa [prefixWord, tailWord_4226225, baseEnd_4226225] using wordTrace_append hprefix tailTrace_4226225
  have hstable : (prefixWord ++ tailWord_4226225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226225).length < 2 ^ (prefixWord ++ tailWord_4226225).sum := by decide
  have hdescent : baseEnd_4226225 < baseStart_4226225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226285 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_4226285 : Nat := 118140960795 + 4226285 * 2 ^ 59
def prefixEnd_4226285 : Nat := 4983230072969 + 3 ^ 40 * 4226285 * 2
def baseEnd_4226285 : Nat := 723371862629034124733725

theorem tailTrace_4226285 : CollatzResearch.WordTrace tailWord_4226285 prefixEnd_4226285 723371862629034124733725 := by
  unfold tailWord_4226285
  simp only [CollatzResearch.WordTrace]
  refine ⟨154145277493898711858312309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102763518329265807905541539 154145277493898711858312309)
  ·
    refine ⟨14451119765053004236716779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154145277493898711858312309 14451119765053004236716779)
    ·
      refine ⟨21676679647579506355075169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14451119765053004236716779 21676679647579506355075169)
      ·
        refine ⟨16257509735684629766306377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21676679647579506355075169 16257509735684629766306377)
        ·
          refine ⟨12193132301763472324729783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16257509735684629766306377 12193132301763472324729783)
          ·
            refine ⟨18289698452645208487094675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12193132301763472324729783 18289698452645208487094675)
            ·
              refine ⟨27434547678967812730642013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18289698452645208487094675 27434547678967812730642013)
              ·
                refine ⟨10287955379612929773990755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27434547678967812730642013 10287955379612929773990755)
                ·
                  refine ⟨15431933069419394660986133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10287955379612929773990755 15431933069419394660986133)
                  ·
                    refine ⟨723371862629034124733725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15431933069419394660986133 723371862629034124733725)
                    ·
                      rfl

theorem cell23_4226285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_4226285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226285 prefixEnd_4226285 := by exact prefixLift 4226285
  have htrace : WordTrace (prefixWord ++ tailWord_4226285) baseStart_4226285 baseEnd_4226285 := by
    simpa [prefixWord, tailWord_4226285, baseEnd_4226285] using wordTrace_append hprefix tailTrace_4226285
  have hstable : (prefixWord ++ tailWord_4226285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226285).length < 2 ^ (prefixWord ++ tailWord_4226285).sum := by decide
  have hdescent : baseEnd_4226285 < baseStart_4226285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226305 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_4226305 : Nat := 118140960795 + 4226305 * 2 ^ 59
def prefixEnd_4226305 : Nat := 4983230072969 + 3 ^ 40 * 4226305 * 2
def baseEnd_4226305 : Nat := 2170125857500192295951083

theorem tailTrace_4226305 : CollatzResearch.WordTrace tailWord_4226305 prefixEnd_4226305 2170125857500192295951083 := by
  unfold tailWord_4226305
  simp only [CollatzResearch.WordTrace]
  refine ⟨154146006953826255274040369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102764004635884170182693579 154146006953826255274040369)
  ·
    refine ⟨115609505215369691455530277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154146006953826255274040369 115609505215369691455530277)
    ·
      refine ⟨21676782227881817147911927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115609505215369691455530277 21676782227881817147911927)
      ·
        refine ⟨32515173341822725721867891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21676782227881817147911927 32515173341822725721867891)
        ·
          refine ⟨48772760012734088582801837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32515173341822725721867891 48772760012734088582801837)
          ·
            refine ⟨18289785004775283218550689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48772760012734088582801837 18289785004775283218550689)
            ·
              refine ⟨13717338753581462413913017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18289785004775283218550689 13717338753581462413913017)
              ·
                refine ⟨10288004065186096810434763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13717338753581462413913017 10288004065186096810434763)
                ·
                  refine ⟨15432006097779145215652145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10288004065186096810434763 15432006097779145215652145)
                  ·
                    refine ⟨11574004573334358911739109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15432006097779145215652145 11574004573334358911739109)
                    ·
                      refine ⟨2170125857500192295951083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11574004573334358911739109 2170125857500192295951083)
                      ·
                        rfl

theorem cell23_4226305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_4226305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226305 prefixEnd_4226305 := by exact prefixLift 4226305
  have htrace : WordTrace (prefixWord ++ tailWord_4226305) baseStart_4226305 baseEnd_4226305 := by
    simpa [prefixWord, tailWord_4226305, baseEnd_4226305] using wordTrace_append hprefix tailTrace_4226305
  have hstable : (prefixWord ++ tailWord_4226305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226305).length < 2 ^ (prefixWord ++ tailWord_4226305).sum := by decide
  have hdescent : baseEnd_4226305 < baseStart_4226305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226306 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_4226306 : Nat := 118140960795 + 4226306 * 2 ^ 59
def prefixEnd_4226306 : Nat := 4983230072969 + 3 ^ 40 * 4226306 * 2
def baseEnd_4226306 : Nat := 723375456993615597346193

theorem tailTrace_4226306 : CollatzResearch.WordTrace tailWord_4226306 prefixEnd_4226306 723375456993615597346193 := by
  unfold tailWord_4226306
  simp only [CollatzResearch.WordTrace]
  refine ⟨38536510856705658111206693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102764028951215088296551181 38536510856705658111206693)
  ·
    refine ⟨7225595785632310895851255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38536510856705658111206693 7225595785632310895851255)
    ·
      refine ⟨10838393678448466343776883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7225595785632310895851255 10838393678448466343776883)
      ·
        refine ⟨16257590517672699515665325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10838393678448466343776883 16257590517672699515665325)
        ·
          refine ⟨6096596444127262318374497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16257590517672699515665325 6096596444127262318374497)
          ·
            refine ⟨4572447333095446738780873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6096596444127262318374497 4572447333095446738780873)
            ·
              refine ⟨3429335499821585054085655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4572447333095446738780873 3429335499821585054085655)
              ·
                refine ⟨5144003249732377581128483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3429335499821585054085655 5144003249732377581128483)
                ·
                  refine ⟨7716004874598566371692725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5144003249732377581128483 7716004874598566371692725)
                  ·
                    refine ⟨723375456993615597346193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7716004874598566371692725 723375456993615597346193)
                    ·
                      rfl

theorem cell23_4226306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_4226306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226306 prefixEnd_4226306 := by exact prefixLift 4226306
  have htrace : WordTrace (prefixWord ++ tailWord_4226306) baseStart_4226306 baseEnd_4226306 := by
    simpa [prefixWord, tailWord_4226306, baseEnd_4226306] using wordTrace_append hprefix tailTrace_4226306
  have hstable : (prefixWord ++ tailWord_4226306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226306).length < 2 ^ (prefixWord ++ tailWord_4226306).sum := by decide
  have hdescent : baseEnd_4226306 < baseStart_4226306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226349 : List Nat := [1, 5, 3, 1, 1, 3, 2, 7]
def baseStart_4226349 : Nat := 118140960795 + 4226349 * 2 ^ 59
def prefixEnd_4226349 : Nat := 4983230072969 + 3 ^ 40 * 4226349 * 2
def baseEnd_4226349 : Nat := 80375868542555189770403

theorem tailTrace_4226349 : CollatzResearch.WordTrace tailWord_4226349 prefixEnd_4226349 80375868542555189770403 := by
  unfold tailWord_4226349
  simp only [CollatzResearch.WordTrace]
  refine ⟨154147611765666850788642101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102765074510444567192428067 154147611765666850788642101)
  ·
    refine ⟨14451338603031267261435197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154147611765666850788642101 14451338603031267261435197)
    ·
      refine ⟨5419251976136725223038199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14451338603031267261435197 5419251976136725223038199)
      ·
        refine ⟨8128877964205087834557299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5419251976136725223038199 8128877964205087834557299)
        ·
          refine ⟨12193316946307631751835949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128877964205087834557299 12193316946307631751835949)
          ·
            refine ⟨4572493854865361906938481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12193316946307631751835949 4572493854865361906938481)
            ·
              refine ⟨3429370391149021430203861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4572493854865361906938481 3429370391149021430203861)
              ·
                refine ⟨80375868542555189770403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3429370391149021430203861 80375868542555189770403)
                ·
                  rfl

theorem cell23_4226349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 7].length) (baseStart_4226349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226349 prefixEnd_4226349 := by exact prefixLift 4226349
  have htrace : WordTrace (prefixWord ++ tailWord_4226349) baseStart_4226349 baseEnd_4226349 := by
    simpa [prefixWord, tailWord_4226349, baseEnd_4226349] using wordTrace_append hprefix tailTrace_4226349
  have hstable : (prefixWord ++ tailWord_4226349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226349).length < 2 ^ (prefixWord ++ tailWord_4226349).sum := by decide
  have hdescent : baseEnd_4226349 < baseStart_4226349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226385 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_4226385 : Nat := 118140960795 + 4226385 * 2 ^ 59
def prefixEnd_4226385 : Nat := 4983230072969 + 3 ^ 40 * 4226385 * 2
def baseEnd_4226385 : Nat := 2170166935952551982950715

theorem tailTrace_4226385 : CollatzResearch.WordTrace tailWord_4226385 prefixEnd_4226385 2170166935952551982950715 := by
  unfold tailWord_4226385
  simp only [CollatzResearch.WordTrace]
  refine ⟨154148924793536428936952609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102765949862357619291301739 154148924793536428936952609)
  ·
    refine ⟨115611693595152321702714457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154148924793536428936952609 115611693595152321702714457)
    ·
      refine ⟨86708770196364241277035843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115611693595152321702714457 86708770196364241277035843)
      ·
        refine ⟨130063155294546361915553765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86708770196364241277035843 130063155294546361915553765)
        ·
          refine ⟨24386841617727442859166331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130063155294546361915553765 24386841617727442859166331)
          ·
            refine ⟨36580262426591164288749497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24386841617727442859166331 36580262426591164288749497)
            ·
              refine ⟨27435196819943373216562123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36580262426591164288749497 27435196819943373216562123)
              ·
                refine ⟨41152795229915059824843185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27435196819943373216562123 41152795229915059824843185)
                ·
                  refine ⟨30864596422436294868632389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41152795229915059824843185 30864596422436294868632389)
                  ·
                    refine ⟨5787111829206805287868573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30864596422436294868632389 5787111829206805287868573)
                    ·
                      refine ⟨2170166935952551982950715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5787111829206805287868573 2170166935952551982950715)
                      ·
                        rfl

theorem cell23_4226385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_4226385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226385 prefixEnd_4226385 := by exact prefixLift 4226385
  have htrace : WordTrace (prefixWord ++ tailWord_4226385) baseStart_4226385 baseEnd_4226385 := by
    simpa [prefixWord, tailWord_4226385, baseEnd_4226385] using wordTrace_append hprefix tailTrace_4226385
  have hstable : (prefixWord ++ tailWord_4226385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226385).length < 2 ^ (prefixWord ++ tailWord_4226385).sum := by decide
  have hdescent : baseEnd_4226385 < baseStart_4226385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226433 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_4226433 : Nat := 118140960795 + 4226433 * 2 ^ 59
def prefixEnd_4226433 : Nat := 4983230072969 + 3 ^ 40 * 4226433 * 2
def baseEnd_4226433 : Nat := 2170191583023967795150495

theorem tailTrace_4226433 : CollatzResearch.WordTrace tailWord_4226433 prefixEnd_4226433 2170191583023967795150495 := by
  unfold tailWord_4226433
  simp only [CollatzResearch.WordTrace]
  refine ⟨154150675497362533134699953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102767116998241688756466635 154150675497362533134699953)
  ·
    refine ⟨115613006623021899851024965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154150675497362533134699953 115613006623021899851024965)
    ·
      refine ⟨21677438741816606222067181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115613006623021899851024965 21677438741816606222067181)
      ·
        refine ⟨8129039528181227333275193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21677438741816606222067181 8129039528181227333275193)
        ·
          refine ⟨6096779646135920499956395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8129039528181227333275193 6096779646135920499956395)
          ·
            refine ⟨9145169469203880749934593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6096779646135920499956395 9145169469203880749934593)
            ·
              refine ⟨6858877101902910562450945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9145169469203880749934593 6858877101902910562450945)
              ·
                refine ⟨5144157826427182921838209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6858877101902910562450945 5144157826427182921838209)
                ·
                  refine ⟨3858118369820387191378657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5144157826427182921838209 3858118369820387191378657)
                  ·
                    refine ⟨2893588777365290393533993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3858118369820387191378657 2893588777365290393533993)
                    ·
                      refine ⟨2170191583023967795150495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893588777365290393533993 2170191583023967795150495)
                      ·
                        rfl

theorem cell23_4226433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_4226433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226433 prefixEnd_4226433 := by exact prefixLift 4226433
  have htrace : WordTrace (prefixWord ++ tailWord_4226433) baseStart_4226433 baseEnd_4226433 := by
    simpa [prefixWord, tailWord_4226433, baseEnd_4226433] using wordTrace_append hprefix tailTrace_4226433
  have hstable : (prefixWord ++ tailWord_4226433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226433).length < 2 ^ (prefixWord ++ tailWord_4226433).sum := by decide
  have hdescent : baseEnd_4226433 < baseStart_4226433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226439 : List Nat := [1, 1, 4, 2, 2, 2, 4, 2, 5]
def baseStart_4226439 : Nat := 118140960795 + 4226439 * 2 ^ 59
def prefixEnd_4226439 : Nat := 4983230072969 + 3 ^ 40 * 4226439 * 2
def baseEnd_4226439 : Nat := 241132740434210530186163

theorem tailTrace_4226439 : CollatzResearch.WordTrace tailWord_4226439 prefixEnd_4226439 241132740434210530186163 := by
  unfold tailWord_4226439
  simp only [CollatzResearch.WordTrace]
  refine ⟨154150894335340796159418371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102767262890227197439612247 154150894335340796159418371)
  ·
    refine ⟨231226341503011194239127557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154150894335340796159418371 231226341503011194239127557)
    ·
      refine ⟨43354939031814598919836417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231226341503011194239127557 43354939031814598919836417)
      ·
        refine ⟨32516204273860949189877313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43354939031814598919836417 32516204273860949189877313)
        ·
          refine ⟨24387153205395711892407985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32516204273860949189877313 24387153205395711892407985)
          ·
            refine ⟨18290364904046783919305989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24387153205395711892407985 18290364904046783919305989)
            ·
              refine ⟨3429443419508771984869873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18290364904046783919305989 3429443419508771984869873)
              ·
                refine ⟨2572082564631578988652405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3429443419508771984869873 2572082564631578988652405)
                ·
                  refine ⟨241132740434210530186163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572082564631578988652405 241132740434210530186163)
                  ·
                    rfl

theorem cell23_4226439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 5].length) (baseStart_4226439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226439 prefixEnd_4226439 := by exact prefixLift 4226439
  have htrace : WordTrace (prefixWord ++ tailWord_4226439) baseStart_4226439 baseEnd_4226439 := by
    simpa [prefixWord, tailWord_4226439, baseEnd_4226439] using wordTrace_append hprefix tailTrace_4226439
  have hstable : (prefixWord ++ tailWord_4226439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226439).length < 2 ^ (prefixWord ++ tailWord_4226439).sum := by decide
  have hdescent : baseEnd_4226439 < baseStart_4226439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226455 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_4226455 : Nat := 118140960795 + 4226455 * 2 ^ 59
def prefixEnd_4226455 : Nat := 4983230072969 + 3 ^ 40 * 4226455 * 2
def baseEnd_4226455 : Nat := 2170202879598366709075393

theorem tailTrace_4226455 : CollatzResearch.WordTrace tailWord_4226455 prefixEnd_4226455 2170202879598366709075393 := by
  unfold tailWord_4226455
  simp only [CollatzResearch.WordTrace]
  refine ⟨154151477903282830892000819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102767651935521887261333879 154151477903282830892000819)
  ·
    refine ⟨231227216854924246338001229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154151477903282830892000819 231227216854924246338001229)
    ·
      refine ⟨86710206320596592376750461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231227216854924246338001229 86710206320596592376750461)
      ·
        refine ⟨32516327370223722141281423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86710206320596592376750461 32516327370223722141281423)
        ·
          refine ⟨48774491055335583211922135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32516327370223722141281423 48774491055335583211922135)
          ·
            refine ⟨73161736583003374817883203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48774491055335583211922135 73161736583003374817883203)
            ·
              refine ⟨109742604874505062226824805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73161736583003374817883203 109742604874505062226824805)
              ·
                refine ⟨20576738413969699167529651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109742604874505062226824805 20576738413969699167529651)
                ·
                  refine ⟨30865107620954548751294477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20576738413969699167529651 30865107620954548751294477)
                  ·
                    refine ⟨11574415357857955781735429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30865107620954548751294477 11574415357857955781735429)
                    ·
                      refine ⟨2170202879598366709075393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11574415357857955781735429 2170202879598366709075393)
                      ·
                        rfl

theorem cell23_4226455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_4226455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226455 prefixEnd_4226455 := by exact prefixLift 4226455
  have htrace : WordTrace (prefixWord ++ tailWord_4226455) baseStart_4226455 baseEnd_4226455 := by
    simpa [prefixWord, tailWord_4226455, baseEnd_4226455] using wordTrace_append hprefix tailTrace_4226455
  have hstable : (prefixWord ++ tailWord_4226455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226455).length < 2 ^ (prefixWord ++ tailWord_4226455).sum := by decide
  have hdescent : baseEnd_4226455 < baseStart_4226455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226499 : List Nat := [1, 1, 1, 3, 1, 1, 6, 4, 1, 4]
def baseStart_4226499 : Nat := 118140960795 + 4226499 * 2 ^ 59
def prefixEnd_4226499 : Nat := 4983230072969 + 3 ^ 40 * 4226499 * 2
def baseEnd_4226499 : Nat := 723408490915721512308397

theorem tailTrace_4226499 : CollatzResearch.WordTrace tailWord_4226499 prefixEnd_4226499 723408490915721512308397 := by
  unfold tailWord_4226499
  simp only [CollatzResearch.WordTrace]
  refine ⟨154153082715123426406602551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102768721810082284271068367 154153082715123426406602551)
  ·
    refine ⟨231229624072685139609903827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154153082715123426406602551 231229624072685139609903827)
    ·
      refine ⟨346844436109027709414855741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231229624072685139609903827 346844436109027709414855741)
      ·
        refine ⟨130066663540885391030570903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346844436109027709414855741 130066663540885391030570903)
        ·
          refine ⟨195099995311328086545856355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130066663540885391030570903 195099995311328086545856355)
          ·
            refine ⟨292649992966992129818784533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195099995311328086545856355 292649992966992129818784533)
            ·
              refine ⟨13717968420327756085255525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 292649992966992129818784533 13717968420327756085255525)
              ·
                refine ⟨2572119078811454265985411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13717968420327756085255525 2572119078811454265985411)
                ·
                  refine ⟨3858178618217181398978117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572119078811454265985411 3858178618217181398978117)
                  ·
                    refine ⟨723408490915721512308397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858178618217181398978117 723408490915721512308397)
                    ·
                      rfl

theorem cell23_4226499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 4].length) (baseStart_4226499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226499 prefixEnd_4226499 := by exact prefixLift 4226499
  have htrace : WordTrace (prefixWord ++ tailWord_4226499) baseStart_4226499 baseEnd_4226499 := by
    simpa [prefixWord, tailWord_4226499, baseEnd_4226499] using wordTrace_append hprefix tailTrace_4226499
  have hstable : (prefixWord ++ tailWord_4226499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226499).length < 2 ^ (prefixWord ++ tailWord_4226499).sum := by decide
  have hdescent : baseEnd_4226499 < baseStart_4226499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226533 : List Nat := [1, 3, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_4226533 : Nat := 118140960795 + 4226533 * 2 ^ 59
def prefixEnd_4226533 : Nat := 4983230072969 + 3 ^ 40 * 4226533 * 2
def baseEnd_4226533 : Nat := 723414310363139134633345

theorem tailTrace_4226533 : CollatzResearch.WordTrace tailWord_4226533 prefixEnd_4226533 723414310363139134633345 := by
  unfold tailWord_4226533
  simp only [CollatzResearch.WordTrace]
  refine ⟨154154322797000250213340253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102769548531333500142226835 154154322797000250213340253)
  ·
    refine ⟨57807871048875093830002595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154154322797000250213340253 57807871048875093830002595)
    ·
      refine ⟨86711806573312640745003893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57807871048875093830002595 86711806573312640745003893)
      ·
        refine ⟨8129231866248060069844115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86711806573312640745003893 8129231866248060069844115)
        ·
          refine ⟨12193847799372090104766173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8129231866248060069844115 12193847799372090104766173)
          ·
            refine ⟨4572692924764533789287315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12193847799372090104766173 4572692924764533789287315)
            ·
              refine ⟨6859039387146800683930973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572692924764533789287315 6859039387146800683930973)
              ·
                refine ⟨2572139770180050256474115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6859039387146800683930973 2572139770180050256474115)
                ·
                  refine ⟨3858209655270075384711173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572139770180050256474115 3858209655270075384711173)
                  ·
                    refine ⟨723414310363139134633345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858209655270075384711173 723414310363139134633345)
                    ·
                      rfl

theorem cell23_4226533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_4226533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226533 prefixEnd_4226533 := by exact prefixLift 4226533
  have htrace : WordTrace (prefixWord ++ tailWord_4226533) baseStart_4226533 baseEnd_4226533 := by
    simpa [prefixWord, tailWord_4226533, baseEnd_4226533] using wordTrace_append hprefix tailTrace_4226533
  have hstable : (prefixWord ++ tailWord_4226533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226533).length < 2 ^ (prefixWord ++ tailWord_4226533).sum := by decide
  have hdescent : baseEnd_4226533 < baseStart_4226533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226555 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 3, 6]
def baseStart_4226555 : Nat := 118140960795 + 4226555 * 2 ^ 59
def prefixEnd_4226555 : Nat := 4983230072969 + 3 ^ 40 * 4226555 * 2
def baseEnd_4226555 : Nat := 723418075887938772608311

theorem tailTrace_4226555 : CollatzResearch.WordTrace tailWord_4226555 prefixEnd_4226555 723418075887938772608311 := by
  unfold tailWord_4226555
  simp only [CollatzResearch.WordTrace]
  refine ⟨154155125202920547970641119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102770083468613698647094079 154155125202920547970641119)
  ·
    refine ⟨231232687804380821955961679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154155125202920547970641119 231232687804380821955961679)
    ·
      refine ⟨346849031706571232933942519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231232687804380821955961679 346849031706571232933942519)
      ·
        refine ⟨520273547559856849400913779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346849031706571232933942519 520273547559856849400913779)
        ·
          refine ⟨780410321339785274101370669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520273547559856849400913779 780410321339785274101370669)
          ·
            refine ⟨292653870502419477788014001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 780410321339785274101370669 292653870502419477788014001)
            ·
              refine ⟨219490402876814608341010501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292653870502419477788014001 219490402876814608341010501)
              ·
                refine ⟨41154450539402739063939469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219490402876814608341010501 41154450539402739063939469)
                ·
                  refine ⟨15432918952276027148977301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41154450539402739063939469 15432918952276027148977301)
                  ·
                    refine ⟨723418075887938772608311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15432918952276027148977301 723418075887938772608311)
                    ·
                      rfl

theorem cell23_4226555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 6].length) (baseStart_4226555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226555 prefixEnd_4226555 := by exact prefixLift 4226555
  have htrace : WordTrace (prefixWord ++ tailWord_4226555) baseStart_4226555 baseEnd_4226555 := by
    simpa [prefixWord, tailWord_4226555, baseEnd_4226555] using wordTrace_append hprefix tailTrace_4226555
  have hstable : (prefixWord ++ tailWord_4226555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226555).length < 2 ^ (prefixWord ++ tailWord_4226555).sum := by decide
  have hdescent : baseEnd_4226555 < baseStart_4226555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226556 : List Nat := [2, 2, 2, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_4226556 : Nat := 118140960795 + 4226556 * 2 ^ 59
def prefixEnd_4226556 : Nat := 4983230072969 + 3 ^ 40 * 4226556 * 2
def baseEnd_4226556 : Nat := 2170254741144470813912429

theorem tailTrace_4226556 : CollatzResearch.WordTrace tailWord_4226556 prefixEnd_4226556 2170254741144470813912429 := by
  unfold tailWord_4226556
  simp only [CollatzResearch.WordTrace]
  refine ⟨77077580837958462570713761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102770107783944616760951681 77077580837958462570713761)
  ·
    refine ⟨57808185628468846928035321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77077580837958462570713761 57808185628468846928035321)
    ·
      refine ⟨43356139221351635196026491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57808185628468846928035321 43356139221351635196026491)
      ·
        refine ⟨65034208832027452794039737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43356139221351635196026491 65034208832027452794039737)
        ·
          refine ⟨48775656624020589595529803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65034208832027452794039737 48775656624020589595529803)
          ·
            refine ⟨73163484936030884393294705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48775656624020589595529803 73163484936030884393294705)
            ·
              refine ⟨54872613702023163294971029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73163484936030884393294705 54872613702023163294971029)
              ·
                refine ⟨2572153767282335779451767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54872613702023163294971029 2572153767282335779451767)
                ·
                  refine ⟨3858230650923503669177651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572153767282335779451767 3858230650923503669177651)
                  ·
                    refine ⟨5787345976385255503766477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3858230650923503669177651 5787345976385255503766477)
                    ·
                      refine ⟨2170254741144470813912429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5787345976385255503766477 2170254741144470813912429)
                      ·
                        rfl

theorem cell23_4226556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_4226556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226556 prefixEnd_4226556 := by exact prefixLift 4226556
  have htrace : WordTrace (prefixWord ++ tailWord_4226556) baseStart_4226556 baseEnd_4226556 := by
    simpa [prefixWord, tailWord_4226556, baseEnd_4226556] using wordTrace_append hprefix tailTrace_4226556
  have hstable : (prefixWord ++ tailWord_4226556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226556).length < 2 ^ (prefixWord ++ tailWord_4226556).sum := by decide
  have hdescent : baseEnd_4226556 < baseStart_4226556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226575 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_4226575 : Nat := 118140960795 + 4226575 * 2 ^ 59
def prefixEnd_4226575 : Nat := 4983230072969 + 3 ^ 40 * 4226575 * 2
def baseEnd_4226575 : Nat := 2170264497276906239574841

theorem tailTrace_4226575 : CollatzResearch.WordTrace tailWord_4226575 prefixEnd_4226575 2170264497276906239574841 := by
  unfold tailWord_4226575
  simp only [CollatzResearch.WordTrace]
  refine ⟨154155854662848091386369179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102770569775232060924246119 154155854662848091386369179)
  ·
    refine ⟨231233781994272137079553769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154155854662848091386369179 231233781994272137079553769)
    ·
      refine ⟨173425336495704102809665327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231233781994272137079553769 173425336495704102809665327)
      ·
        refine ⟨260138004743556154214497991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173425336495704102809665327 260138004743556154214497991)
        ·
          refine ⟨390207007115334231321746987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260138004743556154214497991 390207007115334231321746987)
          ·
            refine ⟨585310510673001346982620481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390207007115334231321746987 585310510673001346982620481)
            ·
              refine ⟨438982883004751010236965361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585310510673001346982620481 438982883004751010236965361)
              ·
                refine ⟨329237162253563257677724021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438982883004751010236965361 329237162253563257677724021)
                ·
                  refine ⟨30865983961271555407286627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329237162253563257677724021 30865983961271555407286627)
                  ·
                    refine ⟨46298975941907333110929941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30865983961271555407286627 46298975941907333110929941)
                    ·
                      refine ⟨2170264497276906239574841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46298975941907333110929941 2170264497276906239574841)
                      ·
                        rfl

theorem cell23_4226575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_4226575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226575 prefixEnd_4226575 := by exact prefixLift 4226575
  have htrace : WordTrace (prefixWord ++ tailWord_4226575) baseStart_4226575 baseEnd_4226575 := by
    simpa [prefixWord, tailWord_4226575, baseEnd_4226575] using wordTrace_append hprefix tailTrace_4226575
  have hstable : (prefixWord ++ tailWord_4226575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226575).length < 2 ^ (prefixWord ++ tailWord_4226575).sum := by decide
  have hdescent : baseEnd_4226575 < baseStart_4226575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226579 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 4]
def baseStart_4226579 : Nat := 118140960795 + 4226579 * 2 ^ 59
def prefixEnd_4226579 : Nat := 4983230072969 + 3 ^ 40 * 4226579 * 2
def baseEnd_4226579 : Nat := 2170266551199524223924823

theorem tailTrace_4226579 : CollatzResearch.WordTrace tailWord_4226579 prefixEnd_4226579 2170266551199524223924823 := by
  unfold tailWord_4226579
  simp only [CollatzResearch.WordTrace]
  refine ⟨154156000554833600069514791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102770667036555733379676527 154156000554833600069514791)
  ·
    refine ⟨231234000832250400104272187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154156000554833600069514791 231234000832250400104272187)
    ·
      refine ⟨346851001248375600156408281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231234000832250400104272187 346851001248375600156408281)
      ·
        refine ⟨260138250936281700117306211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346851001248375600156408281 260138250936281700117306211)
        ·
          refine ⟨390207376404422550175959317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260138250936281700117306211 390207376404422550175959317)
          ·
            refine ⟨18290970768957307039498093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 390207376404422550175959317 18290970768957307039498093)
            ·
              refine ⟨6859114038358990139811785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18290970768957307039498093 6859114038358990139811785)
              ·
                refine ⟨5144335528769242604858839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6859114038358990139811785 5144335528769242604858839)
                ·
                  refine ⟨7716503293153863907288259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5144335528769242604858839 7716503293153863907288259)
                  ·
                    refine ⟨11574754939730795860932389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7716503293153863907288259 11574754939730795860932389)
                    ·
                      refine ⟨2170266551199524223924823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11574754939730795860932389 2170266551199524223924823)
                      ·
                        rfl

theorem cell23_4226579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_4226579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226579 prefixEnd_4226579 := by exact prefixLift 4226579
  have htrace : WordTrace (prefixWord ++ tailWord_4226579) baseStart_4226579 baseEnd_4226579 := by
    simpa [prefixWord, tailWord_4226579, baseEnd_4226579] using wordTrace_append hprefix tailTrace_4226579
  have hstable : (prefixWord ++ tailWord_4226579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226579).length < 2 ^ (prefixWord ++ tailWord_4226579).sum := by decide
  have hdescent : baseEnd_4226579 < baseStart_4226579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226606 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_4226606 : Nat := 118140960795 + 4226606 * 2 ^ 59
def prefixEnd_4226606 : Nat := 4983230072969 + 3 ^ 40 * 4226606 * 2
def baseEnd_4226606 : Nat := 723426805059065206095733

theorem tailTrace_4226606 : CollatzResearch.WordTrace tailWord_4226606 prefixEnd_4226606 723426805059065206095733 := by
  unfold tailWord_4226606
  simp only [CollatzResearch.WordTrace]
  refine ⟨19269623165716972960093459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102771323550490522453831781 19269623165716972960093459)
  ·
    refine ⟨28904434748575459440140189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19269623165716972960093459 28904434748575459440140189)
    ·
      refine ⟨10839163030715797290052571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28904434748575459440140189 10839163030715797290052571)
      ·
        refine ⟨16258744546073695935078857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10839163030715797290052571 16258744546073695935078857)
        ·
          refine ⟨12194058409555271951309143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16258744546073695935078857 12194058409555271951309143)
          ·
            refine ⟨18291087614332907926963715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12194058409555271951309143 18291087614332907926963715)
            ·
              refine ⟨27436631421499361890445573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18291087614332907926963715 27436631421499361890445573)
              ·
                refine ⟨5144368391531130354458545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27436631421499361890445573 5144368391531130354458545)
                ·
                  refine ⟨3858276293648347765843909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5144368391531130354458545 3858276293648347765843909)
                  ·
                    refine ⟨723426805059065206095733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858276293648347765843909 723426805059065206095733)
                    ·
                      rfl

theorem cell23_4226606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_4226606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226606 prefixEnd_4226606 := by exact prefixLift 4226606
  have htrace : WordTrace (prefixWord ++ tailWord_4226606) baseStart_4226606 baseEnd_4226606 := by
    simpa [prefixWord, tailWord_4226606, baseEnd_4226606] using wordTrace_append hprefix tailTrace_4226606
  have hstable : (prefixWord ++ tailWord_4226606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226606).length < 2 ^ (prefixWord ++ tailWord_4226606).sum := by decide
  have hdescent : baseEnd_4226606 < baseStart_4226606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226629 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_4226629 : Nat := 118140960795 + 4226629 * 2 ^ 59
def prefixEnd_4226629 : Nat := 4983230072969 + 3 ^ 40 * 4226629 * 2
def baseEnd_4226629 : Nat := 2170292225232249028299593

theorem tailTrace_4226629 : CollatzResearch.WordTrace tailWord_4226629 prefixEnd_4226629 2170292225232249028299593 := by
  unfold tailWord_4226629
  simp only [CollatzResearch.WordTrace]
  refine ⟨154157824204652458608834941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102771882803101639072556627 154157824204652458608834941)
  ·
    refine ⟨57809184076744671978313103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154157824204652458608834941 57809184076744671978313103)
    ·
      refine ⟨86713776115117007967469655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57809184076744671978313103 86713776115117007967469655)
      ·
        refine ⟨130070664172675511951204483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86713776115117007967469655 130070664172675511951204483)
        ·
          refine ⟨195105996259013267926806725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130070664172675511951204483 195105996259013267926806725)
          ·
            refine ⟨36582374298564987736276261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195105996259013267926806725 36582374298564987736276261)
            ·
              refine ⟨6859195180980935200551799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36582374298564987736276261 6859195180980935200551799)
              ·
                refine ⟨10288792771471402800827699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6859195180980935200551799 10288792771471402800827699)
                ·
                  refine ⟨15433189157207104201241549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10288792771471402800827699 15433189157207104201241549)
                  ·
                    refine ⟨5787445933952664075465581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15433189157207104201241549 5787445933952664075465581)
                    ·
                      refine ⟨2170292225232249028299593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5787445933952664075465581 2170292225232249028299593)
                      ·
                        rfl

theorem cell23_4226629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_4226629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226629 prefixEnd_4226629 := by exact prefixLift 4226629
  have htrace : WordTrace (prefixWord ++ tailWord_4226629) baseStart_4226629 baseEnd_4226629 := by
    simpa [prefixWord, tailWord_4226629, baseEnd_4226629] using wordTrace_append hprefix tailTrace_4226629
  have hstable : (prefixWord ++ tailWord_4226629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226629).length < 2 ^ (prefixWord ++ tailWord_4226629).sum := by decide
  have hdescent : baseEnd_4226629 < baseStart_4226629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226682 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_4226682 : Nat := 118140960795 + 4226682 * 2 ^ 59
def prefixEnd_4226682 : Nat := 4983230072969 + 3 ^ 40 * 4226682 * 2
def baseEnd_4226682 : Nat := 2170319439706937320936849

theorem tailTrace_4226682 : CollatzResearch.WordTrace tailWord_4226682 prefixEnd_4226682 2170319439706937320936849 := by
  unfold tailWord_4226682
  simp only [CollatzResearch.WordTrace]
  refine ⟨38539939318365112165128575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102773171515640299107009533 38539939318365112165128575)
  ·
    refine ⟨57809908977547668247692863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38539939318365112165128575 57809908977547668247692863)
    ·
      refine ⟨86714863466321502371539295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57809908977547668247692863 86714863466321502371539295)
      ·
        refine ⟨130072295199482253557308943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86714863466321502371539295 130072295199482253557308943)
        ·
          refine ⟨195108442799223380335963415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130072295199482253557308943 195108442799223380335963415)
          ·
            refine ⟨292662664198835070503945123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195108442799223380335963415 292662664198835070503945123)
            ·
              refine ⟨438993996298252605755917685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292662664198835070503945123 438993996298252605755917685)
              ·
                refine ⟨41155687152961181789617283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 438993996298252605755917685 41155687152961181789617283)
                ·
                  refine ⟨61733530729441772684425925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41155687152961181789617283 61733530729441772684425925)
                  ·
                    refine ⟨11575037011770332378329861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61733530729441772684425925 11575037011770332378329861)
                    ·
                      refine ⟨2170319439706937320936849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11575037011770332378329861 2170319439706937320936849)
                      ·
                        rfl

theorem cell23_4226682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_4226682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226682 prefixEnd_4226682 := by exact prefixLift 4226682
  have htrace : WordTrace (prefixWord ++ tailWord_4226682) baseStart_4226682 baseEnd_4226682 := by
    simpa [prefixWord, tailWord_4226682, baseEnd_4226682] using wordTrace_append hprefix tailTrace_4226682
  have hstable : (prefixWord ++ tailWord_4226682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226682).length < 2 ^ (prefixWord ++ tailWord_4226682).sum := by decide
  have hdescent : baseEnd_4226682 < baseStart_4226682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226706 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_4226706 : Nat := 118140960795 + 4226706 * 2 ^ 59
def prefixEnd_4226706 : Nat := 4983230072969 + 3 ^ 40 * 4226706 * 2
def baseEnd_4226706 : Nat := 2170331763242645227036739

theorem tailTrace_4226706 : CollatzResearch.WordTrace tailWord_4226706 prefixEnd_4226706 2170331763242645227036739 := by
  unfold tailWord_4226706
  simp only [CollatzResearch.WordTrace]
  refine ⟨38540158156343375189846993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102773755083582333839591981 38540158156343375189846993)
  ·
    refine ⟨28905118617257531392385245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38540158156343375189846993 28905118617257531392385245)
    ·
      refine ⟨10839419481471574272144467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28905118617257531392385245 10839419481471574272144467)
      ·
        refine ⟨16259129222207361408216701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10839419481471574272144467 16259129222207361408216701)
        ·
          refine ⟨6097173458327760528081263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16259129222207361408216701 6097173458327760528081263)
          ·
            refine ⟨9145760187491640792121895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097173458327760528081263 9145760187491640792121895)
            ·
              refine ⟨13718640281237461188182843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9145760187491640792121895 13718640281237461188182843)
              ·
                refine ⟨20577960421856191782274265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13718640281237461188182843 20577960421856191782274265)
                ·
                  refine ⟨15433470316392143836705699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20577960421856191782274265 15433470316392143836705699)
                  ·
                    refine ⟨23150205474588215755058549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15433470316392143836705699 23150205474588215755058549)
                    ·
                      refine ⟨2170331763242645227036739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23150205474588215755058549 2170331763242645227036739)
                      ·
                        rfl

theorem cell23_4226706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_4226706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226706 prefixEnd_4226706 := by exact prefixLift 4226706
  have htrace : WordTrace (prefixWord ++ tailWord_4226706) baseStart_4226706 baseEnd_4226706 := by
    simpa [prefixWord, tailWord_4226706, baseEnd_4226706] using wordTrace_append hprefix tailTrace_4226706
  have hstable : (prefixWord ++ tailWord_4226706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226706).length < 2 ^ (prefixWord ++ tailWord_4226706).sum := by decide
  have hdescent : baseEnd_4226706 < baseStart_4226706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226756 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_4226756 : Nat := 118140960795 + 4226756 * 2 ^ 59
def prefixEnd_4226756 : Nat := 4983230072969 + 3 ^ 40 * 4226756 * 2
def baseEnd_4226756 : Nat := 723452479091790010470503

theorem tailTrace_4226756 : CollatzResearch.WordTrace tailWord_4226756 prefixEnd_4226756 723452479091790010470503 := by
  unfold tailWord_4226756
  simp only [CollatzResearch.WordTrace]
  refine ⟨77081228137596179649354061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102774970850128239532472081 77081228137596179649354061)
  ·
    refine ⟨28905460551598567368507773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77081228137596179649354061 28905460551598567368507773)
    ·
      refine ⟨10839547706849462763190415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28905460551598567368507773 10839547706849462763190415)
      ·
        refine ⟨16259321560274194144785623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10839547706849462763190415 16259321560274194144785623)
        ·
          refine ⟨24388982340411291217178435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16259321560274194144785623 24388982340411291217178435)
          ·
            refine ⟨36583473510616936825767653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24388982340411291217178435 36583473510616936825767653)
            ·
              refine ⟨6859401283240675654831435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36583473510616936825767653 6859401283240675654831435)
              ·
                refine ⟨10289101924861013482247153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6859401283240675654831435 10289101924861013482247153)
                ·
                  refine ⟨7716826443645760111685365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10289101924861013482247153 7716826443645760111685365)
                  ·
                    refine ⟨723452479091790010470503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7716826443645760111685365 723452479091790010470503)
                    ·
                      rfl

theorem cell23_4226756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_4226756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226756 prefixEnd_4226756 := by exact prefixLift 4226756
  have htrace : WordTrace (prefixWord ++ tailWord_4226756) baseStart_4226756 baseEnd_4226756 := by
    simpa [prefixWord, tailWord_4226756, baseEnd_4226756] using wordTrace_append hprefix tailTrace_4226756
  have hstable : (prefixWord ++ tailWord_4226756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226756).length < 2 ^ (prefixWord ++ tailWord_4226756).sum := by decide
  have hdescent : baseEnd_4226756 < baseStart_4226756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226776 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 2, 4, 2]
def baseStart_4226776 : Nat := 118140960795 + 4226776 * 2 ^ 59
def prefixEnd_4226776 : Nat := 4983230072969 + 3 ^ 40 * 4226776 * 2
def baseEnd_4226776 : Nat := 2170367706888459953161417

theorem tailTrace_4226776 : CollatzResearch.WordTrace tailWord_4226776 prefixEnd_4226776 2170367706888459953161417 := by
  unfold tailWord_4226776
  simp only [CollatzResearch.WordTrace]
  refine ⟨77081592867559951357218091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102775457156746601809624121 77081592867559951357218091)
  ·
    refine ⟨115622389301339927035827137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77081592867559951357218091 115622389301339927035827137)
    ·
      refine ⟨86716791976004945276870353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115622389301339927035827137 86716791976004945276870353)
      ·
        refine ⟨65037593982003708957652765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86716791976004945276870353 65037593982003708957652765)
        ·
          refine ⟨24389097743251390859119787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65037593982003708957652765 24389097743251390859119787)
          ·
            refine ⟨36583646614877086288679681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24389097743251390859119787 36583646614877086288679681)
            ·
              refine ⟨27437734961157814716509761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36583646614877086288679681 27437734961157814716509761)
              ·
                refine ⟨20578301220868361037382321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27437734961157814716509761 20578301220868361037382321)
                ·
                  refine ⟨15433725915651270778036741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20578301220868361037382321 15433725915651270778036741)
                  ·
                    refine ⟨2893823609184613270881889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15433725915651270778036741 2893823609184613270881889)
                    ·
                      refine ⟨2170367706888459953161417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893823609184613270881889 2170367706888459953161417)
                      ·
                        rfl

theorem cell23_4226776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_4226776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226776 prefixEnd_4226776 := by exact prefixLift 4226776
  have htrace : WordTrace (prefixWord ++ tailWord_4226776) baseStart_4226776 baseEnd_4226776 := by
    simpa [prefixWord, tailWord_4226776, baseEnd_4226776] using wordTrace_append hprefix tailTrace_4226776
  have hstable : (prefixWord ++ tailWord_4226776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226776).length < 2 ^ (prefixWord ++ tailWord_4226776).sum := by decide
  have hdescent : baseEnd_4226776 < baseStart_4226776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226799 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 6]
def baseStart_4226799 : Nat := 118140960795 + 4226799 * 2 ^ 59
def prefixEnd_4226799 : Nat := 4983230072969 + 3 ^ 40 * 4226799 * 2
def baseEnd_4226799 : Nat := 241153279660390373685979

theorem tailTrace_4226799 : CollatzResearch.WordTrace tailWord_4226799 prefixEnd_4226799 241153279660390373685979 := by
  unfold tailWord_4226799
  simp only [CollatzResearch.WordTrace]
  refine ⟨154164024614036577642523451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102776016409357718428348967 154164024614036577642523451)
  ·
    refine ⟨231246036921054866463785177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154164024614036577642523451 231246036921054866463785177)
    ·
      refine ⟨173434527690791149847838883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231246036921054866463785177 173434527690791149847838883)
      ·
        refine ⟨260151791536186724771758325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173434527690791149847838883 260151791536186724771758325)
        ·
          refine ⟨24389230456517505447352343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260151791536186724771758325 24389230456517505447352343)
          ·
            refine ⟨36583845684776258171028515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24389230456517505447352343 36583845684776258171028515)
            ·
              refine ⟨54875768527164387256542773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36583845684776258171028515 54875768527164387256542773)
              ·
                refine ⟨5144603299421661305300885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54875768527164387256542773 5144603299421661305300885)
                ·
                  refine ⟨241153279660390373685979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5144603299421661305300885 241153279660390373685979)
                  ·
                    rfl

theorem cell23_4226799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 6].length) (baseStart_4226799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226799 prefixEnd_4226799 := by exact prefixLift 4226799
  have htrace : WordTrace (prefixWord ++ tailWord_4226799) baseStart_4226799 baseEnd_4226799 := by
    simpa [prefixWord, tailWord_4226799, baseEnd_4226799] using wordTrace_append hprefix tailTrace_4226799
  have hstable : (prefixWord ++ tailWord_4226799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226799).length < 2 ^ (prefixWord ++ tailWord_4226799).sum := by decide
  have hdescent : baseEnd_4226799 < baseStart_4226799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226820 : List Nat := [2, 3, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_4226820 : Nat := 118140960795 + 4226820 * 2 ^ 59
def prefixEnd_4226820 : Nat := 4983230072969 + 3 ^ 40 * 4226820 * 2
def baseEnd_4226820 : Nat := 723463433345752593670405

theorem tailTrace_4226820 : CollatzResearch.WordTrace tailWord_4226820 prefixEnd_4226820 723463433345752593670405 := by
  unfold tailWord_4226820
  simp only [CollatzResearch.WordTrace]
  refine ⟨77082395273480249114518957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102776527031306998819358609 77082395273480249114518957)
  ·
    refine ⟨28905898227555093417944609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77082395273480249114518957 28905898227555093417944609)
    ·
      refine ⟨21679423670666320063458457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28905898227555093417944609 21679423670666320063458457)
      ·
        refine ⟨16259567752999740047593843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21679423670666320063458457 16259567752999740047593843)
        ·
          refine ⟨24389351629499610071390765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16259567752999740047593843 24389351629499610071390765)
          ·
            refine ⟨9146006861062353776771537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24389351629499610071390765 9146006861062353776771537)
            ·
              refine ⟨6859505145796765332578653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9146006861062353776771537 6859505145796765332578653)
              ·
                refine ⟨2572314429673786999716995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6859505145796765332578653 2572314429673786999716995)
                ·
                  refine ⟨3858471644510680499575493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572314429673786999716995 3858471644510680499575493)
                  ·
                    refine ⟨723463433345752593670405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858471644510680499575493 723463433345752593670405)
                    ·
                      rfl

theorem cell23_4226820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_4226820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226820 prefixEnd_4226820 := by exact prefixLift 4226820
  have htrace : WordTrace (prefixWord ++ tailWord_4226820) baseStart_4226820 baseEnd_4226820 := by
    simpa [prefixWord, tailWord_4226820, baseEnd_4226820] using wordTrace_append hprefix tailTrace_4226820
  have hstable : (prefixWord ++ tailWord_4226820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226820).length < 2 ^ (prefixWord ++ tailWord_4226820).sum := by decide
  have hdescent : baseEnd_4226820 < baseStart_4226820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226870 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4226870 : Nat := 118140960795 + 4226870 * 2 ^ 59
def prefixEnd_4226870 : Nat := 4983230072969 + 3 ^ 40 * 4226870 * 2
def baseEnd_4226870 : Nat := 2170415974069982585385985

theorem tailTrace_4226870 : CollatzResearch.WordTrace tailWord_4226870 prefixEnd_4226870 2170415974069982585385985 := by
  unfold tailWord_4226870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635413387298709798022379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102777742797852904512238709 9635413387298709798022379)
  ·
    refine ⟨14453120080948064697033569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9635413387298709798022379 14453120080948064697033569)
    ·
      refine ⟨10839840060711048522775177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14453120080948064697033569 10839840060711048522775177)
      ·
        refine ⟨8129880045533286392081383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10839840060711048522775177 8129880045533286392081383)
        ·
          refine ⟨12194820068299929588122075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8129880045533286392081383 12194820068299929588122075)
          ·
            refine ⟨18292230102449894382183113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12194820068299929588122075 18292230102449894382183113)
            ·
              refine ⟨13719172576837420786637335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18292230102449894382183113 13719172576837420786637335)
              ·
                refine ⟨20578758865256131179956003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13719172576837420786637335 20578758865256131179956003)
                ·
                  refine ⟨30868138297884196769934005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20578758865256131179956003 30868138297884196769934005)
                  ·
                    refine ⟨2893887965426643447181313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30868138297884196769934005 2893887965426643447181313)
                    ·
                      refine ⟨2170415974069982585385985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893887965426643447181313 2170415974069982585385985)
                      ·
                        rfl

theorem cell23_4226870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4226870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226870 prefixEnd_4226870 := by exact prefixLift 4226870
  have htrace : WordTrace (prefixWord ++ tailWord_4226870) baseStart_4226870 baseEnd_4226870 := by
    simpa [prefixWord, tailWord_4226870, baseEnd_4226870] using wordTrace_append hprefix tailTrace_4226870
  have hstable : (prefixWord ++ tailWord_4226870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226870).length < 2 ^ (prefixWord ++ tailWord_4226870).sum := by decide
  have hdescent : baseEnd_4226870 < baseStart_4226870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226876 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_4226876 : Nat := 118140960795 + 4226876 * 2 ^ 59
def prefixEnd_4226876 : Nat := 4983230072969 + 3 ^ 40 * 4226876 * 2
def baseEnd_4226876 : Nat := 723473018317969853970319

theorem tailTrace_4226876 : CollatzResearch.WordTrace tailWord_4226876 prefixEnd_4226876 723473018317969853970319 := by
  unfold tailWord_4226876
  simp only [CollatzResearch.WordTrace]
  refine ⟨77083416517378809896538241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102777888689838413195384321 77083416517378809896538241)
  ·
    refine ⟨57812562388034107422403681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77083416517378809896538241 57812562388034107422403681)
    ·
      refine ⟨43359421791025580566802761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57812562388034107422403681 43359421791025580566802761)
      ·
        refine ⟨32519566343269185425102071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43359421791025580566802761 32519566343269185425102071)
        ·
          refine ⟨48779349514903778137653107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32519566343269185425102071 48779349514903778137653107)
          ·
            refine ⟨73169024272355667206479661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48779349514903778137653107 73169024272355667206479661)
            ·
              refine ⟨27438384102133375202429873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73169024272355667206479661 27438384102133375202429873)
              ·
                refine ⟨20578788076600031401822405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27438384102133375202429873 20578788076600031401822405)
                ·
                  refine ⟨3858522764362505887841701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20578788076600031401822405 3858522764362505887841701)
                  ·
                    refine ⟨723473018317969853970319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858522764362505887841701 723473018317969853970319)
                    ·
                      rfl

theorem cell23_4226876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_4226876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226876 prefixEnd_4226876 := by exact prefixLift 4226876
  have htrace : WordTrace (prefixWord ++ tailWord_4226876) baseStart_4226876 baseEnd_4226876 := by
    simpa [prefixWord, tailWord_4226876, baseEnd_4226876] using wordTrace_append hprefix tailTrace_4226876
  have hstable : (prefixWord ++ tailWord_4226876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226876).length < 2 ^ (prefixWord ++ tailWord_4226876).sum := by decide
  have hdescent : baseEnd_4226876 < baseStart_4226876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226877 : List Nat := [1, 4, 1, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_4226877 : Nat := 118140960795 + 4226877 * 2 ^ 59
def prefixEnd_4226877 : Nat := 4983230072969 + 3 ^ 40 * 4226877 * 2
def baseEnd_4226877 : Nat := 2170419568434564057998453

theorem tailTrace_4226877 : CollatzResearch.WordTrace tailWord_4226877 prefixEnd_4226877 2170419568434564057998453 := by
  unfold tailWord_4226877
  simp only [CollatzResearch.WordTrace]
  refine ⟨154166869507753996963862885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102777913005169331309241923 154166869507753996963862885)
  ·
    refine ⟨28906288032703874430724291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154166869507753996963862885 28906288032703874430724291)
    ·
      refine ⟨43359432049055811646086437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28906288032703874430724291 43359432049055811646086437)
      ·
        refine ⟨8129893509197964683641207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43359432049055811646086437 8129893509197964683641207)
        ·
          refine ⟨12194840263796947025461811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8129893509197964683641207 12194840263796947025461811)
          ·
            refine ⟨18292260395695420538192717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12194840263796947025461811 18292260395695420538192717)
            ·
              refine ⟨6859597648385782701822269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18292260395695420538192717 6859597648385782701822269)
              ·
                refine ⟨2572349118144668513183351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6859597648385782701822269 2572349118144668513183351)
                ·
                  refine ⟨3858523677217002769775027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572349118144668513183351 3858523677217002769775027)
                  ·
                    refine ⟨5787785515825504154662541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3858523677217002769775027 5787785515825504154662541)
                    ·
                      refine ⟨2170419568434564057998453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5787785515825504154662541 2170419568434564057998453)
                      ·
                        rfl

theorem cell23_4226877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_4226877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226877 prefixEnd_4226877 := by exact prefixLift 4226877
  have htrace : WordTrace (prefixWord ++ tailWord_4226877) baseStart_4226877 baseEnd_4226877 := by
    simpa [prefixWord, tailWord_4226877, baseEnd_4226877] using wordTrace_append hprefix tailTrace_4226877
  have hstable : (prefixWord ++ tailWord_4226877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226877).length < 2 ^ (prefixWord ++ tailWord_4226877).sum := by decide
  have hdescent : baseEnd_4226877 < baseStart_4226877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226933 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4226933 : Nat := 118140960795 + 4226933 * 2 ^ 59
def prefixEnd_4226933 : Nat := 4983230072969 + 3 ^ 40 * 4226933 * 2
def baseEnd_4226933 : Nat := 2170448323351215838898195

theorem tailTrace_4226933 : CollatzResearch.WordTrace tailWord_4226933 prefixEnd_4226933 2170448323351215838898195 := by
  unfold tailWord_4226933
  simp only [CollatzResearch.WordTrace]
  refine ⟨154168911995551118527901453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102779274663700745685267635 154168911995551118527901453)
  ·
    refine ⟨57813341998331669447963045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154168911995551118527901453 57813341998331669447963045)
    ·
      refine ⟨10840001624687188021493071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57813341998331669447963045 10840001624687188021493071)
      ·
        refine ⟨16260002437030782032239607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10840001624687188021493071 16260002437030782032239607)
        ·
          refine ⟨24390003655546173048359411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16260002437030782032239607 24390003655546173048359411)
          ·
            refine ⟨36585005483319259572539117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24390003655546173048359411 36585005483319259572539117)
            ·
              refine ⟨13719377056244722339702169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36585005483319259572539117 13719377056244722339702169)
              ·
                refine ⟨10289532792183541754776627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13719377056244722339702169 10289532792183541754776627)
                ·
                  refine ⟨15434299188275312632164941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10289532792183541754776627 15434299188275312632164941)
                  ·
                    refine ⟨5787862195603242237061853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15434299188275312632164941 5787862195603242237061853)
                    ·
                      refine ⟨2170448323351215838898195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5787862195603242237061853 2170448323351215838898195)
                      ·
                        rfl

theorem cell23_4226933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4226933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226933 prefixEnd_4226933 := by exact prefixLift 4226933
  have htrace : WordTrace (prefixWord ++ tailWord_4226933) baseStart_4226933 baseEnd_4226933 := by
    simpa [prefixWord, tailWord_4226933, baseEnd_4226933] using wordTrace_append hprefix tailTrace_4226933
  have hstable : (prefixWord ++ tailWord_4226933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226933).length < 2 ^ (prefixWord ++ tailWord_4226933).sum := by decide
  have hdescent : baseEnd_4226933 < baseStart_4226933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226951 : List Nat := [1, 1, 4, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_4226951 : Nat := 118140960795 + 4226951 * 2 ^ 59
def prefixEnd_4226951 : Nat := 4983230072969 + 3 ^ 40 * 4226951 * 2
def baseEnd_4226951 : Nat := 2170457566002996768473113

theorem tailTrace_4226951 : CollatzResearch.WordTrace tailWord_4226951 prefixEnd_4226951 2170457566002996768473113 := by
  unfold tailWord_4226951
  simp only [CollatzResearch.WordTrace]
  refine ⟨154169568509485907602056707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102779712339657271734704471 154169568509485907602056707)
  ·
    refine ⟨231254352764228861403085061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154169568509485907602056707 231254352764228861403085061)
    ·
      refine ⟨43360191143292911513078449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231254352764228861403085061 43360191143292911513078449)
      ·
        refine ⟨32520143357469683634808837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43360191143292911513078449 32520143357469683634808837)
        ·
          refine ⟨6097526879525565681526657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32520143357469683634808837 6097526879525565681526657)
          ·
            refine ⟨4573145159644174261144993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6097526879525565681526657 4573145159644174261144993)
            ·
              refine ⟨3429858869733130695858745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4573145159644174261144993 3429858869733130695858745)
              ·
                refine ⟨2572394152299848021894059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3429858869733130695858745 2572394152299848021894059)
                ·
                  refine ⟨3858591228449772032841089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572394152299848021894059 3858591228449772032841089)
                  ·
                    refine ⟨2893943421337329024630817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3858591228449772032841089 2893943421337329024630817)
                    ·
                      refine ⟨2170457566002996768473113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2893943421337329024630817 2170457566002996768473113)
                      ·
                        rfl

theorem cell23_4226951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_4226951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226951 prefixEnd_4226951 := by exact prefixLift 4226951
  have htrace : WordTrace (prefixWord ++ tailWord_4226951) baseStart_4226951 baseEnd_4226951 := by
    simpa [prefixWord, tailWord_4226951, baseEnd_4226951] using wordTrace_append hprefix tailTrace_4226951
  have hstable : (prefixWord ++ tailWord_4226951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226951).length < 2 ^ (prefixWord ++ tailWord_4226951).sum := by decide
  have hdescent : baseEnd_4226951 < baseStart_4226951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4226976 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3]
def baseStart_4226976 : Nat := 118140960795 + 4226976 * 2 ^ 59
def prefixEnd_4226976 : Nat := 4983230072969 + 3 ^ 40 * 4226976 * 2
def baseEnd_4226976 : Nat := 2170470403019359170660497

theorem tailTrace_4226976 : CollatzResearch.WordTrace tailWord_4226976 prefixEnd_4226976 2170470403019359170660497 := by
  unfold tailWord_4226976
  simp only [CollatzResearch.WordTrace]
  refine ⟨77085240167197668435858391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102780320222930224581144521 77085240167197668435858391)
  ·
    refine ⟨115627860250796502653787587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77085240167197668435858391 115627860250796502653787587)
    ·
      refine ⟨173441790376194753980681381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115627860250796502653787587 173441790376194753980681381)
      ·
        refine ⟨32520335695536516371377759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173441790376194753980681381 32520335695536516371377759)
        ·
          refine ⟨48780503543304774557066639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32520335695536516371377759 48780503543304774557066639)
          ·
            refine ⟨73170755314957161835599959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48780503543304774557066639 73170755314957161835599959)
            ·
              refine ⟨109756132972435742753399939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73170755314957161835599959 109756132972435742753399939)
              ·
                refine ⟨164634199458653614130099909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109756132972435742753399939 164634199458653614130099909)
                ·
                  refine ⟨30868912398497552649393733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164634199458653614130099909 30868912398497552649393733)
                  ·
                    refine ⟨5787921074718291121761325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30868912398497552649393733 5787921074718291121761325)
                    ·
                      refine ⟨2170470403019359170660497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5787921074718291121761325 2170470403019359170660497)
                      ·
                        rfl

theorem cell23_4226976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_4226976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4226976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4226976 prefixEnd_4226976 := by exact prefixLift 4226976
  have htrace : WordTrace (prefixWord ++ tailWord_4226976) baseStart_4226976 baseEnd_4226976 := by
    simpa [prefixWord, tailWord_4226976, baseEnd_4226976] using wordTrace_append hprefix tailTrace_4226976
  have hstable : (prefixWord ++ tailWord_4226976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4226976).length < 2 ^ (prefixWord ++ tailWord_4226976).sum := by decide
  have hdescent : baseEnd_4226976 < baseStart_4226976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4226976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227047 : List Nat := [1, 1, 5, 2, 3, 2, 1, 3, 5]
def baseStart_4227047 : Nat := 118140960795 + 4227047 * 2 ^ 59
def prefixEnd_4227047 : Nat := 4983230072969 + 3 ^ 40 * 4227047 * 2
def baseEnd_4227047 : Nat := 241167428905092043652519

theorem tailTrace_4227047 : CollatzResearch.WordTrace tailWord_4227047 prefixEnd_4227047 241167428905092043652519 := by
  unfold tailWord_4227047
  simp only [CollatzResearch.WordTrace]
  refine ⟨154173069917138115997551395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102782046611425410665034263 154173069917138115997551395)
  ·
    refine ⟨231259604875707173996327093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154173069917138115997551395 231259604875707173996327093)
    ·
      refine ⟨21680587957097547562155665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 231259604875707173996327093 21680587957097547562155665)
      ·
        refine ⟨16260440967823160671616749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21680587957097547562155665 16260440967823160671616749)
        ·
          refine ⟨6097665362933685251856281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16260440967823160671616749 6097665362933685251856281)
          ·
            refine ⟨4573249022200263938892211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6097665362933685251856281 4573249022200263938892211)
            ·
              refine ⟨6859873533300395908338317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4573249022200263938892211 6859873533300395908338317)
              ·
                refine ⟨2572452574987648465626869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6859873533300395908338317 2572452574987648465626869)
                ·
                  refine ⟨241167428905092043652519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572452574987648465626869 241167428905092043652519)
                  ·
                    rfl

theorem cell23_4227047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 5].length) (baseStart_4227047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227047 prefixEnd_4227047 := by exact prefixLift 4227047
  have htrace : WordTrace (prefixWord ++ tailWord_4227047) baseStart_4227047 baseEnd_4227047 := by
    simpa [prefixWord, tailWord_4227047, baseEnd_4227047] using wordTrace_append hprefix tailTrace_4227047
  have hstable : (prefixWord ++ tailWord_4227047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227047).length < 2 ^ (prefixWord ++ tailWord_4227047).sum := by decide
  have hdescent : baseEnd_4227047 < baseStart_4227047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227070 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4227070 : Nat := 118140960795 + 4227070 * 2 ^ 59
def prefixEnd_4227070 : Nat := 4983230072969 + 3 ^ 40 * 4227070 * 2
def baseEnd_4227070 : Nat := 2170518670200881802885065

theorem tailTrace_4227070 : CollatzResearch.WordTrace tailWord_4227070 prefixEnd_4227070 2170518670200881802885065 := by
  unfold tailWord_4227070
  simp only [CollatzResearch.WordTrace]
  refine ⟨19271738599506848865704833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102782605864036527283759109 19271738599506848865704833)
  ·
    refine ⟨14453803949630136649278625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19271738599506848865704833 14453803949630136649278625)
    ·
      refine ⟨10840352962222602486958969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14453803949630136649278625 10840352962222602486958969)
      ·
        refine ⟨8130264721666951865219227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10840352962222602486958969 8130264721666951865219227)
        ·
          refine ⟨12195397082500427797828841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8130264721666951865219227 12195397082500427797828841)
          ·
            refine ⟨9146547811875320848371631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12195397082500427797828841 9146547811875320848371631)
            ·
              refine ⟨13719821717812981272557447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9146547811875320848371631 13719821717812981272557447)
              ·
                refine ⟨20579732576719471908836171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13719821717812981272557447 20579732576719471908836171)
                ·
                  refine ⟨30869598865079207863254257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20579732576719471908836171 30869598865079207863254257)
                  ·
                    refine ⟨23152199148809405897440693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30869598865079207863254257 23152199148809405897440693)
                    ·
                      refine ⟨2170518670200881802885065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23152199148809405897440693 2170518670200881802885065)
                      ·
                        rfl

theorem cell23_4227070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4227070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227070 prefixEnd_4227070 := by exact prefixLift 4227070
  have htrace : WordTrace (prefixWord ++ tailWord_4227070) baseStart_4227070 baseEnd_4227070 := by
    simpa [prefixWord, tailWord_4227070, baseEnd_4227070] using wordTrace_append hprefix tailTrace_4227070
  have hstable : (prefixWord ++ tailWord_4227070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227070).length < 2 ^ (prefixWord ++ tailWord_4227070).sum := by decide
  have hdescent : baseEnd_4227070 < baseStart_4227070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227083 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 3]
def baseStart_4227083 : Nat := 118140960795 + 4227083 * 2 ^ 59
def prefixEnd_4227083 : Nat := 4983230072969 + 3 ^ 40 * 4227083 * 2
def baseEnd_4227083 : Nat := 2170525345449390252022505

theorem tailTrace_4227083 : CollatzResearch.WordTrace tailWord_4227083 prefixEnd_4227083 2170525345449390252022505 := by
  unfold tailWord_4227083
  simp only [CollatzResearch.WordTrace]
  refine ⟨154174382945007694145861903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102782921963338462763907935 154174382945007694145861903)
  ·
    refine ⟨231261574417511541218792855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154174382945007694145861903 231261574417511541218792855)
    ·
      refine ⟨346892361626267311828189283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231261574417511541218792855 346892361626267311828189283)
      ·
        refine ⟨520338542439400967742283925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346892361626267311828189283 520338542439400967742283925)
        ·
          refine ⟨24390869176846920362919559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 520338542439400967742283925 24390869176846920362919559)
          ·
            refine ⟨36586303765270380544379339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24390869176846920362919559 36586303765270380544379339)
            ·
              refine ⟨54879455647905570816569009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36586303765270380544379339 54879455647905570816569009)
              ·
                refine ⟨41159591735929178112426757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54879455647905570816569009 41159591735929178112426757)
                ·
                  refine ⟨7717423450486720896080017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41159591735929178112426757 7717423450486720896080017)
                  ·
                    refine ⟨5788067587865040672060013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7717423450486720896080017 5788067587865040672060013)
                    ·
                      refine ⟨2170525345449390252022505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788067587865040672060013 2170525345449390252022505)
                      ·
                        rfl

theorem cell23_4227083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 3].length) (baseStart_4227083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227083 prefixEnd_4227083 := by exact prefixLift 4227083
  have htrace : WordTrace (prefixWord ++ tailWord_4227083) baseStart_4227083 baseEnd_4227083 := by
    simpa [prefixWord, tailWord_4227083, baseEnd_4227083] using wordTrace_append hprefix tailTrace_4227083
  have hstable : (prefixWord ++ tailWord_4227083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227083).length < 2 ^ (prefixWord ++ tailWord_4227083).sum := by decide
  have hdescent : baseEnd_4227083 < baseStart_4227083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227100 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_4227100 : Nat := 118140960795 + 4227100 * 2 ^ 59
def prefixEnd_4227100 : Nat := 4983230072969 + 3 ^ 40 * 4227100 * 2
def baseEnd_4227100 : Nat := 2170534074620516685509927

theorem tailTrace_4227100 : CollatzResearch.WordTrace tailWord_4227100 prefixEnd_4227100 2170534074620516685509927 := by
  unfold tailWord_4227100
  simp only [CollatzResearch.WordTrace]
  refine ⟨77087501492973053024615377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102783335323964070699487169 77087501492973053024615377)
  ·
    refine ⟨57815626119729789768461533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77087501492973053024615377 57815626119729789768461533)
    ·
      refine ⟨21680859794898671163173075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57815626119729789768461533 21680859794898671163173075)
      ·
        refine ⟨32521289692348006744759613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21680859794898671163173075 32521289692348006744759613)
        ·
          refine ⟨12195483634630502529284855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32521289692348006744759613 12195483634630502529284855)
          ·
            refine ⟨18293225451945753793927283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12195483634630502529284855 18293225451945753793927283)
            ·
              refine ⟨27439838177918630690890925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18293225451945753793927283 27439838177918630690890925)
              ·
                refine ⟨10289939316719486509084097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27439838177918630690890925 10289939316719486509084097)
                ·
                  refine ⟨7717454487539614881813073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10289939316719486509084097 7717454487539614881813073)
                  ·
                    refine ⟨5788090865654711161359805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7717454487539614881813073 5788090865654711161359805)
                    ·
                      refine ⟨2170534074620516685509927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788090865654711161359805 2170534074620516685509927)
                      ·
                        rfl

theorem cell23_4227100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_4227100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227100 prefixEnd_4227100 := by exact prefixLift 4227100
  have htrace : WordTrace (prefixWord ++ tailWord_4227100) baseStart_4227100 baseEnd_4227100 := by
    simpa [prefixWord, tailWord_4227100, baseEnd_4227100] using wordTrace_append hprefix tailTrace_4227100
  have hstable : (prefixWord ++ tailWord_4227100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227100).length < 2 ^ (prefixWord ++ tailWord_4227100).sum := by decide
  have hdescent : baseEnd_4227100 < baseStart_4227100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227130 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_4227130 : Nat := 118140960795 + 4227130 * 2 ^ 59
def prefixEnd_4227130 : Nat := 4983230072969 + 3 ^ 40 * 4227130 * 2
def baseEnd_4227130 : Nat := 2170549479040151568134789

theorem tailTrace_4227130 : CollatzResearch.WordTrace tailWord_4227130 prefixEnd_4227130 2170549479040151568134789 := by
  unfold tailWord_4227130
  simp only [CollatzResearch.WordTrace]
  refine ⟨38544024293959355293205711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102784064783891614115215229 38544024293959355293205711)
  ·
    refine ⟨57816036440939032939808567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38544024293959355293205711 57816036440939032939808567)
    ·
      refine ⟨86724054661408549409712851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57816036440939032939808567 86724054661408549409712851)
      ·
        refine ⟨130086081992112824114569277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86724054661408549409712851 130086081992112824114569277)
        ·
          refine ⟨48782280747042309042963479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130086081992112824114569277 48782280747042309042963479)
          ·
            refine ⟨73173421120563463564445219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48782280747042309042963479 73173421120563463564445219)
            ·
              refine ⟨109760131680845195346667829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73173421120563463564445219 109760131680845195346667829)
              ·
                refine ⟨10290012345079237063750109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109760131680845195346667829 10290012345079237063750109)
                ·
                  refine ⟨3858754629404713898906291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10290012345079237063750109 3858754629404713898906291)
                  ·
                    refine ⟨5788131944107070848359437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3858754629404713898906291 5788131944107070848359437)
                    ·
                      refine ⟨2170549479040151568134789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788131944107070848359437 2170549479040151568134789)
                      ·
                        rfl

theorem cell23_4227130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_4227130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227130 prefixEnd_4227130 := by exact prefixLift 4227130
  have htrace : WordTrace (prefixWord ++ tailWord_4227130) baseStart_4227130 baseEnd_4227130 := by
    simpa [prefixWord, tailWord_4227130, baseEnd_4227130] using wordTrace_append hprefix tailTrace_4227130
  have hstable : (prefixWord ++ tailWord_4227130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227130).length < 2 ^ (prefixWord ++ tailWord_4227130).sum := by decide
  have hdescent : baseEnd_4227130 < baseStart_4227130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227133 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_4227133 : Nat := 118140960795 + 4227133 * 2 ^ 59
def prefixEnd_4227133 : Nat := 4983230072969 + 3 ^ 40 * 4227133 * 2
def baseEnd_4227133 : Nat := 723517006494038352132425

theorem tailTrace_4227133 : CollatzResearch.WordTrace tailWord_4227133 prefixEnd_4227133 723517006494038352132425 := by
  unfold tailWord_4227133
  simp only [CollatzResearch.WordTrace]
  refine ⟨154176206594826552685182053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102784137729884368456788035 154176206594826552685182053)
  ·
    refine ⟨28908038736529978628471635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154176206594826552685182053 28908038736529978628471635)
    ·
      refine ⟨43362058104794967942707453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28908038736529978628471635 43362058104794967942707453)
      ·
        refine ⟨16260771789298112978515295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43362058104794967942707453 16260771789298112978515295)
        ·
          refine ⟨24391157683947169467772943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16260771789298112978515295 24391157683947169467772943)
          ·
            refine ⟨36586736525920754201659415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24391157683947169467772943 36586736525920754201659415)
            ·
              refine ⟨54880104788881131302489123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36586736525920754201659415 54880104788881131302489123)
              ·
                refine ⟨82320157183321696953733685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54880104788881131302489123 82320157183321696953733685)
                ·
                  refine ⟨7717514735936409089412533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82320157183321696953733685 7717514735936409089412533)
                  ·
                    refine ⟨723517006494038352132425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7717514735936409089412533 723517006494038352132425)
                    ·
                      rfl

theorem cell23_4227133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_4227133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227133 prefixEnd_4227133 := by exact prefixLift 4227133
  have htrace : WordTrace (prefixWord ++ tailWord_4227133) baseStart_4227133 baseEnd_4227133 := by
    simpa [prefixWord, tailWord_4227133, baseEnd_4227133] using wordTrace_append hprefix tailTrace_4227133
  have hstable : (prefixWord ++ tailWord_4227133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227133).length < 2 ^ (prefixWord ++ tailWord_4227133).sum := by decide
  have hdescent : baseEnd_4227133 < baseStart_4227133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227157 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_4227157 : Nat := 118140960795 + 4227157 * 2 ^ 59
def prefixEnd_4227157 : Nat := 4983230072969 + 3 ^ 40 * 4227157 * 2
def baseEnd_4227157 : Nat := 2170563343017822962497165

theorem tailTrace_4227157 : CollatzResearch.WordTrace tailWord_4227157 prefixEnd_4227157 2170563343017822962497165 := by
  unfold tailWord_4227157
  simp only [CollatzResearch.WordTrace]
  refine ⟨154177081946739604784055725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102784721297826403189370483 154177081946739604784055725)
  ·
    refine ⟨57816405730027351794020897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154177081946739604784055725 57816405730027351794020897)
    ·
      refine ⟨43362304297520513845515673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57816405730027351794020897 43362304297520513845515673)
      ·
        refine ⟨32521728223140385384136755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43362304297520513845515673 32521728223140385384136755)
        ·
          refine ⟨48782592334710578076205133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32521728223140385384136755 48782592334710578076205133)
          ·
            refine ⟨18293472125516466778576925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48782592334710578076205133 18293472125516466778576925)
            ·
              refine ⟨6860052047068675041966347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18293472125516466778576925 6860052047068675041966347)
              ·
                refine ⟨10290078070603012562949521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6860052047068675041966347 10290078070603012562949521)
                ·
                  refine ⟨7717558552952259422212141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10290078070603012562949521 7717558552952259422212141)
                  ·
                    refine ⟨2894084457357097283329553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7717558552952259422212141 2894084457357097283329553)
                    ·
                      refine ⟨2170563343017822962497165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894084457357097283329553 2170563343017822962497165)
                      ·
                        rfl

theorem cell23_4227157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_4227157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227157 prefixEnd_4227157 := by exact prefixLift 4227157
  have htrace : WordTrace (prefixWord ++ tailWord_4227157) baseStart_4227157 baseEnd_4227157 := by
    simpa [prefixWord, tailWord_4227157, baseEnd_4227157] using wordTrace_append hprefix tailTrace_4227157
  have hstable : (prefixWord ++ tailWord_4227157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227157).length < 2 ^ (prefixWord ++ tailWord_4227157).sum := by decide
  have hdescent : baseEnd_4227157 < baseStart_4227157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227164 : List Nat := [2, 2, 4, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_4227164 : Nat := 118140960795 + 4227164 * 2 ^ 59
def prefixEnd_4227164 : Nat := 4983230072969 + 3 ^ 40 * 4227164 * 2
def baseEnd_4227164 : Nat := 2170566937382404435109633

theorem tailTrace_4227164 : CollatzResearch.WordTrace tailWord_4227164 prefixEnd_4227164 2170566937382404435109633 := by
  unfold tailWord_4227164
  simp only [CollatzResearch.WordTrace]
  refine ⟨77088668628857122489780273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102784891505142829986373697 77088668628857122489780273)
  ·
    refine ⟨57816501471642841867335205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77088668628857122489780273 57816501471642841867335205)
    ·
      refine ⟨10840594025933032850125351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57816501471642841867335205 10840594025933032850125351)
      ·
        refine ⟨16260891038899549275188027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10840594025933032850125351 16260891038899549275188027)
        ·
          refine ⟨24391336558349323912782041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16260891038899549275188027 24391336558349323912782041)
          ·
            refine ⟨18293502418761992934586531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24391336558349323912782041 18293502418761992934586531)
            ·
              refine ⟨27440253628142989401879797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18293502418761992934586531 27440253628142989401879797)
              ·
                refine ⟨2572523777638405256426231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27440253628142989401879797 2572523777638405256426231)
                ·
                  refine ⟨3858785666457607884639347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572523777638405256426231 3858785666457607884639347)
                  ·
                    refine ⟨5788178499686411826959021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3858785666457607884639347 5788178499686411826959021)
                    ·
                      refine ⟨2170566937382404435109633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788178499686411826959021 2170566937382404435109633)
                      ·
                        rfl

theorem cell23_4227164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_4227164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227164 prefixEnd_4227164 := by exact prefixLift 4227164
  have htrace : WordTrace (prefixWord ++ tailWord_4227164) baseStart_4227164 baseEnd_4227164 := by
    simpa [prefixWord, tailWord_4227164, baseEnd_4227164] using wordTrace_append hprefix tailTrace_4227164
  have hstable : (prefixWord ++ tailWord_4227164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227164).length < 2 ^ (prefixWord ++ tailWord_4227164).sum := by decide
  have hdescent : baseEnd_4227164 < baseStart_4227164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227180 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_4227180 : Nat := 118140960795 + 4227180 * 2 ^ 59
def prefixEnd_4227180 : Nat := 4983230072969 + 3 ^ 40 * 4227180 * 2
def baseEnd_4227180 : Nat := 723525051024292124169853

theorem tailTrace_4227180 : CollatzResearch.WordTrace tailWord_4227180 prefixEnd_4227180 723525051024292124169853 := by
  unfold tailWord_4227180
  simp only [CollatzResearch.WordTrace]
  refine ⟨77088960412828139856071497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102785280550437519808095329 77088960412828139856071497)
  ·
    refine ⟨57816720309621104892053623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77088960412828139856071497 57816720309621104892053623)
    ·
      refine ⟨86725080464431657338080435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57816720309621104892053623 86725080464431657338080435)
      ·
        refine ⟨130087620696647486007120653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86725080464431657338080435 130087620696647486007120653)
        ·
          refine ⟨48782857761242807252670245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130087620696647486007120653 48782857761242807252670245)
          ·
            refine ⟨9146785830233026359875671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48782857761242807252670245 9146785830233026359875671)
            ·
              refine ⟨13720178745349539539813507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9146785830233026359875671 13720178745349539539813507)
              ·
                refine ⟨20580268118024309309720261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13720178745349539539813507 20580268118024309309720261)
                ·
                  refine ⟨3858800272129557995572549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20580268118024309309720261 3858800272129557995572549)
                  ·
                    refine ⟨723525051024292124169853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858800272129557995572549 723525051024292124169853)
                    ·
                      rfl

theorem cell23_4227180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_4227180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227180 prefixEnd_4227180 := by exact prefixLift 4227180
  have htrace : WordTrace (prefixWord ++ tailWord_4227180) baseStart_4227180 baseEnd_4227180 := by
    simpa [prefixWord, tailWord_4227180, baseEnd_4227180] using wordTrace_append hprefix tailTrace_4227180
  have hstable : (prefixWord ++ tailWord_4227180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227180).length < 2 ^ (prefixWord ++ tailWord_4227180).sum := by decide
  have hdescent : baseEnd_4227180 < baseStart_4227180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227190 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4227190 : Nat := 118140960795 + 4227190 * 2 ^ 59
def prefixEnd_4227190 : Nat := 4983230072969 + 3 ^ 40 * 4227190 * 2
def baseEnd_4227190 : Nat := 2170580287879421333384513

theorem tailTrace_4227190 : CollatzResearch.WordTrace tailWord_4227190 prefixEnd_4227190 2170580287879421333384513 := by
  unfold tailWord_4227190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636142847226253213750439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102785523703746700946671349 9636142847226253213750439)
  ·
    refine ⟨14454214270839379820625659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9636142847226253213750439 14454214270839379820625659)
    ·
      refine ⟨21681321406259069730938489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14454214270839379820625659 21681321406259069730938489)
      ·
        refine ⟨16260991054694302298203867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21681321406259069730938489 16260991054694302298203867)
        ·
          refine ⟨24391486582041453447305801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16260991054694302298203867 24391486582041453447305801)
          ·
            refine ⟨18293614936531090085479351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24391486582041453447305801 18293614936531090085479351)
            ·
              refine ⟨27440422404796635128219027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18293614936531090085479351 27440422404796635128219027)
              ·
                refine ⟨41160633607194952692328541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27440422404796635128219027 41160633607194952692328541)
                ·
                  refine ⟨15435237602698107259623203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41160633607194952692328541 15435237602698107259623203)
                  ·
                    refine ⟨23152856404047160889434805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15435237602698107259623203 23152856404047160889434805)
                    ·
                      refine ⟨2170580287879421333384513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23152856404047160889434805 2170580287879421333384513)
                      ·
                        rfl

theorem cell23_4227190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4227190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227190 prefixEnd_4227190 := by exact prefixLift 4227190
  have htrace : WordTrace (prefixWord ++ tailWord_4227190) baseStart_4227190 baseEnd_4227190 := by
    simpa [prefixWord, tailWord_4227190, baseEnd_4227190] using wordTrace_append hprefix tailTrace_4227190
  have hstable : (prefixWord ++ tailWord_4227190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227190).length < 2 ^ (prefixWord ++ tailWord_4227190).sum := by decide
  have hdescent : baseEnd_4227190 < baseStart_4227190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227210 : List Nat := [3, 1, 2, 3, 1, 2, 4, 7]
def baseStart_4227210 : Nat := 118140960795 + 4227210 * 2 ^ 59
def prefixEnd_4227210 : Nat := 4983230072969 + 3 ^ 40 * 4227210 * 2
def baseEnd_4227210 : Nat := 80392242870093009449423

theorem tailTrace_4227210 : CollatzResearch.WordTrace tailWord_4227210 prefixEnd_4227210 80392242870093009449423 := by
  unfold tailWord_4227210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38544753753886898708933771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102786010010365063223823389 38544753753886898708933771)
  ·
    refine ⟨57817130630830348063400657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38544753753886898708933771 57817130630830348063400657)
    ·
      refine ⟨43362847973122761047550493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57817130630830348063400657 43362847973122761047550493)
      ·
        refine ⟨16261067989921035392831435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43362847973122761047550493 16261067989921035392831435)
        ·
          refine ⟨24391601984881553089247153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16261067989921035392831435 24391601984881553089247153)
          ·
            refine ⟨18293701488661164816935365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24391601984881553089247153 18293701488661164816935365)
            ·
              refine ⟨3430069029123968403175381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18293701488661164816935365 3430069029123968403175381)
              ·
                refine ⟨80392242870093009449423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3430069029123968403175381 80392242870093009449423)
                ·
                  rfl

theorem cell23_4227210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_4227210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227210 prefixEnd_4227210 := by exact prefixLift 4227210
  have htrace : WordTrace (prefixWord ++ tailWord_4227210) baseStart_4227210 baseEnd_4227210 := by
    simpa [prefixWord, tailWord_4227210, baseEnd_4227210] using wordTrace_append hprefix tailTrace_4227210
  have hstable : (prefixWord ++ tailWord_4227210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227210).length < 2 ^ (prefixWord ++ tailWord_4227210).sum := by decide
  have hdescent : baseEnd_4227210 < baseStart_4227210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227237 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_4227237 : Nat := 118140960795 + 4227237 * 2 ^ 59
def prefixEnd_4227237 : Nat := 4983230072969 + 3 ^ 40 * 4227237 * 2
def baseEnd_4227237 : Nat := 2170604421470182649496797

theorem tailTrace_4227237 : CollatzResearch.WordTrace tailWord_4227237 prefixEnd_4227237 2170604421470182649496797 := by
  unfold tailWord_4227237
  simp only [CollatzResearch.WordTrace]
  refine ⟨154179999786449778446967965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102786666524299852297978643 154179999786449778446967965)
  ·
    refine ⟨57817499919918666917612987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154179999786449778446967965 57817499919918666917612987)
    ·
      refine ⟨86726249879878000376419481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57817499919918666917612987 86726249879878000376419481)
      ·
        refine ⟨65044687409908500282314611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86726249879878000376419481 65044687409908500282314611)
        ·
          refine ⟨97567031114862750423471917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65044687409908500282314611 97567031114862750423471917)
          ·
            refine ⟨36587636668073531408801969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97567031114862750423471917 36587636668073531408801969)
            ·
              refine ⟨27440727501055148556601477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36587636668073531408801969 27440727501055148556601477)
              ·
                refine ⟨5145136406447840354362777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27440727501055148556601477 5145136406447840354362777)
                ·
                  refine ⟨3858852304835880265772083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5145136406447840354362777 3858852304835880265772083)
                  ·
                    refine ⟨5788278457253820398658125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3858852304835880265772083 5788278457253820398658125)
                    ·
                      refine ⟨2170604421470182649496797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788278457253820398658125 2170604421470182649496797)
                      ·
                        rfl

theorem cell23_4227237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_4227237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227237 prefixEnd_4227237 := by exact prefixLift 4227237
  have htrace : WordTrace (prefixWord ++ tailWord_4227237) baseStart_4227237 baseEnd_4227237 := by
    simpa [prefixWord, tailWord_4227237, baseEnd_4227237] using wordTrace_append hprefix tailTrace_4227237
  have hstable : (prefixWord ++ tailWord_4227237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227237).length < 2 ^ (prefixWord ++ tailWord_4227237).sum := by decide
  have hdescent : baseEnd_4227237 < baseStart_4227237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227264 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 1, 3, 2]
def baseStart_4227264 : Nat := 118140960795 + 4227264 * 2 ^ 59
def prefixEnd_4227264 : Nat := 4983230072969 + 3 ^ 40 * 4227264 * 2
def baseEnd_4227264 : Nat := 2170618285447854043859173

theorem tailTrace_4227264 : CollatzResearch.WordTrace tailWord_4227264 prefixEnd_4227264 2170618285447854043859173 := by
  unfold tailWord_4227264
  simp only [CollatzResearch.WordTrace]
  refine ⟨77090492278675981029100423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102787323038234641372133897 77090492278675981029100423)
  ·
    refine ⟨115635738418013971543650635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77090492278675981029100423 115635738418013971543650635)
    ·
      refine ⟨173453607627020957315475953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115635738418013971543650635 173453607627020957315475953)
      ·
        refine ⟨130090205720265717986606965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173453607627020957315475953 130090205720265717986606965)
        ·
          refine ⟨12195956786274911061244403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130090205720265717986606965 12195956786274911061244403)
          ·
            refine ⟨18293935179412366591866605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12195956786274911061244403 18293935179412366591866605)
            ·
              refine ⟨6860225692279637471949977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18293935179412366591866605 6860225692279637471949977)
              ·
                refine ⟨5145169269209728103962483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6860225692279637471949977 5145169269209728103962483)
                ·
                  refine ⟨7717753903814592155943725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5145169269209728103962483 7717753903814592155943725)
                  ·
                    refine ⟨2894157713930472058478897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7717753903814592155943725 2894157713930472058478897)
                    ·
                      refine ⟨2170618285447854043859173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894157713930472058478897 2170618285447854043859173)
                      ·
                        rfl

theorem cell23_4227264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_4227264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227264 prefixEnd_4227264 := by exact prefixLift 4227264
  have htrace : WordTrace (prefixWord ++ tailWord_4227264) baseStart_4227264 baseEnd_4227264 := by
    simpa [prefixWord, tailWord_4227264, baseEnd_4227264] using wordTrace_append hprefix tailTrace_4227264
  have hstable : (prefixWord ++ tailWord_4227264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227264).length < 2 ^ (prefixWord ++ tailWord_4227264).sum := by decide
  have hdescent : baseEnd_4227264 < baseStart_4227264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227273 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_4227273 : Nat := 118140960795 + 4227273 * 2 ^ 59
def prefixEnd_4227273 : Nat := 4983230072969 + 3 ^ 40 * 4227273 * 2
def baseEnd_4227273 : Nat := 2170622906773744508646631

theorem tailTrace_4227273 : CollatzResearch.WordTrace tailWord_4227273 prefixEnd_4227273 2170622906773744508646631 := by
  unfold tailWord_4227273
  simp only [CollatzResearch.WordTrace]
  refine ⟨154181312814319356595278473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102787541876212904396852315 154181312814319356595278473)
  ·
    refine ⟨115635984610739517446458855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154181312814319356595278473 115635984610739517446458855)
    ·
      refine ⟨173453976916109276169688283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115635984610739517446458855 173453976916109276169688283)
      ·
        refine ⟨260180965374163914254532425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173453976916109276169688283 260180965374163914254532425)
        ·
          refine ⟨195135724030622935690899319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260180965374163914254532425 195135724030622935690899319)
          ·
            refine ⟨292703586045934403536348979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195135724030622935690899319 292703586045934403536348979)
            ·
              refine ⟨439055379068901605304523469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292703586045934403536348979 439055379068901605304523469)
              ·
                refine ⟨164645767150838101989196301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439055379068901605304523469 164645767150838101989196301)
                ·
                  refine ⟨61742162681564288245948613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164645767150838101989196301 61742162681564288245948613)
                  ·
                    refine ⟨11576655502793304046115365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61742162681564288245948613 11576655502793304046115365)
                    ·
                      refine ⟨2170622906773744508646631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11576655502793304046115365 2170622906773744508646631)
                      ·
                        rfl

theorem cell23_4227273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_4227273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227273 prefixEnd_4227273 := by exact prefixLift 4227273
  have htrace : WordTrace (prefixWord ++ tailWord_4227273) baseStart_4227273 baseEnd_4227273 := by
    simpa [prefixWord, tailWord_4227273, baseEnd_4227273] using wordTrace_append hprefix tailTrace_4227273
  have hstable : (prefixWord ++ tailWord_4227273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227273).length < 2 ^ (prefixWord ++ tailWord_4227273).sum := by decide
  have hdescent : baseEnd_4227273 < baseStart_4227273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227323 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5]
def baseStart_4227323 : Nat := 118140960795 + 4227323 * 2 ^ 59
def prefixEnd_4227323 : Nat := 4983230072969 + 3 ^ 40 * 4227323 * 2
def baseEnd_4227323 : Nat := 2170648580806469313021401

theorem tailTrace_4227323 : CollatzResearch.WordTrace tailWord_4227323 prefixEnd_4227323 2170648580806469313021401 := by
  unfold tailWord_4227323
  simp only [CollatzResearch.WordTrace]
  refine ⟨154183136464138215134598623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102788757642758810089732415 154183136464138215134598623)
  ·
    refine ⟨231274704696207322701897935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154183136464138215134598623 231274704696207322701897935)
    ·
      refine ⟨346912057044310984052846903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231274704696207322701897935 346912057044310984052846903)
      ·
        refine ⟨520368085566466476079270355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346912057044310984052846903 520368085566466476079270355)
        ·
          refine ⟨780552128349699714118905533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520368085566466476079270355 780552128349699714118905533)
          ·
            refine ⟨292707048131137392794589575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 780552128349699714118905533 292707048131137392794589575)
            ·
              refine ⟨439060572196706089191884363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292707048131137392794589575 439060572196706089191884363)
              ·
                refine ⟨658590858295059133787826545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439060572196706089191884363 658590858295059133787826545)
                ·
                  refine ⟨493943143721294350340869909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 658590858295059133787826545 493943143721294350340869909)
                  ·
                    refine ⟨23153584861935672672228277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 493943143721294350340869909 23153584861935672672228277)
                    ·
                      refine ⟨2170648580806469313021401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23153584861935672672228277 2170648580806469313021401)
                      ·
                        rfl

theorem cell23_4227323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_4227323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227323 prefixEnd_4227323 := by exact prefixLift 4227323
  have htrace : WordTrace (prefixWord ++ tailWord_4227323) baseStart_4227323 baseEnd_4227323 := by
    simpa [prefixWord, tailWord_4227323, baseEnd_4227323] using wordTrace_append hprefix tailTrace_4227323
  have hstable : (prefixWord ++ tailWord_4227323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227323).length < 2 ^ (prefixWord ++ tailWord_4227323).sum := by decide
  have hdescent : baseEnd_4227323 < baseStart_4227323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
