import V185TrunkScan23Chunk0008

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_52570 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_52570 : Nat := 118140960795 + 52570 * 2 ^ 59
def prefixEnd_52570 : Nat := 4983230072969 + 3 ^ 40 * 52570 * 2
def baseEnd_52570 : Nat := 26993678006964553333241

theorem tailTrace_52570 : CollatzResearch.WordTrace tailWord_52570 prefixEnd_52570 26993678006964553333241 := by
  unfold tailWord_52570
  simp only [CollatzResearch.WordTrace]
  refine ⟨479346354888835771578791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1278256946370228724210109 479346354888835771578791)
  ·
    refine ⟨719019532333253657368187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 479346354888835771578791 719019532333253657368187)
    ·
      refine ⟨1078529298499880486052281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 719019532333253657368187 1078529298499880486052281)
      ·
        refine ⟨808896973874910364539211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1078529298499880486052281 808896973874910364539211)
        ·
          refine ⟨1213345460812365546808817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808896973874910364539211 1213345460812365546808817)
          ·
            refine ⟨910009095609274160106613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213345460812365546808817 910009095609274160106613)
            ·
              refine ⟨85313352713369452509995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 910009095609274160106613 85313352713369452509995)
              ·
                refine ⟨127970029070054178764993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85313352713369452509995 127970029070054178764993)
                ·
                  refine ⟨95977521802540634073745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127970029070054178764993 95977521802540634073745)
                  ·
                    refine ⟨71983141351905475555309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95977521802540634073745 71983141351905475555309)
                    ·
                      refine ⟨26993678006964553333241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 71983141351905475555309 26993678006964553333241)
                      ·
                        rfl

theorem cell23_52570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_52570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52570 prefixEnd_52570 := by exact prefixLift 52570
  have htrace : WordTrace (prefixWord ++ tailWord_52570) baseStart_52570 baseEnd_52570 := by
    simpa [prefixWord, tailWord_52570, baseEnd_52570] using wordTrace_append hprefix tailTrace_52570
  have hstable : (prefixWord ++ tailWord_52570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52570).length < 2 ^ (prefixWord ++ tailWord_52570).sum := by decide
  have hdescent : baseEnd_52570 < baseStart_52570 := by decide
  rcases family_descends (prefixWord ++ tailWord_52570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52620 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_52620 : Nat := 118140960795 + 52620 * 2 ^ 59
def prefixEnd_52620 : Nat := 4983230072969 + 3 ^ 40 * 52620 * 2
def baseEnd_52620 : Nat := 9006450679896452569337

theorem tailTrace_52620 : CollatzResearch.WordTrace tailWord_52620 prefixEnd_52620 9006450679896452569337 := by
  unfold tailWord_52620
  simp only [CollatzResearch.WordTrace]
  refine ⟨959604534687100812817657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1279472712916134417090209 959604534687100812817657)
  ·
    refine ⟨719703401015325609613243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 959604534687100812817657 719703401015325609613243)
    ·
      refine ⟨1079555101522988414419865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 719703401015325609613243 1079555101522988414419865)
      ·
        refine ⟨809666326142241310814899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1079555101522988414419865 809666326142241310814899)
        ·
          refine ⟨1214499489213361966222349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809666326142241310814899 1214499489213361966222349)
          ·
            refine ⟨455437308455010737333381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1214499489213361966222349 455437308455010737333381)
            ·
              refine ⟨85394495335314513250009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 455437308455010737333381 85394495335314513250009)
              ·
                refine ⟨64045871501485884937507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85394495335314513250009 64045871501485884937507)
                ·
                  refine ⟨96068807252228827406261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64045871501485884937507 96068807252228827406261)
                  ·
                    refine ⟨9006450679896452569337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96068807252228827406261 9006450679896452569337)
                    ·
                      rfl

theorem cell23_52620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_52620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52620 prefixEnd_52620 := by exact prefixLift 52620
  have htrace : WordTrace (prefixWord ++ tailWord_52620) baseStart_52620 baseEnd_52620 := by
    simpa [prefixWord, tailWord_52620, baseEnd_52620] using wordTrace_append hprefix tailTrace_52620
  have hstable : (prefixWord ++ tailWord_52620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52620).length < 2 ^ (prefixWord ++ tailWord_52620).sum := by decide
  have hdescent : baseEnd_52620 < baseStart_52620 := by decide
  rcases family_descends (prefixWord ++ tailWord_52620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52640 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4]
def baseStart_52640 : Nat := 118140960795 + 52640 * 2 ^ 59
def prefixEnd_52640 : Nat := 4983230072969 + 3 ^ 40 * 52640 * 2
def baseEnd_52640 : Nat := 27029621652779279457919

theorem tailTrace_52640 : CollatzResearch.WordTrace tailWord_52640 prefixEnd_52640 27029621652779279457919 := by
  unfold tailWord_52640
  simp only [CollatzResearch.WordTrace]
  refine ⟨959969264650872520681687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1279959019534496694242249 959969264650872520681687)
  ·
    refine ⟨1439953896976308781022531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959969264650872520681687 1439953896976308781022531)
    ·
      refine ⟨2159930845464463171533797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439953896976308781022531 2159930845464463171533797)
      ·
        refine ⟨404987033524586844662587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2159930845464463171533797 404987033524586844662587)
        ·
          refine ⟨607480550286880266993881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404987033524586844662587 607480550286880266993881)
          ·
            refine ⟨455610412715160200245411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607480550286880266993881 455610412715160200245411)
            ·
              refine ⟨683415619072740300368117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455610412715160200245411 683415619072740300368117)
              ·
                refine ⟨64070214288069403159511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 683415619072740300368117 64070214288069403159511)
                ·
                  refine ⟨96105321432104104739267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64070214288069403159511 96105321432104104739267)
                  ·
                    refine ⟨144157982148156157108901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96105321432104104739267 144157982148156157108901)
                    ·
                      refine ⟨27029621652779279457919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 144157982148156157108901 27029621652779279457919)
                      ·
                        rfl

theorem cell23_52640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_52640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52640 prefixEnd_52640 := by exact prefixLift 52640
  have htrace : WordTrace (prefixWord ++ tailWord_52640) baseStart_52640 baseEnd_52640 := by
    simpa [prefixWord, tailWord_52640, baseEnd_52640] using wordTrace_append hprefix tailTrace_52640
  have hstable : (prefixWord ++ tailWord_52640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52640).length < 2 ^ (prefixWord ++ tailWord_52640).sum := by decide
  have hdescent : baseEnd_52640 < baseStart_52640 := by decide
  rcases family_descends (prefixWord ++ tailWord_52640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52663 : List Nat := [1, 1, 3, 1, 3, 2, 4, 8]
def baseStart_52663 : Nat := 118140960795 + 52663 * 2 ^ 59
def prefixEnd_52663 : Nat := 4983230072969 + 3 ^ 40 * 52663 * 2
def baseEnd_52663 : Nat := 1001534507697507017419

theorem tailTrace_52663 : CollatzResearch.WordTrace tailWord_52663 prefixEnd_52663 1001534507697507017419 := by
  unfold tailWord_52663
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920777408218419969450643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1280518272145613312967095 1920777408218419969450643)
  ·
    refine ⟨2881166112327629954175965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1920777408218419969450643 2881166112327629954175965)
    ·
      refine ⟨1080437292122861232815987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2881166112327629954175965 1080437292122861232815987)
      ·
        refine ⟨1620655938184291849223981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080437292122861232815987 1620655938184291849223981)
        ·
          refine ⟨607745976819109443458993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1620655938184291849223981 607745976819109443458993)
          ·
            refine ⟨455809482614332082594245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607745976819109443458993 455809482614332082594245)
            ·
              refine ⟨85464277990187265486421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 455809482614332082594245 85464277990187265486421)
              ·
                refine ⟨1001534507697507017419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 85464277990187265486421 1001534507697507017419)
                ·
                  rfl

theorem cell23_52663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 8].length) (baseStart_52663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52663 prefixEnd_52663 := by exact prefixLift 52663
  have htrace : WordTrace (prefixWord ++ tailWord_52663) baseStart_52663 baseEnd_52663 := by
    simpa [prefixWord, tailWord_52663, baseEnd_52663] using wordTrace_append hprefix tailTrace_52663
  have hstable : (prefixWord ++ tailWord_52663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52663).length < 2 ^ (prefixWord ++ tailWord_52663).sum := by decide
  have hdescent : baseEnd_52663 < baseStart_52663 := by decide
  rcases family_descends (prefixWord ++ tailWord_52663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52670 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_52670 : Nat := 118140960795 + 52670 * 2 ^ 59
def prefixEnd_52670 : Nat := 4983230072969 + 3 ^ 40 * 52670 * 2
def baseEnd_52670 : Nat := 27045026072414162082781

theorem tailTrace_52670 : CollatzResearch.WordTrace tailWord_52670 prefixEnd_52670 27045026072414162082781 := by
  unfold tailWord_52670
  simp only [CollatzResearch.WordTrace]
  refine ⟨240129089899132520619433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1280688479462040109970309 240129089899132520619433)
  ·
    refine ⟨180096817424349390464575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240129089899132520619433 180096817424349390464575)
    ·
      refine ⟨270145226136524085696863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180096817424349390464575 270145226136524085696863)
      ·
        refine ⟨405217839204786128545295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270145226136524085696863 405217839204786128545295)
        ·
          refine ⟨607826758807179192817943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405217839204786128545295 607826758807179192817943)
          ·
            refine ⟨911740138210768789226915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607826758807179192817943 911740138210768789226915)
            ·
              refine ⟨1367610207316153183840373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911740138210768789226915 1367610207316153183840373)
              ·
                refine ⟨128213456935889360985035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367610207316153183840373 128213456935889360985035)
                ·
                  refine ⟨192320185403834041477553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128213456935889360985035 192320185403834041477553)
                  ·
                    refine ⟨144240139052875531108165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 192320185403834041477553 144240139052875531108165)
                    ·
                      refine ⟨27045026072414162082781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 144240139052875531108165 27045026072414162082781)
                      ·
                        rfl

theorem cell23_52670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_52670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52670 prefixEnd_52670 := by exact prefixLift 52670
  have htrace : WordTrace (prefixWord ++ tailWord_52670) baseStart_52670 baseEnd_52670 := by
    simpa [prefixWord, tailWord_52670, baseEnd_52670] using wordTrace_append hprefix tailTrace_52670
  have hstable : (prefixWord ++ tailWord_52670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52670).length < 2 ^ (prefixWord ++ tailWord_52670).sum := by decide
  have hdescent : baseEnd_52670 < baseStart_52670 := by decide
  rcases family_descends (prefixWord ++ tailWord_52670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52694 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_52694 : Nat := 118140960795 + 52694 * 2 ^ 59
def prefixEnd_52694 : Nat := 4983230072969 + 3 ^ 40 * 52694 * 2
def baseEnd_52694 : Nat := 27057349608122068182671

theorem tailTrace_52694 : CollatzResearch.WordTrace tailWord_52694 prefixEnd_52694 27057349608122068182671 := by
  unfold tailWord_52694
  simp only [CollatzResearch.WordTrace]
  refine ⟨120119254444132016489321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1281272047404074842552757 120119254444132016489321)
  ·
    refine ⟨90089440833099012366991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120119254444132016489321 90089440833099012366991)
    ·
      refine ⟨135134161249648518550487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90089440833099012366991 135134161249648518550487)
      ·
        refine ⟨202701241874472777825731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135134161249648518550487 202701241874472777825731)
        ·
          refine ⟨304051862811709166738597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202701241874472777825731 304051862811709166738597)
          ·
            refine ⟨57009724277195468763487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304051862811709166738597 57009724277195468763487)
            ·
              refine ⟨85514586415793203145231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57009724277195468763487 85514586415793203145231)
              ·
                refine ⟨128271879623689804717847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85514586415793203145231 128271879623689804717847)
                ·
                  refine ⟨192407819435534707076771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128271879623689804717847 192407819435534707076771)
                  ·
                    refine ⟨288611729153302060615157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192407819435534707076771 288611729153302060615157)
                    ·
                      refine ⟨27057349608122068182671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 288611729153302060615157 27057349608122068182671)
                      ·
                        rfl

theorem cell23_52694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_52694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52694 prefixEnd_52694 := by exact prefixLift 52694
  have htrace : WordTrace (prefixWord ++ tailWord_52694) baseStart_52694 baseEnd_52694 := by
    simpa [prefixWord, tailWord_52694, baseEnd_52694] using wordTrace_append hprefix tailTrace_52694
  have hstable : (prefixWord ++ tailWord_52694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52694).length < 2 ^ (prefixWord ++ tailWord_52694).sum := by decide
  have hdescent : baseEnd_52694 < baseStart_52694 := by decide
  rcases family_descends (prefixWord ++ tailWord_52694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52742 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_52742 : Nat := 118140960795 + 52742 * 2 ^ 59
def prefixEnd_52742 : Nat := 4983230072969 + 3 ^ 40 * 52742 * 2
def baseEnd_52742 : Nat := 27081996679537880382451

theorem tailTrace_52742 : CollatzResearch.WordTrace tailWord_52742 prefixEnd_52742 27081996679537880382451 := by
  unfold tailWord_52742
  simp only [CollatzResearch.WordTrace]
  refine ⟨60114336716631764424265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1282439183288144307717653 60114336716631764424265)
  ·
    refine ⟨45085752537473823318199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60114336716631764424265 45085752537473823318199)
    ·
      refine ⟨67628628806210734977299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45085752537473823318199 67628628806210734977299)
      ·
        refine ⟨101442943209316102465949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67628628806210734977299 101442943209316102465949)
        ·
          refine ⟨38041103703493538424731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101442943209316102465949 38041103703493538424731)
          ·
            refine ⟨57061655555240307637097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38041103703493538424731 57061655555240307637097)
            ·
              refine ⟨42796241666430230727823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57061655555240307637097 42796241666430230727823)
              ·
                refine ⟨64194362499645346091735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42796241666430230727823 64194362499645346091735)
                ·
                  refine ⟨96291543749468019137603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64194362499645346091735 96291543749468019137603)
                  ·
                    refine ⟨144437315624202028706405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96291543749468019137603 144437315624202028706405)
                    ·
                      refine ⟨27081996679537880382451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 144437315624202028706405 27081996679537880382451)
                      ·
                        rfl

theorem cell23_52742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_52742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52742 prefixEnd_52742 := by exact prefixLift 52742
  have htrace : WordTrace (prefixWord ++ tailWord_52742) baseStart_52742 baseEnd_52742 := by
    simpa [prefixWord, tailWord_52742, baseEnd_52742] using wordTrace_append hprefix tailTrace_52742
  have hstable : (prefixWord ++ tailWord_52742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52742).length < 2 ^ (prefixWord ++ tailWord_52742).sum := by decide
  have hdescent : baseEnd_52742 < baseStart_52742 := by decide
  rcases family_descends (prefixWord ++ tailWord_52742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52753 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 9]
def baseStart_52753 : Nat := 118140960795 + 52753 * 2 ^ 59
def prefixEnd_52753 : Nat := 4983230072969 + 3 ^ 40 * 52753 * 2
def baseEnd_52753 : Nat := 3009738329637481927211

theorem tailTrace_52753 : CollatzResearch.WordTrace tailWord_52753 prefixEnd_52753 3009738329637481927211 := by
  unfold tailWord_52753
  simp only [CollatzResearch.WordTrace]
  refine ⟨1924059977892365340226913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1282706651928243560151275 1924059977892365340226913)
  ·
    refine ⟨1443044983419274005170185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1924059977892365340226913 1443044983419274005170185)
    ·
      refine ⟨1082283737564455503877639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1443044983419274005170185 1082283737564455503877639)
      ·
        refine ⟨1623425606346683255816459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082283737564455503877639 1623425606346683255816459)
        ·
          refine ⟨2435138409520024883724689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623425606346683255816459 2435138409520024883724689)
          ·
            refine ⟨1826353807140018662793517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435138409520024883724689 1826353807140018662793517)
            ·
              refine ⟨684882677677506998547569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1826353807140018662793517 684882677677506998547569)
              ·
                refine ⟨513662008258130248910677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684882677677506998547569 513662008258130248910677)
                ·
                  refine ⟨3009738329637481927211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 513662008258130248910677 3009738329637481927211)
                  ·
                    rfl

theorem cell23_52753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 9].length) (baseStart_52753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52753 prefixEnd_52753 := by exact prefixLift 52753
  have htrace : WordTrace (prefixWord ++ tailWord_52753) baseStart_52753 baseEnd_52753 := by
    simpa [prefixWord, tailWord_52753, baseEnd_52753] using wordTrace_append hprefix tailTrace_52753
  have hstable : (prefixWord ++ tailWord_52753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52753).length < 2 ^ (prefixWord ++ tailWord_52753).sum := by decide
  have hdescent : baseEnd_52753 < baseStart_52753 := by decide
  rcases family_descends (prefixWord ++ tailWord_52753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52764 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_52764 : Nat := 118140960795 + 52764 * 2 ^ 59
def prefixEnd_52764 : Nat := 4983230072969 + 3 ^ 40 * 52764 * 2
def baseEnd_52764 : Nat := 27093293253936794307349

theorem tailTrace_52764 : CollatzResearch.WordTrace tailWord_52764 prefixEnd_52764 27093293253936794307349 := by
  unfold tailWord_52764
  simp only [CollatzResearch.WordTrace]
  refine ⟨962230590426257109438673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1282974120568342812584897 962230590426257109438673)
  ·
    refine ⟨721672942819692832079005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 962230590426257109438673 721672942819692832079005)
    ·
      refine ⟨270627353557384812029627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 721672942819692832079005 270627353557384812029627)
      ·
        refine ⟨405941030336077218044441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270627353557384812029627 405941030336077218044441)
        ·
          refine ⟨304455772752057913533331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405941030336077218044441 304455772752057913533331)
          ·
            refine ⟨456683659128086870299997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304455772752057913533331 456683659128086870299997)
            ·
              refine ⟨171256372173032576362499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456683659128086870299997 171256372173032576362499)
              ·
                refine ⟨256884558259548864543749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171256372173032576362499 256884558259548864543749)
                ·
                  refine ⟨48165854673665412101953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256884558259548864543749 48165854673665412101953)
                  ·
                    refine ⟨36124391005249059076465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48165854673665412101953 36124391005249059076465)
                    ·
                      refine ⟨27093293253936794307349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36124391005249059076465 27093293253936794307349)
                      ·
                        rfl

theorem cell23_52764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_52764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52764 prefixEnd_52764 := by exact prefixLift 52764
  have htrace : WordTrace (prefixWord ++ tailWord_52764) baseStart_52764 baseEnd_52764 := by
    simpa [prefixWord, tailWord_52764, baseEnd_52764] using wordTrace_append hprefix tailTrace_52764
  have hstable : (prefixWord ++ tailWord_52764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52764).length < 2 ^ (prefixWord ++ tailWord_52764).sum := by decide
  have hdescent : baseEnd_52764 < baseStart_52764 := by decide
  rcases family_descends (prefixWord ++ tailWord_52764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52770 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 7]
def baseStart_52770 : Nat := 118140960795 + 52770 * 2 ^ 59
def prefixEnd_52770 : Nat := 4983230072969 + 3 ^ 40 * 52770 * 2
def baseEnd_52770 : Nat := 3010708237540418981369

theorem tailTrace_52770 : CollatzResearch.WordTrace tailWord_52770 prefixEnd_52770 3010708237540418981369 := by
  unfold tailWord_52770
  simp only [CollatzResearch.WordTrace]
  refine ⟨481170004707694310898941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1283120012553851495730509 481170004707694310898941)
  ·
    refine ⟨180438751765385366587103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 481170004707694310898941 180438751765385366587103)
    ·
      refine ⟨270658127648078049880655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180438751765385366587103 270658127648078049880655)
      ·
        refine ⟨405987191472117074820983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270658127648078049880655 405987191472117074820983)
        ·
          refine ⟨608980787208175612231475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405987191472117074820983 608980787208175612231475)
          ·
            refine ⟨913471180812263418347213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608980787208175612231475 913471180812263418347213)
            ·
              refine ⟨342551692804598781880205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 913471180812263418347213 342551692804598781880205)
              ·
                refine ⟨128456884801724543205077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342551692804598781880205 128456884801724543205077)
                ·
                  refine ⟨3010708237540418981369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128456884801724543205077 3010708237540418981369)
                  ·
                    rfl

theorem cell23_52770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_52770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52770 prefixEnd_52770 := by exact prefixLift 52770
  have htrace : WordTrace (prefixWord ++ tailWord_52770) baseStart_52770 baseEnd_52770 := by
    simpa [prefixWord, tailWord_52770, baseEnd_52770] using wordTrace_append hprefix tailTrace_52770
  have hstable : (prefixWord ++ tailWord_52770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52770).length < 2 ^ (prefixWord ++ tailWord_52770).sum := by decide
  have hdescent : baseEnd_52770 < baseStart_52770 := by decide
  rcases family_descends (prefixWord ++ tailWord_52770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52800 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 2, 5]
def baseStart_52800 : Nat := 118140960795 + 52800 * 2 ^ 59
def prefixEnd_52800 : Nat := 4983230072969 + 3 ^ 40 * 52800 * 2
def baseEnd_52800 : Nat := 9037259519166217819061

theorem tailTrace_52800 : CollatzResearch.WordTrace tailWord_52800 prefixEnd_52800 9037259519166217819061 := by
  unfold tailWord_52800
  simp only [CollatzResearch.WordTrace]
  refine ⟨962887104361046183593927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1283849472481394911458569 962887104361046183593927)
  ·
    refine ⟨1444330656541569275390891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962887104361046183593927 1444330656541569275390891)
    ·
      refine ⟨2166495984812353913086337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444330656541569275390891 2166495984812353913086337)
      ·
        refine ⟨1624871988609265434814753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2166495984812353913086337 1624871988609265434814753)
        ·
          refine ⟨1218653991456949076111065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1624871988609265434814753 1218653991456949076111065)
          ·
            refine ⟨913990493592711807083299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218653991456949076111065 913990493592711807083299)
            ·
              refine ⟨1370985740389067710624949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913990493592711807083299 1370985740389067710624949)
              ·
                refine ⟨128529913161475097871089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1370985740389067710624949 128529913161475097871089)
                ·
                  refine ⟨96397434871106323403317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128529913161475097871089 96397434871106323403317)
                  ·
                    refine ⟨9037259519166217819061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96397434871106323403317 9037259519166217819061)
                    ·
                      rfl

theorem cell23_52800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_52800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52800 prefixEnd_52800 := by exact prefixLift 52800
  have htrace : WordTrace (prefixWord ++ tailWord_52800) baseStart_52800 baseEnd_52800 := by
    simpa [prefixWord, tailWord_52800, baseEnd_52800] using wordTrace_append hprefix tailTrace_52800
  have hstable : (prefixWord ++ tailWord_52800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52800).length < 2 ^ (prefixWord ++ tailWord_52800).sum := by decide
  have hdescent : baseEnd_52800 < baseStart_52800 := by decide
  rcases family_descends (prefixWord ++ tailWord_52800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52810 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_52810 : Nat := 118140960795 + 52810 * 2 ^ 59
def prefixEnd_52810 : Nat := 4983230072969 + 3 ^ 40 * 52810 * 2
def baseEnd_52810 : Nat := 27116913364043614332137

theorem tailTrace_52810 : CollatzResearch.WordTrace tailWord_52810 prefixEnd_52810 27116913364043614332137 := by
  unfold tailWord_52810
  simp only [CollatzResearch.WordTrace]
  refine ⟨481534734671466018762971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1284092625790576050034589 481534734671466018762971)
  ·
    refine ⟨722302102007199028144457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481534734671466018762971 722302102007199028144457)
    ·
      refine ⟨541726576505399271108343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722302102007199028144457 541726576505399271108343)
      ·
        refine ⟨812589864758098906662515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541726576505399271108343 812589864758098906662515)
        ·
          refine ⟨1218884797137148359993773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812589864758098906662515 1218884797137148359993773)
          ·
            refine ⟨457081798926430634997665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1218884797137148359993773 457081798926430634997665)
            ·
              refine ⟨342811349194822976248249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457081798926430634997665 342811349194822976248249)
              ·
                refine ⟨257108511896117232186187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342811349194822976248249 257108511896117232186187)
                ·
                  refine ⟨385662767844175848279281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257108511896117232186187 385662767844175848279281)
                  ·
                    refine ⟨289247075883131886209461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385662767844175848279281 289247075883131886209461)
                    ·
                      refine ⟨27116913364043614332137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 289247075883131886209461 27116913364043614332137)
                      ·
                        rfl

theorem cell23_52810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_52810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52810 prefixEnd_52810 := by exact prefixLift 52810
  have htrace : WordTrace (prefixWord ++ tailWord_52810) baseStart_52810 baseEnd_52810 := by
    simpa [prefixWord, tailWord_52810, baseEnd_52810] using wordTrace_append hprefix tailTrace_52810
  have hstable : (prefixWord ++ tailWord_52810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52810).length < 2 ^ (prefixWord ++ tailWord_52810).sum := by decide
  have hdescent : baseEnd_52810 < baseStart_52810 := by decide
  rcases family_descends (prefixWord ++ tailWord_52810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52854 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_52854 : Nat := 118140960795 + 52854 * 2 ^ 59
def prefixEnd_52854 : Nat := 4983230072969 + 3 ^ 40 * 52854 * 2
def baseEnd_52854 : Nat := 27139506512841442181935

theorem tailTrace_52854 : CollatzResearch.WordTrace tailWord_52854 prefixEnd_52854 27139506512841442181935 := by
  unfold tailWord_52854
  simp only [CollatzResearch.WordTrace]
  refine ⟨120483984407903724353351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1285162500350973059769077 120483984407903724353351)
  ·
    refine ⟨180725976611855586530027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120483984407903724353351 180725976611855586530027)
    ·
      refine ⟨271088964917783379795041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180725976611855586530027 271088964917783379795041)
      ·
        refine ⟨203316723688337534846281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271088964917783379795041 203316723688337534846281)
        ·
          refine ⟨152487542766253151134711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203316723688337534846281 152487542766253151134711)
          ·
            refine ⟨228731314149379726702067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152487542766253151134711 228731314149379726702067)
            ·
              refine ⟨343096971224069590053101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228731314149379726702067 343096971224069590053101)
              ·
                refine ⟨128661364209026096269913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343096971224069590053101 128661364209026096269913)
                ·
                  refine ⟨96496023156769572202435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128661364209026096269913 96496023156769572202435)
                  ·
                    refine ⟨144744034735154358303653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96496023156769572202435 144744034735154358303653)
                    ·
                      refine ⟨27139506512841442181935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 144744034735154358303653 27139506512841442181935)
                      ·
                        rfl

theorem cell23_52854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_52854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52854 prefixEnd_52854 := by exact prefixLift 52854
  have htrace : WordTrace (prefixWord ++ tailWord_52854) baseStart_52854 baseEnd_52854 := by
    simpa [prefixWord, tailWord_52854, baseEnd_52854] using wordTrace_append hprefix tailTrace_52854
  have hstable : (prefixWord ++ tailWord_52854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52854).length < 2 ^ (prefixWord ++ tailWord_52854).sum := by decide
  have hdescent : baseEnd_52854 < baseStart_52854 := by decide
  rcases family_descends (prefixWord ++ tailWord_52854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52864 : List Nat := [2, 1, 1, 2, 1, 4, 2, 5, 1, 4]
def baseStart_52864 : Nat := 118140960795 + 52864 * 2 ^ 59
def prefixEnd_52864 : Nat := 4983230072969 + 3 ^ 40 * 52864 * 2
def baseEnd_52864 : Nat := 9048213773128801018963

theorem tailTrace_52864 : CollatzResearch.WordTrace tailWord_52864 prefixEnd_52864 9048213773128801018963 := by
  unfold tailWord_52864
  simp only [CollatzResearch.WordTrace]
  refine ⟨964054240245115648758823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1285405653660154198345097 964054240245115648758823)
  ·
    refine ⟨1446081360367673473138235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964054240245115648758823 1446081360367673473138235)
    ·
      refine ⟨2169122040551510209707353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446081360367673473138235 2169122040551510209707353)
      ·
        refine ⟨1626841530413632657280515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169122040551510209707353 1626841530413632657280515)
        ·
          refine ⟨2440262295620448985920773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626841530413632657280515 2440262295620448985920773)
          ·
            refine ⟨457549180428834184860145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2440262295620448985920773 457549180428834184860145)
            ·
              refine ⟨343161885321625638645109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457549180428834184860145 343161885321625638645109)
              ·
                refine ⟨32171426748902403622979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343161885321625638645109 32171426748902403622979)
                ·
                  refine ⟨48257140123353605434469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32171426748902403622979 48257140123353605434469)
                  ·
                    refine ⟨9048213773128801018963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48257140123353605434469 9048213773128801018963)
                    ·
                      rfl

theorem cell23_52864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 4].length) (baseStart_52864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52864 prefixEnd_52864 := by exact prefixLift 52864
  have htrace : WordTrace (prefixWord ++ tailWord_52864) baseStart_52864 baseEnd_52864 := by
    simpa [prefixWord, tailWord_52864, baseEnd_52864] using wordTrace_append hprefix tailTrace_52864
  have hstable : (prefixWord ++ tailWord_52864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52864).length < 2 ^ (prefixWord ++ tailWord_52864).sum := by decide
  have hdescent : baseEnd_52864 < baseStart_52864 := by decide
  rcases family_descends (prefixWord ++ tailWord_52864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52874 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_52874 : Nat := 118140960795 + 52874 * 2 ^ 59
def prefixEnd_52874 : Nat := 4983230072969 + 3 ^ 40 * 52874 * 2
def baseEnd_52874 : Nat := 27149776125931363931843

theorem tailTrace_52874 : CollatzResearch.WordTrace tailWord_52874 prefixEnd_52874 27149776125931363931843 := by
  unfold tailWord_52874
  simp only [CollatzResearch.WordTrace]
  refine ⟨482118302613500751345419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1285648806969335336921117 482118302613500751345419)
  ·
    refine ⟨723177453920251127018129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 482118302613500751345419 723177453920251127018129)
    ·
      refine ⟨542383090440188345263597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 723177453920251127018129 542383090440188345263597)
      ·
        refine ⟨203393658915070629473849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542383090440188345263597 203393658915070629473849)
        ·
          refine ⟨152545244186302972105387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203393658915070629473849 152545244186302972105387)
          ·
            refine ⟨228817866279454458158081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152545244186302972105387 228817866279454458158081)
            ·
              refine ⟨171613399709590843618561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228817866279454458158081 171613399709590843618561)
              ·
                refine ⟨128710049782193132713921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171613399709590843618561 128710049782193132713921)
                ·
                  refine ⟨96532537336644849535441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128710049782193132713921 96532537336644849535441)
                  ·
                    refine ⟨72399403002483637151581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96532537336644849535441 72399403002483637151581)
                    ·
                      refine ⟨27149776125931363931843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 72399403002483637151581 27149776125931363931843)
                      ·
                        rfl

theorem cell23_52874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_52874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52874 prefixEnd_52874 := by exact prefixLift 52874
  have htrace : WordTrace (prefixWord ++ tailWord_52874) baseStart_52874 baseEnd_52874 := by
    simpa [prefixWord, tailWord_52874, baseEnd_52874] using wordTrace_append hprefix tailTrace_52874
  have hstable : (prefixWord ++ tailWord_52874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52874).length < 2 ^ (prefixWord ++ tailWord_52874).sum := by decide
  have hdescent : baseEnd_52874 < baseStart_52874 := by decide
  rcases family_descends (prefixWord ++ tailWord_52874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52894 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_52894 : Nat := 118140960795 + 52894 * 2 ^ 59
def prefixEnd_52894 : Nat := 4983230072969 + 3 ^ 40 * 52894 * 2
def baseEnd_52894 : Nat := 3017782859891253964639

theorem tailTrace_52894 : CollatzResearch.WordTrace tailWord_52894 prefixEnd_52894 3017782859891253964639 := by
  unfold tailWord_52894
  simp only [CollatzResearch.WordTrace]
  refine ⟨241150333797693302638717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1286135113587697614073157 241150333797693302638717)
  ·
    refine ⟨90431375174134988489519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241150333797693302638717 90431375174134988489519)
    ·
      refine ⟨135647062761202482734279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90431375174134988489519 135647062761202482734279)
      ·
        refine ⟨203470594141803724101419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135647062761202482734279 203470594141803724101419)
        ·
          refine ⟨305205891212705586152129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203470594141803724101419 305205891212705586152129)
          ·
            refine ⟨228904418409529189614097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305205891212705586152129 228904418409529189614097)
            ·
              refine ⟨171678313807146892210573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228904418409529189614097 171678313807146892210573)
              ·
                refine ⟨64379367677680084578965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171678313807146892210573 64379367677680084578965)
                ·
                  refine ⟨3017782859891253964639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64379367677680084578965 3017782859891253964639)
                  ·
                    rfl

theorem cell23_52894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_52894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52894 prefixEnd_52894 := by exact prefixLift 52894
  have htrace : WordTrace (prefixWord ++ tailWord_52894) baseStart_52894 baseEnd_52894 := by
    simpa [prefixWord, tailWord_52894, baseEnd_52894] using wordTrace_append hprefix tailTrace_52894
  have hstable : (prefixWord ++ tailWord_52894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52894).length < 2 ^ (prefixWord ++ tailWord_52894).sum := by decide
  have hdescent : baseEnd_52894 < baseStart_52894 := by decide
  rcases family_descends (prefixWord ++ tailWord_52894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52921 : List Nat := [1, 2, 1, 4, 1, 1, 3, 5, 1, 1, 3]
def baseStart_52921 : Nat := 118140960795 + 52921 * 2 ^ 59
def prefixEnd_52921 : Nat := 4983230072969 + 3 ^ 40 * 52921 * 2
def baseEnd_52921 : Nat := 27173909716692680044127

theorem tailTrace_52921 : CollatzResearch.WordTrace tailWord_52921 prefixEnd_52921 27173909716692680044127 := by
  unfold tailWord_52921
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930187441283730032342617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1286791627522486688228411 1930187441283730032342617)
  ·
    refine ⟨1447640580962797524256963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1930187441283730032342617 1447640580962797524256963)
    ·
      refine ⟨2171460871444196286385445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1447640580962797524256963 2171460871444196286385445)
      ·
        refine ⟨407148913395786803697271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2171460871444196286385445 407148913395786803697271)
        ·
          refine ⟨610723370093680205545907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407148913395786803697271 610723370093680205545907)
          ·
            refine ⟨916085055140520308318861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610723370093680205545907 916085055140520308318861)
            ·
              refine ⟨343531895677695115619573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 916085055140520308318861 343531895677695115619573)
              ·
                refine ⟨32206115219783917089335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343531895677695115619573 32206115219783917089335)
                ·
                  refine ⟨48309172829675875634003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32206115219783917089335 48309172829675875634003)
                  ·
                    refine ⟨72463759244513813451005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48309172829675875634003 72463759244513813451005)
                    ·
                      refine ⟨27173909716692680044127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 72463759244513813451005 27173909716692680044127)
                      ·
                        rfl

theorem cell23_52921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_52921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52921 prefixEnd_52921 := by exact prefixLift 52921
  have htrace : WordTrace (prefixWord ++ tailWord_52921) baseStart_52921 baseEnd_52921 := by
    simpa [prefixWord, tailWord_52921, baseEnd_52921] using wordTrace_append hprefix tailTrace_52921
  have hstable : (prefixWord ++ tailWord_52921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52921).length < 2 ^ (prefixWord ++ tailWord_52921).sum := by decide
  have hdescent : baseEnd_52921 < baseStart_52921 := by decide
  rcases family_descends (prefixWord ++ tailWord_52921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52924 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_52924 : Nat := 118140960795 + 52924 * 2 ^ 59
def prefixEnd_52924 : Nat := 4983230072969 + 3 ^ 40 * 52924 * 2
def baseEnd_52924 : Nat := 9058483386218722768871

theorem tailTrace_52924 : CollatzResearch.WordTrace tailWord_52924 prefixEnd_52924 9058483386218722768871 := by
  unfold tailWord_52924
  simp only [CollatzResearch.WordTrace]
  refine ⟨965148430136430772350913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1286864573515241029801217 965148430136430772350913)
  ·
    refine ⟨723861322602323079263185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 965148430136430772350913 723861322602323079263185)
    ·
      refine ⟨542895991951742309447389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 723861322602323079263185 542895991951742309447389)
      ·
        refine ⟨203585996981903366042771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542895991951742309447389 203585996981903366042771)
        ·
          refine ⟨305378995472855049064157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203585996981903366042771 305378995472855049064157)
          ·
            refine ⟨114517123302320643399059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305378995472855049064157 114517123302320643399059)
            ·
              refine ⟨171775684953480965098589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114517123302320643399059 171775684953480965098589)
              ·
                refine ⟨64415881857555361911971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171775684953480965098589 64415881857555361911971)
                ·
                  refine ⟨96623822786333042867957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64415881857555361911971 96623822786333042867957)
                  ·
                    refine ⟨9058483386218722768871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96623822786333042867957 9058483386218722768871)
                    ·
                      rfl

theorem cell23_52924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_52924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52924 prefixEnd_52924 := by exact prefixLift 52924
  have htrace : WordTrace (prefixWord ++ tailWord_52924) baseStart_52924 baseEnd_52924 := by
    simpa [prefixWord, tailWord_52924, baseEnd_52924] using wordTrace_append hprefix tailTrace_52924
  have hstable : (prefixWord ++ tailWord_52924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52924).length < 2 ^ (prefixWord ++ tailWord_52924).sum := by decide
  have hdescent : baseEnd_52924 < baseStart_52924 := by decide
  rcases family_descends (prefixWord ++ tailWord_52924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52954 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_52954 : Nat := 118140960795 + 52954 * 2 ^ 59
def prefixEnd_52954 : Nat := 4983230072969 + 3 ^ 40 * 52954 * 2
def baseEnd_52954 : Nat := 9063618192763683643825

theorem tailTrace_52954 : CollatzResearch.WordTrace tailWord_52954 prefixEnd_52954 9063618192763683643825 := by
  unfold tailWord_52954
  simp only [CollatzResearch.WordTrace]
  refine ⟨482847762541044167073479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1287594033442784445529277 482847762541044167073479)
  ·
    refine ⟨724271643811566250610219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 482847762541044167073479 724271643811566250610219)
    ·
      refine ⟨1086407465717349375915329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724271643811566250610219 1086407465717349375915329)
      ·
        refine ⟨814805599288012031936497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086407465717349375915329 814805599288012031936497)
        ·
          refine ⟨611104199466009023952373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814805599288012031936497 611104199466009023952373)
          ·
            refine ⟨57291018699938345995535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 611104199466009023952373 57291018699938345995535)
            ·
              refine ⟨85936528049907518993303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57291018699938345995535 85936528049907518993303)
              ·
                refine ⟨128904792074861278489955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85936528049907518993303 128904792074861278489955)
                ·
                  refine ⟨193357188112291917734933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128904792074861278489955 193357188112291917734933)
                  ·
                    refine ⟨9063618192763683643825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 193357188112291917734933 9063618192763683643825)
                    ·
                      rfl

theorem cell23_52954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_52954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52954 prefixEnd_52954 := by exact prefixLift 52954
  have htrace : WordTrace (prefixWord ++ tailWord_52954) baseStart_52954 baseEnd_52954 := by
    simpa [prefixWord, tailWord_52954, baseEnd_52954] using wordTrace_append hprefix tailTrace_52954
  have hstable : (prefixWord ++ tailWord_52954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52954).length < 2 ^ (prefixWord ++ tailWord_52954).sum := by decide
  have hdescent : baseEnd_52954 < baseStart_52954 := by decide
  rcases family_descends (prefixWord ++ tailWord_52954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52961 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_52961 : Nat := 118140960795 + 52961 * 2 ^ 59
def prefixEnd_52961 : Nat := 4983230072969 + 3 ^ 40 * 52961 * 2
def baseEnd_52961 : Nat := 27194448942872523543943

theorem tailTrace_52961 : CollatzResearch.WordTrace tailWord_52961 prefixEnd_52961 27194448942872523543943 := by
  unfold tailWord_52961
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931646361138816863798737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1287764240759211242532491 1931646361138816863798737)
  ·
    refine ⟨1448734770854112647849053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1931646361138816863798737 1448734770854112647849053)
    ·
      refine ⟨543275539070292242943395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1448734770854112647849053 543275539070292242943395)
      ·
        refine ⟨814913308605438364415093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543275539070292242943395 814913308605438364415093)
        ·
          refine ⟨76398122681759846663915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 814913308605438364415093 76398122681759846663915)
          ·
            refine ⟨114597184022639769995873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76398122681759846663915 114597184022639769995873)
            ·
              refine ⟨85947888016979827496905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114597184022639769995873 85947888016979827496905)
              ·
                refine ⟨64460916012734870622679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85947888016979827496905 64460916012734870622679)
                ·
                  refine ⟨96691374019102305934019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64460916012734870622679 96691374019102305934019)
                  ·
                    refine ⟨145037061028653458901029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96691374019102305934019 145037061028653458901029)
                    ·
                      refine ⟨27194448942872523543943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 145037061028653458901029 27194448942872523543943)
                      ·
                        rfl

theorem cell23_52961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_52961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52961 prefixEnd_52961 := by exact prefixLift 52961
  have htrace : WordTrace (prefixWord ++ tailWord_52961) baseStart_52961 baseEnd_52961 := by
    simpa [prefixWord, tailWord_52961, baseEnd_52961] using wordTrace_append hprefix tailTrace_52961
  have hstable : (prefixWord ++ tailWord_52961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52961).length < 2 ^ (prefixWord ++ tailWord_52961).sum := by decide
  have hdescent : baseEnd_52961 < baseStart_52961 := by decide
  rcases family_descends (prefixWord ++ tailWord_52961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53012 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_53012 : Nat := 118140960795 + 53012 * 2 ^ 59
def prefixEnd_53012 : Nat := 4983230072969 + 3 ^ 40 * 53012 * 2
def baseEnd_53012 : Nat := 27220636456251824006209

theorem tailTrace_53012 : CollatzResearch.WordTrace tailWord_53012 prefixEnd_53012 27220636456251824006209 := by
  unfold tailWord_53012
  simp only [CollatzResearch.WordTrace]
  refine ⟨966753241977026286952645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1289004322636035049270193 966753241977026286952645)
  ·
    refine ⟨181266232870692428803621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 966753241977026286952645 181266232870692428803621)
    ·
      refine ⟨33987418663254830400679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181266232870692428803621 33987418663254830400679)
      ·
        refine ⟨50981127994882245601019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33987418663254830400679 50981127994882245601019)
        ·
          refine ⟨76471691992323368401529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50981127994882245601019 76471691992323368401529)
          ·
            refine ⟨57353768994242526301147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76471691992323368401529 57353768994242526301147)
            ·
              refine ⟨86030653491363789451721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57353768994242526301147 86030653491363789451721)
              ·
                refine ⟨64522990118522842088791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86030653491363789451721 64522990118522842088791)
                ·
                  refine ⟨96784485177784263133187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64522990118522842088791 96784485177784263133187)
                  ·
                    refine ⟨145176727766676394699781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96784485177784263133187 145176727766676394699781)
                    ·
                      refine ⟨27220636456251824006209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 145176727766676394699781 27220636456251824006209)
                      ·
                        rfl

theorem cell23_53012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_53012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53012 prefixEnd_53012 := by exact prefixLift 53012
  have htrace : WordTrace (prefixWord ++ tailWord_53012) baseStart_53012 baseEnd_53012 := by
    simpa [prefixWord, tailWord_53012, baseEnd_53012] using wordTrace_append hprefix tailTrace_53012
  have hstable : (prefixWord ++ tailWord_53012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53012).length < 2 ^ (prefixWord ++ tailWord_53012).sum := by decide
  have hdescent : baseEnd_53012 < baseStart_53012 := by decide
  rcases family_descends (prefixWord ++ tailWord_53012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53064 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_53064 : Nat := 118140960795 + 53064 * 2 ^ 59
def prefixEnd_53064 : Nat := 4983230072969 + 3 ^ 40 * 53064 * 2
def baseEnd_53064 : Nat := 27247337450285620555969

theorem tailTrace_53064 : CollatzResearch.WordTrace tailWord_53064 prefixEnd_53064 27247337450285620555969 := by
  unfold tailWord_53064
  simp only [CollatzResearch.WordTrace]
  refine ⟨967701539882832727399123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1290268719843776969865497 967701539882832727399123)
  ·
    refine ⟨1451552309824249091098685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967701539882832727399123 1451552309824249091098685)
    ·
      refine ⟨544332116184093409162007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1451552309824249091098685 544332116184093409162007)
      ·
        refine ⟨816498174276140113743011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544332116184093409162007 816498174276140113743011)
        ·
          refine ⟨1224747261414210170614517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816498174276140113743011 1224747261414210170614517)
          ·
            refine ⟨114820055757582203495111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1224747261414210170614517 114820055757582203495111)
            ·
              refine ⟨172230083636373305242667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114820055757582203495111 172230083636373305242667)
              ·
                refine ⟨258345125454559957864001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172230083636373305242667 258345125454559957864001)
                ·
                  refine ⟨193758844090919968398001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258345125454559957864001 193758844090919968398001)
                  ·
                    refine ⟨145319133068189976298501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193758844090919968398001 145319133068189976298501)
                    ·
                      refine ⟨27247337450285620555969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 145319133068189976298501 27247337450285620555969)
                      ·
                        rfl

theorem cell23_53064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_53064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53064 prefixEnd_53064 := by exact prefixLift 53064
  have htrace : WordTrace (prefixWord ++ tailWord_53064) baseStart_53064 baseEnd_53064 := by
    simpa [prefixWord, tailWord_53064, baseEnd_53064] using wordTrace_append hprefix tailTrace_53064
  have hstable : (prefixWord ++ tailWord_53064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53064).length < 2 ^ (prefixWord ++ tailWord_53064).sum := by decide
  have hdescent : baseEnd_53064 < baseStart_53064 := by decide
  rcases family_descends (prefixWord ++ tailWord_53064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53068 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 1, 4, 2]
def baseStart_53068 : Nat := 118140960795 + 53068 * 2 ^ 59
def prefixEnd_53068 : Nat := 4983230072969 + 3 ^ 40 * 53068 * 2
def baseEnd_53068 : Nat := 27249391372903604905951

theorem tailTrace_53068 : CollatzResearch.WordTrace tailWord_53068 prefixEnd_53068 27249391372903604905951 := by
  unfold tailWord_53068
  simp only [CollatzResearch.WordTrace]
  refine ⟨967774485875587068971929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1290365981167449425295905 967774485875587068971929)
  ·
    refine ⟨725830864406690301728947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 967774485875587068971929 725830864406690301728947)
    ·
      refine ⟨1088746296610035452593421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725830864406690301728947 1088746296610035452593421)
      ·
        refine ⟨408279861228763294722533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1088746296610035452593421 408279861228763294722533)
        ·
          refine ⟨76552473980393117760475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 408279861228763294722533 76552473980393117760475)
          ·
            refine ⟨114828710970589676640713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76552473980393117760475 114828710970589676640713)
            ·
              refine ⟨86121533227942257480535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114828710970589676640713 86121533227942257480535)
              ·
                refine ⟨129182299841913386220803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86121533227942257480535 129182299841913386220803)
                ·
                  refine ⟨193773449762870079331205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129182299841913386220803 193773449762870079331205)
                  ·
                    refine ⟨36332521830538139874601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193773449762870079331205 36332521830538139874601)
                    ·
                      refine ⟨27249391372903604905951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36332521830538139874601 27249391372903604905951)
                      ·
                        rfl

theorem cell23_53068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_53068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53068 prefixEnd_53068 := by exact prefixLift 53068
  have htrace : WordTrace (prefixWord ++ tailWord_53068) baseStart_53068 baseEnd_53068 := by
    simpa [prefixWord, tailWord_53068, baseEnd_53068] using wordTrace_append hprefix tailTrace_53068
  have hstable : (prefixWord ++ tailWord_53068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53068).length < 2 ^ (prefixWord ++ tailWord_53068).sum := by decide
  have hdescent : baseEnd_53068 < baseStart_53068 := by decide
  rcases family_descends (prefixWord ++ tailWord_53068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53074 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 7]
def baseStart_53074 : Nat := 118140960795 + 53074 * 2 ^ 59
def prefixEnd_53074 : Nat := 4983230072969 + 3 ^ 40 * 53074 * 2
def baseEnd_53074 : Nat := 3028052472981175714547

theorem tailTrace_53074 : CollatzResearch.WordTrace tailWord_53074 prefixEnd_53074 3028052472981175714547 := by
  unfold tailWord_53074
  simp only [CollatzResearch.WordTrace]
  refine ⟨483941952432359290665569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1290511873152958108441517 483941952432359290665569)
  ·
    refine ⟨362956464324269467999177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 483941952432359290665569 362956464324269467999177)
    ·
      refine ⟨272217348243202100999383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362956464324269467999177 272217348243202100999383)
      ·
        refine ⟨408326022364803151499075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272217348243202100999383 408326022364803151499075)
        ·
          refine ⟨612489033547204727248613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408326022364803151499075 612489033547204727248613)
          ·
            refine ⟨114841693790100886359115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 612489033547204727248613 114841693790100886359115)
            ·
              refine ⟨172262540685151329538673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114841693790100886359115 172262540685151329538673)
              ·
                refine ⟨129196905513863497154005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172262540685151329538673 129196905513863497154005)
                ·
                  refine ⟨3028052472981175714547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129196905513863497154005 3028052472981175714547)
                  ·
                    rfl

theorem cell23_53074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_53074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53074 prefixEnd_53074 := by exact prefixLift 53074
  have htrace : WordTrace (prefixWord ++ tailWord_53074) baseStart_53074 baseEnd_53074 := by
    simpa [prefixWord, tailWord_53074, baseEnd_53074] using wordTrace_append hprefix tailTrace_53074
  have hstable : (prefixWord ++ tailWord_53074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53074).length < 2 ^ (prefixWord ++ tailWord_53074).sum := by decide
  have hdescent : baseEnd_53074 < baseStart_53074 := by decide
  rcases family_descends (prefixWord ++ tailWord_53074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53097 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_53097 : Nat := 118140960795 + 53097 * 2 ^ 59
def prefixEnd_53097 : Nat := 4983230072969 + 3 ^ 40 * 53097 * 2
def baseEnd_53097 : Nat := 27264282311883991443317

theorem tailTrace_53097 : CollatzResearch.WordTrace tailWord_53097 prefixEnd_53097 27264282311883991443317 := by
  unfold tailWord_53097
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936606688646112090749545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1291071125764074727166363 1936606688646112090749545)
  ·
    refine ⟨1452455016484584068062159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1936606688646112090749545 1452455016484584068062159)
    ·
      refine ⟨2178682524726876102093239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452455016484584068062159 2178682524726876102093239)
      ·
        refine ⟨3268023787090314153139859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178682524726876102093239 3268023787090314153139859)
        ·
          refine ⟨4902035680635471229709789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268023787090314153139859 4902035680635471229709789)
          ·
            refine ⟨1838263380238301711141171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4902035680635471229709789 1838263380238301711141171)
            ·
              refine ⟨2757395070357452566711757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838263380238301711141171 2757395070357452566711757)
              ·
                refine ⟨1034023151384044712516909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2757395070357452566711757 1034023151384044712516909)
                ·
                  refine ⟨387758681769016767193841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034023151384044712516909 387758681769016767193841)
                  ·
                    refine ⟨290819011326762575395381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 387758681769016767193841 290819011326762575395381)
                    ·
                      refine ⟨27264282311883991443317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 290819011326762575395381 27264282311883991443317)
                      ·
                        rfl

theorem cell23_53097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_53097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53097 prefixEnd_53097 := by exact prefixLift 53097
  have htrace : WordTrace (prefixWord ++ tailWord_53097) baseStart_53097 baseEnd_53097 := by
    simpa [prefixWord, tailWord_53097, baseEnd_53097] using wordTrace_append hprefix tailTrace_53097
  have hstable : (prefixWord ++ tailWord_53097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53097).length < 2 ^ (prefixWord ++ tailWord_53097).sum := by decide
  have hdescent : baseEnd_53097 < baseStart_53097 := by decide
  rcases family_descends (prefixWord ++ tailWord_53097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53102 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_53102 : Nat := 118140960795 + 53102 * 2 ^ 59
def prefixEnd_53102 : Nat := 4983230072969 + 3 ^ 40 * 53102 * 2
def baseEnd_53102 : Nat := 27266849715156471880795

theorem tailTrace_53102 : CollatzResearch.WordTrace tailWord_53102 prefixEnd_53102 27266849715156471880795 := by
  unfold tailWord_53102
  simp only [CollatzResearch.WordTrace]
  refine ⟨242098631703499743085195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1291192702418665296454373 242098631703499743085195)
  ·
    refine ⟨363147947555249614627793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242098631703499743085195 363147947555249614627793)
    ·
      refine ⟨272360960666437210970845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363147947555249614627793 272360960666437210970845)
      ·
        refine ⟨102135360249913954114067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272360960666437210970845 102135360249913954114067)
        ·
          refine ⟨153203040374870931171101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102135360249913954114067 153203040374870931171101)
          ·
            refine ⟨57451140140576599189163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153203040374870931171101 57451140140576599189163)
            ·
              refine ⟨86176710210864898783745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57451140140576599189163 86176710210864898783745)
              ·
                refine ⟨64632532658148674087809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86176710210864898783745 64632532658148674087809)
                ·
                  refine ⟨48474399493611505565857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64632532658148674087809 48474399493611505565857)
                  ·
                    refine ⟨36355799620208629174393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48474399493611505565857 36355799620208629174393)
                    ·
                      refine ⟨27266849715156471880795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36355799620208629174393 27266849715156471880795)
                      ·
                        rfl

theorem cell23_53102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_53102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53102 prefixEnd_53102 := by exact prefixLift 53102
  have htrace : WordTrace (prefixWord ++ tailWord_53102) baseStart_53102 baseEnd_53102 := by
    simpa [prefixWord, tailWord_53102, baseEnd_53102] using wordTrace_append hprefix tailTrace_53102
  have hstable : (prefixWord ++ tailWord_53102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53102).length < 2 ^ (prefixWord ++ tailWord_53102).sum := by decide
  have hdescent : baseEnd_53102 < baseStart_53102 := by decide
  rcases family_descends (prefixWord ++ tailWord_53102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53118 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_53118 : Nat := 118140960795 + 53118 * 2 ^ 59
def prefixEnd_53118 : Nat := 4983230072969 + 3 ^ 40 * 53118 * 2
def baseEnd_53118 : Nat := 27275065405628409280721

theorem tailTrace_53118 : CollatzResearch.WordTrace tailWord_53118 prefixEnd_53118 27275065405628409280721 := by
  unfold tailWord_53118
  simp only [CollatzResearch.WordTrace]
  refine ⟨242171577696254084658001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1291581747713355118176005 242171577696254084658001)
  ·
    refine ⟨181628683272190563493501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242171577696254084658001 181628683272190563493501)
    ·
      refine ⟨68110756227071461310063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181628683272190563493501 68110756227071461310063)
      ·
        refine ⟨102166134340607191965095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68110756227071461310063 102166134340607191965095)
        ·
          refine ⟨153249201510910787947643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102166134340607191965095 153249201510910787947643)
          ·
            refine ⟨229873802266366181921465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153249201510910787947643 229873802266366181921465)
            ·
              refine ⟨172405351699774636441099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229873802266366181921465 172405351699774636441099)
              ·
                refine ⟨258608027549661954661649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172405351699774636441099 258608027549661954661649)
                ·
                  refine ⟨193956020662246465996237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258608027549661954661649 193956020662246465996237)
                  ·
                    refine ⟨72733507748342424748589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193956020662246465996237 72733507748342424748589)
                    ·
                      refine ⟨27275065405628409280721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 72733507748342424748589 27275065405628409280721)
                      ·
                        rfl

theorem cell23_53118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_53118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53118 prefixEnd_53118 := by exact prefixLift 53118
  have htrace : WordTrace (prefixWord ++ tailWord_53118) baseStart_53118 baseEnd_53118 := by
    simpa [prefixWord, tailWord_53118, baseEnd_53118] using wordTrace_append hprefix tailTrace_53118
  have hstable : (prefixWord ++ tailWord_53118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53118).length < 2 ^ (prefixWord ++ tailWord_53118).sum := by decide
  have hdescent : baseEnd_53118 < baseStart_53118 := by decide
  rcases family_descends (prefixWord ++ tailWord_53118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53124 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_53124 : Nat := 118140960795 + 53124 * 2 ^ 59
def prefixEnd_53124 : Nat := 4983230072969 + 3 ^ 40 * 53124 * 2
def baseEnd_53124 : Nat := 27278146289555385805693

theorem tailTrace_53124 : CollatzResearch.WordTrace tailWord_53124 prefixEnd_53124 27278146289555385805693 := by
  unfold tailWord_53124
  simp only [CollatzResearch.WordTrace]
  refine ⟨968795729774147850991213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1291727639698863801321617 968795729774147850991213)
  ·
    refine ⟨363298398665305444121705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 968795729774147850991213 363298398665305444121705)
    ·
      refine ⟨272473798998979083091279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363298398665305444121705 272473798998979083091279)
      ·
        refine ⟨408710698498468624636919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272473798998979083091279 408710698498468624636919)
        ·
          refine ⟨613066047747702936955379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408710698498468624636919 613066047747702936955379)
          ·
            refine ⟨919599071621554405433069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613066047747702936955379 919599071621554405433069)
            ·
              refine ⟨344849651858082902037401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919599071621554405433069 344849651858082902037401)
              ·
                refine ⟨258637238893562176528051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344849651858082902037401 258637238893562176528051)
                ·
                  refine ⟨387955858340343264792077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258637238893562176528051 387955858340343264792077)
                  ·
                    refine ⟨145483446877628724297029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387955858340343264792077 145483446877628724297029)
                    ·
                      refine ⟨27278146289555385805693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 145483446877628724297029 27278146289555385805693)
                      ·
                        rfl

theorem cell23_53124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_53124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53124 prefixEnd_53124 := by exact prefixLift 53124
  have htrace : WordTrace (prefixWord ++ tailWord_53124) baseStart_53124 baseEnd_53124 := by
    simpa [prefixWord, tailWord_53124, baseEnd_53124] using wordTrace_append hprefix tailTrace_53124
  have hstable : (prefixWord ++ tailWord_53124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53124).length < 2 ^ (prefixWord ++ tailWord_53124).sum := by decide
  have hdescent : baseEnd_53124 < baseStart_53124 := by decide
  rcases family_descends (prefixWord ++ tailWord_53124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53181 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 6]
def baseStart_53181 : Nat := 118140960795 + 53181 * 2 ^ 59
def prefixEnd_53181 : Nat := 4983230072969 + 3 ^ 40 * 53181 * 2
def baseEnd_53181 : Nat := 3034157187429073643659

theorem tailTrace_53181 : CollatzResearch.WordTrace tailWord_53181 prefixEnd_53181 3034157187429073643659 := by
  unfold tailWord_53181
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939670420341794436807397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1293113613561196291204931 1939670420341794436807397)
  ·
    refine ⟨363688203814086456901387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1939670420341794436807397 363688203814086456901387)
    ·
      refine ⟨545532305721129685352081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363688203814086456901387 545532305721129685352081)
      ·
        refine ⟨409149229290847264014061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545532305721129685352081 409149229290847264014061)
        ·
          refine ⟨153430960984067724005273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409149229290847264014061 153430960984067724005273)
          ·
            refine ⟨115073220738050793003955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153430960984067724005273 115073220738050793003955)
            ·
              refine ⟨172609831107076189505933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115073220738050793003955 172609831107076189505933)
              ·
                refine ⟨64728686665153571064725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172609831107076189505933 64728686665153571064725)
                ·
                  refine ⟨3034157187429073643659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64728686665153571064725 3034157187429073643659)
                  ·
                    rfl

theorem cell23_53181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_53181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53181 prefixEnd_53181 := by exact prefixLift 53181
  have htrace : WordTrace (prefixWord ++ tailWord_53181) baseStart_53181 baseEnd_53181 := by
    simpa [prefixWord, tailWord_53181, baseEnd_53181] using wordTrace_append hprefix tailTrace_53181
  have hstable : (prefixWord ++ tailWord_53181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53181).length < 2 ^ (prefixWord ++ tailWord_53181).sum := by decide
  have hdescent : baseEnd_53181 < baseStart_53181 := by decide
  rcases family_descends (prefixWord ++ tailWord_53181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53191 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_53191 : Nat := 118140960795 + 53191 * 2 ^ 59
def prefixEnd_53191 : Nat := 4983230072969 + 3 ^ 40 * 53191 * 2
def baseEnd_53191 : Nat := 27312549493406623667885

theorem tailTrace_53191 : CollatzResearch.WordTrace tailWord_53191 prefixEnd_53191 27312549493406623667885 := by
  unfold tailWord_53191
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940035150305566144671427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1293356766870377429780951 1940035150305566144671427)
  ·
    refine ⟨2910052725458349217007141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1940035150305566144671427 2910052725458349217007141)
    ·
      refine ⟨545634886023440478188839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2910052725458349217007141 545634886023440478188839)
      ·
        refine ⟨818452329035160717283259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545634886023440478188839 818452329035160717283259)
        ·
          refine ⟨1227678493552741075924889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818452329035160717283259 1227678493552741075924889)
          ·
            refine ⟨920758870164555806943667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1227678493552741075924889 920758870164555806943667)
            ·
              refine ⟨1381138305246833710415501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920758870164555806943667 1381138305246833710415501)
              ·
                refine ⟨517926864467562641405813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381138305246833710415501 517926864467562641405813)
                ·
                  refine ⟨48555643543833997631795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517926864467562641405813 48555643543833997631795)
                  ·
                    refine ⟨72833465315750996447693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48555643543833997631795 72833465315750996447693)
                    ·
                      refine ⟨27312549493406623667885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 72833465315750996447693 27312549493406623667885)
                      ·
                        rfl

theorem cell23_53191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_53191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53191 prefixEnd_53191 := by exact prefixLift 53191
  have htrace : WordTrace (prefixWord ++ tailWord_53191) baseStart_53191 baseEnd_53191 := by
    simpa [prefixWord, tailWord_53191, baseEnd_53191] using wordTrace_append hprefix tailTrace_53191
  have hstable : (prefixWord ++ tailWord_53191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53191).length < 2 ^ (prefixWord ++ tailWord_53191).sum := by decide
  have hdescent : baseEnd_53191 < baseStart_53191 := by decide
  rcases family_descends (prefixWord ++ tailWord_53191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53224 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 5, 6]
def baseStart_53224 : Nat := 118140960795 + 53224 * 2 ^ 59
def prefixEnd_53224 : Nat := 4983230072969 + 3 ^ 40 * 53224 * 2
def baseEnd_53224 : Nat := 9109831451668331518411

theorem tailTrace_53224 : CollatzResearch.WordTrace tailWord_53224 prefixEnd_53224 9109831451668331518411 := by
  unfold tailWord_53224
  simp only [CollatzResearch.WordTrace]
  refine ⟨970619379593006390311363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1294159172790675187081817 970619379593006390311363)
  ·
    refine ⟨1455929069389509585467045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 970619379593006390311363 1455929069389509585467045)
    ·
      refine ⟨272986700510533047275071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1455929069389509585467045 272986700510533047275071)
      ·
        refine ⟨409480050765799570912607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272986700510533047275071 409480050765799570912607)
        ·
          refine ⟨614220076148699356368911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409480050765799570912607 614220076148699356368911)
          ·
            refine ⟨921330114223049034553367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614220076148699356368911 921330114223049034553367)
            ·
              refine ⟨1381995171334573551830051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921330114223049034553367 1381995171334573551830051)
              ·
                refine ⟨2072992757001860327745077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381995171334573551830051 2072992757001860327745077)
                ·
                  refine ⟨194343070968924405726101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2072992757001860327745077 194343070968924405726101)
                  ·
                    refine ⟨9109831451668331518411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194343070968924405726101 9109831451668331518411)
                    ·
                      rfl

theorem cell23_53224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_53224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53224 prefixEnd_53224 := by exact prefixLift 53224
  have htrace : WordTrace (prefixWord ++ tailWord_53224) baseStart_53224 baseEnd_53224 := by
    simpa [prefixWord, tailWord_53224, baseEnd_53224] using wordTrace_append hprefix tailTrace_53224
  have hstable : (prefixWord ++ tailWord_53224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53224).length < 2 ^ (prefixWord ++ tailWord_53224).sum := by decide
  have hdescent : baseEnd_53224 < baseStart_53224 := by decide
  rcases family_descends (prefixWord ++ tailWord_53224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53241 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 1, 6]
def baseStart_53241 : Nat := 118140960795 + 53241 * 2 ^ 59
def prefixEnd_53241 : Nat := 4983230072969 + 3 ^ 40 * 53241 * 2
def baseEnd_53241 : Nat := 9112741175377142680885

theorem tailTrace_53241 : CollatzResearch.WordTrace tailWord_53241 prefixEnd_53241 9112741175377142680885 := by
  unfold tailWord_53241
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941858800124424683991577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1294572533416283122661051 1941858800124424683991577)
  ·
    refine ⟨1456394100093318512993683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1941858800124424683991577 1456394100093318512993683)
    ·
      refine ⟨2184591150139977769490525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456394100093318512993683 2184591150139977769490525)
      ·
        refine ⟨819221681302491663558947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2184591150139977769490525 819221681302491663558947)
        ·
          refine ⟨1228832521953737495338421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819221681302491663558947 1228832521953737495338421)
          ·
            refine ⟨115203048933162890187977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1228832521953737495338421 115203048933162890187977)
            ·
              refine ⟨86402286699872167640983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115203048933162890187977 86402286699872167640983)
              ·
                refine ⟨129603430049808251461475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86402286699872167640983 129603430049808251461475)
                ·
                  refine ⟨194405145074712377192213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129603430049808251461475 194405145074712377192213)
                  ·
                    refine ⟨9112741175377142680885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194405145074712377192213 9112741175377142680885)
                    ·
                      rfl

theorem cell23_53241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_53241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53241 prefixEnd_53241 := by exact prefixLift 53241
  have htrace : WordTrace (prefixWord ++ tailWord_53241) baseStart_53241 baseEnd_53241 := by
    simpa [prefixWord, tailWord_53241, baseEnd_53241] using wordTrace_append hprefix tailTrace_53241
  have hstable : (prefixWord ++ tailWord_53241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53241).length < 2 ^ (prefixWord ++ tailWord_53241).sum := by decide
  have hdescent : baseEnd_53241 < baseStart_53241 := by decide
  rcases family_descends (prefixWord ++ tailWord_53241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53271 : List Nat := [1, 1, 3, 5, 2, 1, 10]
def baseStart_53271 : Nat := 118140960795 + 53271 * 2 ^ 59
def prefixEnd_53271 : Nat := 4983230072969 + 3 ^ 40 * 53271 * 2
def baseEnd_53271 : Nat := 337699110441559390957

theorem tailTrace_53271 : CollatzResearch.WordTrace tailWord_53271 prefixEnd_53271 337699110441559390957 := by
  unfold tailWord_53271
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942952990015739807583667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1295301993343826538389111 1942952990015739807583667)
  ·
    refine ⟨2914429485023609711375501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1942952990015739807583667 2914429485023609711375501)
    ·
      refine ⟨1092911056883853641765813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2914429485023609711375501 1092911056883853641765813)
      ·
        refine ⟨102460411582861278915545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1092911056883853641765813 102460411582861278915545)
        ·
          refine ⟨76845308687145959186659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102460411582861278915545 76845308687145959186659)
          ·
            refine ⟨115267963030718938779989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76845308687145959186659 115267963030718938779989)
            ·
              refine ⟨337699110441559390957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 115267963030718938779989 337699110441559390957)
              ·
                rfl

theorem cell23_53271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 10].length) (baseStart_53271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53271 prefixEnd_53271 := by exact prefixLift 53271
  have htrace : WordTrace (prefixWord ++ tailWord_53271) baseStart_53271 baseEnd_53271 := by
    simpa [prefixWord, tailWord_53271, baseEnd_53271] using wordTrace_append hprefix tailTrace_53271
  have hstable : (prefixWord ++ tailWord_53271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53271).length < 2 ^ (prefixWord ++ tailWord_53271).sum := by decide
  have hdescent : baseEnd_53271 < baseStart_53271 := by decide
  rcases family_descends (prefixWord ++ tailWord_53271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53282 : List Nat := [3, 3, 1, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_53282 : Nat := 118140960795 + 53282 * 2 ^ 59
def prefixEnd_53282 : Nat := 4983230072969 + 3 ^ 40 * 53282 * 2
def baseEnd_53282 : Nat := 27359276232965767629967

theorem tailTrace_53282 : CollatzResearch.WordTrace tailWord_53282 prefixEnd_53282 27359276232965767629967 := by
  unfold tailWord_53282
  simp only [CollatzResearch.WordTrace]
  refine ⟨485838548243972171558525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1295569461983925790822733 485838548243972171558525)
  ·
    refine ⟨182189455591489564334447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 485838548243972171558525 182189455591489564334447)
    ·
      refine ⟨273284183387234346501671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182189455591489564334447 273284183387234346501671)
      ·
        refine ⟨409926275080851519752507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273284183387234346501671 409926275080851519752507)
        ·
          refine ⟨614889412621277279628761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409926275080851519752507 614889412621277279628761)
          ·
            refine ⟨461167059465957959721571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614889412621277279628761 461167059465957959721571)
            ·
              refine ⟨691750589198936939582357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461167059465957959721571 691750589198936939582357)
              ·
                refine ⟨32425808868700169042923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 691750589198936939582357 32425808868700169042923)
                ·
                  refine ⟨48638713303050253564385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32425808868700169042923 48638713303050253564385)
                  ·
                    refine ⟨36479034977287690173289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48638713303050253564385 36479034977287690173289)
                    ·
                      refine ⟨27359276232965767629967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36479034977287690173289 27359276232965767629967)
                      ·
                        rfl

theorem cell23_53282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_53282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53282 prefixEnd_53282 := by exact prefixLift 53282
  have htrace : WordTrace (prefixWord ++ tailWord_53282) baseStart_53282 baseEnd_53282 := by
    simpa [prefixWord, tailWord_53282, baseEnd_53282] using wordTrace_append hprefix tailTrace_53282
  have hstable : (prefixWord ++ tailWord_53282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53282).length < 2 ^ (prefixWord ++ tailWord_53282).sum := by decide
  have hdescent : baseEnd_53282 < baseStart_53282 := by decide
  rcases family_descends (prefixWord ++ tailWord_53282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53291 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 7, 2]
def baseStart_53291 : Nat := 118140960795 + 53291 * 2 ^ 59
def prefixEnd_53291 : Nat := 4983230072969 + 3 ^ 40 * 53291 * 2
def baseEnd_53291 : Nat := 27363897558856232417425

theorem tailTrace_53291 : CollatzResearch.WordTrace tailWord_53291 prefixEnd_53291 27363897558856232417425 := by
  unfold tailWord_53291
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943682449943283223311727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1295788299962188815541151 1943682449943283223311727)
  ·
    refine ⟨2915523674914924834967591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1943682449943283223311727 2915523674914924834967591)
    ·
      refine ⟨4373285512372387252451387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915523674914924834967591 4373285512372387252451387)
      ·
        refine ⟨6559928268558580878677081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373285512372387252451387 6559928268558580878677081)
        ·
          refine ⟨4919946201418935659007811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6559928268558580878677081 4919946201418935659007811)
          ·
            refine ⟨7379919302128403488511717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919946201418935659007811 7379919302128403488511717)
            ·
              refine ⟨1383734869149075654095947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7379919302128403488511717 1383734869149075654095947)
              ·
                refine ⟨2075602303723613481143921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383734869149075654095947 2075602303723613481143921)
                ·
                  refine ⟨1556701727792710110857941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075602303723613481143921 1556701727792710110857941)
                  ·
                    refine ⟨36485196745141643223233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1556701727792710110857941 36485196745141643223233)
                    ·
                      refine ⟨27363897558856232417425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36485196745141643223233 27363897558856232417425)
                      ·
                        rfl

theorem cell23_53291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7, 2].length) (baseStart_53291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53291 prefixEnd_53291 := by exact prefixLift 53291
  have htrace : WordTrace (prefixWord ++ tailWord_53291) baseStart_53291 baseEnd_53291 := by
    simpa [prefixWord, tailWord_53291, baseEnd_53291] using wordTrace_append hprefix tailTrace_53291
  have hstable : (prefixWord ++ tailWord_53291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53291).length < 2 ^ (prefixWord ++ tailWord_53291).sum := by decide
  have hdescent : baseEnd_53291 < baseStart_53291 := by decide
  rcases family_descends (prefixWord ++ tailWord_53291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53298 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_53298 : Nat := 118140960795 + 53298 * 2 ^ 59
def prefixEnd_53298 : Nat := 4983230072969 + 3 ^ 40 * 53298 * 2
def baseEnd_53298 : Nat := 27367491923437705029893

theorem tailTrace_53298 : CollatzResearch.WordTrace tailWord_53298 prefixEnd_53298 27367491923437705029893 := by
  unfold tailWord_53298
  simp only [CollatzResearch.WordTrace]
  refine ⟨485984440229480854704137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1295958507278615612544365 485984440229480854704137)
  ·
    refine ⟨364488330172110641028103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 485984440229480854704137 364488330172110641028103)
    ·
      refine ⟨546732495258165961542155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364488330172110641028103 546732495258165961542155)
      ·
        refine ⟨820098742887248942313233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546732495258165961542155 820098742887248942313233)
        ·
          refine ⟨615074057165436706734925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820098742887248942313233 615074057165436706734925)
          ·
            refine ⟨230652771437038765025597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615074057165436706734925 230652771437038765025597)
            ·
              refine ⟨86494789288889536884599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230652771437038765025597 86494789288889536884599)
              ·
                refine ⟨129742183933334305326899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86494789288889536884599 129742183933334305326899)
                ·
                  refine ⟨194613275900001457990349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129742183933334305326899 194613275900001457990349)
                  ·
                    refine ⟨72979978462500546746381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194613275900001457990349 72979978462500546746381)
                    ·
                      refine ⟨27367491923437705029893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 72979978462500546746381 27367491923437705029893)
                      ·
                        rfl

theorem cell23_53298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_53298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53298 prefixEnd_53298 := by exact prefixLift 53298
  have htrace : WordTrace (prefixWord ++ tailWord_53298) baseStart_53298 baseEnd_53298 := by
    simpa [prefixWord, tailWord_53298, baseEnd_53298] using wordTrace_append hprefix tailTrace_53298
  have hstable : (prefixWord ++ tailWord_53298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53298).length < 2 ^ (prefixWord ++ tailWord_53298).sum := by decide
  have hdescent : baseEnd_53298 < baseStart_53298 := by decide
  rcases family_descends (prefixWord ++ tailWord_53298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53305 : List Nat := [1, 2, 1, 5, 4, 1, 2, 7]
def baseStart_53305 : Nat := 118140960795 + 53305 * 2 ^ 59
def prefixEnd_53305 : Nat := 4983230072969 + 3 ^ 40 * 53305 * 2
def baseEnd_53305 : Nat := 1013743936593302875643

theorem tailTrace_53305 : CollatzResearch.WordTrace tailWord_53305 prefixEnd_53305 1013743936593302875643 := by
  unfold tailWord_53305
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944193071892563614321369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1296128714595042409547579 1944193071892563614321369)
  ·
    refine ⟨1458144803919422710741027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1944193071892563614321369 1458144803919422710741027)
    ·
      refine ⟨2187217205879134066111541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458144803919422710741027 2187217205879134066111541)
      ·
        refine ⟨205051613051168818697957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2187217205879134066111541 205051613051168818697957)
        ·
          refine ⟨38447177447094153505867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205051613051168818697957 38447177447094153505867)
          ·
            refine ⟨57670766170641230258801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38447177447094153505867 57670766170641230258801)
            ·
              refine ⟨43253074627980922694101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57670766170641230258801 43253074627980922694101)
              ·
                refine ⟨1013743936593302875643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43253074627980922694101 1013743936593302875643)
                ·
                  rfl

theorem cell23_53305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 7].length) (baseStart_53305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53305 prefixEnd_53305 := by exact prefixLift 53305
  have htrace : WordTrace (prefixWord ++ tailWord_53305) baseStart_53305 baseEnd_53305 := by
    simpa [prefixWord, tailWord_53305, baseEnd_53305] using wordTrace_append hprefix tailTrace_53305
  have hstable : (prefixWord ++ tailWord_53305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53305).length < 2 ^ (prefixWord ++ tailWord_53305).sum := by decide
  have hdescent : baseEnd_53305 < baseStart_53305 := by decide
  rcases family_descends (prefixWord ++ tailWord_53305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53351 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_53351 : Nat := 118140960795 + 53351 * 2 ^ 59
def prefixEnd_53351 : Nat := 4983230072969 + 3 ^ 40 * 53351 * 2
def baseEnd_53351 : Nat := 27394706398125997667149

theorem tailTrace_53351 : CollatzResearch.WordTrace tailWord_53351 prefixEnd_53351 27394706398125997667149 := by
  unfold tailWord_53351
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945870829725913470495907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1297247219817275646997271 1945870829725913470495907)
  ·
    refine ⟨2918806244588870205743861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1945870829725913470495907 2918806244588870205743861)
    ·
      refine ⟨273638085430206581788487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2918806244588870205743861 273638085430206581788487)
      ·
        refine ⟨410457128145309872682731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273638085430206581788487 410457128145309872682731)
        ·
          refine ⟨615685692217964809024097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410457128145309872682731 615685692217964809024097)
          ·
            refine ⟨461764269163473606768073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615685692217964809024097 461764269163473606768073)
            ·
              refine ⟨346323201872605205076055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461764269163473606768073 346323201872605205076055)
              ·
                refine ⟨519484802808907807614083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346323201872605205076055 519484802808907807614083)
                ·
                  refine ⟨779227204213361711421125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519484802808907807614083 779227204213361711421125)
                  ·
                    refine ⟨146105100790005320891461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 779227204213361711421125 146105100790005320891461)
                    ·
                      refine ⟨27394706398125997667149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 146105100790005320891461 27394706398125997667149)
                      ·
                        rfl

theorem cell23_53351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_53351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53351 prefixEnd_53351 := by exact prefixLift 53351
  have htrace : WordTrace (prefixWord ++ tailWord_53351) baseStart_53351 baseEnd_53351 := by
    simpa [prefixWord, tailWord_53351, baseEnd_53351] using wordTrace_append hprefix tailTrace_53351
  have hstable : (prefixWord ++ tailWord_53351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53351).length < 2 ^ (prefixWord ++ tailWord_53351).sum := by decide
  have hdescent : baseEnd_53351 < baseStart_53351 := by decide
  rcases family_descends (prefixWord ++ tailWord_53351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53371 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 3]
def baseStart_53371 : Nat := 118140960795 + 53371 * 2 ^ 59
def prefixEnd_53371 : Nat := 4983230072969 + 3 ^ 40 * 53371 * 2
def baseEnd_53371 : Nat := 27404976011215919417057

theorem tailTrace_53371 : CollatzResearch.WordTrace tailWord_53371 prefixEnd_53371 27404976011215919417057 := by
  unfold tailWord_53371
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946600289653456886223967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1297733526435637924149311 1946600289653456886223967)
  ·
    refine ⟨2919900434480185329335951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1946600289653456886223967 2919900434480185329335951)
    ·
      refine ⟨4379850651720277994003927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2919900434480185329335951 4379850651720277994003927)
      ·
        refine ⟨6569775977580416991005891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4379850651720277994003927 6569775977580416991005891)
        ·
          refine ⟨9854663966370625486508837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6569775977580416991005891 9854663966370625486508837)
          ·
            refine ⟨1847749493694492278720407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9854663966370625486508837 1847749493694492278720407)
            ·
              refine ⟨2771624240541738418080611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847749493694492278720407 2771624240541738418080611)
              ·
                refine ⟨4157436360812607627120917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771624240541738418080611 4157436360812607627120917)
                ·
                  refine ⟨194879829413090982521293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4157436360812607627120917 194879829413090982521293)
                  ·
                    refine ⟨73079936029909118445485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194879829413090982521293 73079936029909118445485)
                    ·
                      refine ⟨27404976011215919417057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 73079936029909118445485 27404976011215919417057)
                      ·
                        rfl

theorem cell23_53371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 3].length) (baseStart_53371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53371 prefixEnd_53371 := by exact prefixLift 53371
  have htrace : WordTrace (prefixWord ++ tailWord_53371) baseStart_53371 baseEnd_53371 := by
    simpa [prefixWord, tailWord_53371, baseEnd_53371] using wordTrace_append hprefix tailTrace_53371
  have hstable : (prefixWord ++ tailWord_53371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53371).length < 2 ^ (prefixWord ++ tailWord_53371).sum := by decide
  have hdescent : baseEnd_53371 < baseStart_53371 := by decide
  rcases family_descends (prefixWord ++ tailWord_53371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53448 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_53448 : Nat := 118140960795 + 53448 * 2 ^ 59
def prefixEnd_53448 : Nat := 4983230072969 + 3 ^ 40 * 53448 * 2
def baseEnd_53448 : Nat := 27444514021612118154203

theorem tailTrace_53448 : CollatzResearch.WordTrace tailWord_53448 prefixEnd_53448 27444514021612118154203 := by
  unfold tailWord_53448
  simp only [CollatzResearch.WordTrace]
  refine ⟨974704355187249518388499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1299605806916332691184665 974704355187249518388499)
  ·
    refine ⟨1462056532780874277582749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 974704355187249518388499 1462056532780874277582749)
    ·
      refine ⟨548271199792827854093531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1462056532780874277582749 548271199792827854093531)
      ·
        refine ⟨822406799689241781140297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548271199792827854093531 822406799689241781140297)
        ·
          refine ⟨616805099766931335855223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822406799689241781140297 616805099766931335855223)
          ·
            refine ⟨925207649650397003782835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616805099766931335855223 925207649650397003782835)
            ·
              refine ⟨1387811474475595505674253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925207649650397003782835 1387811474475595505674253)
              ·
                refine ⟨520429302928348314627845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1387811474475595505674253 520429302928348314627845)
                ·
                  refine ⟨97580494299065308992721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 520429302928348314627845 97580494299065308992721)
                  ·
                    refine ⟨73185370724298981744541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97580494299065308992721 73185370724298981744541)
                    ·
                      refine ⟨27444514021612118154203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 73185370724298981744541 27444514021612118154203)
                      ·
                        rfl

theorem cell23_53448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_53448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53448 prefixEnd_53448 := by exact prefixLift 53448
  have htrace : WordTrace (prefixWord ++ tailWord_53448) baseStart_53448 baseEnd_53448 := by
    simpa [prefixWord, tailWord_53448, baseEnd_53448] using wordTrace_append hprefix tailTrace_53448
  have hstable : (prefixWord ++ tailWord_53448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53448).length < 2 ^ (prefixWord ++ tailWord_53448).sum := by decide
  have hdescent : baseEnd_53448 < baseStart_53448 := by decide
  rcases family_descends (prefixWord ++ tailWord_53448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53451 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 8]
def baseStart_53451 : Nat := 118140960795 + 53451 * 2 ^ 59
def prefixEnd_53451 : Nat := 4983230072969 + 3 ^ 40 * 53451 * 2
def baseEnd_53451 : Nat := 3049561607063956268521

theorem tailTrace_53451 : CollatzResearch.WordTrace tailWord_53451 prefixEnd_53451 3049561607063956268521 := by
  unfold tailWord_53451
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949518129363630549136207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1299678752909087032757471 1949518129363630549136207)
  ·
    refine ⟨2924277194045445823704311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1949518129363630549136207 2924277194045445823704311)
    ·
      refine ⟨4386415791068168735556467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924277194045445823704311 4386415791068168735556467)
      ·
        refine ⟨6579623686602253103334701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386415791068168735556467 6579623686602253103334701)
        ·
          refine ⟨2467358882475844913750513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6579623686602253103334701 2467358882475844913750513)
          ·
            refine ⟨1850519161856883685312885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467358882475844913750513 1850519161856883685312885)
            ·
              refine ⟨173486171424082845498083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1850519161856883685312885 173486171424082845498083)
              ·
                refine ⟨260229257136124268247125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173486171424082845498083 260229257136124268247125)
                ·
                  refine ⟨3049561607063956268521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 260229257136124268247125 3049561607063956268521)
                  ·
                    rfl

theorem cell23_53451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 8].length) (baseStart_53451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53451 prefixEnd_53451 := by exact prefixLift 53451
  have htrace : WordTrace (prefixWord ++ tailWord_53451) baseStart_53451 baseEnd_53451 := by
    simpa [prefixWord, tailWord_53451, baseEnd_53451] using wordTrace_append hprefix tailTrace_53451
  have hstable : (prefixWord ++ tailWord_53451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53451).length < 2 ^ (prefixWord ++ tailWord_53451).sum := by decide
  have hdescent : baseEnd_53451 < baseStart_53451 := by decide
  rcases family_descends (prefixWord ++ tailWord_53451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53455 : List Nat := [1, 1, 2, 1, 1, 3, 3, 6, 1, 4]
def baseStart_53455 : Nat := 118140960795 + 53455 * 2 ^ 59
def prefixEnd_53455 : Nat := 4983230072969 + 3 ^ 40 * 53455 * 2
def baseEnd_53455 : Nat := 9149369462064530255557

theorem tailTrace_53455 : CollatzResearch.WordTrace tailWord_53455 prefixEnd_53455 9149369462064530255557 := by
  unfold tailWord_53455
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949664021349139232281819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1299776014232759488187879 1949664021349139232281819)
  ·
    refine ⟨2924496032023708848422729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1949664021349139232281819 2924496032023708848422729)
    ·
      refine ⟨2193372024017781636317047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2924496032023708848422729 2193372024017781636317047)
      ·
        refine ⟨3290058036026672454475571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193372024017781636317047 3290058036026672454475571)
        ·
          refine ⟨4935087054040008681713357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290058036026672454475571 4935087054040008681713357)
          ·
            refine ⟨1850657645265003255642509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4935087054040008681713357 1850657645265003255642509)
            ·
              refine ⟨693996616974376220865941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1850657645265003255642509 693996616974376220865941)
              ·
                refine ⟨32531091420673885353091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 693996616974376220865941 32531091420673885353091)
                ·
                  refine ⟨48796637131010828029637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32531091420673885353091 48796637131010828029637)
                  ·
                    refine ⟨9149369462064530255557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48796637131010828029637 9149369462064530255557)
                    ·
                      rfl

theorem cell23_53455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 4].length) (baseStart_53455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53455 prefixEnd_53455 := by exact prefixLift 53455
  have htrace : WordTrace (prefixWord ++ tailWord_53455) baseStart_53455 baseEnd_53455 := by
    simpa [prefixWord, tailWord_53455, baseEnd_53455] using wordTrace_append hprefix tailTrace_53455
  have hstable : (prefixWord ++ tailWord_53455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53455).length < 2 ^ (prefixWord ++ tailWord_53455).sum := by decide
  have hdescent : baseEnd_53455 < baseStart_53455 := by decide
  rcases family_descends (prefixWord ++ tailWord_53455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53471 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_53471 : Nat := 118140960795 + 53471 * 2 ^ 59
def prefixEnd_53471 : Nat := 4983230072969 + 3 ^ 40 * 53471 * 2
def baseEnd_53471 : Nat := 27456324076665528166597

theorem tailTrace_53471 : CollatzResearch.WordTrace tailWord_53471 prefixEnd_53471 27456324076665528166597 := by
  unfold tailWord_53471
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950247589291173964864267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1300165059527449309909511 1950247589291173964864267)
  ·
    refine ⟨2925371383936760947296401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1950247589291173964864267 2925371383936760947296401)
    ·
      refine ⟨2194028537952570710472301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2925371383936760947296401 2194028537952570710472301)
      ·
        refine ⟨822760701732214016427113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2194028537952570710472301 822760701732214016427113)
        ·
          refine ⟨617070526299160512320335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822760701732214016427113 617070526299160512320335)
          ·
            refine ⟨925605789448740768480503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617070526299160512320335 925605789448740768480503)
            ·
              refine ⟨1388408684173111152720755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925605789448740768480503 1388408684173111152720755)
              ·
                refine ⟨2082613026259666729081133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388408684173111152720755 2082613026259666729081133)
                ·
                  refine ⟨780979884847375023405425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2082613026259666729081133 780979884847375023405425)
                  ·
                    refine ⟨585734913635531267554069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 780979884847375023405425 585734913635531267554069)
                    ·
                      refine ⟨27456324076665528166597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 585734913635531267554069 27456324076665528166597)
                      ·
                        rfl

theorem cell23_53471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_53471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53471 prefixEnd_53471 := by exact prefixLift 53471
  have htrace : WordTrace (prefixWord ++ tailWord_53471) baseStart_53471 baseEnd_53471 := by
    simpa [prefixWord, tailWord_53471, baseEnd_53471] using wordTrace_append hprefix tailTrace_53471
  have hstable : (prefixWord ++ tailWord_53471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53471).length < 2 ^ (prefixWord ++ tailWord_53471).sum := by decide
  have hdescent : baseEnd_53471 < baseStart_53471 := by decide
  rcases family_descends (prefixWord ++ tailWord_53471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53506 : List Nat := [3, 4, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_53506 : Nat := 118140960795 + 53506 * 2 ^ 59
def prefixEnd_53506 : Nat := 4983230072969 + 3 ^ 40 * 53506 * 2
def baseEnd_53506 : Nat := 9158098633190963742979

theorem tailTrace_53506 : CollatzResearch.WordTrace tailWord_53506 prefixEnd_53506 9158098633190963742979 := by
  unfold tailWord_53506
  simp only [CollatzResearch.WordTrace]
  refine ⟨487881036041093735597093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1301016096109583294925581 487881036041093735597093)
  ·
    refine ⟨91477694257705075424455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 487881036041093735597093 91477694257705075424455)
    ·
      refine ⟨137216541386557613136683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91477694257705075424455 137216541386557613136683)
      ·
        refine ⟨205824812079836419705025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137216541386557613136683 205824812079836419705025)
        ·
          refine ⟨154368609059877314778769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205824812079836419705025 154368609059877314778769)
          ·
            refine ⟨115776456794907986084077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154368609059877314778769 115776456794907986084077)
            ·
              refine ⟨43416171298090494781529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115776456794907986084077 43416171298090494781529)
              ·
                refine ⟨32562128473567871086147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43416171298090494781529 32562128473567871086147)
                ·
                  refine ⟨48843192710351806629221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32562128473567871086147 48843192710351806629221)
                  ·
                    refine ⟨9158098633190963742979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48843192710351806629221 9158098633190963742979)
                    ·
                      rfl

theorem cell23_53506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_53506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53506 prefixEnd_53506 := by exact prefixLift 53506
  have htrace : WordTrace (prefixWord ++ tailWord_53506) baseStart_53506 baseEnd_53506 := by
    simpa [prefixWord, tailWord_53506, baseEnd_53506] using wordTrace_append hprefix tailTrace_53506
  have hstable : (prefixWord ++ tailWord_53506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53506).length < 2 ^ (prefixWord ++ tailWord_53506).sum := by decide
  have hdescent : baseEnd_53506 < baseStart_53506 := by decide
  rcases family_descends (prefixWord ++ tailWord_53506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53512 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_53512 : Nat := 118140960795 + 53512 * 2 ^ 59
def prefixEnd_53512 : Nat := 4983230072969 + 3 ^ 40 * 53512 * 2
def baseEnd_53512 : Nat := 27477376783499867753909

theorem tailTrace_53512 : CollatzResearch.WordTrace tailWord_53512 prefixEnd_53512 27477376783499867753909 := by
  unfold tailWord_53512
  simp only [CollatzResearch.WordTrace]
  refine ⟨975871491071318983553395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1301161988095091978071193 975871491071318983553395)
  ·
    refine ⟨1463807236606978475330093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975871491071318983553395 1463807236606978475330093)
    ·
      refine ⟨548927713727616928248785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1463807236606978475330093 548927713727616928248785)
      ·
        refine ⟨411695785295712696186589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548927713727616928248785 411695785295712696186589)
        ·
          refine ⟨154385919485892261069971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411695785295712696186589 154385919485892261069971)
          ·
            refine ⟨231578879228838391604957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154385919485892261069971 231578879228838391604957)
            ·
              refine ⟨86842079710814396851859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231578879228838391604957 86842079710814396851859)
              ·
                refine ⟨130263119566221595277789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86842079710814396851859 130263119566221595277789)
                ·
                  refine ⟨48848669837333098229171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130263119566221595277789 48848669837333098229171)
                  ·
                    refine ⟨73273004755999647343757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48848669837333098229171 73273004755999647343757)
                    ·
                      refine ⟨27477376783499867753909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 73273004755999647343757 27477376783499867753909)
                      ·
                        rfl

theorem cell23_53512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_53512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53512 prefixEnd_53512 := by exact prefixLift 53512
  have htrace : WordTrace (prefixWord ++ tailWord_53512) baseStart_53512 baseEnd_53512 := by
    simpa [prefixWord, tailWord_53512, baseEnd_53512] using wordTrace_append hprefix tailTrace_53512
  have hstable : (prefixWord ++ tailWord_53512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53512).length < 2 ^ (prefixWord ++ tailWord_53512).sum := by decide
  have hdescent : baseEnd_53512 < baseStart_53512 := by decide
  rcases family_descends (prefixWord ++ tailWord_53512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53528 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 1, 6]
def baseStart_53528 : Nat := 118140960795 + 53528 * 2 ^ 59
def prefixEnd_53528 : Nat := 4983230072969 + 3 ^ 40 * 53528 * 2
def baseEnd_53528 : Nat := 9161864157990601717945

theorem tailTrace_53528 : CollatzResearch.WordTrace tailWord_53528 prefixEnd_53528 9161864157990601717945 := by
  unfold tailWord_53528
  simp only [CollatzResearch.WordTrace]
  refine ⟨976163275042336349844619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1301551033389781799792825 976163275042336349844619)
  ·
    refine ⟨1464244912563504524766929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 976163275042336349844619 1464244912563504524766929)
    ·
      refine ⟨1098183684422628393575197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464244912563504524766929 1098183684422628393575197)
      ·
        refine ⟨411818881658485647590699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1098183684422628393575197 411818881658485647590699)
        ·
          refine ⟨617728322487728471386049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411818881658485647590699 617728322487728471386049)
          ·
            refine ⟨463296241865796353539537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617728322487728471386049 463296241865796353539537)
            ·
              refine ⟨347472181399347265154653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463296241865796353539537 347472181399347265154653)
              ·
                refine ⟨130302068024755224432995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347472181399347265154653 130302068024755224432995)
                ·
                  refine ⟨195453102037132836649493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130302068024755224432995 195453102037132836649493)
                  ·
                    refine ⟨9161864157990601717945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195453102037132836649493 9161864157990601717945)
                    ·
                      rfl

theorem cell23_53528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_53528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53528 prefixEnd_53528 := by exact prefixLift 53528
  have htrace : WordTrace (prefixWord ++ tailWord_53528) baseStart_53528 baseEnd_53528 := by
    simpa [prefixWord, tailWord_53528, baseEnd_53528] using wordTrace_append hprefix tailTrace_53528
  have hstable : (prefixWord ++ tailWord_53528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53528).length < 2 ^ (prefixWord ++ tailWord_53528).sum := by decide
  have hdescent : baseEnd_53528 < baseStart_53528 := by decide
  rcases family_descends (prefixWord ++ tailWord_53528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53535 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_53535 : Nat := 118140960795 + 53535 * 2 ^ 59
def prefixEnd_53535 : Nat := 4983230072969 + 3 ^ 40 * 53535 * 2
def baseEnd_53535 : Nat := 27489186838553277766303

theorem tailTrace_53535 : CollatzResearch.WordTrace tailWord_53535 prefixEnd_53535 27489186838553277766303 := by
  unfold tailWord_53535
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952581861059312895194059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1301721240706208596796039 1952581861059312895194059)
  ·
    refine ⟨2928872791588969342791089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1952581861059312895194059 2928872791588969342791089)
    ·
      refine ⟨2196654593691727007093317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2928872791588969342791089 2196654593691727007093317)
      ·
        refine ⟨411872736317198813829997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2196654593691727007093317 411872736317198813829997)
        ·
          refine ⟨154452276118949555186249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411872736317198813829997 154452276118949555186249)
          ·
            refine ⟨115839207089212166389687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154452276118949555186249 115839207089212166389687)
            ·
              refine ⟨173758810633818249584531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115839207089212166389687 173758810633818249584531)
              ·
                refine ⟨260638215950727374376797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173758810633818249584531 260638215950727374376797)
                ·
                  refine ⟨97739330981522765391299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260638215950727374376797 97739330981522765391299)
                  ·
                    refine ⟨146608996472284148086949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97739330981522765391299 146608996472284148086949)
                    ·
                      refine ⟨27489186838553277766303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 146608996472284148086949 27489186838553277766303)
                      ·
                        rfl

theorem cell23_53535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_53535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53535 prefixEnd_53535 := by exact prefixLift 53535
  have htrace : WordTrace (prefixWord ++ tailWord_53535) baseStart_53535 baseEnd_53535 := by
    simpa [prefixWord, tailWord_53535, baseEnd_53535] using wordTrace_append hprefix tailTrace_53535
  have hstable : (prefixWord ++ tailWord_53535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53535).length < 2 ^ (prefixWord ++ tailWord_53535).sum := by decide
  have hdescent : baseEnd_53535 < baseStart_53535 := by decide
  rcases family_descends (prefixWord ++ tailWord_53535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53548 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_53548 : Nat := 118140960795 + 53548 * 2 ^ 59
def prefixEnd_53548 : Nat := 4983230072969 + 3 ^ 40 * 53548 * 2
def baseEnd_53548 : Nat := 27495862087061726903743

theorem tailTrace_53548 : CollatzResearch.WordTrace tailWord_53548 prefixEnd_53548 27495862087061726903743 := by
  unfold tailWord_53548
  simp only [CollatzResearch.WordTrace]
  refine ⟨976528005006108057708649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1302037340008144076944865 976528005006108057708649)
  ·
    refine ⟨732396003754581043281487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 976528005006108057708649 732396003754581043281487)
    ·
      refine ⟨1098594005631871564922231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732396003754581043281487 1098594005631871564922231)
      ·
        refine ⟨1647891008447807347383347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098594005631871564922231 1647891008447807347383347)
        ·
          refine ⟨2471836512671711021075021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647891008447807347383347 2471836512671711021075021)
          ·
            refine ⟨926938692251891632903133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2471836512671711021075021 926938692251891632903133)
            ·
              refine ⟨347602009594459362338675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926938692251891632903133 347602009594459362338675)
              ·
                refine ⟨521403014391689043508013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347602009594459362338675 521403014391689043508013)
                ·
                  refine ⟨195526130396883391315505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521403014391689043508013 195526130396883391315505)
                  ·
                    refine ⟨146644597797662543486629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 195526130396883391315505 146644597797662543486629)
                    ·
                      refine ⟨27495862087061726903743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 146644597797662543486629 27495862087061726903743)
                      ·
                        rfl

theorem cell23_53548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_53548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53548 prefixEnd_53548 := by exact prefixLift 53548
  have htrace : WordTrace (prefixWord ++ tailWord_53548) baseStart_53548 baseEnd_53548 := by
    simpa [prefixWord, tailWord_53548, baseEnd_53548] using wordTrace_append hprefix tailTrace_53548
  have hstable : (prefixWord ++ tailWord_53548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53548).length < 2 ^ (prefixWord ++ tailWord_53548).sum := by decide
  have hdescent : baseEnd_53548 < baseStart_53548 := by decide
  rcases family_descends (prefixWord ++ tailWord_53548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53558 : List Nat := [5, 1, 2, 15]
def baseStart_53558 : Nat := 118140960795 + 53558 * 2 ^ 59
def prefixEnd_53558 : Nat := 4983230072969 + 3 ^ 40 * 53558 * 2
def baseEnd_53558 : Nat := 12574758524740140731

theorem tailTrace_53558 : CollatzResearch.WordTrace tailWord_53558 prefixEnd_53558 12574758524740140731 := by
  unfold tailWord_53558
  simp only [CollatzResearch.WordTrace]
  refine ⟨122088796248499238955083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1302280493317325215520885 122088796248499238955083)
  ·
    refine ⟨183133194372748858432625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122088796248499238955083 183133194372748858432625)
    ·
      refine ⟨137349895779561643824469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183133194372748858432625 137349895779561643824469)
      ·
        refine ⟨12574758524740140731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 137349895779561643824469 12574758524740140731)
        ·
          rfl

theorem cell23_53558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 15].length) (baseStart_53558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53558 prefixEnd_53558 := by exact prefixLift 53558
  have htrace : WordTrace (prefixWord ++ tailWord_53558) baseStart_53558 baseEnd_53558 := by
    simpa [prefixWord, tailWord_53558, baseEnd_53558] using wordTrace_append hprefix tailTrace_53558
  have hstable : (prefixWord ++ tailWord_53558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53558).length < 2 ^ (prefixWord ++ tailWord_53558).sum := by decide
  have hdescent : baseEnd_53558 < baseStart_53558 := by decide
  rcases family_descends (prefixWord ++ tailWord_53558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53562 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_53562 : Nat := 118140960795 + 53562 * 2 ^ 59
def prefixEnd_53562 : Nat := 4983230072969 + 3 ^ 40 * 53562 * 2
def baseEnd_53562 : Nat := 9167683605408224042893

theorem tailTrace_53562 : CollatzResearch.WordTrace tailWord_53562 prefixEnd_53562 9167683605408224042893 := by
  unfold tailWord_53562
  simp only [CollatzResearch.WordTrace]
  refine ⟨488391657990374126606735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1302377754640997670951293 488391657990374126606735)
  ·
    refine ⟨732587486985561189910103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488391657990374126606735 732587486985561189910103)
    ·
      refine ⟨1098881230478341784865155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732587486985561189910103 1098881230478341784865155)
      ·
        refine ⟨1648321845717512677297733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098881230478341784865155 1648321845717512677297733)
        ·
          refine ⟨309060346072033626993325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1648321845717512677297733 309060346072033626993325)
          ·
            refine ⟨115897629777012610122497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309060346072033626993325 115897629777012610122497)
            ·
              refine ⟨86923222332759457591873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115897629777012610122497 86923222332759457591873)
              ·
                refine ⟨65192416749569593193905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86923222332759457591873 65192416749569593193905)
                ·
                  refine ⟨48894312562177194895429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65192416749569593193905 48894312562177194895429)
                  ·
                    refine ⟨9167683605408224042893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48894312562177194895429 9167683605408224042893)
                    ·
                      rfl

theorem cell23_53562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_53562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53562 prefixEnd_53562 := by exact prefixLift 53562
  have htrace : WordTrace (prefixWord ++ tailWord_53562) baseStart_53562 baseEnd_53562 := by
    simpa [prefixWord, tailWord_53562, baseEnd_53562] using wordTrace_append hprefix tailTrace_53562
  have hstable : (prefixWord ++ tailWord_53562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53562).length < 2 ^ (prefixWord ++ tailWord_53562).sum := by decide
  have hdescent : baseEnd_53562 < baseStart_53562 := by decide
  rcases family_descends (prefixWord ++ tailWord_53562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53585 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_53585 : Nat := 118140960795 + 53585 * 2 ^ 59
def prefixEnd_53585 : Nat := 4983230072969 + 3 ^ 40 * 53585 * 2
def baseEnd_53585 : Nat := 27514860871278082141073

theorem tailTrace_53585 : CollatzResearch.WordTrace tailWord_53585 prefixEnd_53585 27514860871278082141073 := by
  unfold tailWord_53585
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954405510878171434514209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1302937007252114289676139 1954405510878171434514209)
  ·
    refine ⟨1465804133158628575885657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1954405510878171434514209 1465804133158628575885657)
    ·
      refine ⟨1099353099868971431914243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1465804133158628575885657 1099353099868971431914243)
      ·
        refine ⟨1649029649803457147871365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099353099868971431914243 1649029649803457147871365)
        ·
          refine ⟨309193059338148215225881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1649029649803457147871365 309193059338148215225881)
          ·
            refine ⟨231894794503611161419411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309193059338148215225881 231894794503611161419411)
            ·
              refine ⟨347842191755416742129117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231894794503611161419411 347842191755416742129117)
              ·
                refine ⟨130440821908281278298419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347842191755416742129117 130440821908281278298419)
                ·
                  refine ⟨195661232862421917447629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130440821908281278298419 195661232862421917447629)
                  ·
                    refine ⟨73372962323408219042861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195661232862421917447629 73372962323408219042861)
                    ·
                      refine ⟨27514860871278082141073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 73372962323408219042861 27514860871278082141073)
                      ·
                        rfl

theorem cell23_53585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_53585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53585 prefixEnd_53585 := by exact prefixLift 53585
  have htrace : WordTrace (prefixWord ++ tailWord_53585) baseStart_53585 baseEnd_53585 := by
    simpa [prefixWord, tailWord_53585, baseEnd_53585] using wordTrace_append hprefix tailTrace_53585
  have hstable : (prefixWord ++ tailWord_53585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53585).length < 2 ^ (prefixWord ++ tailWord_53585).sum := by decide
  have hdescent : baseEnd_53585 < baseStart_53585 := by decide
  rcases family_descends (prefixWord ++ tailWord_53585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53602 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_53602 : Nat := 118140960795 + 53602 * 2 ^ 59
def prefixEnd_53602 : Nat := 4983230072969 + 3 ^ 40 * 53602 * 2
def baseEnd_53602 : Nat := 27523590042404515628495

theorem tailTrace_53602 : CollatzResearch.WordTrace tailWord_53602 prefixEnd_53602 27523590042404515628495 := by
  unfold tailWord_53602
  simp only [CollatzResearch.WordTrace]
  refine ⟨488756387954145834470765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1303350367877722225255373 488756387954145834470765)
  ·
    refine ⟨183283645482804687926537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 488756387954145834470765 183283645482804687926537)
    ·
      refine ⟨137462734112103515944903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183283645482804687926537 137462734112103515944903)
      ·
        refine ⟨206194101168155273917355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137462734112103515944903 206194101168155273917355)
        ·
          refine ⟨309291151752232910876033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206194101168155273917355 309291151752232910876033)
          ·
            refine ⟨231968363814174683157025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309291151752232910876033 231968363814174683157025)
            ·
              refine ⟨173976272860631012367769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231968363814174683157025 173976272860631012367769)
              ·
                refine ⟨130482204645473259275827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173976272860631012367769 130482204645473259275827)
                ·
                  refine ⟨195723306968209888913741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130482204645473259275827 195723306968209888913741)
                  ·
                    refine ⟨73396240113078708342653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195723306968209888913741 73396240113078708342653)
                    ·
                      refine ⟨27523590042404515628495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 73396240113078708342653 27523590042404515628495)
                      ·
                        rfl

theorem cell23_53602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_53602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53602 prefixEnd_53602 := by exact prefixLift 53602
  have htrace : WordTrace (prefixWord ++ tailWord_53602) baseStart_53602 baseEnd_53602 := by
    simpa [prefixWord, tailWord_53602, baseEnd_53602] using wordTrace_append hprefix tailTrace_53602
  have hstable : (prefixWord ++ tailWord_53602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53602).length < 2 ^ (prefixWord ++ tailWord_53602).sum := by decide
  have hdescent : baseEnd_53602 < baseStart_53602 := by decide
  rcases family_descends (prefixWord ++ tailWord_53602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53628 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_53628 : Nat := 118140960795 + 53628 * 2 ^ 59
def prefixEnd_53628 : Nat := 4983230072969 + 3 ^ 40 * 53628 * 2
def baseEnd_53628 : Nat := 27536940539421413903375

theorem tailTrace_53628 : CollatzResearch.WordTrace tailWord_53628 prefixEnd_53628 27536940539421413903375 := by
  unfold tailWord_53628
  simp only [CollatzResearch.WordTrace]
  refine ⟨977986924861194889164769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1303982566481593185553025 977986924861194889164769)
  ·
    refine ⟨733490193645896166873577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 977986924861194889164769 733490193645896166873577)
    ·
      refine ⟨550117645234422125155183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 733490193645896166873577 550117645234422125155183)
      ·
        refine ⟨825176467851633187732775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550117645234422125155183 825176467851633187732775)
        ·
          refine ⟨1237764701777449781599163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825176467851633187732775 1237764701777449781599163)
          ·
            refine ⟨1856647052666174672398745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237764701777449781599163 1856647052666174672398745)
            ·
              refine ⟨1392485289499631004299059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856647052666174672398745 1392485289499631004299059)
              ·
                refine ⟨2088727934249446506448589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392485289499631004299059 2088727934249446506448589)
                ·
                  refine ⟨783272975343542439918221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2088727934249446506448589 783272975343542439918221)
                  ·
                    refine ⟨293727365753828414969333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783272975343542439918221 293727365753828414969333)
                    ·
                      refine ⟨27536940539421413903375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 293727365753828414969333 27536940539421413903375)
                      ·
                        rfl

theorem cell23_53628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_53628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53628 prefixEnd_53628 := by exact prefixLift 53628
  have htrace : WordTrace (prefixWord ++ tailWord_53628) baseStart_53628 baseEnd_53628 := by
    simpa [prefixWord, tailWord_53628, baseEnd_53628] using wordTrace_append hprefix tailTrace_53628
  have hstable : (prefixWord ++ tailWord_53628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53628).length < 2 ^ (prefixWord ++ tailWord_53628).sum := by decide
  have hdescent : baseEnd_53628 < baseStart_53628 := by decide
  rcases family_descends (prefixWord ++ tailWord_53628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53646 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_53646 : Nat := 118140960795 + 53646 * 2 ^ 59
def prefixEnd_53646 : Nat := 4983230072969 + 3 ^ 40 * 53646 * 2
def baseEnd_53646 : Nat := 27546183191202343478293

theorem tailTrace_53646 : CollatzResearch.WordTrace tailWord_53646 prefixEnd_53646 27546183191202343478293 := by
  unfold tailWord_53646
  simp only [CollatzResearch.WordTrace]
  refine ⟨244578795457147356560599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1304420242438119234989861 244578795457147356560599)
  ·
    refine ⟨366868193185721034840899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244578795457147356560599 366868193185721034840899)
    ·
      refine ⟨550302289778581552261349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366868193185721034840899 550302289778581552261349)
      ·
        refine ⟨103181679333484041049003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 550302289778581552261349 103181679333484041049003)
        ·
          refine ⟨154772519000226061573505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103181679333484041049003 154772519000226061573505)
          ·
            refine ⟨116079389250169546180129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154772519000226061573505 116079389250169546180129)
            ·
              refine ⟨87059541937627159635097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116079389250169546180129 87059541937627159635097)
              ·
                refine ⟨65294656453220369726323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87059541937627159635097 65294656453220369726323)
                ·
                  refine ⟨97941984679830554589485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65294656453220369726323 97941984679830554589485)
                  ·
                    refine ⟨36728244254936457971057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97941984679830554589485 36728244254936457971057)
                    ·
                      refine ⟨27546183191202343478293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36728244254936457971057 27546183191202343478293)
                      ·
                        rfl

theorem cell23_53646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_53646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53646 prefixEnd_53646 := by exact prefixLift 53646
  have htrace : WordTrace (prefixWord ++ tailWord_53646) baseStart_53646 baseEnd_53646 := by
    simpa [prefixWord, tailWord_53646, baseEnd_53646] using wordTrace_append hprefix tailTrace_53646
  have hstable : (prefixWord ++ tailWord_53646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53646).length < 2 ^ (prefixWord ++ tailWord_53646).sum := by decide
  have hdescent : baseEnd_53646 < baseStart_53646 := by decide
  rcases family_descends (prefixWord ++ tailWord_53646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53654 : List Nat := [5, 3, 1, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_53654 : Nat := 118140960795 + 53654 * 2 ^ 59
def prefixEnd_53654 : Nat := 4983230072969 + 3 ^ 40 * 53654 * 2
def baseEnd_53654 : Nat := 27550291036438312178257

theorem tailTrace_53654 : CollatzResearch.WordTrace tailWord_53654 prefixEnd_53654 27550291036438312178257 := by
  unfold tailWord_53654
  simp only [CollatzResearch.WordTrace]
  refine ⟨122307634226762263673501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1304614765085464145850677 122307634226762263673501)
  ·
    refine ⟨45865362835035848877563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122307634226762263673501 45865362835035848877563)
    ·
      refine ⟨68798044252553773316345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45865362835035848877563 68798044252553773316345)
      ·
        refine ⟨51598533189415329987259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68798044252553773316345 51598533189415329987259)
        ·
          refine ⟨77397799784122994980889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51598533189415329987259 77397799784122994980889)
          ·
            refine ⟨58048349838092246235667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77397799784122994980889 58048349838092246235667)
            ·
              refine ⟨87072524757138369353501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58048349838092246235667 87072524757138369353501)
              ·
                refine ⟨32652196783926888507563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87072524757138369353501 32652196783926888507563)
                ·
                  refine ⟨48978295175890332761345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32652196783926888507563 48978295175890332761345)
                  ·
                    refine ⟨36733721381917749571009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48978295175890332761345 36733721381917749571009)
                    ·
                      refine ⟨27550291036438312178257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36733721381917749571009 27550291036438312178257)
                      ·
                        rfl

theorem cell23_53654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_53654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53654 prefixEnd_53654 := by exact prefixLift 53654
  have htrace : WordTrace (prefixWord ++ tailWord_53654) baseStart_53654 baseEnd_53654 := by
    simpa [prefixWord, tailWord_53654, baseEnd_53654] using wordTrace_append hprefix tailTrace_53654
  have hstable : (prefixWord ++ tailWord_53654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53654).length < 2 ^ (prefixWord ++ tailWord_53654).sum := by decide
  have hdescent : baseEnd_53654 < baseStart_53654 := by decide
  rcases family_descends (prefixWord ++ tailWord_53654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53662 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_53662 : Nat := 118140960795 + 53662 * 2 ^ 59
def prefixEnd_53662 : Nat := 4983230072969 + 3 ^ 40 * 53662 * 2
def baseEnd_53662 : Nat := 27554398881674280878219

theorem tailTrace_53662 : CollatzResearch.WordTrace tailWord_53662 prefixEnd_53662 27554398881674280878219 := by
  unfold tailWord_53662
  simp only [CollatzResearch.WordTrace]
  refine ⟨244651741449901698133405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1304809287732809056711493 244651741449901698133405)
  ·
    refine ⟨91744403043713136800027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244651741449901698133405 91744403043713136800027)
    ·
      refine ⟨137616604565569705200041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91744403043713136800027 137616604565569705200041)
      ·
        refine ⟨103212453424177278900031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137616604565569705200041 103212453424177278900031)
        ·
          refine ⟨154818680136265918350047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103212453424177278900031 154818680136265918350047)
          ·
            refine ⟨232228020204398877525071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154818680136265918350047 232228020204398877525071)
            ·
              refine ⟨348342030306598316287607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232228020204398877525071 348342030306598316287607)
              ·
                refine ⟨522513045459897474431411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348342030306598316287607 522513045459897474431411)
                ·
                  refine ⟨783769568189846211647117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522513045459897474431411 783769568189846211647117)
                  ·
                    refine ⟨293913588071192329367669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783769568189846211647117 293913588071192329367669)
                    ·
                      refine ⟨27554398881674280878219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 293913588071192329367669 27554398881674280878219)
                      ·
                        rfl

theorem cell23_53662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_53662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53662 prefixEnd_53662 := by exact prefixLift 53662
  have htrace : WordTrace (prefixWord ++ tailWord_53662) baseStart_53662 baseEnd_53662 := by
    simpa [prefixWord, tailWord_53662, baseEnd_53662] using wordTrace_append hprefix tailTrace_53662
  have hstable : (prefixWord ++ tailWord_53662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53662).length < 2 ^ (prefixWord ++ tailWord_53662).sum := by decide
  have hdescent : baseEnd_53662 < baseStart_53662 := by decide
  rcases family_descends (prefixWord ++ tailWord_53662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53693 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_53693 : Nat := 118140960795 + 53693 * 2 ^ 59
def prefixEnd_53693 : Nat := 4983230072969 + 3 ^ 40 * 53693 * 2
def baseEnd_53693 : Nat := 27570316781963659590577

theorem tailTrace_53693 : CollatzResearch.WordTrace tailWord_53693 prefixEnd_53693 27570316781963659590577 := by
  unfold tailWord_53693
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958344594486905879445733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1305563062991270586297155 1958344594486905879445733)
  ·
    refine ⟨367189611466294852396075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1958344594486905879445733 367189611466294852396075)
    ·
      refine ⟨550784417199442278594113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367189611466294852396075 550784417199442278594113)
      ·
        refine ⟨413088312899581708945585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550784417199442278594113 413088312899581708945585)
        ·
          refine ⟨309816234674686281709189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413088312899581708945585 309816234674686281709189)
          ·
            refine ⟨58090544001503677820473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309816234674686281709189 58090544001503677820473)
            ·
              refine ⟨43567908001127758365355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58090544001503677820473 43567908001127758365355)
              ·
                refine ⟨65351862001691637548033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43567908001127758365355 65351862001691637548033)
                ·
                  refine ⟨49013896501268728161025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65351862001691637548033 49013896501268728161025)
                  ·
                    refine ⟨36760422375951546120769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49013896501268728161025 36760422375951546120769)
                    ·
                      refine ⟨27570316781963659590577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36760422375951546120769 27570316781963659590577)
                      ·
                        rfl

theorem cell23_53693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_53693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53693 prefixEnd_53693 := by exact prefixLift 53693
  have htrace : WordTrace (prefixWord ++ tailWord_53693) baseStart_53693 baseEnd_53693 := by
    simpa [prefixWord, tailWord_53693, baseEnd_53693] using wordTrace_append hprefix tailTrace_53693
  have hstable : (prefixWord ++ tailWord_53693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53693).length < 2 ^ (prefixWord ++ tailWord_53693).sum := by decide
  have hdescent : baseEnd_53693 < baseStart_53693 := by decide
  rcases family_descends (prefixWord ++ tailWord_53693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53697 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_53697 : Nat := 118140960795 + 53697 * 2 ^ 59
def prefixEnd_53697 : Nat := 4983230072969 + 3 ^ 40 * 53697 * 2
def baseEnd_53697 : Nat := 27572370704581643940559

theorem tailTrace_53697 : CollatzResearch.WordTrace tailWord_53697 prefixEnd_53697 27572370704581643940559 := by
  unfold tailWord_53697
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958490486472414562591345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1305660324314943041727563 1958490486472414562591345)
  ·
    refine ⟨1468867864854310921943509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1958490486472414562591345 1468867864854310921943509)
    ·
      refine ⟨34426590582522912233051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1468867864854310921943509 34426590582522912233051)
      ·
        refine ⟨51639885873784368349577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34426590582522912233051 51639885873784368349577)
        ·
          refine ⟨38729914405338276262183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51639885873784368349577 38729914405338276262183)
          ·
            refine ⟨58094871608007414393275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38729914405338276262183 58094871608007414393275)
            ·
              refine ⟨87142307412011121589913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58094871608007414393275 87142307412011121589913)
              ·
                refine ⟨65356730559008341192435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87142307412011121589913 65356730559008341192435)
                ·
                  refine ⟨98035095838512511788653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65356730559008341192435 98035095838512511788653)
                  ·
                    refine ⟨36763160939442191920745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98035095838512511788653 36763160939442191920745)
                    ·
                      refine ⟨27572370704581643940559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36763160939442191920745 27572370704581643940559)
                      ·
                        rfl

theorem cell23_53697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_53697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53697 prefixEnd_53697 := by exact prefixLift 53697
  have htrace : WordTrace (prefixWord ++ tailWord_53697) baseStart_53697 baseEnd_53697 := by
    simpa [prefixWord, tailWord_53697, baseEnd_53697] using wordTrace_append hprefix tailTrace_53697
  have hstable : (prefixWord ++ tailWord_53697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53697).length < 2 ^ (prefixWord ++ tailWord_53697).sum := by decide
  have hdescent : baseEnd_53697 < baseStart_53697 := by decide
  rcases family_descends (prefixWord ++ tailWord_53697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53733 : List Nat := [1, 3, 1, 5, 3, 1, 2, 2, 5]
def baseStart_53733 : Nat := 118140960795 + 53733 * 2 ^ 59
def prefixEnd_53733 : Nat := 4983230072969 + 3 ^ 40 * 53733 * 2
def baseEnd_53733 : Nat := 3065650667571500343377

theorem tailTrace_53733 : CollatzResearch.WordTrace tailWord_53733 prefixEnd_53733 3065650667571500343377 := by
  unfold tailWord_53733
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959803514341992710901853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1306535676227995140601235 1959803514341992710901853)
  ·
    refine ⟨734926317878247266588195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1959803514341992710901853 734926317878247266588195)
    ·
      refine ⟨1102389476817370899882293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 734926317878247266588195 1102389476817370899882293)
      ·
        refine ⟨103349013451628521863965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1102389476817370899882293 103349013451628521863965)
        ·
          refine ⟨38755880044360695698987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103349013451628521863965 38755880044360695698987)
          ·
            refine ⟨58133820066541043548481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38755880044360695698987 58133820066541043548481)
            ·
              refine ⟨43600365049905782661361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58133820066541043548481 43600365049905782661361)
              ·
                refine ⟨32700273787429336996021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43600365049905782661361 32700273787429336996021)
                ·
                  refine ⟨3065650667571500343377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32700273787429336996021 3065650667571500343377)
                  ·
                    rfl

theorem cell23_53733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_53733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53733 prefixEnd_53733 := by exact prefixLift 53733
  have htrace : WordTrace (prefixWord ++ tailWord_53733) baseStart_53733 baseEnd_53733 := by
    simpa [prefixWord, tailWord_53733, baseEnd_53733] using wordTrace_append hprefix tailTrace_53733
  have hstable : (prefixWord ++ tailWord_53733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53733).length < 2 ^ (prefixWord ++ tailWord_53733).sum := by decide
  have hdescent : baseEnd_53733 < baseStart_53733 := by decide
  rcases family_descends (prefixWord ++ tailWord_53733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53735 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_53735 : Nat := 118140960795 + 53735 * 2 ^ 59
def prefixEnd_53735 : Nat := 4983230072969 + 3 ^ 40 * 53735 * 2
def baseEnd_53735 : Nat := 27591882969452495265383

theorem tailTrace_53735 : CollatzResearch.WordTrace tailWord_53735 prefixEnd_53735 27591882969452495265383 := by
  unfold tailWord_53735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959876460334747052474659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1306584306889831368316439 1959876460334747052474659)
  ·
    refine ⟨2939814690502120578711989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1959876460334747052474659 2939814690502120578711989)
    ·
      refine ⟨275607627234573804254249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2939814690502120578711989 275607627234573804254249)
      ·
        refine ⟨206705720425930353190687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275607627234573804254249 206705720425930353190687)
        ·
          refine ⟨310058580638895529786031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206705720425930353190687 310058580638895529786031)
          ·
            refine ⟨465087870958343294679047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310058580638895529786031 465087870958343294679047)
            ·
              refine ⟨697631806437514942018571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465087870958343294679047 697631806437514942018571)
              ·
                refine ⟨1046447709656272413027857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697631806437514942018571 1046447709656272413027857)
                ·
                  refine ⟨784835782242204309770893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046447709656272413027857 784835782242204309770893)
                  ·
                    refine ⟨294313418340826616164085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 784835782242204309770893 294313418340826616164085)
                    ·
                      refine ⟨27591882969452495265383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 294313418340826616164085 27591882969452495265383)
                      ·
                        rfl

theorem cell23_53735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_53735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53735 prefixEnd_53735 := by exact prefixLift 53735
  have htrace : WordTrace (prefixWord ++ tailWord_53735) baseStart_53735 baseEnd_53735 := by
    simpa [prefixWord, tailWord_53735, baseEnd_53735] using wordTrace_append hprefix tailTrace_53735
  have hstable : (prefixWord ++ tailWord_53735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53735).length < 2 ^ (prefixWord ++ tailWord_53735).sum := by decide
  have hdescent : baseEnd_53735 < baseStart_53735 := by decide
  rcases family_descends (prefixWord ++ tailWord_53735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53789 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 6]
def baseStart_53789 : Nat := 118140960795 + 53789 * 2 ^ 59
def prefixEnd_53789 : Nat := 4983230072969 + 3 ^ 40 * 53789 * 2
def baseEnd_53789 : Nat := 3068845658310587110015

theorem tailTrace_53789 : CollatzResearch.WordTrace tailWord_53789 prefixEnd_53789 3068845658310587110015 := by
  unfold tailWord_53789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961846002139114274940421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1307897334759409516626947 1961846002139114274940421)
  ·
    refine ⟨367846125401083926551329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1961846002139114274940421 367846125401083926551329)
    ·
      refine ⟨275884594050812944913497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367846125401083926551329 275884594050812944913497)
      ·
        refine ⟨206913445538109708685123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275884594050812944913497 206913445538109708685123)
        ·
          refine ⟨310370168307164563027685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206913445538109708685123 310370168307164563027685)
          ·
            refine ⟨58194406557593355567691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310370168307164563027685 58194406557593355567691)
            ·
              refine ⟨87291609836390033351537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58194406557593355567691 87291609836390033351537)
              ·
                refine ⟨65468707377292525013653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87291609836390033351537 65468707377292525013653)
                ·
                  refine ⟨3068845658310587110015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65468707377292525013653 3068845658310587110015)
                  ·
                    rfl

theorem cell23_53789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_53789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53789 prefixEnd_53789 := by exact prefixLift 53789
  have htrace : WordTrace (prefixWord ++ tailWord_53789) baseStart_53789 baseEnd_53789 := by
    simpa [prefixWord, tailWord_53789, baseEnd_53789] using wordTrace_append hprefix tailTrace_53789
  have hstable : (prefixWord ++ tailWord_53789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53789).length < 2 ^ (prefixWord ++ tailWord_53789).sum := by decide
  have hdescent : baseEnd_53789 < baseStart_53789 := by decide
  rcases family_descends (prefixWord ++ tailWord_53789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53806 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_53806 : Nat := 118140960795 + 53806 * 2 ^ 59
def prefixEnd_53806 : Nat := 4983230072969 + 3 ^ 40 * 53806 * 2
def baseEnd_53806 : Nat := 3069815566213524164173

theorem tailTrace_53806 : CollatzResearch.WordTrace tailWord_53806 prefixEnd_53806 3069815566213524164173 := by
  unfold tailWord_53806
  simp only [CollatzResearch.WordTrace]
  refine ⟨245308255384690772288659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1308310695385017452206181 245308255384690772288659)
  ·
    refine ⟨367962383077036158432989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245308255384690772288659 367962383077036158432989)
    ·
      refine ⟨137985893653888559412371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367962383077036158432989 137985893653888559412371)
      ·
        refine ⟨206978840480832839118557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137985893653888559412371 206978840480832839118557)
        ·
          refine ⟨77617065180312314669459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206978840480832839118557 77617065180312314669459)
          ·
            refine ⟨116425597770468472004189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77617065180312314669459 116425597770468472004189)
            ·
              refine ⟨43659599163925677001571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116425597770468472004189 43659599163925677001571)
              ·
                refine ⟨65489398745888515502357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43659599163925677001571 65489398745888515502357)
                ·
                  refine ⟨3069815566213524164173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65489398745888515502357 3069815566213524164173)
                  ·
                    rfl

theorem cell23_53806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_53806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53806 prefixEnd_53806 := by exact prefixLift 53806
  have htrace : WordTrace (prefixWord ++ tailWord_53806) baseStart_53806 baseEnd_53806 := by
    simpa [prefixWord, tailWord_53806, baseEnd_53806] using wordTrace_append hprefix tailTrace_53806
  have hstable : (prefixWord ++ tailWord_53806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53806).length < 2 ^ (prefixWord ++ tailWord_53806).sum := by decide
  have hdescent : baseEnd_53806 < baseStart_53806 := by decide
  rcases family_descends (prefixWord ++ tailWord_53806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53839 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 5, 2, 2]
def baseStart_53839 : Nat := 118140960795 + 53839 * 2 ^ 59
def prefixEnd_53839 : Nat := 4983230072969 + 3 ^ 40 * 53839 * 2
def baseEnd_53839 : Nat := 27645284957520088364905

theorem tailTrace_53839 : CollatzResearch.WordTrace tailWord_53839 prefixEnd_53839 27645284957520088364905 := by
  unfold tailWord_53839
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963669651957972814260571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1309113101305315209507047 1963669651957972814260571)
  ·
    refine ⟨2945504477936959221390857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1963669651957972814260571 2945504477936959221390857)
    ·
      refine ⟨2209128358452719416043143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2945504477936959221390857 2209128358452719416043143)
      ·
        refine ⟨3313692537679079124064715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209128358452719416043143 3313692537679079124064715)
        ·
          refine ⟨4970538806518618686097073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313692537679079124064715 4970538806518618686097073)
          ·
            refine ⟨3727904104888964014572805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4970538806518618686097073 3727904104888964014572805)
            ·
              refine ⟨698982019666680752732401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3727904104888964014572805 698982019666680752732401)
              ·
                refine ⟨524236514750010564549301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698982019666680752732401 524236514750010564549301)
                ·
                  refine ⟨49147173257813490426497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524236514750010564549301 49147173257813490426497)
                  ·
                    refine ⟨36860379943360117819873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49147173257813490426497 36860379943360117819873)
                    ·
                      refine ⟨27645284957520088364905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36860379943360117819873 27645284957520088364905)
                      ·
                        rfl

theorem cell23_53839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 2, 2].length) (baseStart_53839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53839 prefixEnd_53839 := by exact prefixLift 53839
  have htrace : WordTrace (prefixWord ++ tailWord_53839) baseStart_53839 baseEnd_53839 := by
    simpa [prefixWord, tailWord_53839, baseEnd_53839] using wordTrace_append hprefix tailTrace_53839
  have hstable : (prefixWord ++ tailWord_53839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53839).length < 2 ^ (prefixWord ++ tailWord_53839).sum := by decide
  have hdescent : baseEnd_53839 < baseStart_53839 := by decide
  rcases family_descends (prefixWord ++ tailWord_53839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53845 : List Nat := [1, 3, 2, 2, 1, 1, 13]
def baseStart_53845 : Nat := 118140960795 + 53845 * 2 ^ 59
def prefixEnd_53845 : Nat := 4983230072969 + 3 ^ 40 * 53845 * 2
def baseEnd_53845 : Nat := 341337849894408208517

theorem tailTrace_53845 : CollatzResearch.WordTrace tailWord_53845 prefixEnd_53845 341337849894408208517 := by
  unfold tailWord_53845
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963888489936235838978989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1309258993290823892652659 1963888489936235838978989)
  ·
    refine ⟨736458183726088439617121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1963888489936235838978989 736458183726088439617121)
    ·
      refine ⟨552343637794566329712841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 736458183726088439617121 552343637794566329712841)
      ·
        refine ⟨414257728345924747284631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552343637794566329712841 414257728345924747284631)
        ·
          refine ⟨621386592518887120926947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414257728345924747284631 621386592518887120926947)
          ·
            refine ⟨932079888778330681390421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621386592518887120926947 932079888778330681390421)
            ·
              refine ⟨341337849894408208517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 932079888778330681390421 341337849894408208517)
              ·
                rfl

theorem cell23_53845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 13].length) (baseStart_53845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53845 prefixEnd_53845 := by exact prefixLift 53845
  have htrace : WordTrace (prefixWord ++ tailWord_53845) baseStart_53845 baseEnd_53845 := by
    simpa [prefixWord, tailWord_53845, baseEnd_53845] using wordTrace_append hprefix tailTrace_53845
  have hstable : (prefixWord ++ tailWord_53845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53845).length < 2 ^ (prefixWord ++ tailWord_53845).sum := by decide
  have hdescent : baseEnd_53845 < baseStart_53845 := by decide
  rcases family_descends (prefixWord ++ tailWord_53845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53856 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 3, 2, 2]
def baseStart_53856 : Nat := 118140960795 + 53856 * 2 ^ 59
def prefixEnd_53856 : Nat := 4983230072969 + 3 ^ 40 * 53856 * 2
def baseEnd_53856 : Nat := 27654014128646521852327

theorem tailTrace_53856 : CollatzResearch.WordTrace tailWord_53856 prefixEnd_53856 27654014128646521852327 := by
  unfold tailWord_53856
  simp only [CollatzResearch.WordTrace]
  refine ⟨982144846448192358814711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1309526461930923145086281 982144846448192358814711)
  ·
    refine ⟨1473217269672288538222067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982144846448192358814711 1473217269672288538222067)
    ·
      refine ⟨2209825904508432807333101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473217269672288538222067 2209825904508432807333101)
      ·
        refine ⟨828684714190662302749913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2209825904508432807333101 828684714190662302749913)
        ·
          refine ⟨621513535642996727062435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828684714190662302749913 621513535642996727062435)
          ·
            refine ⟨932270303464495090593653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621513535642996727062435 932270303464495090593653)
            ·
              refine ⟨87400340949796414743155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 932270303464495090593653 87400340949796414743155)
              ·
                refine ⟨131100511424694622114733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87400340949796414743155 131100511424694622114733)
                ·
                  refine ⟨49162691784260483293025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131100511424694622114733 49162691784260483293025)
                  ·
                    refine ⟨36872018838195362469769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49162691784260483293025 36872018838195362469769)
                    ·
                      refine ⟨27654014128646521852327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36872018838195362469769 27654014128646521852327)
                      ·
                        rfl

theorem cell23_53856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_53856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53856 prefixEnd_53856 := by exact prefixLift 53856
  have htrace : WordTrace (prefixWord ++ tailWord_53856) baseStart_53856 baseEnd_53856 := by
    simpa [prefixWord, tailWord_53856, baseEnd_53856] using wordTrace_append hprefix tailTrace_53856
  have hstable : (prefixWord ++ tailWord_53856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53856).length < 2 ^ (prefixWord ++ tailWord_53856).sum := by decide
  have hdescent : baseEnd_53856 < baseStart_53856 := by decide
  rcases family_descends (prefixWord ++ tailWord_53856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53865 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_53865 : Nat := 118140960795 + 53865 * 2 ^ 59
def prefixEnd_53865 : Nat := 4983230072969 + 3 ^ 40 * 53865 * 2
def baseEnd_53865 : Nat := 27658635454536986639785

theorem tailTrace_53865 : CollatzResearch.WordTrace tailWord_53865 prefixEnd_53865 27658635454536986639785 := by
  unfold tailWord_53865
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964617949863779254707049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1309745299909186169804699 1964617949863779254707049)
  ·
    refine ⟨1473463462397834441030287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1964617949863779254707049 1473463462397834441030287)
    ·
      refine ⟨2210195193596751661545431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473463462397834441030287 2210195193596751661545431)
      ·
        refine ⟨3315292790395127492318147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210195193596751661545431 3315292790395127492318147)
        ·
          refine ⟨4972939185592691238477221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3315292790395127492318147 4972939185592691238477221)
          ·
            refine ⟨932426097298629607214479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4972939185592691238477221 932426097298629607214479)
            ·
              refine ⟨1398639145947944410821719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932426097298629607214479 1398639145947944410821719)
              ·
                refine ⟨2097958718921916616232579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398639145947944410821719 2097958718921916616232579)
                ·
                  refine ⟨3146938078382874924348869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097958718921916616232579 3146938078382874924348869)
                  ·
                    refine ⟨590050889696789048315413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3146938078382874924348869 590050889696789048315413)
                    ·
                      refine ⟨27658635454536986639785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 590050889696789048315413 27658635454536986639785)
                      ·
                        rfl

theorem cell23_53865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_53865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53865 prefixEnd_53865 := by exact prefixLift 53865
  have htrace : WordTrace (prefixWord ++ tailWord_53865) baseStart_53865 baseEnd_53865 := by
    simpa [prefixWord, tailWord_53865, baseEnd_53865] using wordTrace_append hprefix tailTrace_53865
  have hstable : (prefixWord ++ tailWord_53865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53865).length < 2 ^ (prefixWord ++ tailWord_53865).sum := by decide
  have hdescent : baseEnd_53865 < baseStart_53865 := by decide
  rcases family_descends (prefixWord ++ tailWord_53865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53875 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 4, 7]
def baseStart_53875 : Nat := 118140960795 + 53875 * 2 ^ 59
def prefixEnd_53875 : Nat := 4983230072969 + 3 ^ 40 * 53875 * 2
def baseEnd_53875 : Nat := 9221256753693982504913

theorem tailTrace_53875 : CollatzResearch.WordTrace tailWord_53875 prefixEnd_53875 9221256753693982504913 := by
  unfold tailWord_53875
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964982679827550962571079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1309988453218367308380719 1964982679827550962571079)
  ·
    refine ⟨2947474019741326443856619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1964982679827550962571079 2947474019741326443856619)
    ·
      refine ⟨4421211029611989665784929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947474019741326443856619 4421211029611989665784929)
      ·
        refine ⟨3315908272208992249338697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4421211029611989665784929 3315908272208992249338697)
        ·
          refine ⟨2486931204156744187004023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3315908272208992249338697 2486931204156744187004023)
          ·
            refine ⟨3730396806235116280506035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486931204156744187004023 3730396806235116280506035)
            ·
              refine ⟨5595595209352674420759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730396806235116280506035 5595595209352674420759053)
              ·
                refine ⟨2098348203507252907784645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5595595209352674420759053 2098348203507252907784645)
                ·
                  refine ⟨393440288157609920209621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098348203507252907784645 393440288157609920209621)
                  ·
                    refine ⟨9221256753693982504913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 393440288157609920209621 9221256753693982504913)
                    ·
                      rfl

theorem cell23_53875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 7].length) (baseStart_53875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53875 prefixEnd_53875 := by exact prefixLift 53875
  have htrace : WordTrace (prefixWord ++ tailWord_53875) baseStart_53875 baseEnd_53875 := by
    simpa [prefixWord, tailWord_53875, baseEnd_53875] using wordTrace_append hprefix tailTrace_53875
  have hstable : (prefixWord ++ tailWord_53875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53875).length < 2 ^ (prefixWord ++ tailWord_53875).sum := by decide
  have hdescent : baseEnd_53875 < baseStart_53875 := by decide
  rcases family_descends (prefixWord ++ tailWord_53875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53889 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_53889 : Nat := 118140960795 + 53889 * 2 ^ 59
def prefixEnd_53889 : Nat := 4983230072969 + 3 ^ 40 * 53889 * 2
def baseEnd_53889 : Nat := 27670958990244892739675

theorem tailTrace_53889 : CollatzResearch.WordTrace tailWord_53889 prefixEnd_53889 27670958990244892739675 := by
  unfold tailWord_53889
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965493301776831353580721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1310328867851220902387147 1965493301776831353580721)
  ·
    refine ⟨1474119976332623515185541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1965493301776831353580721 1474119976332623515185541)
    ·
      refine ⟨276397495562366909097289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1474119976332623515185541 276397495562366909097289)
      ·
        refine ⟨207298121671775181822967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276397495562366909097289 207298121671775181822967)
        ·
          refine ⟨310947182507662772734451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207298121671775181822967 310947182507662772734451)
          ·
            refine ⟨466420773761494159101677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310947182507662772734451 466420773761494159101677)
            ·
              refine ⟨174907790160560309663129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466420773761494159101677 174907790160560309663129)
              ·
                refine ⟨131180842620420232247347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174907790160560309663129 131180842620420232247347)
                ·
                  refine ⟨196771263930630348371021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131180842620420232247347 196771263930630348371021)
                  ·
                    refine ⟨73789223973986380639133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196771263930630348371021 73789223973986380639133)
                    ·
                      refine ⟨27670958990244892739675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 73789223973986380639133 27670958990244892739675)
                      ·
                        rfl

theorem cell23_53889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_53889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53889 prefixEnd_53889 := by exact prefixLift 53889
  have htrace : WordTrace (prefixWord ++ tailWord_53889) baseStart_53889 baseEnd_53889 := by
    simpa [prefixWord, tailWord_53889, baseEnd_53889] using wordTrace_append hprefix tailTrace_53889
  have hstable : (prefixWord ++ tailWord_53889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53889).length < 2 ^ (prefixWord ++ tailWord_53889).sum := by decide
  have hdescent : baseEnd_53889 < baseStart_53889 := by decide
  rcases family_descends (prefixWord ++ tailWord_53889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53912 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_53912 : Nat := 118140960795 + 53912 * 2 ^ 59
def prefixEnd_53912 : Nat := 4983230072969 + 3 ^ 40 * 53912 * 2
def baseEnd_53912 : Nat := 27682769045298302752069

theorem tailTrace_53912 : CollatzResearch.WordTrace tailWord_53912 prefixEnd_53912 27682769045298302752069 := by
  unfold tailWord_53912
  simp only [CollatzResearch.WordTrace]
  refine ⟨983166090346753140833995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1310888120462337521111993 983166090346753140833995)
  ·
    refine ⟨1474749135520129711250993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 983166090346753140833995 1474749135520129711250993)
    ·
      refine ⟨1106061851640097283438245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1474749135520129711250993 1106061851640097283438245)
      ·
        refine ⟨207386597182518240644671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1106061851640097283438245 207386597182518240644671)
        ·
          refine ⟨311079895773777360967007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207386597182518240644671 311079895773777360967007)
          ·
            refine ⟨466619843660666041450511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311079895773777360967007 466619843660666041450511)
            ·
              refine ⟨699929765490999062175767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466619843660666041450511 699929765490999062175767)
              ·
                refine ⟨1049894648236498593263651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699929765490999062175767 1049894648236498593263651)
                ·
                  refine ⟨1574841972354747889895477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049894648236498593263651 1574841972354747889895477)
                  ·
                    refine ⟨147641434908257614677701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1574841972354747889895477 147641434908257614677701)
                    ·
                      refine ⟨27682769045298302752069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 147641434908257614677701 27682769045298302752069)
                      ·
                        rfl

theorem cell23_53912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_53912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53912 prefixEnd_53912 := by exact prefixLift 53912
  have htrace : WordTrace (prefixWord ++ tailWord_53912) baseStart_53912 baseEnd_53912 := by
    simpa [prefixWord, tailWord_53912, baseEnd_53912] using wordTrace_append hprefix tailTrace_53912
  have hstable : (prefixWord ++ tailWord_53912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53912).length < 2 ^ (prefixWord ++ tailWord_53912).sum := by decide
  have hdescent : baseEnd_53912 < baseStart_53912 := by decide
  rcases family_descends (prefixWord ++ tailWord_53912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53916 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_53916 : Nat := 118140960795 + 53916 * 2 ^ 59
def prefixEnd_53916 : Nat := 4983230072969 + 3 ^ 40 * 53916 * 2
def baseEnd_53916 : Nat := 27684822967916287102051

theorem tailTrace_53916 : CollatzResearch.WordTrace tailWord_53916 prefixEnd_53916 27684822967916287102051 := by
  unfold tailWord_53916
  simp only [CollatzResearch.WordTrace]
  refine ⟨983239036339507482406801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1310985381786009976542401 983239036339507482406801)
  ·
    refine ⟨737429277254630611805101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 983239036339507482406801 737429277254630611805101)
    ·
      refine ⟨276535978970486479426913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 737429277254630611805101 276535978970486479426913)
      ·
        refine ⟨207401984227864859570185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276535978970486479426913 207401984227864859570185)
        ·
          refine ⟨155551488170898644677639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207401984227864859570185 155551488170898644677639)
          ·
            refine ⟨233327232256347967016459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155551488170898644677639 233327232256347967016459)
            ·
              refine ⟨349990848384521950524689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233327232256347967016459 349990848384521950524689)
              ·
                refine ⟨262493136288391462893517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349990848384521950524689 262493136288391462893517)
                ·
                  refine ⟨98434926108146798585069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262493136288391462893517 98434926108146798585069)
                  ·
                    refine ⟨36913097290555049469401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98434926108146798585069 36913097290555049469401)
                    ·
                      refine ⟨27684822967916287102051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36913097290555049469401 27684822967916287102051)
                      ·
                        rfl

theorem cell23_53916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_53916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53916 prefixEnd_53916 := by exact prefixLift 53916
  have htrace : WordTrace (prefixWord ++ tailWord_53916) baseStart_53916 baseEnd_53916 := by
    simpa [prefixWord, tailWord_53916, baseEnd_53916] using wordTrace_append hprefix tailTrace_53916
  have hstable : (prefixWord ++ tailWord_53916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53916).length < 2 ^ (prefixWord ++ tailWord_53916).sum := by decide
  have hdescent : baseEnd_53916 < baseStart_53916 := by decide
  rcases family_descends (prefixWord ++ tailWord_53916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53929 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 1, 4, 2]
def baseStart_53929 : Nat := 118140960795 + 53929 * 2 ^ 59
def prefixEnd_53929 : Nat := 4983230072969 + 3 ^ 40 * 53929 * 2
def baseEnd_53929 : Nat := 27691498216424736239491

theorem tailTrace_53929 : CollatzResearch.WordTrace tailWord_53929 prefixEnd_53929 27691498216424736239491 := by
  unfold tailWord_53929
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966952221631918185036841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1311301481087945456691227 1966952221631918185036841)
  ·
    refine ⟨1475214166223938638777631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1966952221631918185036841 1475214166223938638777631)
    ·
      refine ⟨2212821249335907958166447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475214166223938638777631 2212821249335907958166447)
      ·
        refine ⟨3319231874003861937249671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212821249335907958166447 3319231874003861937249671)
        ·
          refine ⟨4978847811005792905874507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319231874003861937249671 4978847811005792905874507)
          ·
            refine ⟨7468271716508689358811761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978847811005792905874507 7468271716508689358811761)
            ·
              refine ⟨5601203787381517019108821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7468271716508689358811761 5601203787381517019108821)
              ·
                refine ⟨131278213766754305135363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5601203787381517019108821 131278213766754305135363)
                ·
                  refine ⟨196917320650131457703045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131278213766754305135363 196917320650131457703045)
                  ·
                    refine ⟨36921997621899648319321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196917320650131457703045 36921997621899648319321)
                    ·
                      refine ⟨27691498216424736239491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36921997621899648319321 27691498216424736239491)
                      ·
                        rfl

theorem cell23_53929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 4, 2].length) (baseStart_53929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53929 prefixEnd_53929 := by exact prefixLift 53929
  have htrace : WordTrace (prefixWord ++ tailWord_53929) baseStart_53929 baseEnd_53929 := by
    simpa [prefixWord, tailWord_53929, baseEnd_53929] using wordTrace_append hprefix tailTrace_53929
  have hstable : (prefixWord ++ tailWord_53929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53929).length < 2 ^ (prefixWord ++ tailWord_53929).sum := by decide
  have hdescent : baseEnd_53929 < baseStart_53929 := by decide
  rcases family_descends (prefixWord ++ tailWord_53929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53946 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2]
def baseStart_53946 : Nat := 118140960795 + 53946 * 2 ^ 59
def prefixEnd_53946 : Nat := 4983230072969 + 3 ^ 40 * 53946 * 2
def baseEnd_53946 : Nat := 27700227387551169726913

theorem tailTrace_53946 : CollatzResearch.WordTrace tailWord_53946 prefixEnd_53946 27700227387551169726913 := by
  unfold tailWord_53946
  simp only [CollatzResearch.WordTrace]
  refine ⟨491893065642582522101423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1311714841713553392270461 491893065642582522101423)
  ·
    refine ⟨737839598463873783152135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 491893065642582522101423 737839598463873783152135)
    ·
      refine ⟨1106759397695810674728203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737839598463873783152135 1106759397695810674728203)
      ·
        refine ⟨1660139096543716012092305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106759397695810674728203 1660139096543716012092305)
        ·
          refine ⟨1245104322407787009069229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660139096543716012092305 1245104322407787009069229)
          ·
            refine ⟨466914120902920128400961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245104322407787009069229 466914120902920128400961)
            ·
              refine ⟨350185590677190096300721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466914120902920128400961 350185590677190096300721)
              ·
                refine ⟨262639193007892572225541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350185590677190096300721 262639193007892572225541)
                ·
                  refine ⟨49244848688979857292289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262639193007892572225541 49244848688979857292289)
                  ·
                    refine ⟨36933636516734892969217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49244848688979857292289 36933636516734892969217)
                    ·
                      refine ⟨27700227387551169726913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36933636516734892969217 27700227387551169726913)
                      ·
                        rfl

theorem cell23_53946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_53946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53946 prefixEnd_53946 := by exact prefixLift 53946
  have htrace : WordTrace (prefixWord ++ tailWord_53946) baseStart_53946 baseEnd_53946 := by
    simpa [prefixWord, tailWord_53946, baseEnd_53946] using wordTrace_append hprefix tailTrace_53946
  have hstable : (prefixWord ++ tailWord_53946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53946).length < 2 ^ (prefixWord ++ tailWord_53946).sum := by decide
  have hdescent : baseEnd_53946 < baseStart_53946 := by decide
  rcases family_descends (prefixWord ++ tailWord_53946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53969 : List Nat := [1, 2, 2, 1, 2, 3, 1, 6, 5]
def baseStart_53969 : Nat := 118140960795 + 53969 * 2 ^ 59
def prefixEnd_53969 : Nat := 4983230072969 + 3 ^ 40 * 53969 * 2
def baseEnd_53969 : Nat := 3079115271400508859923

theorem tailTrace_53969 : CollatzResearch.WordTrace tailWord_53969 prefixEnd_53969 3079115271400508859923 := by
  unfold tailWord_53969
  simp only [CollatzResearch.WordTrace]
  refine ⟨1968411141487005016492961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1312274094324670010995307 1968411141487005016492961)
  ·
    refine ⟨1476308356115253762369721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1968411141487005016492961 1476308356115253762369721)
    ·
      refine ⟨1107231267086440321777291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1476308356115253762369721 1107231267086440321777291)
      ·
        refine ⟨1660846900629660482665937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107231267086440321777291 1660846900629660482665937)
        ·
          refine ⟨1245635175472245361999453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660846900629660482665937 1245635175472245361999453)
          ·
            refine ⟨467113190802092010749795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245635175472245361999453 467113190802092010749795)
            ·
              refine ⟨700669786203138016124693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467113190802092010749795 700669786203138016124693)
              ·
                refine ⟨32843896228272094505845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 700669786203138016124693 32843896228272094505845)
                ·
                  refine ⟨3079115271400508859923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32843896228272094505845 3079115271400508859923)
                  ·
                    rfl

theorem cell23_53969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 5].length) (baseStart_53969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53969 prefixEnd_53969 := by exact prefixLift 53969
  have htrace : WordTrace (prefixWord ++ tailWord_53969) baseStart_53969 baseEnd_53969 := by
    simpa [prefixWord, tailWord_53969, baseEnd_53969] using wordTrace_append hprefix tailTrace_53969
  have hstable : (prefixWord ++ tailWord_53969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53969).length < 2 ^ (prefixWord ++ tailWord_53969).sum := by decide
  have hdescent : baseEnd_53969 < baseStart_53969 := by decide
  rcases family_descends (prefixWord ++ tailWord_53969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53980 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_53980 : Nat := 118140960795 + 53980 * 2 ^ 59
def prefixEnd_53980 : Nat := 4983230072969 + 3 ^ 40 * 53980 * 2
def baseEnd_53980 : Nat := 27717685729804036701757

theorem tailTrace_53980 : CollatzResearch.WordTrace tailWord_53980 prefixEnd_53980 27717685729804036701757 := by
  unfold tailWord_53980
  simp only [CollatzResearch.WordTrace]
  refine ⟨984406172223576947571697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1312541562964769263428929 984406172223576947571697)
  ·
    refine ⟨738304629167682710678773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 984406172223576947571697 738304629167682710678773)
    ·
      refine ⟨69216058984470254126135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 738304629167682710678773 69216058984470254126135)
      ·
        refine ⟨103824088476705381189203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69216058984470254126135 103824088476705381189203)
        ·
          refine ⟨155736132715058071783805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103824088476705381189203 155736132715058071783805)
          ·
            refine ⟨58401049768146776918927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155736132715058071783805 58401049768146776918927)
            ·
              refine ⟨87601574652220165378391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58401049768146776918927 87601574652220165378391)
              ·
                refine ⟨131402361978330248067587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87601574652220165378391 131402361978330248067587)
                ·
                  refine ⟨197103542967495372101381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131402361978330248067587 197103542967495372101381)
                  ·
                    refine ⟨36956914306405382269009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197103542967495372101381 36956914306405382269009)
                    ·
                      refine ⟨27717685729804036701757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 36956914306405382269009 27717685729804036701757)
                      ·
                        rfl

theorem cell23_53980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_53980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_53980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_53980 prefixEnd_53980 := by exact prefixLift 53980
  have htrace : WordTrace (prefixWord ++ tailWord_53980) baseStart_53980 baseEnd_53980 := by
    simpa [prefixWord, tailWord_53980, baseEnd_53980] using wordTrace_append hprefix tailTrace_53980
  have hstable : (prefixWord ++ tailWord_53980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53980).length < 2 ^ (prefixWord ++ tailWord_53980).sum := by decide
  have hdescent : baseEnd_53980 < baseStart_53980 := by decide
  rcases family_descends (prefixWord ++ tailWord_53980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54089 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 3, 5]
def baseStart_54089 : Nat := 118140960795 + 54089 * 2 ^ 59
def prefixEnd_54089 : Nat := 4983230072969 + 3 ^ 40 * 54089 * 2
def baseEnd_54089 : Nat := 9257885040381370079585

theorem tailTrace_54089 : CollatzResearch.WordTrace tailWord_54089 prefixEnd_54089 9257885040381370079585 := by
  unfold tailWord_54089
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972787901052265510861321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1315191934034843673907547 1972787901052265510861321)
  ·
    refine ⟨1479590925789199133145991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1972787901052265510861321 1479590925789199133145991)
    ·
      refine ⟨2219386388683798699718987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479590925789199133145991 2219386388683798699718987)
      ·
        refine ⟨3329079583025698049578481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219386388683798699718987 3329079583025698049578481)
        ·
          refine ⟨2496809687269273537183861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329079583025698049578481 2496809687269273537183861)
          ·
            refine ⟨234075908181494394110987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2496809687269273537183861 234075908181494394110987)
            ·
              refine ⟨351113862272241591166481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234075908181494394110987 351113862272241591166481)
              ·
                refine ⟨263335396704181193374861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351113862272241591166481 263335396704181193374861)
                ·
                  refine ⟨98750773764067947515573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263335396704181193374861 98750773764067947515573)
                  ·
                    refine ⟨9257885040381370079585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98750773764067947515573 9257885040381370079585)
                    ·
                      rfl

theorem cell23_54089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_54089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54089 prefixEnd_54089 := by exact prefixLift 54089
  have htrace : WordTrace (prefixWord ++ tailWord_54089) baseStart_54089 baseEnd_54089 := by
    simpa [prefixWord, tailWord_54089, baseEnd_54089] using wordTrace_append hprefix tailTrace_54089
  have hstable : (prefixWord ++ tailWord_54089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54089).length < 2 ^ (prefixWord ++ tailWord_54089).sum := by decide
  have hdescent : baseEnd_54089 < baseStart_54089 := by decide
  rcases family_descends (prefixWord ++ tailWord_54089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54096 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 4, 3, 2]
def baseStart_54096 : Nat := 118140960795 + 54096 * 2 ^ 59
def prefixEnd_54096 : Nat := 4983230072969 + 3 ^ 40 * 54096 * 2
def baseEnd_54096 : Nat := 27777249485725582851223

theorem tailTrace_54096 : CollatzResearch.WordTrace tailWord_54096 prefixEnd_54096 27777249485725582851223 := by
  unfold tailWord_54096
  simp only [CollatzResearch.WordTrace]
  refine ⟨986521606013452853183071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1315362141351270470910761 986521606013452853183071)
  ·
    refine ⟨1479782409020179279774607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986521606013452853183071 1479782409020179279774607)
    ·
      refine ⟨2219673613530268919661911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479782409020179279774607 2219673613530268919661911)
      ·
        refine ⟨3329510420295403379492867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219673613530268919661911 3329510420295403379492867)
        ·
          refine ⟨4994265630443105069239301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329510420295403379492867 4994265630443105069239301)
          ·
            refine ⟨936424805708082200482369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4994265630443105069239301 936424805708082200482369)
            ·
              refine ⟨702318604281061650361777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936424805708082200482369 702318604281061650361777)
              ·
                refine ⟨526738953210796237771333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702318604281061650361777 526738953210796237771333)
                ·
                  refine ⟨98763553727024294582125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526738953210796237771333 98763553727024294582125)
                  ·
                    refine ⟨37036332647634110468297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98763553727024294582125 37036332647634110468297)
                    ·
                      refine ⟨27777249485725582851223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37036332647634110468297 27777249485725582851223)
                      ·
                        rfl

theorem cell23_54096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 3, 2].length) (baseStart_54096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54096 prefixEnd_54096 := by exact prefixLift 54096
  have htrace : WordTrace (prefixWord ++ tailWord_54096) baseStart_54096 baseEnd_54096 := by
    simpa [prefixWord, tailWord_54096, baseEnd_54096] using wordTrace_append hprefix tailTrace_54096
  have hstable : (prefixWord ++ tailWord_54096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54096).length < 2 ^ (prefixWord ++ tailWord_54096).sum := by decide
  have hdescent : baseEnd_54096 < baseStart_54096 := by decide
  rcases family_descends (prefixWord ++ tailWord_54096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54103 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_54103 : Nat := 118140960795 + 54103 * 2 ^ 59
def prefixEnd_54103 : Nat := 4983230072969 + 3 ^ 40 * 54103 * 2
def baseEnd_54103 : Nat := 27780843850307055463691

theorem tailTrace_54103 : CollatzResearch.WordTrace tailWord_54103 prefixEnd_54103 27780843850307055463691 := by
  unfold tailWord_54103
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973298523001545901870963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1315532348667697267913975 1973298523001545901870963)
  ·
    refine ⟨2959947784502318852806445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973298523001545901870963 2959947784502318852806445)
    ·
      refine ⟨1109980419188369569802417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2959947784502318852806445 1109980419188369569802417)
      ·
        refine ⟨832485314391277177351813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1109980419188369569802417 832485314391277177351813)
        ·
          refine ⟨156090996448364470753465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 832485314391277177351813 156090996448364470753465)
          ·
            refine ⟨117068247336273353065099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156090996448364470753465 117068247336273353065099)
            ·
              refine ⟨175602371004410029597649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117068247336273353065099 175602371004410029597649)
              ·
                refine ⟨131701778253307522198237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175602371004410029597649 131701778253307522198237)
                ·
                  refine ⟨49388166844990320824339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131701778253307522198237 49388166844990320824339)
                  ·
                    refine ⟨74082250267485481236509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49388166844990320824339 74082250267485481236509)
                    ·
                      refine ⟨27780843850307055463691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74082250267485481236509 27780843850307055463691)
                      ·
                        rfl

theorem cell23_54103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_54103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54103 prefixEnd_54103 := by exact prefixLift 54103
  have htrace : WordTrace (prefixWord ++ tailWord_54103) baseStart_54103 baseEnd_54103 := by
    simpa [prefixWord, tailWord_54103, baseEnd_54103] using wordTrace_append hprefix tailTrace_54103
  have hstable : (prefixWord ++ tailWord_54103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54103).length < 2 ^ (prefixWord ++ tailWord_54103).sum := by decide
  have hdescent : baseEnd_54103 < baseStart_54103 := by decide
  rcases family_descends (prefixWord ++ tailWord_54103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54120 : List Nat := [2, 1, 4, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_54120 : Nat := 118140960795 + 54120 * 2 ^ 59
def prefixEnd_54120 : Nat := 4983230072969 + 3 ^ 40 * 54120 * 2
def baseEnd_54120 : Nat := 27789573021433488951113

theorem tailTrace_54120 : CollatzResearch.WordTrace tailWord_54120 prefixEnd_54120 27789573021433488951113 := by
  unfold tailWord_54120
  simp only [CollatzResearch.WordTrace]
  refine ⟨986959281969978902619907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1315945709293305203493209 986959281969978902619907)
  ·
    refine ⟨1480438922954968353929861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986959281969978902619907 1480438922954968353929861)
    ·
      refine ⟨277582298054056566361849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1480438922954968353929861 277582298054056566361849)
      ·
        refine ⟨208186723540542424771387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277582298054056566361849 208186723540542424771387)
        ·
          refine ⟨312280085310813637157081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208186723540542424771387 312280085310813637157081)
          ·
            refine ⟨234210063983110227867811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312280085310813637157081 234210063983110227867811)
            ·
              refine ⟨351315095974665341801717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234210063983110227867811 351315095974665341801717)
              ·
                refine ⟨32935790247624875793911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351315095974665341801717 32935790247624875793911)
                ·
                  refine ⟨49403685371437313690867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32935790247624875793911 49403685371437313690867)
                  ·
                    refine ⟨74105528057155970536301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49403685371437313690867 74105528057155970536301)
                    ·
                      refine ⟨27789573021433488951113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74105528057155970536301 27789573021433488951113)
                      ·
                        rfl

theorem cell23_54120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_54120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54120 prefixEnd_54120 := by exact prefixLift 54120
  have htrace : WordTrace (prefixWord ++ tailWord_54120) baseStart_54120 baseEnd_54120 := by
    simpa [prefixWord, tailWord_54120, baseEnd_54120] using wordTrace_append hprefix tailTrace_54120
  have hstable : (prefixWord ++ tailWord_54120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54120).length < 2 ^ (prefixWord ++ tailWord_54120).sum := by decide
  have hdescent : baseEnd_54120 < baseStart_54120 := by decide
  rcases family_descends (prefixWord ++ tailWord_54120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54136 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 2, 4]
def baseStart_54136 : Nat := 118140960795 + 54136 * 2 ^ 59
def prefixEnd_54136 : Nat := 4983230072969 + 3 ^ 40 * 54136 * 2
def baseEnd_54136 : Nat := 9265929570635142117013

theorem tailTrace_54136 : CollatzResearch.WordTrace tailWord_54136 prefixEnd_54136 9265929570635142117013 := by
  unfold tailWord_54136
  simp only [CollatzResearch.WordTrace]
  refine ⟨987251065940996268911131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1316334754587995025214841 987251065940996268911131)
  ·
    refine ⟨1480876598911494403366697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 987251065940996268911131 1480876598911494403366697)
    ·
      refine ⟨1110657449183620802525023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1480876598911494403366697 1110657449183620802525023)
      ·
        refine ⟨1665986173775431203787535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110657449183620802525023 1665986173775431203787535)
        ·
          refine ⟨2498979260663146805681303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665986173775431203787535 2498979260663146805681303)
          ·
            refine ⟨3748468890994720208521955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498979260663146805681303 3748468890994720208521955)
            ·
              refine ⟨5622703336492080312782933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748468890994720208521955 5622703336492080312782933)
              ·
                refine ⟨65891054724516566165425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5622703336492080312782933 65891054724516566165425)
                ·
                  refine ⟨49418291043387424624069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65891054724516566165425 49418291043387424624069)
                  ·
                    refine ⟨9265929570635142117013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49418291043387424624069 9265929570635142117013)
                    ·
                      rfl

theorem cell23_54136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_54136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54136 prefixEnd_54136 := by exact prefixLift 54136
  have htrace : WordTrace (prefixWord ++ tailWord_54136) baseStart_54136 baseEnd_54136 := by
    simpa [prefixWord, tailWord_54136, baseEnd_54136] using wordTrace_append hprefix tailTrace_54136
  have hstable : (prefixWord ++ tailWord_54136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54136).length < 2 ^ (prefixWord ++ tailWord_54136).sum := by decide
  have hdescent : baseEnd_54136 < baseStart_54136 := by decide
  rcases family_descends (prefixWord ++ tailWord_54136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54139 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4]
def baseStart_54139 : Nat := 118140960795 + 54139 * 2 ^ 59
def prefixEnd_54139 : Nat := 4983230072969 + 3 ^ 40 * 54139 * 2
def baseEnd_54139 : Nat := 27799329153868914613525

theorem tailTrace_54139 : CollatzResearch.WordTrace tailWord_54139 prefixEnd_54139 27799329153868914613525 := by
  unfold tailWord_54139
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974611550871124050181471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1316407700580749366787647 1974611550871124050181471)
  ·
    refine ⟨2961917326306686075272207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974611550871124050181471 2961917326306686075272207)
    ·
      refine ⟨4442875989460029112908311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961917326306686075272207 4442875989460029112908311)
      ·
        refine ⟨6664313984190043669362467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442875989460029112908311 6664313984190043669362467)
        ·
          refine ⟨9996470976285065504043701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664313984190043669362467 9996470976285065504043701)
          ·
            refine ⟨937169154026724891004097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9996470976285065504043701 937169154026724891004097)
            ·
              refine ⟨702876865520043668253073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937169154026724891004097 702876865520043668253073)
              ·
                refine ⟨527157649140032751189805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702876865520043668253073 527157649140032751189805)
                ·
                  refine ⟨197684118427512281696177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527157649140032751189805 197684118427512281696177)
                  ·
                    refine ⟨148263088820634211272133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197684118427512281696177 148263088820634211272133)
                    ·
                      refine ⟨27799329153868914613525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 148263088820634211272133 27799329153868914613525)
                      ·
                        rfl

theorem cell23_54139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_54139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54139 prefixEnd_54139 := by exact prefixLift 54139
  have htrace : WordTrace (prefixWord ++ tailWord_54139) baseStart_54139 baseEnd_54139 := by
    simpa [prefixWord, tailWord_54139, baseEnd_54139] using wordTrace_append hprefix tailTrace_54139
  have hstable : (prefixWord ++ tailWord_54139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54139).length < 2 ^ (prefixWord ++ tailWord_54139).sum := by decide
  have hdescent : baseEnd_54139 < baseStart_54139 := by decide
  rcases family_descends (prefixWord ++ tailWord_54139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54143 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 3, 2, 2]
def baseStart_54143 : Nat := 118140960795 + 54143 * 2 ^ 59
def prefixEnd_54143 : Nat := 4983230072969 + 3 ^ 40 * 54143 * 2
def baseEnd_54143 : Nat := 27801383076486898963507

theorem tailTrace_54143 : CollatzResearch.WordTrace tailWord_54143 prefixEnd_54143 27801383076486898963507 := by
  unfold tailWord_54143
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974757442856632733327083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1316504961904421822218055 1974757442856632733327083)
  ·
    refine ⟨2962136164284949099990625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974757442856632733327083 2962136164284949099990625)
    ·
      refine ⟨2221602123213711824992969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2962136164284949099990625 2221602123213711824992969)
      ·
        refine ⟨1666201592410283868744727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2221602123213711824992969 1666201592410283868744727)
        ·
          refine ⟨2499302388615425803117091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666201592410283868744727 2499302388615425803117091)
          ·
            refine ⟨3748953582923138704675637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499302388615425803117091 3748953582923138704675637)
            ·
              refine ⟨351464398399044253563341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3748953582923138704675637 351464398399044253563341)
              ·
                refine ⟨131799149399641595086253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351464398399044253563341 131799149399641595086253)
                ·
                  refine ⟨49424681024865598157345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131799149399641595086253 49424681024865598157345)
                  ·
                    refine ⟨37068510768649198618009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49424681024865598157345 37068510768649198618009)
                    ·
                      refine ⟨27801383076486898963507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37068510768649198618009 27801383076486898963507)
                      ·
                        rfl

theorem cell23_54143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_54143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54143 prefixEnd_54143 := by exact prefixLift 54143
  have htrace : WordTrace (prefixWord ++ tailWord_54143) baseStart_54143 baseEnd_54143 := by
    simpa [prefixWord, tailWord_54143, baseEnd_54143] using wordTrace_append hprefix tailTrace_54143
  have hstable : (prefixWord ++ tailWord_54143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54143).length < 2 ^ (prefixWord ++ tailWord_54143).sum := by decide
  have hdescent : baseEnd_54143 < baseStart_54143 := by decide
  rcases family_descends (prefixWord ++ tailWord_54143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54156 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_54156 : Nat := 118140960795 + 54156 * 2 ^ 59
def prefixEnd_54156 : Nat := 4983230072969 + 3 ^ 40 * 54156 * 2
def baseEnd_54156 : Nat := 27808058324995348100947

theorem tailTrace_54156 : CollatzResearch.WordTrace tailWord_54156 prefixEnd_54156 27808058324995348100947 := by
  unfold tailWord_54156
  simp only [CollatzResearch.WordTrace]
  refine ⟨987615795904767976775161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1316821061206357302366881 987615795904767976775161)
  ·
    refine ⟨740711846928575982581371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 987615795904767976775161 740711846928575982581371)
    ·
      refine ⟨1111067770392863973872057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740711846928575982581371 1111067770392863973872057)
      ·
        refine ⟨833300827794647980404043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1111067770392863973872057 833300827794647980404043)
        ·
          refine ⟨1249951241691971970606065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833300827794647980404043 1249951241691971970606065)
          ·
            refine ⟨937463431268978977954549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249951241691971970606065 937463431268978977954549)
            ·
              refine ⟨87887196681466779183239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 937463431268978977954549 87887196681466779183239)
              ·
                refine ⟨131830795022200168774859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87887196681466779183239 131830795022200168774859)
                ·
                  refine ⟨197746192533300253162289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131830795022200168774859 197746192533300253162289)
                  ·
                    refine ⟨148309644399975189871717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197746192533300253162289 148309644399975189871717)
                    ·
                      refine ⟨27808058324995348100947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 148309644399975189871717 27808058324995348100947)
                      ·
                        rfl

theorem cell23_54156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_54156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54156 prefixEnd_54156 := by exact prefixLift 54156
  have htrace : WordTrace (prefixWord ++ tailWord_54156) baseStart_54156 baseEnd_54156 := by
    simpa [prefixWord, tailWord_54156, baseEnd_54156] using wordTrace_append hprefix tailTrace_54156
  have hstable : (prefixWord ++ tailWord_54156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54156).length < 2 ^ (prefixWord ++ tailWord_54156).sum := by decide
  have hdescent : baseEnd_54156 < baseStart_54156 := by decide
  rcases family_descends (prefixWord ++ tailWord_54156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54176 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3]
def baseStart_54176 : Nat := 118140960795 + 54176 * 2 ^ 59
def prefixEnd_54176 : Nat := 4983230072969 + 3 ^ 40 * 54176 * 2
def baseEnd_54176 : Nat := 27818327938085269850855

theorem tailTrace_54176 : CollatzResearch.WordTrace tailWord_54176 prefixEnd_54176 27818327938085269850855 := by
  unfold tailWord_54176
  simp only [CollatzResearch.WordTrace]
  refine ⟨987980525868539684639191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1317307367824719579518921 987980525868539684639191)
  ·
    refine ⟨1481970788802809526958787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 987980525868539684639191 1481970788802809526958787)
    ·
      refine ⟨2222956183204214290438181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1481970788802809526958787 2222956183204214290438181)
      ·
        refine ⟨416804284350790179457159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2222956183204214290438181 416804284350790179457159)
        ·
          refine ⟨625206426526185269185739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416804284350790179457159 625206426526185269185739)
          ·
            refine ⟨937809639789277903778609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625206426526185269185739 937809639789277903778609)
            ·
              refine ⟨703357229841958427833957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937809639789277903778609 703357229841958427833957)
              ·
                refine ⟨131879480595367205218867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 703357229841958427833957 131879480595367205218867)
                ·
                  refine ⟨197819220893050807828301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131879480595367205218867 197819220893050807828301)
                  ·
                    refine ⟨74182207834894052935613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197819220893050807828301 74182207834894052935613)
                    ·
                      refine ⟨27818327938085269850855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74182207834894052935613 27818327938085269850855)
                      ·
                        rfl

theorem cell23_54176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_54176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54176 prefixEnd_54176 := by exact prefixLift 54176
  have htrace : WordTrace (prefixWord ++ tailWord_54176) baseStart_54176 baseEnd_54176 := by
    simpa [prefixWord, tailWord_54176, baseEnd_54176] using wordTrace_append hprefix tailTrace_54176
  have hstable : (prefixWord ++ tailWord_54176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54176).length < 2 ^ (prefixWord ++ tailWord_54176).sum := by decide
  have hdescent : baseEnd_54176 < baseStart_54176 := by decide
  rcases family_descends (prefixWord ++ tailWord_54176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54183 : List Nat := [1, 1, 6, 1, 4, 1, 9]
def baseStart_54183 : Nat := 118140960795 + 54183 * 2 ^ 59
def prefixEnd_54183 : Nat := 4983230072969 + 3 ^ 40 * 54183 * 2
def baseEnd_54183 : Nat := 343480522255144968683

theorem tailTrace_54183 : CollatzResearch.WordTrace tailWord_54183 prefixEnd_54183 343480522255144968683 := by
  unfold tailWord_54183
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976216362711719564783203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1317477575141146376522135 1976216362711719564783203)
  ·
    refine ⟨2964324544067579347174805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1976216362711719564783203 2964324544067579347174805)
    ·
      refine ⟨138952713003167781898819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2964324544067579347174805 138952713003167781898819)
      ·
        refine ⟨208429069504751672848229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138952713003167781898819 208429069504751672848229)
        ·
          refine ⟨39080450532140938659043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208429069504751672848229 39080450532140938659043)
          ·
            refine ⟨58620675798211407988565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39080450532140938659043 58620675798211407988565)
            ·
              refine ⟨343480522255144968683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 58620675798211407988565 343480522255144968683)
              ·
                rfl

theorem cell23_54183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 9].length) (baseStart_54183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54183 prefixEnd_54183 := by exact prefixLift 54183
  have htrace : WordTrace (prefixWord ++ tailWord_54183) baseStart_54183 baseEnd_54183 := by
    simpa [prefixWord, tailWord_54183, baseEnd_54183] using wordTrace_append hprefix tailTrace_54183
  have hstable : (prefixWord ++ tailWord_54183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54183).length < 2 ^ (prefixWord ++ tailWord_54183).sum := by decide
  have hdescent : baseEnd_54183 < baseStart_54183 := by decide
  rcases family_descends (prefixWord ++ tailWord_54183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54233 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 3, 4, 2]
def baseStart_54233 : Nat := 118140960795 + 54233 * 2 ^ 59
def prefixEnd_54233 : Nat := 4983230072969 + 3 ^ 40 * 54233 * 2
def baseEnd_54233 : Nat := 27847596335391546838093

theorem tailTrace_54233 : CollatzResearch.WordTrace tailWord_54233 prefixEnd_54233 27847596335391546838093 := by
  unfold tailWord_54233
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978040012530578104103353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1318693341687052069402235 1978040012530578104103353)
  ·
    refine ⟨1483530009397933578077515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1978040012530578104103353 1483530009397933578077515)
    ·
      refine ⟨2225295014096900367116273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483530009397933578077515 2225295014096900367116273)
      ·
        refine ⟨1668971260572675275337205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2225295014096900367116273 1668971260572675275337205)
        ·
          refine ⟨156466055678688307062863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1668971260572675275337205 156466055678688307062863)
          ·
            refine ⟨234699083518032460594295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156466055678688307062863 234699083518032460594295)
            ·
              refine ⟨352048625277048690891443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234699083518032460594295 352048625277048690891443)
              ·
                refine ⟨528072937915573036337165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352048625277048690891443 528072937915573036337165)
                ·
                  refine ⟨198027351718339888626437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528072937915573036337165 198027351718339888626437)
                  ·
                    refine ⟨37130128447188729117457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198027351718339888626437 37130128447188729117457)
                    ·
                      refine ⟨27847596335391546838093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37130128447188729117457 27847596335391546838093)
                      ·
                        rfl

theorem cell23_54233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_54233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54233 prefixEnd_54233 := by exact prefixLift 54233
  have htrace : WordTrace (prefixWord ++ tailWord_54233) baseStart_54233 baseEnd_54233 := by
    simpa [prefixWord, tailWord_54233, baseEnd_54233] using wordTrace_append hprefix tailTrace_54233
  have hstable : (prefixWord ++ tailWord_54233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54233).length < 2 ^ (prefixWord ++ tailWord_54233).sum := by decide
  have hdescent : baseEnd_54233 < baseStart_54233 := by decide
  rcases family_descends (prefixWord ++ tailWord_54233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54259 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8]
def baseStart_54259 : Nat := 118140960795 + 54259 * 2 ^ 59
def prefixEnd_54259 : Nat := 4983230072969 + 3 ^ 40 * 54259 * 2
def baseEnd_54259 : Nat := 27860946832408445112973

theorem tailTrace_54259 : CollatzResearch.WordTrace tailWord_54259 prefixEnd_54259 27860946832408445112973 := by
  unfold tailWord_54259
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978988310436384544549831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1319325540290923029699887 1978988310436384544549831)
  ·
    refine ⟨2968482465654576816824747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978988310436384544549831 2968482465654576816824747)
    ·
      refine ⟨4452723698481865225237121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968482465654576816824747 4452723698481865225237121)
      ·
        refine ⟨3339542773861398918927841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4452723698481865225237121 3339542773861398918927841)
        ·
          refine ⟨2504657080396049189195881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3339542773861398918927841 2504657080396049189195881)
          ·
            refine ⟨1878492810297036891896911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2504657080396049189195881 1878492810297036891896911)
            ·
              refine ⟨2817739215445555337845367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878492810297036891896911 2817739215445555337845367)
              ·
                refine ⟨4226608823168333006768051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817739215445555337845367 4226608823168333006768051)
                ·
                  refine ⟨6339913234752499510152077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4226608823168333006768051 6339913234752499510152077)
                  ·
                    refine ⟨2377467463032187316307029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6339913234752499510152077 2377467463032187316307029)
                    ·
                      refine ⟨27860946832408445112973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 2377467463032187316307029 27860946832408445112973)
                      ·
                        rfl

theorem cell23_54259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_54259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54259 prefixEnd_54259 := by exact prefixLift 54259
  have htrace : WordTrace (prefixWord ++ tailWord_54259) baseStart_54259 baseEnd_54259 := by
    simpa [prefixWord, tailWord_54259, baseEnd_54259] using wordTrace_append hprefix tailTrace_54259
  have hstable : (prefixWord ++ tailWord_54259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54259).length < 2 ^ (prefixWord ++ tailWord_54259).sum := by decide
  have hdescent : baseEnd_54259 < baseStart_54259 := by decide
  rcases family_descends (prefixWord ++ tailWord_54259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54301 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_54301 : Nat := 118140960795 + 54301 * 2 ^ 59
def prefixEnd_54301 : Nat := 4983230072969 + 3 ^ 40 * 54301 * 2
def baseEnd_54301 : Nat := 27882513019897280787781

theorem tailTrace_54301 : CollatzResearch.WordTrace tailWord_54301 prefixEnd_54301 27882513019897280787781 := by
  unfold tailWord_54301
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980520176284225717578757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1320346784189483811719171 1980520176284225717578757)
  ·
    refine ⟨371347533053292322046017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1980520176284225717578757 371347533053292322046017)
    ·
      refine ⟨278510649789969241534513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371347533053292322046017 278510649789969241534513)
      ·
        refine ⟨208882987342476931150885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278510649789969241534513 208882987342476931150885)
        ·
          refine ⟨39165560126714424590791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208882987342476931150885 39165560126714424590791)
          ·
            refine ⟨58748340190071636886187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39165560126714424590791 58748340190071636886187)
            ·
              refine ⟨88122510285107455329281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58748340190071636886187 88122510285107455329281)
              ·
                refine ⟨66091882713830591496961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88122510285107455329281 66091882713830591496961)
                ·
                  refine ⟨49568912035372943622721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66091882713830591496961 49568912035372943622721)
                  ·
                    refine ⟨37176684026529707717041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49568912035372943622721 37176684026529707717041)
                    ·
                      refine ⟨27882513019897280787781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37176684026529707717041 27882513019897280787781)
                      ·
                        rfl

theorem cell23_54301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_54301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54301 prefixEnd_54301 := by exact prefixLift 54301
  have htrace : WordTrace (prefixWord ++ tailWord_54301) baseStart_54301 baseEnd_54301 := by
    simpa [prefixWord, tailWord_54301, baseEnd_54301] using wordTrace_append hprefix tailTrace_54301
  have hstable : (prefixWord ++ tailWord_54301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54301).length < 2 ^ (prefixWord ++ tailWord_54301).sum := by decide
  have hdescent : baseEnd_54301 < baseStart_54301 := by decide
  rcases family_descends (prefixWord ++ tailWord_54301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54336 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_54336 : Nat := 118140960795 + 54336 * 2 ^ 59
def prefixEnd_54336 : Nat := 4983230072969 + 3 ^ 40 * 54336 * 2
def baseEnd_54336 : Nat := 27900484842804643850119

theorem tailTrace_54336 : CollatzResearch.WordTrace tailWord_54336 prefixEnd_54336 27900484842804643850119 := by
  unfold tailWord_54336
  simp only [CollatzResearch.WordTrace]
  refine ⟨990898365578713347551431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1321197820771617796735241 990898365578713347551431)
  ·
    refine ⟨1486347548368070021327147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990898365578713347551431 1486347548368070021327147)
    ·
      refine ⟨2229521322552105031990721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1486347548368070021327147 2229521322552105031990721)
      ·
        refine ⟨1672140991914078773993041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229521322552105031990721 1672140991914078773993041)
        ·
          refine ⟨1254105743935559080494781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1672140991914078773993041 1254105743935559080494781)
          ·
            refine ⟨470289653975834655185543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1254105743935559080494781 470289653975834655185543)
            ·
              refine ⟨705434480963751982778315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470289653975834655185543 705434480963751982778315)
              ·
                refine ⟨1058151721445627974167473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705434480963751982778315 1058151721445627974167473)
                ·
                  refine ⟨793613791084220980625605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058151721445627974167473 793613791084220980625605)
                  ·
                    refine ⟨148802585828291433867301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793613791084220980625605 148802585828291433867301)
                    ·
                      refine ⟨27900484842804643850119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 148802585828291433867301 27900484842804643850119)
                      ·
                        rfl

theorem cell23_54336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_54336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54336 prefixEnd_54336 := by exact prefixLift 54336
  have htrace : WordTrace (prefixWord ++ tailWord_54336) baseStart_54336 baseEnd_54336 := by
    simpa [prefixWord, tailWord_54336, baseEnd_54336] using wordTrace_append hprefix tailTrace_54336
  have hstable : (prefixWord ++ tailWord_54336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54336).length < 2 ^ (prefixWord ++ tailWord_54336).sum := by decide
  have hdescent : baseEnd_54336 < baseStart_54336 := by decide
  rcases family_descends (prefixWord ++ tailWord_54336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54343 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_54343 : Nat := 118140960795 + 54343 * 2 ^ 59
def prefixEnd_54343 : Nat := 4983230072969 + 3 ^ 40 * 54343 * 2
def baseEnd_54343 : Nat := 27904079207386116462587

theorem tailTrace_54343 : CollatzResearch.WordTrace tailWord_54343 prefixEnd_54343 27904079207386116462587 := by
  unfold tailWord_54343
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982052042132066890607683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1321368028088044593738455 1982052042132066890607683)
  ·
    refine ⟨2973078063198100335911525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1982052042132066890607683 2973078063198100335911525)
    ·
      refine ⟨557452136849643812983411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2973078063198100335911525 557452136849643812983411)
      ·
        refine ⟨836178205274465719475117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557452136849643812983411 836178205274465719475117)
        ·
          refine ⟨313566826977924644803169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 836178205274465719475117 313566826977924644803169)
          ·
            refine ⟨235175120233443483602377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313566826977924644803169 235175120233443483602377)
            ·
              refine ⟨176381340175082612701783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235175120233443483602377 176381340175082612701783)
              ·
                refine ⟨264572010262623919052675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176381340175082612701783 264572010262623919052675)
                ·
                  refine ⟨396858015393935878579013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264572010262623919052675 396858015393935878579013)
                  ·
                    refine ⟨74410877886362977233565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396858015393935878579013 74410877886362977233565)
                    ·
                      refine ⟨27904079207386116462587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74410877886362977233565 27904079207386116462587)
                      ·
                        rfl

theorem cell23_54343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_54343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54343 prefixEnd_54343 := by exact prefixLift 54343
  have htrace : WordTrace (prefixWord ++ tailWord_54343) baseStart_54343 baseEnd_54343 := by
    simpa [prefixWord, tailWord_54343, baseEnd_54343] using wordTrace_append hprefix tailTrace_54343
  have hstable : (prefixWord ++ tailWord_54343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54343).length < 2 ^ (prefixWord ++ tailWord_54343).sum := by decide
  have hdescent : baseEnd_54343 < baseStart_54343 := by decide
  rcases family_descends (prefixWord ++ tailWord_54343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54346 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 8]
def baseStart_54346 : Nat := 118140960795 + 54346 * 2 ^ 59
def prefixEnd_54346 : Nat := 4983230072969 + 3 ^ 40 * 54346 * 2
def baseEnd_54346 : Nat := 3100624405483289413897

theorem tailTrace_54346 : CollatzResearch.WordTrace tailWord_54346 prefixEnd_54346 3100624405483289413897 := by
  unfold tailWord_54346
  simp only [CollatzResearch.WordTrace]
  refine ⟨495540365280299600741723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1321440974080798935311261 495540365280299600741723)
  ·
    refine ⟨743310547920449401112585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 495540365280299600741723 743310547920449401112585)
    ·
      refine ⟨557482910940337050834439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 743310547920449401112585 557482910940337050834439)
      ·
        refine ⟨836224366410505576251659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557482910940337050834439 836224366410505576251659)
        ·
          refine ⟨1254336549615758364377489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836224366410505576251659 1254336549615758364377489)
          ·
            refine ⟨940752412211818773283117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254336549615758364377489 940752412211818773283117)
            ·
              refine ⟨352782154579432039981169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 940752412211818773283117 352782154579432039981169)
              ·
                refine ⟨264586615934574029985877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352782154579432039981169 264586615934574029985877)
                ·
                  refine ⟨3100624405483289413897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 264586615934574029985877 3100624405483289413897)
                  ·
                    rfl

theorem cell23_54346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_54346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54346 prefixEnd_54346 := by exact prefixLift 54346
  have htrace : WordTrace (prefixWord ++ tailWord_54346) baseStart_54346 baseEnd_54346 := by
    simpa [prefixWord, tailWord_54346, baseEnd_54346] using wordTrace_append hprefix tailTrace_54346
  have hstable : (prefixWord ++ tailWord_54346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54346).length < 2 ^ (prefixWord ++ tailWord_54346).sum := by decide
  have hdescent : baseEnd_54346 < baseStart_54346 := by decide
  rcases family_descends (prefixWord ++ tailWord_54346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54367 : List Nat := [1, 1, 2, 3, 1, 1, 7, 2, 1, 4]
def baseStart_54367 : Nat := 118140960795 + 54367 * 2 ^ 59
def prefixEnd_54367 : Nat := 4983230072969 + 3 ^ 40 * 54367 * 2
def baseEnd_54367 : Nat := 9305467581031340854159

theorem tailTrace_54367 : CollatzResearch.WordTrace tailWord_54367 prefixEnd_54367 9305467581031340854159 := by
  unfold tailWord_54367
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982927394045118989481355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1321951596030079326320903 1982927394045118989481355)
  ·
    refine ⟨2974391091067678484222033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1982927394045118989481355 2974391091067678484222033)
    ·
      refine ⟨2230793318300758863166525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2974391091067678484222033 2230793318300758863166525)
      ·
        refine ⟨836547494362784573687447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2230793318300758863166525 836547494362784573687447)
        ·
          refine ⟨1254821241544176860531171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836547494362784573687447 1254821241544176860531171)
          ·
            refine ⟨1882231862316265290796757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254821241544176860531171 1882231862316265290796757)
            ·
              refine ⟨44114809273037467753049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1882231862316265290796757 44114809273037467753049)
              ·
                refine ⟨33086106954778100814787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44114809273037467753049 33086106954778100814787)
                ·
                  refine ⟨49629160432167151222181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33086106954778100814787 49629160432167151222181)
                  ·
                    refine ⟨9305467581031340854159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49629160432167151222181 9305467581031340854159)
                    ·
                      rfl

theorem cell23_54367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 4].length) (baseStart_54367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54367 prefixEnd_54367 := by exact prefixLift 54367
  have htrace : WordTrace (prefixWord ++ tailWord_54367) baseStart_54367 baseEnd_54367 := by
    simpa [prefixWord, tailWord_54367, baseEnd_54367] using wordTrace_append hprefix tailTrace_54367
  have hstable : (prefixWord ++ tailWord_54367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54367).length < 2 ^ (prefixWord ++ tailWord_54367).sum := by decide
  have hdescent : baseEnd_54367 < baseStart_54367 := by decide
  rcases family_descends (prefixWord ++ tailWord_54367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54400 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 2, 3, 2]
def baseStart_54400 : Nat := 118140960795 + 54400 * 2 ^ 59
def prefixEnd_54400 : Nat := 4983230072969 + 3 ^ 40 * 54400 * 2
def baseEnd_54400 : Nat := 27933347604692393449825

theorem tailTrace_54400 : CollatzResearch.WordTrace tailWord_54400 prefixEnd_54400 27933347604692393449825 := by
  unfold tailWord_54400
  simp only [CollatzResearch.WordTrace]
  refine ⟨992065501462782812716327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1322754001950377083621769 992065501462782812716327)
  ·
    refine ⟨1488098252194174219074491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 992065501462782812716327 1488098252194174219074491)
    ·
      refine ⟨2232147378291261328611737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488098252194174219074491 2232147378291261328611737)
      ·
        refine ⟨1674110533718445996458803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2232147378291261328611737 1674110533718445996458803)
        ·
          refine ⟨2511165800577668994688205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674110533718445996458803 2511165800577668994688205)
          ·
            refine ⟨941687175216625873008077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2511165800577668994688205 941687175216625873008077)
            ·
              refine ⟨353132690706234702378029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941687175216625873008077 353132690706234702378029)
              ·
                refine ⟨132424759014838013391761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353132690706234702378029 132424759014838013391761)
                ·
                  refine ⟨99318569261128510043821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132424759014838013391761 99318569261128510043821)
                  ·
                    refine ⟨37244463472923191266433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99318569261128510043821 37244463472923191266433)
                    ·
                      refine ⟨27933347604692393449825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37244463472923191266433 27933347604692393449825)
                      ·
                        rfl

theorem cell23_54400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_54400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54400 prefixEnd_54400 := by exact prefixLift 54400
  have htrace : WordTrace (prefixWord ++ tailWord_54400) baseStart_54400 baseEnd_54400 := by
    simpa [prefixWord, tailWord_54400, baseEnd_54400] using wordTrace_append hprefix tailTrace_54400
  have hstable : (prefixWord ++ tailWord_54400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54400).length < 2 ^ (prefixWord ++ tailWord_54400).sum := by decide
  have hdescent : baseEnd_54400 < baseStart_54400 := by decide
  rcases family_descends (prefixWord ++ tailWord_54400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54407 : List Nat := [1, 1, 4, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_54407 : Nat := 118140960795 + 54407 * 2 ^ 59
def prefixEnd_54407 : Nat := 4983230072969 + 3 ^ 40 * 54407 * 2
def baseEnd_54407 : Nat := 27936941969273866062293

theorem tailTrace_54407 : CollatzResearch.WordTrace tailWord_54407 prefixEnd_54407 27936941969273866062293 := by
  unfold tailWord_54407
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984386313900205820937475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1322924209266803880624983 1984386313900205820937475)
  ·
    refine ⟨2976579470850308731406213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1984386313900205820937475 2976579470850308731406213)
    ·
      refine ⟨558108650784432887138665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2976579470850308731406213 558108650784432887138665)
      ·
        refine ⟨418581488088324665353999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558108650784432887138665 418581488088324665353999)
        ·
          refine ⟨627872232132486998030999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418581488088324665353999 627872232132486998030999)
          ·
            refine ⟨941808348198730497046499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627872232132486998030999 941808348198730497046499)
            ·
              refine ⟨1412712522298095745569749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941808348198730497046499 1412712522298095745569749)
              ·
                refine ⟨33110449741361619036791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1412712522298095745569749 33110449741361619036791)
                ·
                  refine ⟨49665674612042428555187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33110449741361619036791 49665674612042428555187)
                  ·
                    refine ⟨74498511918063642832781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49665674612042428555187 74498511918063642832781)
                    ·
                      refine ⟨27936941969273866062293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74498511918063642832781 27936941969273866062293)
                      ·
                        rfl

theorem cell23_54407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_54407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54407 prefixEnd_54407 := by exact prefixLift 54407
  have htrace : WordTrace (prefixWord ++ tailWord_54407) baseStart_54407 baseEnd_54407 := by
    simpa [prefixWord, tailWord_54407, baseEnd_54407] using wordTrace_append hprefix tailTrace_54407
  have hstable : (prefixWord ++ tailWord_54407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54407).length < 2 ^ (prefixWord ++ tailWord_54407).sum := by decide
  have hdescent : baseEnd_54407 < baseStart_54407 := by decide
  rcases family_descends (prefixWord ++ tailWord_54407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54424 : List Nat := [2, 1, 2, 4, 2, 2, 1, 4, 1, 1, 3]
def baseStart_54424 : Nat := 118140960795 + 54424 * 2 ^ 59
def prefixEnd_54424 : Nat := 4983230072969 + 3 ^ 40 * 54424 * 2
def baseEnd_54424 : Nat := 27945671140400299549715

theorem tailTrace_54424 : CollatzResearch.WordTrace tailWord_54424 prefixEnd_54424 27945671140400299549715 := by
  unfold tailWord_54424
  simp only [CollatzResearch.WordTrace]
  refine ⟨992503177419308862153163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1323337569892411816204217 992503177419308862153163)
  ·
    refine ⟨1488754766128963293229745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 992503177419308862153163 1488754766128963293229745)
    ·
      refine ⟨1116566074596722469922309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1488754766128963293229745 1116566074596722469922309)
      ·
        refine ⟨209356138986885463110433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1116566074596722469922309 209356138986885463110433)
        ·
          refine ⟨157017104240164097332825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209356138986885463110433 157017104240164097332825)
          ·
            refine ⟨117762828180123072999619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157017104240164097332825 117762828180123072999619)
            ·
              refine ⟨176644242270184609499429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117762828180123072999619 176644242270184609499429)
              ·
                refine ⟨33120795425659614281143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176644242270184609499429 33120795425659614281143)
                ·
                  refine ⟨49681193138489421421715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33120795425659614281143 49681193138489421421715)
                  ·
                    refine ⟨74521789707734132132573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49681193138489421421715 74521789707734132132573)
                    ·
                      refine ⟨27945671140400299549715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74521789707734132132573 27945671140400299549715)
                      ·
                        rfl

theorem cell23_54424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_54424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54424 prefixEnd_54424 := by exact prefixLift 54424
  have htrace : WordTrace (prefixWord ++ tailWord_54424) baseStart_54424 baseEnd_54424 := by
    simpa [prefixWord, tailWord_54424, baseEnd_54424] using wordTrace_append hprefix tailTrace_54424
  have hstable : (prefixWord ++ tailWord_54424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54424).length < 2 ^ (prefixWord ++ tailWord_54424).sum := by decide
  have hdescent : baseEnd_54424 < baseStart_54424 := by decide
  rcases family_descends (prefixWord ++ tailWord_54424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54433 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_54433 : Nat := 118140960795 + 54433 * 2 ^ 59
def prefixEnd_54433 : Nat := 4983230072969 + 3 ^ 40 * 54433 * 2
def baseEnd_54433 : Nat := 27950292466290764337173

theorem tailTrace_54433 : CollatzResearch.WordTrace tailWord_54433 prefixEnd_54433 27950292466290764337173 := by
  unfold tailWord_54433
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985334611806012261383953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1323556407870674840922635 1985334611806012261383953)
  ·
    refine ⟨1489000958854509196037965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1985334611806012261383953 1489000958854509196037965)
    ·
      refine ⟨558375359570440948514237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1489000958854509196037965 558375359570440948514237)
      ·
        refine ⟨209390759838915355692839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558375359570440948514237 209390759838915355692839)
        ·
          refine ⟨314086139758373033539259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209390759838915355692839 314086139758373033539259)
          ·
            refine ⟨471129209637559550308889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314086139758373033539259 471129209637559550308889)
            ·
              refine ⟨353346907228169662731667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471129209637559550308889 353346907228169662731667)
              ·
                refine ⟨530020360842254494097501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353346907228169662731667 530020360842254494097501)
                ·
                  refine ⟨198757635315845435286563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530020360842254494097501 198757635315845435286563)
                  ·
                    refine ⟨298136452973768152929845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198757635315845435286563 298136452973768152929845)
                    ·
                      refine ⟨27950292466290764337173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 298136452973768152929845 27950292466290764337173)
                      ·
                        rfl

theorem cell23_54433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_54433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54433 prefixEnd_54433 := by exact prefixLift 54433
  have htrace : WordTrace (prefixWord ++ tailWord_54433) baseStart_54433 baseEnd_54433 := by
    simpa [prefixWord, tailWord_54433, baseEnd_54433] using wordTrace_append hprefix tailTrace_54433
  have hstable : (prefixWord ++ tailWord_54433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54433).length < 2 ^ (prefixWord ++ tailWord_54433).sum := by decide
  have hdescent : baseEnd_54433 < baseStart_54433 := by decide
  rcases family_descends (prefixWord ++ tailWord_54433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54450 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_54450 : Nat := 118140960795 + 54450 * 2 ^ 59
def prefixEnd_54450 : Nat := 4983230072969 + 3 ^ 40 * 54450 * 2
def baseEnd_54450 : Nat := 27959021637417197824595

theorem tailTrace_54450 : CollatzResearch.WordTrace tailWord_54450 prefixEnd_54450 27959021637417197824595 := by
  unfold tailWord_54450
  simp only [CollatzResearch.WordTrace]
  refine ⟨496488663186106041188201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1323969768496282776501869 496488663186106041188201)
  ·
    refine ⟨372366497389579530891151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 496488663186106041188201 372366497389579530891151)
    ·
      refine ⟨558549746084369296336727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372366497389579530891151 558549746084369296336727)
      ·
        refine ⟨837824619126553944505091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558549746084369296336727 837824619126553944505091)
        ·
          refine ⟨1256736928689830916757637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837824619126553944505091 1256736928689830916757637)
          ·
            refine ⟨235638174129343296892057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1256736928689830916757637 235638174129343296892057)
            ·
              refine ⟨176728630597007472669043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235638174129343296892057 176728630597007472669043)
              ·
                refine ⟨265092945895511209003565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176728630597007472669043 265092945895511209003565)
                ·
                  refine ⟨99409854710816703376337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265092945895511209003565 99409854710816703376337)
                  ·
                    refine ⟨74557391033112527532253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99409854710816703376337 74557391033112527532253)
                    ·
                      refine ⟨27959021637417197824595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74557391033112527532253 27959021637417197824595)
                      ·
                        rfl

theorem cell23_54450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_54450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54450 prefixEnd_54450 := by exact prefixLift 54450
  have htrace : WordTrace (prefixWord ++ tailWord_54450) baseStart_54450 baseEnd_54450 := by
    simpa [prefixWord, tailWord_54450, baseEnd_54450] using wordTrace_append hprefix tailTrace_54450
  have hstable : (prefixWord ++ tailWord_54450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54450).length < 2 ^ (prefixWord ++ tailWord_54450).sum := by decide
  have hdescent : baseEnd_54450 < baseStart_54450 := by decide
  rcases family_descends (prefixWord ++ tailWord_54450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54460 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_54460 : Nat := 118140960795 + 54460 * 2 ^ 59
def prefixEnd_54460 : Nat := 4983230072969 + 3 ^ 40 * 54460 * 2
def baseEnd_54460 : Nat := 27964156443962158699549

theorem tailTrace_54460 : CollatzResearch.WordTrace tailWord_54460 prefixEnd_54460 27964156443962158699549 := by
  unfold tailWord_54460
  simp only [CollatzResearch.WordTrace]
  refine ⟨993159691354097936308417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1324212921805463915077889 993159691354097936308417)
  ·
    refine ⟨744869768515573452231313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 993159691354097936308417 744869768515573452231313)
    ·
      refine ⟨558652326386680089173485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 744869768515573452231313 558652326386680089173485)
      ·
        refine ⟨209494622395005033440057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558652326386680089173485 209494622395005033440057)
        ·
          refine ⟨157120966796253775080043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209494622395005033440057 157120966796253775080043)
          ·
            refine ⟨235681450194380662620065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157120966796253775080043 235681450194380662620065)
            ·
              refine ⟨176761087645785496965049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235681450194380662620065 176761087645785496965049)
              ·
                refine ⟨132570815734339122723787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176761087645785496965049 132570815734339122723787)
                ·
                  refine ⟨198856223601508684085681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132570815734339122723787 198856223601508684085681)
                  ·
                    refine ⟨149142167701131513064261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198856223601508684085681 149142167701131513064261)
                    ·
                      refine ⟨27964156443962158699549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 149142167701131513064261 27964156443962158699549)
                      ·
                        rfl

theorem cell23_54460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_54460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54460 prefixEnd_54460 := by exact prefixLift 54460
  have htrace : WordTrace (prefixWord ++ tailWord_54460) baseStart_54460 baseEnd_54460 := by
    simpa [prefixWord, tailWord_54460, baseEnd_54460] using wordTrace_append hprefix tailTrace_54460
  have hstable : (prefixWord ++ tailWord_54460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54460).length < 2 ^ (prefixWord ++ tailWord_54460).sum := by decide
  have hdescent : baseEnd_54460 < baseStart_54460 := by decide
  rcases family_descends (prefixWord ++ tailWord_54460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54464 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 1, 1, 4]
def baseStart_54464 : Nat := 118140960795 + 54464 * 2 ^ 59
def prefixEnd_54464 : Nat := 4983230072969 + 3 ^ 40 * 54464 * 2
def baseEnd_54464 : Nat := 27966210366580143049531

theorem tailTrace_54464 : CollatzResearch.WordTrace tailWord_54464 prefixEnd_54464 27966210366580143049531 := by
  unfold tailWord_54464
  simp only [CollatzResearch.WordTrace]
  refine ⟨993232637346852277881223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1324310183129136370508297 993232637346852277881223)
  ·
    refine ⟨1489848956020278416821835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 993232637346852277881223 1489848956020278416821835)
    ·
      refine ⟨2234773434030417625232753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1489848956020278416821835 2234773434030417625232753)
      ·
        refine ⟨1676080075522813218924565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2234773434030417625232753 1676080075522813218924565)
        ·
          refine ⟨78566253540131869637089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1676080075522813218924565 78566253540131869637089)
          ·
            refine ⟨58924690155098902227817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78566253540131869637089 58924690155098902227817)
            ·
              refine ⟨44193517616324176670863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58924690155098902227817 44193517616324176670863)
              ·
                refine ⟨66290276424486265006295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44193517616324176670863 66290276424486265006295)
                ·
                  refine ⟨99435414636729397509443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66290276424486265006295 99435414636729397509443)
                  ·
                    refine ⟨149153121955094096264165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99435414636729397509443 149153121955094096264165)
                    ·
                      refine ⟨27966210366580143049531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 149153121955094096264165 27966210366580143049531)
                      ·
                        rfl

theorem cell23_54464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_54464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54464 prefixEnd_54464 := by exact prefixLift 54464
  have htrace : WordTrace (prefixWord ++ tailWord_54464) baseStart_54464 baseEnd_54464 := by
    simpa [prefixWord, tailWord_54464, baseEnd_54464] using wordTrace_append hprefix tailTrace_54464
  have hstable : (prefixWord ++ tailWord_54464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54464).length < 2 ^ (prefixWord ++ tailWord_54464).sum := by decide
  have hdescent : baseEnd_54464 < baseStart_54464 := by decide
  rcases family_descends (prefixWord ++ tailWord_54464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54497 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_54497 : Nat := 118140960795 + 54497 * 2 ^ 59
def prefixEnd_54497 : Nat := 4983230072969 + 3 ^ 40 * 54497 * 2
def baseEnd_54497 : Nat := 27983155228178513936879

theorem tailTrace_54497 : CollatzResearch.WordTrace tailWord_54497 prefixEnd_54497 27983155228178513936879 := by
  unfold tailWord_54497
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987668883574151191713745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1325112589049434127809163 1987668883574151191713745)
  ·
    refine ⟨1490751662680613393785309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1987668883574151191713745 1490751662680613393785309)
    ·
      refine ⟨559031873505230022669491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1490751662680613393785309 559031873505230022669491)
      ·
        refine ⟨838547810257845034004237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559031873505230022669491 838547810257845034004237)
        ·
          refine ⟨314455428846691887751589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 838547810257845034004237 314455428846691887751589)
          ·
            refine ⟨58960392908754728953423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314455428846691887751589 58960392908754728953423)
            ·
              refine ⟨88440589363132093430135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58960392908754728953423 88440589363132093430135)
              ·
                refine ⟨132660884044698140145203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88440589363132093430135 132660884044698140145203)
                ·
                  refine ⟨198991326067047210217805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132660884044698140145203 198991326067047210217805)
                  ·
                    refine ⟨74621747275142703831677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198991326067047210217805 74621747275142703831677)
                    ·
                      refine ⟨27983155228178513936879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74621747275142703831677 27983155228178513936879)
                      ·
                        rfl

theorem cell23_54497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_54497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54497 prefixEnd_54497 := by exact prefixLift 54497
  have htrace : WordTrace (prefixWord ++ tailWord_54497) baseStart_54497 baseEnd_54497 := by
    simpa [prefixWord, tailWord_54497, baseEnd_54497] using wordTrace_append hprefix tailTrace_54497
  have hstable : (prefixWord ++ tailWord_54497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54497).length < 2 ^ (prefixWord ++ tailWord_54497).sum := by decide
  have hdescent : baseEnd_54497 < baseStart_54497 := by decide
  rcases family_descends (prefixWord ++ tailWord_54497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54507 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 1, 3, 2]
def baseStart_54507 : Nat := 118140960795 + 54507 * 2 ^ 59
def prefixEnd_54507 : Nat := 4983230072969 + 3 ^ 40 * 54507 * 2
def baseEnd_54507 : Nat := 27988290034723474811833

theorem tailTrace_54507 : CollatzResearch.WordTrace tailWord_54507 prefixEnd_54507 27988290034723474811833 := by
  unfold tailWord_54507
  simp only [CollatzResearch.WordTrace]
  refine ⟨1988033613537922899577775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1325355742358615266385183 1988033613537922899577775)
  ·
    refine ⟨2982050420306884349366663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1988033613537922899577775 2982050420306884349366663)
    ·
      refine ⟨4473075630460326524049995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2982050420306884349366663 4473075630460326524049995)
      ·
        refine ⟨6709613445690489786074993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473075630460326524049995 6709613445690489786074993)
        ·
          refine ⟨5032210084267867339556245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6709613445690489786074993 5032210084267867339556245)
          ·
            refine ⟨235884847700056281541699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5032210084267867339556245 235884847700056281541699)
            ·
              refine ⟨353827271550084422312549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235884847700056281541699 353827271550084422312549)
              ·
                refine ⟨66342613415640829183603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353827271550084422312549 66342613415640829183603)
                ·
                  refine ⟨99513920123461243775405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66342613415640829183603 99513920123461243775405)
                  ·
                    refine ⟨37317720046297966415777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99513920123461243775405 37317720046297966415777)
                    ·
                      refine ⟨27988290034723474811833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37317720046297966415777 27988290034723474811833)
                      ·
                        rfl

theorem cell23_54507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 3, 2].length) (baseStart_54507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54507 prefixEnd_54507 := by exact prefixLift 54507
  have htrace : WordTrace (prefixWord ++ tailWord_54507) baseStart_54507 baseEnd_54507 := by
    simpa [prefixWord, tailWord_54507, baseEnd_54507] using wordTrace_append hprefix tailTrace_54507
  have hstable : (prefixWord ++ tailWord_54507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54507).length < 2 ^ (prefixWord ++ tailWord_54507).sum := by decide
  have hdescent : baseEnd_54507 < baseStart_54507 := by decide
  rcases family_descends (prefixWord ++ tailWord_54507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54537 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 4, 2, 2]
def baseStart_54537 : Nat := 118140960795 + 54537 * 2 ^ 59
def prefixEnd_54537 : Nat := 4983230072969 + 3 ^ 40 * 54537 * 2
def baseEnd_54537 : Nat := 28003694454358357436695

theorem tailTrace_54537 : CollatzResearch.WordTrace tailWord_54537 prefixEnd_54537 28003694454358357436695 := by
  unfold tailWord_54537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989127803429238023169865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1326085202286158682113243 1989127803429238023169865)
  ·
    refine ⟨1491845852571928517377399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1989127803429238023169865 1491845852571928517377399)
    ·
      refine ⟨2237768778857892776066099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491845852571928517377399 2237768778857892776066099)
      ·
        refine ⟨3356653168286839164099149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237768778857892776066099 3356653168286839164099149)
        ·
          refine ⟨1258744938107564686537181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3356653168286839164099149 1258744938107564686537181)
          ·
            refine ⟨472029351790336757451443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1258744938107564686537181 472029351790336757451443)
            ·
              refine ⟨708044027685505136177165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472029351790336757451443 708044027685505136177165)
              ·
                refine ⟨265516510382064426066437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708044027685505136177165 265516510382064426066437)
                ·
                  refine ⟨49784345696637079887457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265516510382064426066437 49784345696637079887457)
                  ·
                    refine ⟨37338259272477809915593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49784345696637079887457 37338259272477809915593)
                    ·
                      refine ⟨28003694454358357436695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37338259272477809915593 28003694454358357436695)
                      ·
                        rfl

theorem cell23_54537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 2, 2].length) (baseStart_54537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54537 prefixEnd_54537 := by exact prefixLift 54537
  have htrace : WordTrace (prefixWord ++ tailWord_54537) baseStart_54537 baseEnd_54537 := by
    simpa [prefixWord, tailWord_54537, baseEnd_54537] using wordTrace_append hprefix tailTrace_54537
  have hstable : (prefixWord ++ tailWord_54537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54537).length < 2 ^ (prefixWord ++ tailWord_54537).sum := by decide
  have hdescent : baseEnd_54537 < baseStart_54537 := by decide
  rcases family_descends (prefixWord ++ tailWord_54537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54610 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_54610 : Nat := 118140960795 + 54610 * 2 ^ 59
def prefixEnd_54610 : Nat := 4983230072969 + 3 ^ 40 * 54610 * 2
def baseEnd_54610 : Nat := 28041178542136571823859

theorem tailTrace_54610 : CollatzResearch.WordTrace tailWord_54610 prefixEnd_54610 28041178542136571823859 := by
  unfold tailWord_54610
  simp only [CollatzResearch.WordTrace]
  refine ⟨497947583041192872644321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1327860221443180993718189 497947583041192872644321)
  ·
    refine ⟨373460687280894654483241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 497947583041192872644321 373460687280894654483241)
    ·
      refine ⟨280095515460670990862431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373460687280894654483241 280095515460670990862431)
      ·
        refine ⟨420143273191006486293647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280095515460670990862431 420143273191006486293647)
        ·
          refine ⟨630214909786509729440471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420143273191006486293647 630214909786509729440471)
          ·
            refine ⟨945322364679764594160707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630214909786509729440471 945322364679764594160707)
            ·
              refine ⟨1417983547019646891241061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945322364679764594160707 1417983547019646891241061)
              ·
                refine ⟨265871915066183792107699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1417983547019646891241061 265871915066183792107699)
                ·
                  refine ⟨398807872599275688161549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265871915066183792107699 398807872599275688161549)
                  ·
                    refine ⟨149552952224728383060581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398807872599275688161549 149552952224728383060581)
                    ·
                      refine ⟨28041178542136571823859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 149552952224728383060581 28041178542136571823859)
                      ·
                        rfl

theorem cell23_54610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_54610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54610 prefixEnd_54610 := by exact prefixLift 54610
  have htrace : WordTrace (prefixWord ++ tailWord_54610) baseStart_54610 baseEnd_54610 := by
    simpa [prefixWord, tailWord_54610, baseEnd_54610] using wordTrace_append hprefix tailTrace_54610
  have hstable : (prefixWord ++ tailWord_54610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54610).length < 2 ^ (prefixWord ++ tailWord_54610).sum := by decide
  have hdescent : baseEnd_54610 < baseStart_54610 := by decide
  rcases family_descends (prefixWord ++ tailWord_54610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54627 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 4]
def baseStart_54627 : Nat := 118140960795 + 54627 * 2 ^ 59
def prefixEnd_54627 : Nat := 4983230072969 + 3 ^ 40 * 54627 * 2
def baseEnd_54627 : Nat := 28049907713263005311281

theorem tailTrace_54627 : CollatzResearch.WordTrace tailWord_54627 prefixEnd_54627 28049907713263005311281 := by
  unfold tailWord_54627
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992410373103183393946135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1328273582068788929297423 1992410373103183393946135)
  ·
    refine ⟨2988615559654775090919203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1992410373103183393946135 2988615559654775090919203)
    ·
      refine ⟨4482923339482162636378805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988615559654775090919203 4482923339482162636378805)
      ·
        refine ⟨420274063076452747160513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4482923339482162636378805 420274063076452747160513)
        ·
          refine ⟨315205547307339560370385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420274063076452747160513 315205547307339560370385)
          ·
            refine ⟨236404160480504670277789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315205547307339560370385 236404160480504670277789)
            ·
              refine ⟨88651560180189251354171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236404160480504670277789 88651560180189251354171)
              ·
                refine ⟨132977340270283877031257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88651560180189251354171 132977340270283877031257)
                ·
                  refine ⟨99733005202712907773443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132977340270283877031257 99733005202712907773443)
                  ·
                    refine ⟨149599507804069361660165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99733005202712907773443 149599507804069361660165)
                    ·
                      refine ⟨28049907713263005311281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 149599507804069361660165 28049907713263005311281)
                      ·
                        rfl

theorem cell23_54627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_54627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54627 prefixEnd_54627 := by exact prefixLift 54627
  have htrace : WordTrace (prefixWord ++ tailWord_54627) baseStart_54627 baseEnd_54627 := by
    simpa [prefixWord, tailWord_54627, baseEnd_54627] using wordTrace_append hprefix tailTrace_54627
  have hstable : (prefixWord ++ tailWord_54627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54627).length < 2 ^ (prefixWord ++ tailWord_54627).sum := by decide
  have hdescent : baseEnd_54627 < baseStart_54627 := by decide
  rcases family_descends (prefixWord ++ tailWord_54627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54667 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 6]
def baseStart_54667 : Nat := 118140960795 + 54667 * 2 ^ 59
def prefixEnd_54667 : Nat := 4983230072969 + 3 ^ 40 * 54667 * 2
def baseEnd_54667 : Nat := 3118938548826983201233

theorem tailTrace_54667 : CollatzResearch.WordTrace tailWord_54667 prefixEnd_54667 3118938548826983201233 := by
  unfold tailWord_54667
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993869292958270225402255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1329246195305513483601503 1993869292958270225402255)
  ·
    refine ⟨2990803939437405338103383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993869292958270225402255 2990803939437405338103383)
    ·
      refine ⟨4486205909156108007155075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2990803939437405338103383 4486205909156108007155075)
      ·
        refine ⟨6729308863734162010732613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486205909156108007155075 6729308863734162010732613)
        ·
          refine ⟨1261745411950155377012365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6729308863734162010732613 1261745411950155377012365)
          ·
            refine ⟨473154529481308266379637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1261745411950155377012365 473154529481308266379637)
            ·
              refine ⟨44358237138872649973091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 473154529481308266379637 44358237138872649973091)
              ·
                refine ⟨66537355708308974959637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44358237138872649973091 66537355708308974959637)
                ·
                  refine ⟨3118938548826983201233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66537355708308974959637 3118938548826983201233)
                  ·
                    rfl

theorem cell23_54667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 6].length) (baseStart_54667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54667 prefixEnd_54667 := by exact prefixLift 54667
  have htrace : WordTrace (prefixWord ++ tailWord_54667) baseStart_54667 baseEnd_54667 := by
    simpa [prefixWord, tailWord_54667, baseEnd_54667] using wordTrace_append hprefix tailTrace_54667
  have hstable : (prefixWord ++ tailWord_54667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54667).length < 2 ^ (prefixWord ++ tailWord_54667).sum := by decide
  have hdescent : baseEnd_54667 < baseStart_54667 := by decide
  rcases family_descends (prefixWord ++ tailWord_54667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54717 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_54717 : Nat := 118140960795 + 54717 * 2 ^ 59
def prefixEnd_54717 : Nat := 4983230072969 + 3 ^ 40 * 54717 * 2
def baseEnd_54717 : Nat := 28096120972167653185867

theorem tailTrace_54717 : CollatzResearch.WordTrace tailWord_54717 prefixEnd_54717 28096120972167653185867 := by
  unfold tailWord_54717
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995692942777128764722405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1330461961851419176481603 1995692942777128764722405)
  ·
    refine ⟨374192426770711643385451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1995692942777128764722405 374192426770711643385451)
    ·
      refine ⟨561288640156067465078177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374192426770711643385451 561288640156067465078177)
      ·
        refine ⟨420966480117050598808633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561288640156067465078177 420966480117050598808633)
        ·
          refine ⟨315724860087787949106475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420966480117050598808633 315724860087787949106475)
          ·
            refine ⟨473587290131681923659713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315724860087787949106475 473587290131681923659713)
            ·
              refine ⟨355190467598761442744785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473587290131681923659713 355190467598761442744785)
              ·
                refine ⟨266392850699071082058589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355190467598761442744785 266392850699071082058589)
                ·
                  refine ⟨99897319012151655771971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266392850699071082058589 99897319012151655771971)
                  ·
                    refine ⟨149845978518227483657957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99897319012151655771971 149845978518227483657957)
                    ·
                      refine ⟨28096120972167653185867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 149845978518227483657957 28096120972167653185867)
                      ·
                        rfl

theorem cell23_54717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_54717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54717 prefixEnd_54717 := by exact prefixLift 54717
  have htrace : WordTrace (prefixWord ++ tailWord_54717) baseStart_54717 baseEnd_54717 := by
    simpa [prefixWord, tailWord_54717, baseEnd_54717] using wordTrace_append hprefix tailTrace_54717
  have hstable : (prefixWord ++ tailWord_54717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54717).length < 2 ^ (prefixWord ++ tailWord_54717).sum := by decide
  have hdescent : baseEnd_54717 < baseStart_54717 := by decide
  rcases family_descends (prefixWord ++ tailWord_54717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54734 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_54734 : Nat := 118140960795 + 54734 * 2 ^ 59
def prefixEnd_54734 : Nat := 4983230072969 + 3 ^ 40 * 54734 * 2
def baseEnd_54734 : Nat := 28104850143294086673289

theorem tailTrace_54734 : CollatzResearch.WordTrace tailWord_54734 prefixEnd_54734 28104850143294086673289 := by
  unfold tailWord_54734
  simp only [CollatzResearch.WordTrace]
  refine ⟨249539122964442583511407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1330875322477027112060837 249539122964442583511407)
  ·
    refine ⟨374308684446663875267111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249539122964442583511407 374308684446663875267111)
    ·
      refine ⟨561463026669995812900667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374308684446663875267111 561463026669995812900667)
      ·
        refine ⟨842194540004993719351001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561463026669995812900667 842194540004993719351001)
        ·
          refine ⟨631645905003745289513251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842194540004993719351001 631645905003745289513251)
          ·
            refine ⟨947468857505617934269877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631645905003745289513251 947468857505617934269877)
            ·
              refine ⟨88825205391151681337801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 947468857505617934269877 88825205391151681337801)
              ·
                refine ⟨66618904043363761003351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88825205391151681337801 66618904043363761003351)
                ·
                  refine ⟨99928356065045641505027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66618904043363761003351 99928356065045641505027)
                  ·
                    refine ⟨149892534097568462257541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99928356065045641505027 149892534097568462257541)
                    ·
                      refine ⟨28104850143294086673289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 149892534097568462257541 28104850143294086673289)
                      ·
                        rfl

theorem cell23_54734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_54734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54734 prefixEnd_54734 := by exact prefixLift 54734
  have htrace : WordTrace (prefixWord ++ tailWord_54734) baseStart_54734 baseEnd_54734 := by
    simpa [prefixWord, tailWord_54734, baseEnd_54734] using wordTrace_append hprefix tailTrace_54734
  have hstable : (prefixWord ++ tailWord_54734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54734).length < 2 ^ (prefixWord ++ tailWord_54734).sum := by decide
  have hdescent : baseEnd_54734 < baseStart_54734 := by decide
  rcases family_descends (prefixWord ++ tailWord_54734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54762 : List Nat := [3, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_54762 : Nat := 118140960795 + 54762 * 2 ^ 59
def prefixEnd_54762 : Nat := 4983230072969 + 3 ^ 40 * 54762 * 2
def baseEnd_54762 : Nat := 28119227601619977123161

theorem tailTrace_54762 : CollatzResearch.WordTrace tailWord_54762 prefixEnd_54762 28119227601619977123161 := by
  unfold tailWord_54762
  simp only [CollatzResearch.WordTrace]
  refine ⟨499333556903525362527635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1331556151742734300073693 499333556903525362527635)
  ·
    refine ⟨749000335355288043791453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499333556903525362527635 749000335355288043791453)
    ·
      refine ⟨280875125758233016421795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 749000335355288043791453 280875125758233016421795)
      ·
        refine ⟨421312688637349524632693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280875125758233016421795 421312688637349524632693)
        ·
          refine ⟨39498064559751517934315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421312688637349524632693 39498064559751517934315)
          ·
            refine ⟨59247096839627276901473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39498064559751517934315 59247096839627276901473)
            ·
              refine ⟨44435322629720457676105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59247096839627276901473 44435322629720457676105)
              ·
                refine ⟨33326491972290343257079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44435322629720457676105 33326491972290343257079)
                ·
                  refine ⟨49989737958435514885619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33326491972290343257079 49989737958435514885619)
                  ·
                    refine ⟨74984606937653272328429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49989737958435514885619 74984606937653272328429)
                    ·
                      refine ⟨28119227601619977123161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 74984606937653272328429 28119227601619977123161)
                      ·
                        rfl

theorem cell23_54762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_54762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54762 prefixEnd_54762 := by exact prefixLift 54762
  have htrace : WordTrace (prefixWord ++ tailWord_54762) baseStart_54762 baseEnd_54762 := by
    simpa [prefixWord, tailWord_54762, baseEnd_54762] using wordTrace_append hprefix tailTrace_54762
  have hstable : (prefixWord ++ tailWord_54762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54762).length < 2 ^ (prefixWord ++ tailWord_54762).sum := by decide
  have hdescent : baseEnd_54762 < baseStart_54762 := by decide
  rcases family_descends (prefixWord ++ tailWord_54762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54768 : List Nat := [2, 1, 1, 1, 3, 5, 1, 4, 1, 2, 2]
def baseStart_54768 : Nat := 118140960795 + 54768 * 2 ^ 59
def prefixEnd_54768 : Nat := 4983230072969 + 3 ^ 40 * 54768 * 2
def baseEnd_54768 : Nat := 28122308485546953648133

theorem tailTrace_54768 : CollatzResearch.WordTrace tailWord_54768 prefixEnd_54768 28122308485546953648133 := by
  unfold tailWord_54768
  simp only [CollatzResearch.WordTrace]
  refine ⟨998776532796182237414479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1331702043728242983219305 998776532796182237414479)
  ·
    refine ⟨1498164799194273356121719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998776532796182237414479 1498164799194273356121719)
    ·
      refine ⟨2247247198791410034182579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1498164799194273356121719 2247247198791410034182579)
      ·
        refine ⟨3370870798187115051273869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247247198791410034182579 3370870798187115051273869)
        ·
          refine ⟨1264076549320168144227701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3370870798187115051273869 1264076549320168144227701)
          ·
            refine ⟨118507176498765763521347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1264076549320168144227701 118507176498765763521347)
            ·
              refine ⟨177760764748148645282021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118507176498765763521347 177760764748148645282021)
              ·
                refine ⟨33330143390277870990379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177760764748148645282021 33330143390277870990379)
                ·
                  refine ⟨49995215085416806485569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33330143390277870990379 49995215085416806485569)
                  ·
                    refine ⟨37496411314062604864177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49995215085416806485569 37496411314062604864177)
                    ·
                      refine ⟨28122308485546953648133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37496411314062604864177 28122308485546953648133)
                      ·
                        rfl

theorem cell23_54768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 2, 2].length) (baseStart_54768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54768 prefixEnd_54768 := by exact prefixLift 54768
  have htrace : WordTrace (prefixWord ++ tailWord_54768) baseStart_54768 baseEnd_54768 := by
    simpa [prefixWord, tailWord_54768, baseEnd_54768] using wordTrace_append hprefix tailTrace_54768
  have hstable : (prefixWord ++ tailWord_54768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54768).length < 2 ^ (prefixWord ++ tailWord_54768).sum := by decide
  have hdescent : baseEnd_54768 < baseStart_54768 := by decide
  rcases family_descends (prefixWord ++ tailWord_54768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54774 : List Nat := [5, 1, 1, 1, 2, 4, 1, 8]
def baseStart_54774 : Nat := 118140960795 + 54774 * 2 ^ 59
def prefixEnd_54774 : Nat := 4983230072969 + 3 ^ 40 * 54774 * 2
def baseEnd_54774 : Nat := 1041681087758293710115

theorem tailTrace_54774 : CollatzResearch.WordTrace tailWord_54774 prefixEnd_54774 1041681087758293710115 := by
  unfold tailWord_54774
  simp only [CollatzResearch.WordTrace]
  refine ⟨124860743973164218721711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1331847935713751666364917 124860743973164218721711)
  ·
    refine ⟨187291115959746328082567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124860743973164218721711 187291115959746328082567)
    ·
      refine ⟨280936673939619492123851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187291115959746328082567 280936673939619492123851)
      ·
        refine ⟨421405010909429238185777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280936673939619492123851 421405010909429238185777)
        ·
          refine ⟨316053758182071928639333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421405010909429238185777 316053758182071928639333)
          ·
            refine ⟨59260079659138486619875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316053758182071928639333 59260079659138486619875)
            ·
              refine ⟨88890119488707729929813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59260079659138486619875 88890119488707729929813)
              ·
                refine ⟨1041681087758293710115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 88890119488707729929813 1041681087758293710115)
                ·
                  rfl

theorem cell23_54774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_54774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54774 prefixEnd_54774 := by exact prefixLift 54774
  have htrace : WordTrace (prefixWord ++ tailWord_54774) baseStart_54774 baseEnd_54774 := by
    simpa [prefixWord, tailWord_54774, baseEnd_54774] using wordTrace_append hprefix tailTrace_54774
  have hstable : (prefixWord ++ tailWord_54774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54774).length < 2 ^ (prefixWord ++ tailWord_54774).sum := by decide
  have hdescent : baseEnd_54774 < baseStart_54774 := by decide
  rcases family_descends (prefixWord ++ tailWord_54774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54817 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 2, 6]
def baseStart_54817 : Nat := 118140960795 + 54817 * 2 ^ 59
def prefixEnd_54817 : Nat := 4983230072969 + 3 ^ 40 * 54817 * 2
def baseEnd_54817 : Nat := 9382489679205753978469

theorem tailTrace_54817 : CollatzResearch.WordTrace tailWord_54817 prefixEnd_54817 9382489679205753978469 := by
  unfold tailWord_54817
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999340242414845843362705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1332893494943230562241803 1999340242414845843362705)
  ·
    refine ⟨1499505181811134382522029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1999340242414845843362705 1499505181811134382522029)
    ·
      refine ⟨562314443179175393445761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1499505181811134382522029 562314443179175393445761)
      ·
        refine ⟨421735832384381545084321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562314443179175393445761 421735832384381545084321)
        ·
          refine ⟨316301874288286158813241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421735832384381545084321 316301874288286158813241)
          ·
            refine ⟨237226405716214619109931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316301874288286158813241 237226405716214619109931)
            ·
              refine ⟨355839608574321928664897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237226405716214619109931 355839608574321928664897)
              ·
                refine ⟨266879706430741446498673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355839608574321928664897 266879706430741446498673)
                ·
                  refine ⟨200159779823056084874005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266879706430741446498673 200159779823056084874005)
                  ·
                    refine ⟨9382489679205753978469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 200159779823056084874005 9382489679205753978469)
                    ·
                      rfl

theorem cell23_54817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_54817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54817 prefixEnd_54817 := by exact prefixLift 54817
  have htrace : WordTrace (prefixWord ++ tailWord_54817) baseStart_54817 baseEnd_54817 := by
    simpa [prefixWord, tailWord_54817, baseEnd_54817] using wordTrace_append hprefix tailTrace_54817
  have hstable : (prefixWord ++ tailWord_54817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54817).length < 2 ^ (prefixWord ++ tailWord_54817).sum := by decide
  have hdescent : baseEnd_54817 < baseStart_54817 := by decide
  rcases family_descends (prefixWord ++ tailWord_54817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54841 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 1, 4, 2]
def baseStart_54841 : Nat := 118140960795 + 54841 * 2 ^ 59
def prefixEnd_54841 : Nat := 4983230072969 + 3 ^ 40 * 54841 * 2
def baseEnd_54841 : Nat := 28159792573325168035297

theorem tailTrace_54841 : CollatzResearch.WordTrace tailWord_54841 prefixEnd_54841 28159792573325168035297 := by
  unfold tailWord_54841
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000215594327897942236377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1333477062885265294824251 2000215594327897942236377)
  ·
    refine ⟨1500161695745923456677283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2000215594327897942236377 1500161695745923456677283)
    ·
      refine ⟨2250242543618885185015925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500161695745923456677283 2250242543618885185015925)
      ·
        refine ⟨210960238464270486095243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2250242543618885185015925 210960238464270486095243)
        ·
          refine ⟨316440357696405729142865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210960238464270486095243 316440357696405729142865)
          ·
            refine ⟨237330268272304296857149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316440357696405729142865 237330268272304296857149)
            ·
              refine ⟨88998850602114111321431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237330268272304296857149 88998850602114111321431)
              ·
                refine ⟨133498275903171166982147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88998850602114111321431 133498275903171166982147)
                ·
                  refine ⟨200247413854756750473221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133498275903171166982147 200247413854756750473221)
                  ·
                    refine ⟨37546390097766890713729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200247413854756750473221 37546390097766890713729)
                    ·
                      refine ⟨28159792573325168035297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37546390097766890713729 28159792573325168035297)
                      ·
                        rfl

theorem cell23_54841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_54841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54841 prefixEnd_54841 := by exact prefixLift 54841
  have htrace : WordTrace (prefixWord ++ tailWord_54841) baseStart_54841 baseEnd_54841 := by
    simpa [prefixWord, tailWord_54841, baseEnd_54841] using wordTrace_append hprefix tailTrace_54841
  have hstable : (prefixWord ++ tailWord_54841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54841).length < 2 ^ (prefixWord ++ tailWord_54841).sum := by decide
  have hdescent : baseEnd_54841 < baseStart_54841 := by decide
  rcases family_descends (prefixWord ++ tailWord_54841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54847 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 7]
def baseStart_54847 : Nat := 118140960795 + 54847 * 2 ^ 59
def prefixEnd_54847 : Nat := 4983230072969 + 3 ^ 40 * 54847 * 2
def baseEnd_54847 : Nat := 3129208161916904951141

theorem tailTrace_54847 : CollatzResearch.WordTrace tailWord_54847 prefixEnd_54847 3129208161916904951141 := by
  unfold tailWord_54847
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000434432306160966954795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1333622954870773977969863 2000434432306160966954795)
  ·
    refine ⟨3000651648459241450432193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000434432306160966954795 3000651648459241450432193)
    ·
      refine ⟨2250488736344431087824145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3000651648459241450432193 2250488736344431087824145)
      ·
        refine ⟨1687866552258323315868109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2250488736344431087824145 1687866552258323315868109)
        ·
          refine ⟨632949957096871243450541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1687866552258323315868109 632949957096871243450541)
          ·
            refine ⟨237356233911326716293953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632949957096871243450541 237356233911326716293953)
            ·
              refine ⟨178017175433495037220465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237356233911326716293953 178017175433495037220465)
              ·
                refine ⟨133512881575121277915349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178017175433495037220465 133512881575121277915349)
                ·
                  refine ⟨3129208161916904951141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 133512881575121277915349 3129208161916904951141)
                  ·
                    rfl

theorem cell23_54847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 7].length) (baseStart_54847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54847 prefixEnd_54847 := by exact prefixLift 54847
  have htrace : WordTrace (prefixWord ++ tailWord_54847) baseStart_54847 baseEnd_54847 := by
    simpa [prefixWord, tailWord_54847, baseEnd_54847] using wordTrace_append hprefix tailTrace_54847
  have hstable : (prefixWord ++ tailWord_54847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54847).length < 2 ^ (prefixWord ++ tailWord_54847).sum := by decide
  have hdescent : baseEnd_54847 < baseStart_54847 := by decide
  rcases family_descends (prefixWord ++ tailWord_54847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54857 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 3]
def baseStart_54857 : Nat := 118140960795 + 54857 * 2 ^ 59
def prefixEnd_54857 : Nat := 4983230072969 + 3 ^ 40 * 54857 * 2
def baseEnd_54857 : Nat := 28168008263797105435223

theorem tailTrace_54857 : CollatzResearch.WordTrace tailWord_54857 prefixEnd_54857 28168008263797105435223 := by
  unfold tailWord_54857
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000799162269932674818825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1333866108179955116545883 2000799162269932674818825)
  ·
    refine ⟨1500599371702449506114119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2000799162269932674818825 1500599371702449506114119)
    ·
      refine ⟨2250899057553674259171179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500599371702449506114119 2250899057553674259171179)
      ·
        refine ⟨3376348586330511388756769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250899057553674259171179 3376348586330511388756769)
        ·
          refine ⟨2532261439747883541567577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3376348586330511388756769 2532261439747883541567577)
          ·
            refine ⟨1899196079810912656175683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532261439747883541567577 1899196079810912656175683)
            ·
              refine ⟨2848794119716368984263525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899196079810912656175683 2848794119716368984263525)
              ·
                refine ⟨534148897446819184549411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2848794119716368984263525 534148897446819184549411)
                ·
                  refine ⟨801223346170228776824117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534148897446819184549411 801223346170228776824117)
                  ·
                    refine ⟨75114688703458947827261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 801223346170228776824117 75114688703458947827261)
                    ·
                      refine ⟨28168008263797105435223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 75114688703458947827261 28168008263797105435223)
                      ·
                        rfl

theorem cell23_54857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_54857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54857 prefixEnd_54857 := by exact prefixLift 54857
  have htrace : WordTrace (prefixWord ++ tailWord_54857) baseStart_54857 baseEnd_54857 := by
    simpa [prefixWord, tailWord_54857, baseEnd_54857] using wordTrace_append hprefix tailTrace_54857
  have hstable : (prefixWord ++ tailWord_54857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54857).length < 2 ^ (prefixWord ++ tailWord_54857).sum := by decide
  have hdescent : baseEnd_54857 < baseStart_54857 := by decide
  rcases family_descends (prefixWord ++ tailWord_54857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54861 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_54861 : Nat := 118140960795 + 54861 * 2 ^ 59
def prefixEnd_54861 : Nat := 4983230072969 + 3 ^ 40 * 54861 * 2
def baseEnd_54861 : Nat := 28170062186415089785205

theorem tailTrace_54861 : CollatzResearch.WordTrace tailWord_54861 prefixEnd_54861 28170062186415089785205 := by
  unfold tailWord_54861
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000945054255441357964437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1333963369503627571976291 2000945054255441357964437)
  ·
    refine ⟨93794299418223813654583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2000945054255441357964437 93794299418223813654583)
    ·
      refine ⟨140691449127335720481875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93794299418223813654583 140691449127335720481875)
      ·
        refine ⟨211037173691003580722813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140691449127335720481875 211037173691003580722813)
        ·
          refine ⟨79138940134126342771055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211037173691003580722813 79138940134126342771055)
          ·
            refine ⟨118708410201189514156583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79138940134126342771055 118708410201189514156583)
            ·
              refine ⟨178062615301784271234875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118708410201189514156583 178062615301784271234875)
              ·
                refine ⟨267093922952676406852313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178062615301784271234875 267093922952676406852313)
                ·
                  refine ⟨200320442214507305139235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267093922952676406852313 200320442214507305139235)
                  ·
                    refine ⟨300480663321760957708853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200320442214507305139235 300480663321760957708853)
                    ·
                      refine ⟨28170062186415089785205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 300480663321760957708853 28170062186415089785205)
                      ·
                        rfl

theorem cell23_54861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_54861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54861 prefixEnd_54861 := by exact prefixLift 54861
  have htrace : WordTrace (prefixWord ++ tailWord_54861) baseStart_54861 baseEnd_54861 := by
    simpa [prefixWord, tailWord_54861, baseEnd_54861] using wordTrace_append hprefix tailTrace_54861
  have hstable : (prefixWord ++ tailWord_54861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54861).length < 2 ^ (prefixWord ++ tailWord_54861).sum := by decide
  have hdescent : baseEnd_54861 < baseStart_54861 := by decide
  rcases family_descends (prefixWord ++ tailWord_54861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54881 : List Nat := [1, 2, 3, 1, 1, 3, 5, 2, 5]
def baseStart_54881 : Nat := 118140960795 + 54881 * 2 ^ 59
def prefixEnd_54881 : Nat := 4983230072969 + 3 ^ 40 * 54881 * 2
def baseEnd_54881 : Nat := 3131147977722779059457

theorem tailTrace_54881 : CollatzResearch.WordTrace tailWord_54881 prefixEnd_54881 3131147977722779059457 := by
  unfold tailWord_54881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001674514182984773692497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1334449676121989849128331 2001674514182984773692497)
  ·
    refine ⟨1501255885637238580269373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2001674514182984773692497 1501255885637238580269373)
    ·
      refine ⟨562970957113964467601015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1501255885637238580269373 562970957113964467601015)
      ·
        refine ⟨844456435670946701401523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562970957113964467601015 844456435670946701401523)
        ·
          refine ⟨1266684653506420052102285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844456435670946701401523 1266684653506420052102285)
          ·
            refine ⟨475006745064907519538357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1266684653506420052102285 475006745064907519538357)
            ·
              refine ⟨44531882349835079956721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 475006745064907519538357 44531882349835079956721)
              ·
                refine ⟨33398911762376309967541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44531882349835079956721 33398911762376309967541)
                ·
                  refine ⟨3131147977722779059457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33398911762376309967541 3131147977722779059457)
                  ·
                    rfl

theorem cell23_54881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 5].length) (baseStart_54881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54881 prefixEnd_54881 := by exact prefixLift 54881
  have htrace : WordTrace (prefixWord ++ tailWord_54881) baseStart_54881 baseEnd_54881 := by
    simpa [prefixWord, tailWord_54881, baseEnd_54881] using wordTrace_append hprefix tailTrace_54881
  have hstable : (prefixWord ++ tailWord_54881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54881).length < 2 ^ (prefixWord ++ tailWord_54881).sum := by decide
  have hdescent : baseEnd_54881 < baseStart_54881 := by decide
  rcases family_descends (prefixWord ++ tailWord_54881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54887 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_54887 : Nat := 118140960795 + 54887 * 2 ^ 59
def prefixEnd_54887 : Nat := 4983230072969 + 3 ^ 40 * 54887 * 2
def baseEnd_54887 : Nat := 28183412683431988060085

theorem tailTrace_54887 : CollatzResearch.WordTrace tailWord_54887 prefixEnd_54887 28183412683431988060085 := by
  unfold tailWord_54887
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001893352161247798410915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1334595568107498532273943 2001893352161247798410915)
  ·
    refine ⟨3002840028241871697616373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001893352161247798410915 3002840028241871697616373)
    ·
      refine ⟨281516252647675471651535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3002840028241871697616373 281516252647675471651535)
      ·
        refine ⟨422274378971513207477303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281516252647675471651535 422274378971513207477303)
        ·
          refine ⟨633411568457269811215955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422274378971513207477303 633411568457269811215955)
          ·
            refine ⟨950117352685904716823933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633411568457269811215955 950117352685904716823933)
            ·
              refine ⟨356294007257214268808975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950117352685904716823933 356294007257214268808975)
              ·
                refine ⟨534441010885821403213463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356294007257214268808975 534441010885821403213463)
                ·
                  refine ⟨801661516328732104820195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534441010885821403213463 801661516328732104820195)
                  ·
                    refine ⟨1202492274493098157230293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 801661516328732104820195 1202492274493098157230293)
                    ·
                      refine ⟨28183412683431988060085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1202492274493098157230293 28183412683431988060085)
                      ·
                        rfl

theorem cell23_54887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_54887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54887 prefixEnd_54887 := by exact prefixLift 54887
  have htrace : WordTrace (prefixWord ++ tailWord_54887) baseStart_54887 baseEnd_54887 := by
    simpa [prefixWord, tailWord_54887, baseEnd_54887] using wordTrace_append hprefix tailTrace_54887
  have hstable : (prefixWord ++ tailWord_54887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54887).length < 2 ^ (prefixWord ++ tailWord_54887).sum := by decide
  have hdescent : baseEnd_54887 < baseStart_54887 := by decide
  rcases family_descends (prefixWord ++ tailWord_54887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54897 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_54897 : Nat := 118140960795 + 54897 * 2 ^ 59
def prefixEnd_54897 : Nat := 4983230072969 + 3 ^ 40 * 54897 * 2
def baseEnd_54897 : Nat := 28188547489976948935039

theorem tailTrace_54897 : CollatzResearch.WordTrace tailWord_54897 prefixEnd_54897 28188547489976948935039 := by
  unfold tailWord_54897
  simp only [CollatzResearch.WordTrace]
  refine ⟨2002258082125019506274945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1334838721416679670849963 2002258082125019506274945)
  ·
    refine ⟨1501693561593764629706209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2002258082125019506274945 1501693561593764629706209)
    ·
      refine ⟨1126270171195323472279657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1501693561593764629706209 1126270171195323472279657)
      ·
        refine ⟨844702628396492604209743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1126270171195323472279657 844702628396492604209743)
        ·
          refine ⟨1267053942594738906314615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844702628396492604209743 1267053942594738906314615)
          ·
            refine ⟨1900580913892108359471923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267053942594738906314615 1900580913892108359471923)
            ·
              refine ⟨2850871370838162539207885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900580913892108359471923 2850871370838162539207885)
              ·
                refine ⟨1069076764064310952202957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2850871370838162539207885 1069076764064310952202957)
                ·
                  refine ⟨400903786524116607076109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069076764064310952202957 400903786524116607076109)
                  ·
                    refine ⟨150338919946543727653541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400903786524116607076109 150338919946543727653541)
                    ·
                      refine ⟨28188547489976948935039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 150338919946543727653541 28188547489976948935039)
                      ·
                        rfl

theorem cell23_54897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_54897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54897 prefixEnd_54897 := by exact prefixLift 54897
  have htrace : WordTrace (prefixWord ++ tailWord_54897) baseStart_54897 baseEnd_54897 := by
    simpa [prefixWord, tailWord_54897, baseEnd_54897] using wordTrace_append hprefix tailTrace_54897
  have hstable : (prefixWord ++ tailWord_54897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54897).length < 2 ^ (prefixWord ++ tailWord_54897).sum := by decide
  have hdescent : baseEnd_54897 < baseStart_54897 := by decide
  rcases family_descends (prefixWord ++ tailWord_54897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54932 : List Nat := [2, 4, 2, 2, 3, 1, 2, 2, 5]
def baseStart_54932 : Nat := 118140960795 + 54932 * 2 ^ 59
def prefixEnd_54932 : Nat := 4983230072969 + 3 ^ 40 * 54932 * 2
def baseEnd_54932 : Nat := 3134057701431590221931

theorem tailTrace_54932 : CollatzResearch.WordTrace tailWord_54932 prefixEnd_54932 3134057701431590221931 := by
  unfold tailWord_54932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001767318499110241899525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1335689757998813655866033 1001767318499110241899525)
  ·
    refine ⟨187831372218583170356161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1001767318499110241899525 187831372218583170356161)
    ·
      refine ⟨140873529163937377767121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187831372218583170356161 140873529163937377767121)
      ·
        refine ⟨105655146872953033325341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140873529163937377767121 105655146872953033325341)
        ·
          refine ⟨39620680077357387497003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105655146872953033325341 39620680077357387497003)
          ·
            refine ⟨59431020116036081245505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39620680077357387497003 59431020116036081245505)
            ·
              refine ⟨44573265087027060934129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59431020116036081245505 44573265087027060934129)
              ·
                refine ⟨33429948815270295700597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44573265087027060934129 33429948815270295700597)
                ·
                  refine ⟨3134057701431590221931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33429948815270295700597 3134057701431590221931)
                  ·
                    rfl

theorem cell23_54932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_54932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54932 prefixEnd_54932 := by exact prefixLift 54932
  have htrace : WordTrace (prefixWord ++ tailWord_54932) baseStart_54932 baseEnd_54932 := by
    simpa [prefixWord, tailWord_54932, baseEnd_54932] using wordTrace_append hprefix tailTrace_54932
  have hstable : (prefixWord ++ tailWord_54932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54932).length < 2 ^ (prefixWord ++ tailWord_54932).sum := by decide
  have hdescent : baseEnd_54932 < baseStart_54932 := by decide
  rcases family_descends (prefixWord ++ tailWord_54932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54965 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_54965 : Nat := 118140960795 + 54965 * 2 ^ 59
def prefixEnd_54965 : Nat := 4983230072969 + 3 ^ 40 * 54965 * 2
def baseEnd_54965 : Nat := 28223464174482682884727

theorem tailTrace_54965 : CollatzResearch.WordTrace tailWord_54965 prefixEnd_54965 28223464174482682884727 := by
  unfold tailWord_54965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004738245878667119750349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1336492163919111413166899 2004738245878667119750349)
  ·
    refine ⟨751776842204500169906381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2004738245878667119750349 751776842204500169906381)
    ·
      refine ⟨281916315826687563714893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 751776842204500169906381 281916315826687563714893)
      ·
        refine ⟨105718618435007836393085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281916315826687563714893 105718618435007836393085)
        ·
          refine ⟨39644481913127938647407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105718618435007836393085 39644481913127938647407)
          ·
            refine ⟨59466722869691907971111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39644481913127938647407 59466722869691907971111)
            ·
              refine ⟨89200084304537861956667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59466722869691907971111 89200084304537861956667)
              ·
                refine ⟨133800126456806792935001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89200084304537861956667 133800126456806792935001)
                ·
                  refine ⟨100350094842605094701251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133800126456806792935001 100350094842605094701251)
                  ·
                    refine ⟨150525142263907642051877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100350094842605094701251 150525142263907642051877)
                    ·
                      refine ⟨28223464174482682884727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 150525142263907642051877 28223464174482682884727)
                      ·
                        rfl

theorem cell23_54965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_54965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54965 prefixEnd_54965 := by exact prefixLift 54965
  have htrace : WordTrace (prefixWord ++ tailWord_54965) baseStart_54965 baseEnd_54965 := by
    simpa [prefixWord, tailWord_54965, baseEnd_54965] using wordTrace_append hprefix tailTrace_54965
  have hstable : (prefixWord ++ tailWord_54965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54965).length < 2 ^ (prefixWord ++ tailWord_54965).sum := by decide
  have hdescent : baseEnd_54965 < baseStart_54965 := by decide
  rcases family_descends (prefixWord ++ tailWord_54965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54988 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 6]
def baseStart_54988 : Nat := 118140960795 + 54988 * 2 ^ 59
def prefixEnd_54988 : Nat := 4983230072969 + 3 ^ 40 * 54988 * 2
def baseEnd_54988 : Nat := 3137252692170676988569

theorem tailTrace_54988 : CollatzResearch.WordTrace tailWord_54988 prefixEnd_54988 3137252692170676988569 := by
  unfold tailWord_54988
  simp only [CollatzResearch.WordTrace]
  refine ⟨1002788562397671023918809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1337051416530228031891745 1002788562397671023918809)
  ·
    refine ⟨752091421798253267939107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1002788562397671023918809 752091421798253267939107)
    ·
      refine ⟨1128137132697379901908661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752091421798253267939107 1128137132697379901908661)
      ·
        refine ⟨105762856190379365803937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1128137132697379901908661 105762856190379365803937)
        ·
          refine ⟨79322142142784524352953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105762856190379365803937 79322142142784524352953)
          ·
            refine ⟨59491606607088393264715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79322142142784524352953 59491606607088393264715)
            ·
              refine ⟨89237409910632589897073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59491606607088393264715 89237409910632589897073)
              ·
                refine ⟨66928057432974442422805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89237409910632589897073 66928057432974442422805)
                ·
                  refine ⟨3137252692170676988569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66928057432974442422805 3137252692170676988569)
                  ·
                    rfl

theorem cell23_54988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_54988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54988 prefixEnd_54988 := by exact prefixLift 54988
  have htrace : WordTrace (prefixWord ++ tailWord_54988) baseStart_54988 baseEnd_54988 := by
    simpa [prefixWord, tailWord_54988, baseEnd_54988] using wordTrace_append hprefix tailTrace_54988
  have hstable : (prefixWord ++ tailWord_54988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54988).length < 2 ^ (prefixWord ++ tailWord_54988).sum := by decide
  have hdescent : baseEnd_54988 < baseStart_54988 := by decide
  rcases family_descends (prefixWord ++ tailWord_54988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54991 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 2, 3, 2]
def baseStart_54991 : Nat := 118140960795 + 54991 * 2 ^ 59
def prefixEnd_54991 : Nat := 4983230072969 + 3 ^ 40 * 54991 * 2
def baseEnd_54991 : Nat := 28236814671499581159607

theorem tailTrace_54991 : CollatzResearch.WordTrace tailWord_54991 prefixEnd_54991 28236814671499581159607 := by
  unfold tailWord_54991
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005686543784473560196827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1337124362522982373464551 2005686543784473560196827)
  ·
    refine ⟨3008529815676710340295241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2005686543784473560196827 3008529815676710340295241)
    ·
      refine ⟨2256397361757532755221431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3008529815676710340295241 2256397361757532755221431)
      ·
        refine ⟨3384596042636299132832147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256397361757532755221431 3384596042636299132832147)
        ·
          refine ⟨5076894063954448699248221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384596042636299132832147 5076894063954448699248221)
          ·
            refine ⟨1903835273982918262218083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5076894063954448699248221 1903835273982918262218083)
            ·
              refine ⟨2855752910974377393327125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903835273982918262218083 2855752910974377393327125)
              ·
                refine ⟨133863417701923940312209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2855752910974377393327125 133863417701923940312209)
                ·
                  refine ⟨100397563276442955234157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133863417701923940312209 100397563276442955234157)
                  ·
                    refine ⟨37649086228666108212809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100397563276442955234157 37649086228666108212809)
                    ·
                      refine ⟨28236814671499581159607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37649086228666108212809 28236814671499581159607)
                      ·
                        rfl

theorem cell23_54991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3, 2].length) (baseStart_54991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_54991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_54991 prefixEnd_54991 := by exact prefixLift 54991
  have htrace : WordTrace (prefixWord ++ tailWord_54991) baseStart_54991 baseEnd_54991 := by
    simpa [prefixWord, tailWord_54991, baseEnd_54991] using wordTrace_append hprefix tailTrace_54991
  have hstable : (prefixWord ++ tailWord_54991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54991).length < 2 ^ (prefixWord ++ tailWord_54991).sum := by decide
  have hdescent : baseEnd_54991 < baseStart_54991 := by decide
  rcases family_descends (prefixWord ++ tailWord_54991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55005 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 6]
def baseStart_55005 : Nat := 118140960795 + 55005 * 2 ^ 59
def prefixEnd_55005 : Nat := 4983230072969 + 3 ^ 40 * 55005 * 2
def baseEnd_55005 : Nat := 3138222600073614042727

theorem tailTrace_55005 : CollatzResearch.WordTrace tailWord_55005 prefixEnd_55005 3138222600073614042727 := by
  unfold tailWord_55005
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006197165733753951206469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1337464777155835967470979 2006197165733753951206469)
  ·
    refine ⟨376161968575078865851213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2006197165733753951206469 376161968575078865851213)
    ·
      refine ⟨141060738215654574694205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376161968575078865851213 141060738215654574694205)
      ·
        refine ⟨52897776830870465510327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141060738215654574694205 52897776830870465510327)
        ·
          refine ⟨79346665246305698265491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52897776830870465510327 79346665246305698265491)
          ·
            refine ⟨119019997869458547398237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79346665246305698265491 119019997869458547398237)
            ·
              refine ⟨44632499201046955274339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119019997869458547398237 44632499201046955274339)
              ·
                refine ⟨66948748801570432911509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44632499201046955274339 66948748801570432911509)
                ·
                  refine ⟨3138222600073614042727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66948748801570432911509 3138222600073614042727)
                  ·
                    rfl

theorem cell23_55005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_55005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55005 prefixEnd_55005 := by exact prefixLift 55005
  have htrace : WordTrace (prefixWord ++ tailWord_55005) baseStart_55005 baseEnd_55005 := by
    simpa [prefixWord, tailWord_55005, baseEnd_55005] using wordTrace_append hprefix tailTrace_55005
  have hstable : (prefixWord ++ tailWord_55005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55005).length < 2 ^ (prefixWord ++ tailWord_55005).sum := by decide
  have hdescent : baseEnd_55005 < baseStart_55005 := by decide
  rcases family_descends (prefixWord ++ tailWord_55005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55034 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_55034 : Nat := 118140960795 + 55034 * 2 ^ 59
def prefixEnd_55034 : Nat := 4983230072969 + 3 ^ 40 * 55034 * 2
def baseEnd_55034 : Nat := 28258894339642912921909

theorem tailTrace_55034 : CollatzResearch.WordTrace tailWord_55034 prefixEnd_55034 28258894339642912921909 := by
  unfold tailWord_55034
  simp only [CollatzResearch.WordTrace]
  refine ⟨501813720657172976003039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1338169921752461269341437 501813720657172976003039)
  ·
    refine ⟨752720580985759464004559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 501813720657172976003039 752720580985759464004559)
    ·
      refine ⟨1129080871478639196006839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752720580985759464004559 1129080871478639196006839)
      ·
        refine ⟨1693621307217958794010259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129080871478639196006839 1693621307217958794010259)
        ·
          refine ⟨2540431960826938191015389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693621307217958794010259 2540431960826938191015389)
          ·
            refine ⟨952661985310101821630771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2540431960826938191015389 952661985310101821630771)
            ·
              refine ⟨1428992977965152732446157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952661985310101821630771 1428992977965152732446157)
              ·
                refine ⟨535872366736932274667309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1428992977965152732446157 535872366736932274667309)
                ·
                  refine ⟨200952137526349603000241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535872366736932274667309 200952137526349603000241)
                  ·
                    refine ⟨150714103144762202250181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200952137526349603000241 150714103144762202250181)
                    ·
                      refine ⟨28258894339642912921909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 150714103144762202250181 28258894339642912921909)
                      ·
                        rfl

theorem cell23_55034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_55034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55034 prefixEnd_55034 := by exact prefixLift 55034
  have htrace : WordTrace (prefixWord ++ tailWord_55034) baseStart_55034 baseEnd_55034 := by
    simpa [prefixWord, tailWord_55034, baseEnd_55034] using wordTrace_append hprefix tailTrace_55034
  have hstable : (prefixWord ++ tailWord_55034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55034).length < 2 ^ (prefixWord ++ tailWord_55034).sum := by decide
  have hdescent : baseEnd_55034 < baseStart_55034 := by decide
  rcases family_descends (prefixWord ++ tailWord_55034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55044 : List Nat := [2, 3, 2, 2, 1, 2, 11]
def baseStart_55044 : Nat := 118140960795 + 55044 * 2 ^ 59
def prefixEnd_55044 : Nat := 4983230072969 + 3 ^ 40 * 55044 * 2
def baseEnd_55044 : Nat := 348938631434418195023

theorem tailTrace_55044 : CollatzResearch.WordTrace tailWord_55044 prefixEnd_55044 348938631434418195023 := by
  unfold tailWord_55044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003809806296231805938093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1338413075061642407917457 1003809806296231805938093)
  ·
    refine ⟨376428677361086927226785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1003809806296231805938093 376428677361086927226785)
    ·
      refine ⟨282321508020815195420089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376428677361086927226785 282321508020815195420089)
      ·
        refine ⟨211741131015611396565067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282321508020815195420089 211741131015611396565067)
        ·
          refine ⟨317611696523417094847601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211741131015611396565067 317611696523417094847601)
          ·
            refine ⟨238208772392562821135701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317611696523417094847601 238208772392562821135701)
            ·
              refine ⟨348938631434418195023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 238208772392562821135701 348938631434418195023)
              ·
                rfl

theorem cell23_55044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 11].length) (baseStart_55044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55044 prefixEnd_55044 := by exact prefixLift 55044
  have htrace : WordTrace (prefixWord ++ tailWord_55044) baseStart_55044 baseEnd_55044 := by
    simpa [prefixWord, tailWord_55044, baseEnd_55044] using wordTrace_append hprefix tailTrace_55044
  have hstable : (prefixWord ++ tailWord_55044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55044).length < 2 ^ (prefixWord ++ tailWord_55044).sum := by decide
  have hdescent : baseEnd_55044 < baseStart_55044 := by decide
  rcases family_descends (prefixWord ++ tailWord_55044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55058 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_55058 : Nat := 118140960795 + 55058 * 2 ^ 59
def prefixEnd_55058 : Nat := 4983230072969 + 3 ^ 40 * 55058 * 2
def baseEnd_55058 : Nat := 28271217875350819021799

theorem tailTrace_55058 : CollatzResearch.WordTrace tailWord_55058 prefixEnd_55058 28271217875350819021799 := by
  unfold tailWord_55058
  simp only [CollatzResearch.WordTrace]
  refine ⟨502032558635436000721457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1338753489694496001923885 502032558635436000721457)
  ·
    refine ⟨376524418976577000541093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 502032558635436000721457 376524418976577000541093)
    ·
      refine ⟨70598328558108187601455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376524418976577000541093 70598328558108187601455)
      ·
        refine ⟨105897492837162281402183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70598328558108187601455 105897492837162281402183)
        ·
          refine ⟨158846239255743422103275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105897492837162281402183 158846239255743422103275)
          ·
            refine ⟨238269358883615133154913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158846239255743422103275 238269358883615133154913)
            ·
              refine ⟨178702019162711349866185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238269358883615133154913 178702019162711349866185)
              ·
                refine ⟨134026514372033512399639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178702019162711349866185 134026514372033512399639)
                ·
                  refine ⟨201039771558050268599459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134026514372033512399639 201039771558050268599459)
                  ·
                    refine ⟨301559657337075402899189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 201039771558050268599459 301559657337075402899189)
                    ·
                      refine ⟨28271217875350819021799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 301559657337075402899189 28271217875350819021799)
                      ·
                        rfl

theorem cell23_55058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_55058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55058 prefixEnd_55058 := by exact prefixLift 55058
  have htrace : WordTrace (prefixWord ++ tailWord_55058) baseStart_55058 baseEnd_55058 := by
    simpa [prefixWord, tailWord_55058, baseEnd_55058] using wordTrace_append hprefix tailTrace_55058
  have hstable : (prefixWord ++ tailWord_55058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55058).length < 2 ^ (prefixWord ++ tailWord_55058).sum := by decide
  have hdescent : baseEnd_55058 < baseStart_55058 := by decide
  rcases family_descends (prefixWord ++ tailWord_55058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55071 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 3]
def baseStart_55071 : Nat := 118140960795 + 55071 * 2 ^ 59
def prefixEnd_55071 : Nat := 4983230072969 + 3 ^ 40 * 55071 * 2
def baseEnd_55071 : Nat := 28277893123859268159239

theorem tailTrace_55071 : CollatzResearch.WordTrace tailWord_55071 prefixEnd_55071 28277893123859268159239 := by
  unfold tailWord_55071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008604383494647223109067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1339069588996431482072711 2008604383494647223109067)
  ·
    refine ⟨3012906575241970834663601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2008604383494647223109067 3012906575241970834663601)
    ·
      refine ⟨2259679931431478125997701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3012906575241970834663601 2259679931431478125997701)
      ·
        refine ⟨423689987143402148624569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2259679931431478125997701 423689987143402148624569)
        ·
          refine ⟨317767490357551611468427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423689987143402148624569 317767490357551611468427)
          ·
            refine ⟨476651235536327417202641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317767490357551611468427 476651235536327417202641)
            ·
              refine ⟨357488426652245562901981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476651235536327417202641 357488426652245562901981)
              ·
                refine ⟨134058159994592086088243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357488426652245562901981 134058159994592086088243)
                ·
                  refine ⟨201087239991888129132365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134058159994592086088243 201087239991888129132365)
                  ·
                    refine ⟨75407714996958048424637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201087239991888129132365 75407714996958048424637)
                    ·
                      refine ⟨28277893123859268159239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 75407714996958048424637 28277893123859268159239)
                      ·
                        rfl

theorem cell23_55071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_55071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55071 prefixEnd_55071 := by exact prefixLift 55071
  have htrace : WordTrace (prefixWord ++ tailWord_55071) baseStart_55071 baseEnd_55071 := by
    simpa [prefixWord, tailWord_55071, baseEnd_55071] using wordTrace_append hprefix tailTrace_55071
  have hstable : (prefixWord ++ tailWord_55071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55071).length < 2 ^ (prefixWord ++ tailWord_55071).sum := by decide
  have hdescent : baseEnd_55071 < baseStart_55071 := by decide
  rcases family_descends (prefixWord ++ tailWord_55071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55092 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_55092 : Nat := 118140960795 + 55092 * 2 ^ 59
def prefixEnd_55092 : Nat := 4983230072969 + 3 ^ 40 * 55092 * 2
def baseEnd_55092 : Nat := 28288676217603685996643

theorem tailTrace_55092 : CollatzResearch.WordTrace tailWord_55092 prefixEnd_55092 28288676217603685996643 := by
  unfold tailWord_55092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004685158209283904811765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1339580210945711873082353 1004685158209283904811765)
  ·
    refine ⟨94189233582120366076103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1004685158209283904811765 94189233582120366076103)
    ·
      refine ⟨141283850373180549114155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94189233582120366076103 141283850373180549114155)
      ·
        refine ⟨211925775559770823671233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141283850373180549114155 211925775559770823671233)
        ·
          refine ⟨158944331669828117753425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211925775559770823671233 158944331669828117753425)
          ·
            refine ⟨119208248752371088315069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158944331669828117753425 119208248752371088315069)
            ·
              refine ⟨44703093282139158118151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119208248752371088315069 44703093282139158118151)
              ·
                refine ⟨67054639923208737177227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44703093282139158118151 67054639923208737177227)
                ·
                  refine ⟨100581959884813105765841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67054639923208737177227 100581959884813105765841)
                  ·
                    refine ⟨75436469913609829324381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100581959884813105765841 75436469913609829324381)
                    ·
                      refine ⟨28288676217603685996643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 75436469913609829324381 28288676217603685996643)
                      ·
                        rfl

theorem cell23_55092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_55092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55092 prefixEnd_55092 := by exact prefixLift 55092
  have htrace : WordTrace (prefixWord ++ tailWord_55092) baseStart_55092 baseEnd_55092 := by
    simpa [prefixWord, tailWord_55092, baseEnd_55092] using wordTrace_append hprefix tailTrace_55092
  have hstable : (prefixWord ++ tailWord_55092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55092).length < 2 ^ (prefixWord ++ tailWord_55092).sum := by decide
  have hdescent : baseEnd_55092 < baseStart_55092 := by decide
  rcases family_descends (prefixWord ++ tailWord_55092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55121 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 2, 6]
def baseStart_55121 : Nat := 118140960795 + 55121 * 2 ^ 59
def prefixEnd_55121 : Nat := 4983230072969 + 3 ^ 40 * 55121 * 2
def baseEnd_55121 : Nat := 9434522385528024178003

theorem tailTrace_55121 : CollatzResearch.WordTrace tailWord_55121 prefixEnd_55121 9434522385528024178003 := by
  unfold tailWord_55121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010428033313505762429217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1340285355542337174952811 2010428033313505762429217)
  ·
    refine ⟨1507821024985129321821913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2010428033313505762429217 1507821024985129321821913)
    ·
      refine ⟨1130865768738846991366435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1507821024985129321821913 1130865768738846991366435)
      ·
        refine ⟨1696298653108270487049653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130865768738846991366435 1696298653108270487049653)
        ·
          refine ⟨159027998728900358160905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1696298653108270487049653 159027998728900358160905)
          ·
            refine ⟨119270999046675268620679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159027998728900358160905 119270999046675268620679)
            ·
              refine ⟨178906498570012902931019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119270999046675268620679 178906498570012902931019)
              ·
                refine ⟨268359747855019354396529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178906498570012902931019 268359747855019354396529)
                ·
                  refine ⟨201269810891264515797397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268359747855019354396529 201269810891264515797397)
                  ·
                    refine ⟨9434522385528024178003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201269810891264515797397 9434522385528024178003)
                    ·
                      rfl

theorem cell23_55121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_55121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55121 prefixEnd_55121 := by exact prefixLift 55121
  have htrace : WordTrace (prefixWord ++ tailWord_55121) baseStart_55121 baseEnd_55121 := by
    simpa [prefixWord, tailWord_55121, baseEnd_55121] using wordTrace_append hprefix tailTrace_55121
  have hstable : (prefixWord ++ tailWord_55121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55121).length < 2 ^ (prefixWord ++ tailWord_55121).sum := by decide
  have hdescent : baseEnd_55121 < baseStart_55121 := by decide
  rcases family_descends (prefixWord ++ tailWord_55121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55128 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 8, 2, 2]
def baseStart_55128 : Nat := 118140960795 + 55128 * 2 ^ 59
def prefixEnd_55128 : Nat := 4983230072969 + 3 ^ 40 * 55128 * 2
def baseEnd_55128 : Nat := 28307161521165545146477

theorem tailTrace_55128 : CollatzResearch.WordTrace tailWord_55128 prefixEnd_55128 28307161521165545146477 := by
  unfold tailWord_55128
  simp only [CollatzResearch.WordTrace]
  refine ⟨1005341672144072978967019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1340455562858763971956025 1005341672144072978967019)
  ·
    refine ⟨1508012508216109468450529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1005341672144072978967019 1508012508216109468450529)
    ·
      refine ⟨1131009381162082101337897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1508012508216109468450529 1131009381162082101337897)
      ·
        refine ⟨848257035871561576003423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131009381162082101337897 848257035871561576003423)
        ·
          refine ⟨1272385553807342364005135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848257035871561576003423 1272385553807342364005135)
          ·
            refine ⟨1908578330711013546007703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272385553807342364005135 1908578330711013546007703)
            ·
              refine ⟨2862867496066520319011555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908578330711013546007703 2862867496066520319011555)
              ·
                refine ⟨4294301244099780478517333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862867496066520319011555 4294301244099780478517333)
                ·
                  refine ⟨50323842704294302482625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4294301244099780478517333 50323842704294302482625)
                  ·
                    refine ⟨37742882028220726861969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50323842704294302482625 37742882028220726861969)
                    ·
                      refine ⟨28307161521165545146477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37742882028220726861969 28307161521165545146477)
                      ·
                        rfl

theorem cell23_55128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_55128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55128 prefixEnd_55128 := by exact prefixLift 55128
  have htrace : WordTrace (prefixWord ++ tailWord_55128) baseStart_55128 baseEnd_55128 := by
    simpa [prefixWord, tailWord_55128, baseEnd_55128] using wordTrace_append hprefix tailTrace_55128
  have hstable : (prefixWord ++ tailWord_55128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55128).length < 2 ^ (prefixWord ++ tailWord_55128).sum := by decide
  have hdescent : baseEnd_55128 < baseStart_55128 := by decide
  rcases family_descends (prefixWord ++ tailWord_55128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55161 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 3]
def baseStart_55161 : Nat := 118140960795 + 55161 * 2 ^ 59
def prefixEnd_55161 : Nat := 4983230072969 + 3 ^ 40 * 55161 * 2
def baseEnd_55161 : Nat := 28324106382763916033825

theorem tailTrace_55161 : CollatzResearch.WordTrace tailWord_55161 prefixEnd_55161 28324106382763916033825 := by
  unfold tailWord_55161
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011886953168592593885337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1341257968779061729256891 2011886953168592593885337)
  ·
    refine ⟨1508915214876444445414003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2011886953168592593885337 1508915214876444445414003)
    ·
      refine ⟨2263372822314666668121005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1508915214876444445414003 2263372822314666668121005)
      ·
        refine ⟨848764808368000000545377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2263372822314666668121005 848764808368000000545377)
        ·
          refine ⟨636573606276000000409033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848764808368000000545377 636573606276000000409033)
          ·
            refine ⟨477430204707000000306775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636573606276000000409033 477430204707000000306775)
            ·
              refine ⟨716145307060500000460163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477430204707000000306775 716145307060500000460163)
              ·
                refine ⟨1074217960590750000690245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716145307060500000460163 1074217960590750000690245)
                ·
                  refine ⟨201415867610765625129421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074217960590750000690245 201415867610765625129421)
                  ·
                    refine ⟨75530950354037109423533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201415867610765625129421 75530950354037109423533)
                    ·
                      refine ⟨28324106382763916033825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 75530950354037109423533 28324106382763916033825)
                      ·
                        rfl

theorem cell23_55161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_55161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55161 prefixEnd_55161 := by exact prefixLift 55161
  have htrace : WordTrace (prefixWord ++ tailWord_55161) baseStart_55161 baseEnd_55161 := by
    simpa [prefixWord, tailWord_55161, baseEnd_55161] using wordTrace_append hprefix tailTrace_55161
  have hstable : (prefixWord ++ tailWord_55161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55161).length < 2 ^ (prefixWord ++ tailWord_55161).sum := by decide
  have hdescent : baseEnd_55161 < baseStart_55161 := by decide
  rcases family_descends (prefixWord ++ tailWord_55161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55202 : List Nat := [3, 3, 1, 2, 3, 2, 1, 3, 5]
def baseStart_55202 : Nat := 118140960795 + 55202 * 2 ^ 59
def prefixEnd_55202 : Nat := 4983230072969 + 3 ^ 40 * 55202 * 2
def baseEnd_55202 : Nat := 3149462121066472846793

theorem tailTrace_55202 : CollatzResearch.WordTrace tailWord_55202 prefixEnd_55202 3149462121066472846793 := by
  unfold tailWord_55202
  simp only [CollatzResearch.WordTrace]
  refine ⟨503345586505014149031965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1342254897346704397418573 503345586505014149031965)
  ·
    refine ⟨188754594939380305886987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 503345586505014149031965 188754594939380305886987)
    ·
      refine ⟨283131892409070458830481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188754594939380305886987 283131892409070458830481)
      ·
        refine ⟨212348919306802844122861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283131892409070458830481 212348919306802844122861)
        ·
          refine ⟨79630844740051066546073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212348919306802844122861 79630844740051066546073)
          ·
            refine ⟨59723133555038299909555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79630844740051066546073 59723133555038299909555)
            ·
              refine ⟨89584700332557449864333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59723133555038299909555 89584700332557449864333)
              ·
                refine ⟨33594262624709043699125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89584700332557449864333 33594262624709043699125)
                ·
                  refine ⟨3149462121066472846793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33594262624709043699125 3149462121066472846793)
                  ·
                    rfl

theorem cell23_55202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_55202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55202 prefixEnd_55202 := by exact prefixLift 55202
  have htrace : WordTrace (prefixWord ++ tailWord_55202) baseStart_55202 baseEnd_55202 := by
    simpa [prefixWord, tailWord_55202, baseEnd_55202] using wordTrace_append hprefix tailTrace_55202
  have hstable : (prefixWord ++ tailWord_55202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55202).length < 2 ^ (prefixWord ++ tailWord_55202).sum := by decide
  have hdescent : baseEnd_55202 < baseStart_55202 := by decide
  rcases family_descends (prefixWord ++ tailWord_55202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55218 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_55218 : Nat := 118140960795 + 55218 * 2 ^ 59
def prefixEnd_55218 : Nat := 4983230072969 + 3 ^ 40 * 55218 * 2
def baseEnd_55218 : Nat := 28353374780070193021063

theorem tailTrace_55218 : CollatzResearch.WordTrace tailWord_55218 prefixEnd_55218 28353374780070193021063 := by
  unfold tailWord_55218
  simp only [CollatzResearch.WordTrace]
  refine ⟨503491478490522832177577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1342643942641394219140205 503491478490522832177577)
  ·
    refine ⟨377618608867892124133183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 503491478490522832177577 377618608867892124133183)
    ·
      refine ⟨566427913301838186199775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377618608867892124133183 566427913301838186199775)
      ·
        refine ⟨849641869952757279299663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566427913301838186199775 849641869952757279299663)
        ·
          refine ⟨1274462804929135918949495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849641869952757279299663 1274462804929135918949495)
          ·
            refine ⟨1911694207393703878424243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274462804929135918949495 1911694207393703878424243)
            ·
              refine ⟨2867541311090555817636365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911694207393703878424243 2867541311090555817636365)
              ·
                refine ⟨1075327991658958431613637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2867541311090555817636365 1075327991658958431613637)
                ·
                  refine ⟨201623998436054705927557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1075327991658958431613637 201623998436054705927557)
                  ·
                    refine ⟨37804499706760257361417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201623998436054705927557 37804499706760257361417)
                    ·
                      refine ⟨28353374780070193021063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37804499706760257361417 28353374780070193021063)
                      ·
                        rfl

theorem cell23_55218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_55218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55218 prefixEnd_55218 := by exact prefixLift 55218
  have htrace : WordTrace (prefixWord ++ tailWord_55218) baseStart_55218 baseEnd_55218 := by
    simpa [prefixWord, tailWord_55218, baseEnd_55218] using wordTrace_append hprefix tailTrace_55218
  have hstable : (prefixWord ++ tailWord_55218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55218).length < 2 ^ (prefixWord ++ tailWord_55218).sum := by decide
  have hdescent : baseEnd_55218 < baseStart_55218 := by decide
  rcases family_descends (prefixWord ++ tailWord_55218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55241 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 6]
def baseStart_55241 : Nat := 118140960795 + 55241 * 2 ^ 59
def prefixEnd_55241 : Nat := 4983230072969 + 3 ^ 40 * 55241 * 2
def baseEnd_55241 : Nat := 3151687203902622559273

theorem tailTrace_55241 : CollatzResearch.WordTrace tailWord_55241 prefixEnd_55241 3151687203902622559273 := by
  unfold tailWord_55241
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014804792878766256797577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1343203195252510837865051 2014804792878766256797577)
  ·
    refine ⟨1511103594659074692598183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2014804792878766256797577 1511103594659074692598183)
    ·
      refine ⟨2266655391988612038897275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511103594659074692598183 2266655391988612038897275)
      ·
        refine ⟨3399983087982918058345913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266655391988612038897275 3399983087982918058345913)
        ·
          refine ⟨2549987315987188543759435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3399983087982918058345913 2549987315987188543759435)
          ·
            refine ⟨3824980973980782815639153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549987315987188543759435 3824980973980782815639153)
            ·
              refine ⟨2868735730485587111729365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3824980973980782815639153 2868735730485587111729365)
              ·
                refine ⟨67235993683255947931157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2868735730485587111729365 67235993683255947931157)
                ·
                  refine ⟨3151687203902622559273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67235993683255947931157 3151687203902622559273)
                  ·
                    rfl

theorem cell23_55241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 6].length) (baseStart_55241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55241 prefixEnd_55241 := by exact prefixLift 55241
  have htrace : WordTrace (prefixWord ++ tailWord_55241) baseStart_55241 baseEnd_55241 := by
    simpa [prefixWord, tailWord_55241, baseEnd_55241] using wordTrace_append hprefix tailTrace_55241
  have hstable : (prefixWord ++ tailWord_55241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55241).length < 2 ^ (prefixWord ++ tailWord_55241).sum := by decide
  have hdescent : baseEnd_55241 < baseStart_55241 := by decide
  rcases family_descends (prefixWord ++ tailWord_55241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55308 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_55308 : Nat := 118140960795 + 55308 * 2 ^ 59
def prefixEnd_55308 : Nat := 4983230072969 + 3 ^ 40 * 55308 * 2
def baseEnd_55308 : Nat := 28399588038974840895649

theorem tailTrace_55308 : CollatzResearch.WordTrace tailWord_55308 prefixEnd_55308 28399588038974840895649 := by
  unfold tailWord_55308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008624241818018349743289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1344832322424024466324385 1008624241818018349743289)
  ·
    refine ⟨756468181363513762307467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1008624241818018349743289 756468181363513762307467)
    ·
      refine ⟨1134702272045270643461201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756468181363513762307467 1134702272045270643461201)
      ·
        refine ⟨851026704033952982595901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1134702272045270643461201 851026704033952982595901)
        ·
          refine ⟨319135014012732368473463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851026704033952982595901 319135014012732368473463)
          ·
            refine ⟨478702521019098552710195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319135014012732368473463 478702521019098552710195)
            ·
              refine ⟨718053781528647829065293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478702521019098552710195 718053781528647829065293)
              ·
                refine ⟨269270168073242935899485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718053781528647829065293 269270168073242935899485)
                ·
                  refine ⟨100976313027466100962307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269270168073242935899485 100976313027466100962307)
                  ·
                    refine ⟨151464469541199151443461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100976313027466100962307 151464469541199151443461)
                    ·
                      refine ⟨28399588038974840895649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 151464469541199151443461 28399588038974840895649)
                      ·
                        rfl

theorem cell23_55308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_55308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55308 prefixEnd_55308 := by exact prefixLift 55308
  have htrace : WordTrace (prefixWord ++ tailWord_55308) baseStart_55308 baseEnd_55308 := by
    simpa [prefixWord, tailWord_55308, baseEnd_55308] using wordTrace_append hprefix tailTrace_55308
  have hstable : (prefixWord ++ tailWord_55308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55308).length < 2 ^ (prefixWord ++ tailWord_55308).sum := by decide
  have hdescent : baseEnd_55308 < baseStart_55308 := by decide
  rcases family_descends (prefixWord ++ tailWord_55308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55321 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_55321 : Nat := 118140960795 + 55321 * 2 ^ 59
def prefixEnd_55321 : Nat := 4983230072969 + 3 ^ 40 * 55321 * 2
def baseEnd_55321 : Nat := 28406263287483290033089

theorem tailTrace_55321 : CollatzResearch.WordTrace tailWord_55321 prefixEnd_55321 28406263287483290033089 := by
  unfold tailWord_55321
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017722632588939919709817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1345148421725959946473211 2017722632588939919709817)
  ·
    refine ⟨1513291974441704939782363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2017722632588939919709817 1513291974441704939782363)
    ·
      refine ⟨2269937961662557409673545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1513291974441704939782363 2269937961662557409673545)
      ·
        refine ⟨1702453471246918057255159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2269937961662557409673545 1702453471246918057255159)
        ·
          refine ⟨2553680206870377085882739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702453471246918057255159 2553680206870377085882739)
          ·
            refine ⟨3830520310305565628824109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553680206870377085882739 3830520310305565628824109)
            ·
              refine ⟨1436445116364587110809041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3830520310305565628824109 1436445116364587110809041)
              ·
                refine ⟨1077333837273440333106781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436445116364587110809041 1077333837273440333106781)
                ·
                  refine ⟨404000188977540124915043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077333837273440333106781 404000188977540124915043)
                  ·
                    refine ⟨606000283466310187372565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 404000188977540124915043 606000283466310187372565)
                    ·
                      refine ⟨28406263287483290033089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 606000283466310187372565 28406263287483290033089)
                      ·
                        rfl

theorem cell23_55321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_55321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55321 prefixEnd_55321 := by exact prefixLift 55321
  have htrace : WordTrace (prefixWord ++ tailWord_55321) baseStart_55321 baseEnd_55321 := by
    simpa [prefixWord, tailWord_55321, baseEnd_55321] using wordTrace_append hprefix tailTrace_55321
  have hstable : (prefixWord ++ tailWord_55321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55321).length < 2 ^ (prefixWord ++ tailWord_55321).sum := by decide
  have hdescent : baseEnd_55321 < baseStart_55321 := by decide
  rcases family_descends (prefixWord ++ tailWord_55321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55322 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_55322 : Nat := 118140960795 + 55322 * 2 ^ 59
def prefixEnd_55322 : Nat := 4983230072969 + 3 ^ 40 * 55322 * 2
def baseEnd_55322 : Nat := 9468925589379262040195

theorem tailTrace_55322 : CollatzResearch.WordTrace tailWord_55322 prefixEnd_55322 9468925589379262040195 := by
  unfold tailWord_55322
  simp only [CollatzResearch.WordTrace]
  refine ⟨504439776396329272624055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1345172737056878060330813 504439776396329272624055)
  ·
    refine ⟨756659664594493908936083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 504439776396329272624055 756659664594493908936083)
    ·
      refine ⟨1134989496891740863404125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756659664594493908936083 1134989496891740863404125)
      ·
        refine ⟨425621061334402823776547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1134989496891740863404125 425621061334402823776547)
        ·
          refine ⟨638431592001604235664821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425621061334402823776547 638431592001604235664821)
          ·
            refine ⟨59852961750150397093577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 638431592001604235664821 59852961750150397093577)
            ·
              refine ⟨44889721312612797820183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59852961750150397093577 44889721312612797820183)
              ·
                refine ⟨67334581968919196730275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44889721312612797820183 67334581968919196730275)
                ·
                  refine ⟨101001872953378795095413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67334581968919196730275 101001872953378795095413)
                  ·
                    refine ⟨9468925589379262040195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101001872953378795095413 9468925589379262040195)
                    ·
                      rfl

theorem cell23_55322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_55322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55322 prefixEnd_55322 := by exact prefixLift 55322
  have htrace : WordTrace (prefixWord ++ tailWord_55322) baseStart_55322 baseEnd_55322 := by
    simpa [prefixWord, tailWord_55322, baseEnd_55322] using wordTrace_append hprefix tailTrace_55322
  have hstable : (prefixWord ++ tailWord_55322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55322).length < 2 ^ (prefixWord ++ tailWord_55322).sum := by decide
  have hdescent : baseEnd_55322 < baseStart_55322 := by decide
  rcases family_descends (prefixWord ++ tailWord_55322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55331 : List Nat := [1, 1, 1, 4, 3, 1, 12]
def baseStart_55331 : Nat := 118140960795 + 55331 * 2 ^ 59
def prefixEnd_55331 : Nat := 4983230072969 + 3 ^ 40 * 55331 * 2
def baseEnd_55331 : Nat := 350758001160842603803

theorem tailTrace_55331 : CollatzResearch.WordTrace tailWord_55331 prefixEnd_55331 350758001160842603803 := by
  unfold tailWord_55331
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018087362552711627573847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1345391575035141085049231 2018087362552711627573847)
  ·
    refine ⟨3027131043829067441360771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2018087362552711627573847 3027131043829067441360771)
    ·
      refine ⟨4540696565743601162041157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027131043829067441360771 4540696565743601162041157)
      ·
        refine ⟨851380606076925217882717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4540696565743601162041157 851380606076925217882717)
        ·
          refine ⟨319267727278846956706019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851380606076925217882717 319267727278846956706019)
          ·
            refine ⟨478901590918270435059029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319267727278846956706019 478901590918270435059029)
            ·
              refine ⟨350758001160842603803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 478901590918270435059029 350758001160842603803)
              ·
                rfl

theorem cell23_55331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 12].length) (baseStart_55331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55331 prefixEnd_55331 := by exact prefixLift 55331
  have htrace : WordTrace (prefixWord ++ tailWord_55331) baseStart_55331 baseEnd_55331 := by
    simpa [prefixWord, tailWord_55331, baseEnd_55331] using wordTrace_append hprefix tailTrace_55331
  have hstable : (prefixWord ++ tailWord_55331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55331).length < 2 ^ (prefixWord ++ tailWord_55331).sum := by decide
  have hdescent : baseEnd_55331 < baseStart_55331 := by decide
  rcases family_descends (prefixWord ++ tailWord_55331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55352 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 1, 6]
def baseStart_55352 : Nat := 118140960795 + 55352 * 2 ^ 59
def prefixEnd_55352 : Nat := 4983230072969 + 3 ^ 40 * 55352 * 2
def baseEnd_55352 : Nat := 9474060395924222915149

theorem tailTrace_55352 : CollatzResearch.WordTrace tailWord_55352 prefixEnd_55352 9474060395924222915149 := by
  unfold tailWord_55352
  simp only [CollatzResearch.WordTrace]
  refine ⟨1009426647738316107044155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1345902196984421476058873 1009426647738316107044155)
  ·
    refine ⟨1514139971607474160566233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1009426647738316107044155 1514139971607474160566233)
    ·
      refine ⟨1135604978705605620424675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1514139971607474160566233 1135604978705605620424675)
      ·
        refine ⟨1703407468058408430637013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135604978705605620424675 1703407468058408430637013)
        ·
          refine ⟨39923612532618947593055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1703407468058408430637013 39923612532618947593055)
          ·
            refine ⟨59885418798928421389583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39923612532618947593055 59885418798928421389583)
            ·
              refine ⟨89828128198392632084375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59885418798928421389583 89828128198392632084375)
              ·
                refine ⟨134742192297588948126563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89828128198392632084375 134742192297588948126563)
                ·
                  refine ⟨202113288446383422189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134742192297588948126563 202113288446383422189845)
                  ·
                    refine ⟨9474060395924222915149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 202113288446383422189845 9474060395924222915149)
                    ·
                      rfl

theorem cell23_55352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_55352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55352 prefixEnd_55352 := by exact prefixLift 55352
  have htrace : WordTrace (prefixWord ++ tailWord_55352) baseStart_55352 baseEnd_55352 := by
    simpa [prefixWord, tailWord_55352, baseEnd_55352] using wordTrace_append hprefix tailTrace_55352
  have hstable : (prefixWord ++ tailWord_55352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55352).length < 2 ^ (prefixWord ++ tailWord_55352).sum := by decide
  have hdescent : baseEnd_55352 < baseStart_55352 := by decide
  rcases family_descends (prefixWord ++ tailWord_55352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55382 : List Nat := [5, 2, 2, 1, 1, 3, 9]
def baseStart_55382 : Nat := 118140960795 + 55382 * 2 ^ 59
def prefixEnd_55382 : Nat := 4983230072969 + 3 ^ 40 * 55382 * 2
def baseEnd_55382 : Nat := 351081303795154955189

theorem tailTrace_55382 : CollatzResearch.WordTrace tailWord_55382 prefixEnd_55382 351081303795154955189 := by
  unfold tailWord_55382
  simp only [CollatzResearch.WordTrace]
  refine ⟨126246717835496708605025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1346631656911964891786933 126246717835496708605025)
  ·
    refine ⟨94685038376622531453769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126246717835496708605025 94685038376622531453769)
    ·
      refine ⟨71013778782466898590327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94685038376622531453769 71013778782466898590327)
      ·
        refine ⟨106520668173700347885491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71013778782466898590327 106520668173700347885491)
        ·
          refine ⟨159781002260550521828237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106520668173700347885491 159781002260550521828237)
          ·
            refine ⟨59917875847706445685589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159781002260550521828237 59917875847706445685589)
            ·
              refine ⟨351081303795154955189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 59917875847706445685589 351081303795154955189)
              ·
                rfl

theorem cell23_55382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 9].length) (baseStart_55382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55382 prefixEnd_55382 := by exact prefixLift 55382
  have htrace : WordTrace (prefixWord ++ tailWord_55382) baseStart_55382 baseEnd_55382 := by
    simpa [prefixWord, tailWord_55382, baseEnd_55382] using wordTrace_append hprefix tailTrace_55382
  have hstable : (prefixWord ++ tailWord_55382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55382).length < 2 ^ (prefixWord ++ tailWord_55382).sum := by decide
  have hdescent : baseEnd_55382 < baseStart_55382 := by decide
  rcases family_descends (prefixWord ++ tailWord_55382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55432 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_55432 : Nat := 118140960795 + 55432 * 2 ^ 59
def prefixEnd_55432 : Nat := 4983230072969 + 3 ^ 40 * 55432 * 2
def baseEnd_55432 : Nat := 28463259640132355745079

theorem tailTrace_55432 : CollatzResearch.WordTrace tailWord_55432 prefixEnd_55432 28463259640132355745079 := by
  unfold tailWord_55432
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010885567593402938500275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1347847423457870584667033 1010885567593402938500275)
  ·
    refine ⟨1516328351390104407750413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010885567593402938500275 1516328351390104407750413)
    ·
      refine ⟨568623131771289152906405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1516328351390104407750413 568623131771289152906405)
      ·
        refine ⟨106616837207116716169951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 568623131771289152906405 106616837207116716169951)
        ·
          refine ⟨159925255810675074254927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106616837207116716169951 159925255810675074254927)
          ·
            refine ⟨239887883716012611382391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159925255810675074254927 239887883716012611382391)
            ·
              refine ⟨359831825574018917073587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239887883716012611382391 359831825574018917073587)
              ·
                refine ⟨539747738361028375610381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359831825574018917073587 539747738361028375610381)
                ·
                  refine ⟨202405401885385640853893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539747738361028375610381 202405401885385640853893)
                  ·
                    refine ⟨37951012853509807660105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202405401885385640853893 37951012853509807660105)
                    ·
                      refine ⟨28463259640132355745079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37951012853509807660105 28463259640132355745079)
                      ·
                        rfl

theorem cell23_55432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_55432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55432 prefixEnd_55432 := by exact prefixLift 55432
  have htrace : WordTrace (prefixWord ++ tailWord_55432) baseStart_55432 baseEnd_55432 := by
    simpa [prefixWord, tailWord_55432, baseEnd_55432] using wordTrace_append hprefix tailTrace_55432
  have hstable : (prefixWord ++ tailWord_55432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55432).length < 2 ^ (prefixWord ++ tailWord_55432).sum := by decide
  have hdescent : baseEnd_55432 < baseStart_55432 := by decide
  rcases family_descends (prefixWord ++ tailWord_55432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55466 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_55466 : Nat := 118140960795 + 55466 * 2 ^ 59
def prefixEnd_55466 : Nat := 4983230072969 + 3 ^ 40 * 55466 * 2
def baseEnd_55466 : Nat := 28480717982385222719923

theorem tailTrace_55466 : CollatzResearch.WordTrace tailWord_55466 prefixEnd_55466 28480717982385222719923 := by
  unfold tailWord_55466
  simp only [CollatzResearch.WordTrace]
  refine ⟨505752804265907420934563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1348674144709086455825501 505752804265907420934563)
  ·
    refine ⟨758629206398861131401845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 505752804265907420934563 758629206398861131401845)
    ·
      refine ⟨71121488099893231068923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 758629206398861131401845 71121488099893231068923)
      ·
        refine ⟨106682232149839846603385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71121488099893231068923 106682232149839846603385)
        ·
          refine ⟨80011674112379884952539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106682232149839846603385 80011674112379884952539)
          ·
            refine ⟨120017511168569827428809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80011674112379884952539 120017511168569827428809)
            ·
              refine ⟨90013133376427370571607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120017511168569827428809 90013133376427370571607)
              ·
                refine ⟨135019700064641055857411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90013133376427370571607 135019700064641055857411)
                ·
                  refine ⟨202529550096961583786117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135019700064641055857411 202529550096961583786117)
                  ·
                    refine ⟨37974290643180296959897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202529550096961583786117 37974290643180296959897)
                    ·
                      refine ⟨28480717982385222719923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37974290643180296959897 28480717982385222719923)
                      ·
                        rfl

theorem cell23_55466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_55466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55466 prefixEnd_55466 := by exact prefixLift 55466
  have htrace : WordTrace (prefixWord ++ tailWord_55466) baseStart_55466 baseEnd_55466 := by
    simpa [prefixWord, tailWord_55466, baseEnd_55466] using wordTrace_append hprefix tailTrace_55466
  have hstable : (prefixWord ++ tailWord_55466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55466).length < 2 ^ (prefixWord ++ tailWord_55466).sum := by decide
  have hdescent : baseEnd_55466 < baseStart_55466 := by decide
  rcases family_descends (prefixWord ++ tailWord_55466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55475 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 4, 5, 2]
def baseStart_55475 : Nat := 118140960795 + 55475 * 2 ^ 59
def prefixEnd_55475 : Nat := 4983230072969 + 3 ^ 40 * 55475 * 2
def baseEnd_55475 : Nat := 28485339308275687507381

theorem tailTrace_55475 : CollatzResearch.WordTrace tailWord_55475 prefixEnd_55475 28485339308275687507381 := by
  unfold tailWord_55475
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023339474031024220815879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1348892982687349480543919 2023339474031024220815879)
  ·
    refine ⟨3035009211046536331223819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023339474031024220815879 3035009211046536331223819)
    ·
      refine ⟨4552513816569804496835729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035009211046536331223819 4552513816569804496835729)
      ·
        refine ⟨3414385362427353372626797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4552513816569804496835729 3414385362427353372626797)
        ·
          refine ⟨1280394510910257514735049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3414385362427353372626797 1280394510910257514735049)
          ·
            refine ⟨960295883182693136051287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280394510910257514735049 960295883182693136051287)
            ·
              refine ⟨1440443824774039704076931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960295883182693136051287 1440443824774039704076931)
              ·
                refine ⟨2160665737161059556115397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440443824774039704076931 2160665737161059556115397)
                ·
                  refine ⟨405124825717698666771637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160665737161059556115397 405124825717698666771637)
                  ·
                    refine ⟨37980452411034250009841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 405124825717698666771637 37980452411034250009841)
                    ·
                      refine ⟨28485339308275687507381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37980452411034250009841 28485339308275687507381)
                      ·
                        rfl

theorem cell23_55475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5, 2].length) (baseStart_55475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55475 prefixEnd_55475 := by exact prefixLift 55475
  have htrace : WordTrace (prefixWord ++ tailWord_55475) baseStart_55475 baseEnd_55475 := by
    simpa [prefixWord, tailWord_55475, baseEnd_55475] using wordTrace_append hprefix tailTrace_55475
  have hstable : (prefixWord ++ tailWord_55475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55475).length < 2 ^ (prefixWord ++ tailWord_55475).sum := by decide
  have hdescent : baseEnd_55475 < baseStart_55475 := by decide
  rcases family_descends (prefixWord ++ tailWord_55475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55500 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 2, 2, 2]
def baseStart_55500 : Nat := 118140960795 + 55500 * 2 ^ 59
def prefixEnd_55500 : Nat := 4983230072969 + 3 ^ 40 * 55500 * 2
def baseEnd_55500 : Nat := 28498176324638089694767

theorem tailTrace_55500 : CollatzResearch.WordTrace tailWord_55500 prefixEnd_55500 28498176324638089694767 := by
  unfold tailWord_55500
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012125649470226745237977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1349500865960302326983969 1012125649470226745237977)
  ·
    refine ⟨759094237102670058928483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1012125649470226745237977 759094237102670058928483)
    ·
      refine ⟨1138641355654005088392725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759094237102670058928483 1138641355654005088392725)
      ·
        refine ⟨53373813546281488518409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1138641355654005088392725 53373813546281488518409)
        ·
          refine ⟨40030360159711116388807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53373813546281488518409 40030360159711116388807)
          ·
            refine ⟨60045540239566674583211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40030360159711116388807 60045540239566674583211)
            ·
              refine ⟨90068310359350011874817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60045540239566674583211 90068310359350011874817)
              ·
                refine ⟨67551232769512508906113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90068310359350011874817 67551232769512508906113)
                ·
                  refine ⟨50663424577134381679585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67551232769512508906113 50663424577134381679585)
                  ·
                    refine ⟨37997568432850786259689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50663424577134381679585 37997568432850786259689)
                    ·
                      refine ⟨28498176324638089694767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 37997568432850786259689 28498176324638089694767)
                      ·
                        rfl

theorem cell23_55500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_55500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55500 prefixEnd_55500 := by exact prefixLift 55500
  have htrace : WordTrace (prefixWord ++ tailWord_55500) baseStart_55500 baseEnd_55500 := by
    simpa [prefixWord, tailWord_55500, baseEnd_55500] using wordTrace_append hprefix tailTrace_55500
  have hstable : (prefixWord ++ tailWord_55500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55500).length < 2 ^ (prefixWord ++ tailWord_55500).sum := by decide
  have hdescent : baseEnd_55500 < baseStart_55500 := by decide
  rcases family_descends (prefixWord ++ tailWord_55500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55505 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_55505 : Nat := 118140960795 + 55505 * 2 ^ 59
def prefixEnd_55505 : Nat := 4983230072969 + 3 ^ 40 * 55505 * 2
def baseEnd_55505 : Nat := 28500743727910570132243

theorem tailTrace_55505 : CollatzResearch.WordTrace tailWord_55505 prefixEnd_55505 28500743727910570132243 := by
  unfold tailWord_55505
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024433663922339344407969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1349622442614892896271979 2024433663922339344407969)
  ·
    refine ⟨1518325247941754508305977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2024433663922339344407969 1518325247941754508305977)
    ·
      refine ⟨1138743935956315881229483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1518325247941754508305977 1138743935956315881229483)
      ·
        refine ⟨1708115903934473821844225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138743935956315881229483 1708115903934473821844225)
        ·
          refine ⟨1281086927950855366383169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708115903934473821844225 1281086927950855366383169)
          ·
            refine ⟨960815195963141524787377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1281086927950855366383169 960815195963141524787377)
            ·
              refine ⟨720611396972356143590533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960815195963141524787377 720611396972356143590533)
              ·
                refine ⟨135114636932316776923225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720611396972356143590533 135114636932316776923225)
                ·
                  refine ⟨101335977699237582692419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135114636932316776923225 101335977699237582692419)
                  ·
                    refine ⟨152003966548856374038629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101335977699237582692419 152003966548856374038629)
                    ·
                      refine ⟨28500743727910570132243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 152003966548856374038629 28500743727910570132243)
                      ·
                        rfl

theorem cell23_55505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_55505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55505 prefixEnd_55505 := by exact prefixLift 55505
  have htrace : WordTrace (prefixWord ++ tailWord_55505) baseStart_55505 baseEnd_55505 := by
    simpa [prefixWord, tailWord_55505, baseEnd_55505] using wordTrace_append hprefix tailTrace_55505
  have hstable : (prefixWord ++ tailWord_55505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55505).length < 2 ^ (prefixWord ++ tailWord_55505).sum := by decide
  have hdescent : baseEnd_55505 < baseStart_55505 := by decide
  rcases family_descends (prefixWord ++ tailWord_55505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55515 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 3, 4]
def baseStart_55515 : Nat := 118140960795 + 55515 * 2 ^ 59
def prefixEnd_55515 : Nat := 4983230072969 + 3 ^ 40 * 55515 * 2
def baseEnd_55515 : Nat := 9501959511485177002399

theorem tailTrace_55515 : CollatzResearch.WordTrace tailWord_55515 prefixEnd_55515 9501959511485177002399 := by
  unfold tailWord_55515
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024798393886111052271999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1349865595924074034847999 2024798393886111052271999)
  ·
    refine ⟨3037197590829166578407999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2024798393886111052271999 3037197590829166578407999)
    ·
      refine ⟨4555796386243749867611999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3037197590829166578407999 4555796386243749867611999)
      ·
        refine ⟨6833694579365624801417999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4555796386243749867611999 6833694579365624801417999)
        ·
          refine ⟨10250541869048437202126999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833694579365624801417999 10250541869048437202126999)
          ·
            refine ⟨15375812803572655803190499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250541869048437202126999 15375812803572655803190499)
            ·
              refine ⟨23063719205358983704785749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15375812803572655803190499 23063719205358983704785749)
              ·
                refine ⟨135138979718900295145229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23063719205358983704785749 135138979718900295145229)
                ·
                  refine ⟨50677117394587610679461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135138979718900295145229 50677117394587610679461)
                  ·
                    refine ⟨9501959511485177002399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50677117394587610679461 9501959511485177002399)
                    ·
                      rfl

theorem cell23_55515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 4].length) (baseStart_55515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55515 prefixEnd_55515 := by exact prefixLift 55515
  have htrace : WordTrace (prefixWord ++ tailWord_55515) baseStart_55515 baseEnd_55515 := by
    simpa [prefixWord, tailWord_55515, baseEnd_55515] using wordTrace_append hprefix tailTrace_55515
  have hstable : (prefixWord ++ tailWord_55515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55515).length < 2 ^ (prefixWord ++ tailWord_55515).sum := by decide
  have hdescent : baseEnd_55515 < baseStart_55515 := by decide
  rcases family_descends (prefixWord ++ tailWord_55515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55542 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_55542 : Nat := 118140960795 + 55542 * 2 ^ 59
def prefixEnd_55542 : Nat := 4983230072969 + 3 ^ 40 * 55542 * 2
def baseEnd_55542 : Nat := 28519742512126925369573

theorem tailTrace_55542 : CollatzResearch.WordTrace tailWord_55542 prefixEnd_55542 28519742512126925369573 := by
  unfold tailWord_55542
  simp only [CollatzResearch.WordTrace]
  refine ⟨126611447799268416469055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1350522109858863109003253 126611447799268416469055)
  ·
    refine ⟨189917171698902624703583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126611447799268416469055 189917171698902624703583)
    ·
      refine ⟨284875757548353937055375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189917171698902624703583 284875757548353937055375)
      ·
        refine ⟨427313636322530905583063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284875757548353937055375 427313636322530905583063)
        ·
          refine ⟨640970454483796358374595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427313636322530905583063 640970454483796358374595)
          ·
            refine ⟨961455681725694537561893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640970454483796358374595 961455681725694537561893)
            ·
              refine ⟨180272940323567725792855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 961455681725694537561893 180272940323567725792855)
              ·
                refine ⟨270409410485351588689283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180272940323567725792855 270409410485351588689283)
                ·
                  refine ⟨405614115728027383033925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270409410485351588689283 405614115728027383033925)
                  ·
                    refine ⟨76052646699005134318861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405614115728027383033925 76052646699005134318861)
                    ·
                      refine ⟨28519742512126925369573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 76052646699005134318861 28519742512126925369573)
                      ·
                        rfl

theorem cell23_55542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_55542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55542 prefixEnd_55542 := by exact prefixLift 55542
  have htrace : WordTrace (prefixWord ++ tailWord_55542) baseStart_55542 baseEnd_55542 := by
    simpa [prefixWord, tailWord_55542, baseEnd_55542] using wordTrace_append hprefix tailTrace_55542
  have hstable : (prefixWord ++ tailWord_55542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55542).length < 2 ^ (prefixWord ++ tailWord_55542).sum := by decide
  have hdescent : baseEnd_55542 < baseStart_55542 := by decide
  rcases family_descends (prefixWord ++ tailWord_55542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55566 : List Nat := [4, 1, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_55566 : Nat := 118140960795 + 55566 * 2 ^ 59
def prefixEnd_55566 : Nat := 4983230072969 + 3 ^ 40 * 55566 * 2
def baseEnd_55566 : Nat := 9510688682611610489821

theorem tailTrace_55566 : CollatzResearch.WordTrace tailWord_55566 prefixEnd_55566 9510688682611610489821 := by
  unfold tailWord_55566
  simp only [CollatzResearch.WordTrace]
  refine ⟨253332314587668345297319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1351105677800897841585701 253332314587668345297319)
  ·
    refine ⟨379998471881502517945979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253332314587668345297319 379998471881502517945979)
    ·
      refine ⟨569997707822253776918969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379998471881502517945979 569997707822253776918969)
      ·
        refine ⟨427498280866690332689227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569997707822253776918969 427498280866690332689227)
        ·
          refine ⟨641247421300035499033841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427498280866690332689227 641247421300035499033841)
          ·
            refine ⟨480935565975026624275381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641247421300035499033841 480935565975026624275381)
            ·
              refine ⟨45087709310158746025817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 480935565975026624275381 45087709310158746025817)
              ·
                refine ⟨33815781982619059519363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45087709310158746025817 33815781982619059519363)
                ·
                  refine ⟨50723672973928589279045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33815781982619059519363 50723672973928589279045)
                  ·
                    refine ⟨9510688682611610489821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50723672973928589279045 9510688682611610489821)
                    ·
                      rfl

theorem cell23_55566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_55566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55566 prefixEnd_55566 := by exact prefixLift 55566
  have htrace : WordTrace (prefixWord ++ tailWord_55566) baseStart_55566 baseEnd_55566 := by
    simpa [prefixWord, tailWord_55566, baseEnd_55566] using wordTrace_append hprefix tailTrace_55566
  have hstable : (prefixWord ++ tailWord_55566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55566).length < 2 ^ (prefixWord ++ tailWord_55566).sum := by decide
  have hdescent : baseEnd_55566 < baseStart_55566 := by decide
  rcases family_descends (prefixWord ++ tailWord_55566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55625 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_55625 : Nat := 118140960795 + 55625 * 2 ^ 59
def prefixEnd_55625 : Nat := 4983230072969 + 3 ^ 40 * 55625 * 2
def baseEnd_55625 : Nat := 28562361406450100631691

theorem tailTrace_55625 : CollatzResearch.WordTrace tailWord_55625 prefixEnd_55625 28562361406450100631691 := by
  unfold tailWord_55625
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028810423487599838776329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1352540282325066559184219 2028810423487599838776329)
  ·
    refine ⟨1521607817615699879082247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2028810423487599838776329 1521607817615699879082247)
    ·
      refine ⟨2282411726423549818623371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521607817615699879082247 2282411726423549818623371)
      ·
        refine ⟨3423617589635324727935057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282411726423549818623371 3423617589635324727935057)
        ·
          refine ⟨2567713192226493545951293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423617589635324727935057 2567713192226493545951293)
          ·
            refine ⟨962892447084935079731735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2567713192226493545951293 962892447084935079731735)
            ·
              refine ⟨1444338670627402619597603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962892447084935079731735 1444338670627402619597603)
              ·
                refine ⟨2166508005941103929396405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444338670627402619597603 2166508005941103929396405)
                ·
                  refine ⟨203110125556978493380913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2166508005941103929396405 203110125556978493380913)
                  ·
                    refine ⟨152332594167733870035685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203110125556978493380913 152332594167733870035685)
                    ·
                      refine ⟨28562361406450100631691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 152332594167733870035685 28562361406450100631691)
                      ·
                        rfl

theorem cell23_55625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_55625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55625 prefixEnd_55625 := by exact prefixLift 55625
  have htrace : WordTrace (prefixWord ++ tailWord_55625) baseStart_55625 baseEnd_55625 := by
    simpa [prefixWord, tailWord_55625, baseEnd_55625] using wordTrace_append hprefix tailTrace_55625
  have hstable : (prefixWord ++ tailWord_55625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55625).length < 2 ^ (prefixWord ++ tailWord_55625).sum := by decide
  have hdescent : baseEnd_55625 < baseStart_55625 := by decide
  rcases family_descends (prefixWord ++ tailWord_55625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55632 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3]
def baseStart_55632 : Nat := 118140960795 + 55632 * 2 ^ 59
def prefixEnd_55632 : Nat := 4983230072969 + 3 ^ 40 * 55632 * 2
def baseEnd_55632 : Nat := 28565955771031573244159

theorem tailTrace_55632 : CollatzResearch.WordTrace tailWord_55632 prefixEnd_55632 28565955771031573244159 := by
  unfold tailWord_55632
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014532867231120017140575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1352710489641493356187433 1014532867231120017140575)
  ·
    refine ⟨1521799300846680025710863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1014532867231120017140575 1521799300846680025710863)
    ·
      refine ⟨2282698951270020038566295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521799300846680025710863 2282698951270020038566295)
      ·
        refine ⟨3424048426905030057849443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282698951270020038566295 3424048426905030057849443)
        ·
          refine ⟨5136072640357545086774165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424048426905030057849443 5136072640357545086774165)
          ·
            refine ⟨240753405016759925942539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5136072640357545086774165 240753405016759925942539)
            ·
              refine ⟨361130107525139888913809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240753405016759925942539 361130107525139888913809)
              ·
                refine ⟨270847580643854916685357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361130107525139888913809 270847580643854916685357)
                ·
                  refine ⟨101567842741445593757009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270847580643854916685357 101567842741445593757009)
                  ·
                    refine ⟨76175882056084195317757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101567842741445593757009 76175882056084195317757)
                    ·
                      refine ⟨28565955771031573244159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 76175882056084195317757 28565955771031573244159)
                      ·
                        rfl

theorem cell23_55632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_55632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55632 prefixEnd_55632 := by exact prefixLift 55632
  have htrace : WordTrace (prefixWord ++ tailWord_55632) baseStart_55632 baseEnd_55632 := by
    simpa [prefixWord, tailWord_55632, baseEnd_55632] using wordTrace_append hprefix tailTrace_55632
  have hstable : (prefixWord ++ tailWord_55632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55632).length < 2 ^ (prefixWord ++ tailWord_55632).sum := by decide
  have hdescent : baseEnd_55632 < baseStart_55632 := by decide
  rcases family_descends (prefixWord ++ tailWord_55632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55652 : List Nat := [2, 3, 1, 1, 3, 1, 5, 7]
def baseStart_55652 : Nat := 118140960795 + 55652 * 2 ^ 59
def prefixEnd_55652 : Nat := 4983230072969 + 3 ^ 40 * 55652 * 2
def baseEnd_55652 : Nat := 1058378717930425740521

theorem tailTrace_55652 : CollatzResearch.WordTrace tailWord_55652 prefixEnd_55652 1058378717930425740521 := by
  unfold tailWord_55652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014897597194891725004605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1353196796259855633339473 1014897597194891725004605)
  ·
    refine ⟨380586598948084396876727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1014897597194891725004605 380586598948084396876727)
    ·
      refine ⟨570879898422126595315091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380586598948084396876727 570879898422126595315091)
      ·
        refine ⟨856319847633189892972637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570879898422126595315091 856319847633189892972637)
        ·
          refine ⟨321119942862446209864739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 856319847633189892972637 321119942862446209864739)
          ·
            refine ⟨481679914293669314797109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321119942862446209864739 481679914293669314797109)
            ·
              refine ⟨45157491965031498262229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 481679914293669314797109 45157491965031498262229)
              ·
                refine ⟨1058378717930425740521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45157491965031498262229 1058378717930425740521)
                ·
                  rfl

theorem cell23_55652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 7].length) (baseStart_55652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55652 prefixEnd_55652 := by exact prefixLift 55652
  have htrace : WordTrace (prefixWord ++ tailWord_55652) baseStart_55652 baseEnd_55652 := by
    simpa [prefixWord, tailWord_55652, baseEnd_55652] using wordTrace_append hprefix tailTrace_55652
  have hstable : (prefixWord ++ tailWord_55652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55652).length < 2 ^ (prefixWord ++ tailWord_55652).sum := by decide
  have hdescent : baseEnd_55652 < baseStart_55652 := by decide
  rcases family_descends (prefixWord ++ tailWord_55652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55666 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_55666 : Nat := 118140960795 + 55666 * 2 ^ 59
def prefixEnd_55666 : Nat := 4983230072969 + 3 ^ 40 * 55666 * 2
def baseEnd_55666 : Nat := 28583414113284440219003

theorem tailTrace_55666 : CollatzResearch.WordTrace tailWord_55666 prefixEnd_55666 28583414113284440219003 := by
  unfold tailWord_55666
  simp only [CollatzResearch.WordTrace]
  refine ⟨507576454084765960254713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1353537210892709227345901 507576454084765960254713)
  ·
    refine ⟨380682340563574470191035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 507576454084765960254713 380682340563574470191035)
    ·
      refine ⟨571023510845361705286553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380682340563574470191035 571023510845361705286553)
      ·
        refine ⟨428267633134021278964915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571023510845361705286553 428267633134021278964915)
        ·
          refine ⟨642401449701031918447373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428267633134021278964915 642401449701031918447373)
          ·
            refine ⟨240900543637886969417765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642401449701031918447373 240900543637886969417765)
            ·
              refine ⟨45168851932103806765831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240900543637886969417765 45168851932103806765831)
              ·
                refine ⟨67753277898155710148747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45168851932103806765831 67753277898155710148747)
                ·
                  refine ⟨101629916847233565223121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67753277898155710148747 101629916847233565223121)
                  ·
                    refine ⟨76222437635425173917341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101629916847233565223121 76222437635425173917341)
                    ·
                      refine ⟨28583414113284440219003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 76222437635425173917341 28583414113284440219003)
                      ·
                        rfl

theorem cell23_55666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_55666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55666 prefixEnd_55666 := by exact prefixLift 55666
  have htrace : WordTrace (prefixWord ++ tailWord_55666) baseStart_55666 baseEnd_55666 := by
    simpa [prefixWord, tailWord_55666, baseEnd_55666] using wordTrace_append hprefix tailTrace_55666
  have hstable : (prefixWord ++ tailWord_55666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55666).length < 2 ^ (prefixWord ++ tailWord_55666).sum := by decide
  have hdescent : baseEnd_55666 < baseStart_55666 := by decide
  rcases family_descends (prefixWord ++ tailWord_55666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55706 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2]
def baseStart_55706 : Nat := 118140960795 + 55706 * 2 ^ 59
def prefixEnd_55706 : Nat := 4983230072969 + 3 ^ 40 * 55706 * 2
def baseEnd_55706 : Nat := 28603953339464283718819

theorem tailTrace_55706 : CollatzResearch.WordTrace tailWord_55706 prefixEnd_55706 28603953339464283718819 := by
  unfold tailWord_55706
  simp only [CollatzResearch.WordTrace]
  refine ⟨507941184048537668118743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1354509824129433781649981 507941184048537668118743)
  ·
    refine ⟨761911776072806502178115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 507941184048537668118743 761911776072806502178115)
    ·
      refine ⟨1142867664109209753267173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761911776072806502178115 1142867664109209753267173)
      ·
        refine ⟨214287687020476828737595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1142867664109209753267173 214287687020476828737595)
        ·
          refine ⟨321431530530715243106393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214287687020476828737595 321431530530715243106393)
          ·
            refine ⟨241073647898036432329795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321431530530715243106393 241073647898036432329795)
            ·
              refine ⟨361610471847054648494693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241073647898036432329795 361610471847054648494693)
              ·
                refine ⟨67801963471322746592755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361610471847054648494693 67801963471322746592755)
                ·
                  refine ⟨101702945206984119889133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67801963471322746592755 101702945206984119889133)
                  ·
                    refine ⟨38138604452619044958425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101702945206984119889133 38138604452619044958425)
                    ·
                      refine ⟨28603953339464283718819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38138604452619044958425 28603953339464283718819)
                      ·
                        rfl

theorem cell23_55706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_55706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55706 prefixEnd_55706 := by exact prefixLift 55706
  have htrace : WordTrace (prefixWord ++ tailWord_55706) baseStart_55706 baseEnd_55706 := by
    simpa [prefixWord, tailWord_55706, baseEnd_55706] using wordTrace_append hprefix tailTrace_55706
  have hstable : (prefixWord ++ tailWord_55706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55706).length < 2 ^ (prefixWord ++ tailWord_55706).sum := by decide
  have hdescent : baseEnd_55706 < baseStart_55706 := by decide
  rcases family_descends (prefixWord ++ tailWord_55706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55736 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 2, 2, 2]
def baseStart_55736 : Nat := 118140960795 + 55736 * 2 ^ 59
def prefixEnd_55736 : Nat := 4983230072969 + 3 ^ 40 * 55736 * 2
def baseEnd_55736 : Nat := 28619357759099166343681

theorem tailTrace_55736 : CollatzResearch.WordTrace tailWord_55736 prefixEnd_55736 28619357759099166343681 := by
  unfold tailWord_55736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016429463042732898033531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1355239284056977197378041 1016429463042732898033531)
  ·
    refine ⟨1524644194564099347050297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1016429463042732898033531 1524644194564099347050297)
    ·
      refine ⟨1143483145923074510287723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524644194564099347050297 1143483145923074510287723)
      ·
        refine ⟨1715224718884611765431585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143483145923074510287723 1715224718884611765431585)
        ·
          refine ⟨1286418539163458824073689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1715224718884611765431585 1286418539163458824073689)
          ·
            refine ⟨964813904372594118055267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286418539163458824073689 964813904372594118055267)
            ·
              refine ⟨1447220856558891177082901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964813904372594118055267 1447220856558891177082901)
              ·
                refine ⟨67838477651198023925761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1447220856558891177082901 67838477651198023925761)
                ·
                  refine ⟨50878858238398517944321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67838477651198023925761 50878858238398517944321)
                  ·
                    refine ⟨38159143678798888458241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50878858238398517944321 38159143678798888458241)
                    ·
                      refine ⟨28619357759099166343681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38159143678798888458241 28619357759099166343681)
                      ·
                        rfl

theorem cell23_55736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_55736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55736 prefixEnd_55736 := by exact prefixLift 55736
  have htrace : WordTrace (prefixWord ++ tailWord_55736) baseStart_55736 baseEnd_55736 := by
    simpa [prefixWord, tailWord_55736, baseEnd_55736] using wordTrace_append hprefix tailTrace_55736
  have hstable : (prefixWord ++ tailWord_55736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55736).length < 2 ^ (prefixWord ++ tailWord_55736).sum := by decide
  have hdescent : baseEnd_55736 < baseStart_55736 := by decide
  rcases family_descends (prefixWord ++ tailWord_55736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55753 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 2, 2, 2]
def baseStart_55753 : Nat := 118140960795 + 55753 * 2 ^ 59
def prefixEnd_55753 : Nat := 4983230072969 + 3 ^ 40 * 55753 * 2
def baseEnd_55753 : Nat := 28628086930225599831103

theorem tailTrace_55753 : CollatzResearch.WordTrace tailWord_55753 prefixEnd_55753 28628086930225599831103 := by
  unfold tailWord_55753
  simp only [CollatzResearch.WordTrace]
  refine ⟨2033478967023877699435913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1355652644682585132957275 2033478967023877699435913)
  ·
    refine ⟨1525109225267908274576935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2033478967023877699435913 1525109225267908274576935)
    ·
      refine ⟨2287663837901862411865403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525109225267908274576935 2287663837901862411865403)
      ·
        refine ⟨3431495756852793617798105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2287663837901862411865403 3431495756852793617798105)
        ·
          refine ⟨2573621817639595213348579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431495756852793617798105 2573621817639595213348579)
          ·
            refine ⟨3860432726459392820022869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573621817639595213348579 3860432726459392820022869)
            ·
              refine ⟨45239446013196009609643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3860432726459392820022869 45239446013196009609643)
              ·
                refine ⟨67859169019794014414465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45239446013196009609643 67859169019794014414465)
                ·
                  refine ⟨50894376764845510810849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67859169019794014414465 50894376764845510810849)
                  ·
                    refine ⟨38170782573634133108137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50894376764845510810849 38170782573634133108137)
                    ·
                      refine ⟨28628086930225599831103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38170782573634133108137 28628086930225599831103)
                      ·
                        rfl

theorem cell23_55753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 2, 2].length) (baseStart_55753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55753 prefixEnd_55753 := by exact prefixLift 55753
  have htrace : WordTrace (prefixWord ++ tailWord_55753) baseStart_55753 baseEnd_55753 := by
    simpa [prefixWord, tailWord_55753, baseEnd_55753] using wordTrace_append hprefix tailTrace_55753
  have hstable : (prefixWord ++ tailWord_55753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55753).length < 2 ^ (prefixWord ++ tailWord_55753).sum := by decide
  have hdescent : baseEnd_55753 < baseStart_55753 := by decide
  rcases family_descends (prefixWord ++ tailWord_55753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55819 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 5, 4]
def baseStart_55819 : Nat := 118140960795 + 55819 * 2 ^ 59
def prefixEnd_55819 : Nat := 4983230072969 + 3 ^ 40 * 55819 * 2
def baseEnd_55819 : Nat := 9553992217807447201933

theorem tailTrace_55819 : CollatzResearch.WordTrace tailWord_55819 prefixEnd_55819 9553992217807447201933 := by
  unfold tailWord_55819
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035886184784770971338511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1357257456523180647559007 2035886184784770971338511)
  ·
    refine ⟨3053829277177156457007767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2035886184784770971338511 3053829277177156457007767)
    ·
      refine ⟨4580743915765734685511651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3053829277177156457007767 4580743915765734685511651)
      ·
        refine ⟨6871115873648602028267477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4580743915765734685511651 6871115873648602028267477)
        ·
          refine ⟨161041778288639110037519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6871115873648602028267477 161041778288639110037519)
          ·
            refine ⟨241562667432958665056279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161041778288639110037519 241562667432958665056279)
            ·
              refine ⟨362344001149437997584419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241562667432958665056279 362344001149437997584419)
              ·
                refine ⟨543516001724156996376629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362344001149437997584419 543516001724156996376629)
                ·
                  refine ⟨50954625161639718410309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 543516001724156996376629 50954625161639718410309)
                  ·
                    refine ⟨9553992217807447201933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50954625161639718410309 9553992217807447201933)
                    ·
                      rfl

theorem cell23_55819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 4].length) (baseStart_55819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55819 prefixEnd_55819 := by exact prefixLift 55819
  have htrace : WordTrace (prefixWord ++ tailWord_55819) baseStart_55819 baseEnd_55819 := by
    simpa [prefixWord, tailWord_55819, baseEnd_55819] using wordTrace_append hprefix tailTrace_55819
  have hstable : (prefixWord ++ tailWord_55819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55819).length < 2 ^ (prefixWord ++ tailWord_55819).sum := by decide
  have hdescent : baseEnd_55819 < baseStart_55819 := by decide
  rcases family_descends (prefixWord ++ tailWord_55819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55829 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_55829 : Nat := 118140960795 + 55829 * 2 ^ 59
def prefixEnd_55829 : Nat := 4983230072969 + 3 ^ 40 * 55829 * 2
def baseEnd_55829 : Nat := 28667111459967302480753

theorem tailTrace_55829 : CollatzResearch.WordTrace tailWord_55829 prefixEnd_55829 28667111459967302480753 := by
  unfold tailWord_55829
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036250914748542679202541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1357500609832361786135027 2036250914748542679202541)
  ·
    refine ⟨763594093030703504700953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2036250914748542679202541 763594093030703504700953)
    ·
      refine ⟨572695569773027628525715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 763594093030703504700953 572695569773027628525715)
      ·
        refine ⟨859043354659541442788573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572695569773027628525715 859043354659541442788573)
        ·
          refine ⟨322141257997328041045715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 859043354659541442788573 322141257997328041045715)
          ·
            refine ⟨483211886995992061568573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322141257997328041045715 483211886995992061568573)
            ·
              refine ⟨181204457623497023088215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483211886995992061568573 181204457623497023088215)
              ·
                refine ⟨271806686435245534632323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181204457623497023088215 271806686435245534632323)
                ·
                  refine ⟨407710029652868301948485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271806686435245534632323 407710029652868301948485)
                  ·
                    refine ⟨76445630559912806615341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 407710029652868301948485 76445630559912806615341)
                    ·
                      refine ⟨28667111459967302480753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 76445630559912806615341 28667111459967302480753)
                      ·
                        rfl

theorem cell23_55829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_55829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55829 prefixEnd_55829 := by exact prefixLift 55829
  have htrace : WordTrace (prefixWord ++ tailWord_55829) baseStart_55829 baseEnd_55829 := by
    simpa [prefixWord, tailWord_55829, baseEnd_55829] using wordTrace_append hprefix tailTrace_55829
  have hstable : (prefixWord ++ tailWord_55829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55829).length < 2 ^ (prefixWord ++ tailWord_55829).sum := by decide
  have hdescent : baseEnd_55829 < baseStart_55829 := by decide
  rcases family_descends (prefixWord ++ tailWord_55829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55866 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 6]
def baseStart_55866 : Nat := 118140960795 + 55866 * 2 ^ 59
def prefixEnd_55866 : Nat := 4983230072969 + 3 ^ 40 * 55866 * 2
def baseEnd_55866 : Nat := 3187345582687073079787

theorem tailTrace_55866 : CollatzResearch.WordTrace tailWord_55866 prefixEnd_55866 3187345582687073079787 := by
  unfold tailWord_55866
  simp only [CollatzResearch.WordTrace]
  refine ⟨509400103903624499574863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1358400277076331998866301 509400103903624499574863)
  ·
    refine ⟨764100155855436749362295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 509400103903624499574863 764100155855436749362295)
    ·
      refine ⟨1146150233783155124043443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764100155855436749362295 1146150233783155124043443)
      ·
        refine ⟨1719225350674732686065165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146150233783155124043443 1719225350674732686065165)
        ·
          refine ⟨644709506503024757274437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1719225350674732686065165 644709506503024757274437)
          ·
            refine ⟨120883032469317141988957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 644709506503024757274437 120883032469317141988957)
            ·
              refine ⟨45331137175993928245859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120883032469317141988957 45331137175993928245859)
              ·
                refine ⟨67996705763990892368789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45331137175993928245859 67996705763990892368789)
                ·
                  refine ⟨3187345582687073079787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67996705763990892368789 3187345582687073079787)
                  ·
                    rfl

theorem cell23_55866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_55866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55866 prefixEnd_55866 := by exact prefixLift 55866
  have htrace : WordTrace (prefixWord ++ tailWord_55866) baseStart_55866 baseEnd_55866 := by
    simpa [prefixWord, tailWord_55866, baseEnd_55866] using wordTrace_append hprefix tailTrace_55866
  have hstable : (prefixWord ++ tailWord_55866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55866).length < 2 ^ (prefixWord ++ tailWord_55866).sum := by decide
  have hdescent : baseEnd_55866 < baseStart_55866 := by decide
  rcases family_descends (prefixWord ++ tailWord_55866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55872 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_55872 : Nat := 118140960795 + 55872 * 2 ^ 59
def prefixEnd_55872 : Nat := 4983230072969 + 3 ^ 40 * 55872 * 2
def baseEnd_55872 : Nat := 28689191128110634243055

theorem tailTrace_55872 : CollatzResearch.WordTrace tailWord_55872 prefixEnd_55872 28689191128110634243055 := by
  unfold tailWord_55872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018909626796380511508935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1358546169061840682011913 1018909626796380511508935)
  ·
    refine ⟨1528364440194570767263403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1018909626796380511508935 1528364440194570767263403)
    ·
      refine ⟨2292546660291856150895105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528364440194570767263403 2292546660291856150895105)
      ·
        refine ⟨1719409995218892113171329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2292546660291856150895105 1719409995218892113171329)
        ·
          refine ⟨1289557496414169084878497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719409995218892113171329 1289557496414169084878497)
          ·
            refine ⟨967168122310626813658873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289557496414169084878497 967168122310626813658873)
            ·
              refine ⟨725376091732970110244155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967168122310626813658873 725376091732970110244155)
              ·
                refine ⟨1088064137599455165366233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725376091732970110244155 1088064137599455165366233)
                ·
                  refine ⟨816048103199591374024675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1088064137599455165366233 816048103199591374024675)
                  ·
                    refine ⟨1224072154799387061037013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816048103199591374024675 1224072154799387061037013)
                    ·
                      refine ⟨28689191128110634243055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1224072154799387061037013 28689191128110634243055)
                      ·
                        rfl

theorem cell23_55872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_55872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55872 prefixEnd_55872 := by exact prefixLift 55872
  have htrace : WordTrace (prefixWord ++ tailWord_55872) baseStart_55872 baseEnd_55872 := by
    simpa [prefixWord, tailWord_55872, baseEnd_55872] using wordTrace_append hprefix tailTrace_55872
  have hstable : (prefixWord ++ tailWord_55872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55872).length < 2 ^ (prefixWord ++ tailWord_55872).sum := by decide
  have hdescent : baseEnd_55872 < baseStart_55872 := by decide
  rcases family_descends (prefixWord ++ tailWord_55872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55886 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_55886 : Nat := 118140960795 + 55886 * 2 ^ 59
def prefixEnd_55886 : Nat := 4983230072969 + 3 ^ 40 * 55886 * 2
def baseEnd_55886 : Nat := 28696379857273579467991

theorem tailTrace_55886 : CollatzResearch.WordTrace tailWord_55886 prefixEnd_55886 28696379857273579467991 := by
  unfold tailWord_55886
  simp only [CollatzResearch.WordTrace]
  refine ⟨254791234442755176753439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1358886583694694276018341 254791234442755176753439)
  ·
    refine ⟨382186851664132765130159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254791234442755176753439 382186851664132765130159)
    ·
      refine ⟨573280277496199147695239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382186851664132765130159 573280277496199147695239)
      ·
        refine ⟨859920416244298721542859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573280277496199147695239 859920416244298721542859)
        ·
          refine ⟨1289880624366448082314289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859920416244298721542859 1289880624366448082314289)
          ·
            refine ⟨967410468274836061735717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289880624366448082314289 967410468274836061735717)
            ·
              refine ⟨181389462801531761575447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 967410468274836061735717 181389462801531761575447)
              ·
                refine ⟨272084194202297642363171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181389462801531761575447 272084194202297642363171)
                ·
                  refine ⟨408126291303446463544757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272084194202297642363171 408126291303446463544757)
                  ·
                    refine ⟨38261839809698105957321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 408126291303446463544757 38261839809698105957321)
                    ·
                      refine ⟨28696379857273579467991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38261839809698105957321 28696379857273579467991)
                      ·
                        rfl

theorem cell23_55886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_55886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55886 prefixEnd_55886 := by exact prefixLift 55886
  have htrace : WordTrace (prefixWord ++ tailWord_55886) baseStart_55886 baseEnd_55886 := by
    simpa [prefixWord, tailWord_55886, baseEnd_55886] using wordTrace_append hprefix tailTrace_55886
  have hstable : (prefixWord ++ tailWord_55886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55886).length < 2 ^ (prefixWord ++ tailWord_55886).sum := by decide
  have hdescent : baseEnd_55886 < baseStart_55886 := by decide
  rcases family_descends (prefixWord ++ tailWord_55886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55919 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_55919 : Nat := 118140960795 + 55919 * 2 ^ 59
def prefixEnd_55919 : Nat := 4983230072969 + 3 ^ 40 * 55919 * 2
def baseEnd_55919 : Nat := 28713324718871950355339

theorem tailTrace_55919 : CollatzResearch.WordTrace tailWord_55919 prefixEnd_55919 28713324718871950355339 := by
  unfold tailWord_55919
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039533484422488049978811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1359688989614992033319207 2039533484422488049978811)
  ·
    refine ⟨3059300226633732074968217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2039533484422488049978811 3059300226633732074968217)
    ·
      refine ⟨2294475169975299056226163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3059300226633732074968217 2294475169975299056226163)
      ·
        refine ⟨3441712754962948584339245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294475169975299056226163 3441712754962948584339245)
        ·
          refine ⟨1290642283111105719127217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3441712754962948584339245 1290642283111105719127217)
          ·
            refine ⟨967981712333329289345413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290642283111105719127217 967981712333329289345413)
            ·
              refine ⟨181496571062499241752265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 967981712333329289345413 181496571062499241752265)
              ·
                refine ⟨136122428296874431314199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181496571062499241752265 136122428296874431314199)
                ·
                  refine ⟨204183642445311646971299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136122428296874431314199 204183642445311646971299)
                  ·
                    refine ⟨306275463667967470456949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204183642445311646971299 306275463667967470456949)
                    ·
                      refine ⟨28713324718871950355339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 306275463667967470456949 28713324718871950355339)
                      ·
                        rfl

theorem cell23_55919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_55919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55919 prefixEnd_55919 := by exact prefixLift 55919
  have htrace : WordTrace (prefixWord ++ tailWord_55919) baseStart_55919 baseEnd_55919 := by
    simpa [prefixWord, tailWord_55919, baseEnd_55919] using wordTrace_append hprefix tailTrace_55919
  have hstable : (prefixWord ++ tailWord_55919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55919).length < 2 ^ (prefixWord ++ tailWord_55919).sum := by decide
  have hdescent : baseEnd_55919 < baseStart_55919 := by decide
  rcases family_descends (prefixWord ++ tailWord_55919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55929 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_55929 : Nat := 118140960795 + 55929 * 2 ^ 59
def prefixEnd_55929 : Nat := 4983230072969 + 3 ^ 40 * 55929 * 2
def baseEnd_55929 : Nat := 28718459525416911230293

theorem tailTrace_55929 : CollatzResearch.WordTrace tailWord_55929 prefixEnd_55929 28718459525416911230293 := by
  unfold tailWord_55929
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039898214386259757842841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1359932142924173171895227 2039898214386259757842841)
  ·
    refine ⟨1529923660789694818382131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2039898214386259757842841 1529923660789694818382131)
    ·
      refine ⟨2294885491184542227573197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1529923660789694818382131 2294885491184542227573197)
      ·
        refine ⟨860582059194203335339949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2294885491184542227573197 860582059194203335339949)
        ·
          refine ⟨322718272197826250752481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 860582059194203335339949 322718272197826250752481)
          ·
            refine ⟨242038704148369688064361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322718272197826250752481 242038704148369688064361)
            ·
              refine ⟨181529028111277266048271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242038704148369688064361 181529028111277266048271)
              ·
                refine ⟨272293542166915899072407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181529028111277266048271 272293542166915899072407)
                ·
                  refine ⟨408440313250373848608611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272293542166915899072407 408440313250373848608611)
                  ·
                    refine ⟨612660469875560772912917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 408440313250373848608611 612660469875560772912917)
                    ·
                      refine ⟨28718459525416911230293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 612660469875560772912917 28718459525416911230293)
                      ·
                        rfl

theorem cell23_55929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_55929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55929 prefixEnd_55929 := by exact prefixLift 55929
  have htrace : WordTrace (prefixWord ++ tailWord_55929) baseStart_55929 baseEnd_55929 := by
    simpa [prefixWord, tailWord_55929, baseEnd_55929] using wordTrace_append hprefix tailTrace_55929
  have hstable : (prefixWord ++ tailWord_55929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55929).length < 2 ^ (prefixWord ++ tailWord_55929).sum := by decide
  have hdescent : baseEnd_55929 < baseStart_55929 := by decide
  rcases family_descends (prefixWord ++ tailWord_55929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55936 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3]
def baseStart_55936 : Nat := 118140960795 + 55936 * 2 ^ 59
def prefixEnd_55936 : Nat := 4983230072969 + 3 ^ 40 * 55936 * 2
def baseEnd_55936 : Nat := 28722053889998383842761

theorem tailTrace_55936 : CollatzResearch.WordTrace tailWord_55936 prefixEnd_55936 28722053889998383842761 := by
  unfold tailWord_55936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020076762680449976673831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1360102350240599968898441 1020076762680449976673831)
  ·
    refine ⟨1530115144020674965010747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1020076762680449976673831 1530115144020674965010747)
    ·
      refine ⟨2295172716031012447516121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530115144020674965010747 2295172716031012447516121)
      ·
        refine ⟨1721379537023259335637091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2295172716031012447516121 1721379537023259335637091)
        ·
          refine ⟨2582069305534889003455637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721379537023259335637091 2582069305534889003455637)
          ·
            refine ⟨121034498696947922036983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2582069305534889003455637 121034498696947922036983)
            ·
              refine ⟨181551748045421883055475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121034498696947922036983 181551748045421883055475)
              ·
                refine ⟨272327622068132824583213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181551748045421883055475 272327622068132824583213)
                ·
                  refine ⟨102122858275549809218705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272327622068132824583213 102122858275549809218705)
                  ·
                    refine ⟨76592143706662356914029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102122858275549809218705 76592143706662356914029)
                    ·
                      refine ⟨28722053889998383842761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 76592143706662356914029 28722053889998383842761)
                      ·
                        rfl

theorem cell23_55936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_55936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55936 prefixEnd_55936 := by exact prefixLift 55936
  have htrace : WordTrace (prefixWord ++ tailWord_55936) baseStart_55936 baseEnd_55936 := by
    simpa [prefixWord, tailWord_55936, baseEnd_55936] using wordTrace_append hprefix tailTrace_55936
  have hstable : (prefixWord ++ tailWord_55936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55936).length < 2 ^ (prefixWord ++ tailWord_55936).sum := by decide
  have hdescent : baseEnd_55936 < baseStart_55936 := by decide
  rcases family_descends (prefixWord ++ tailWord_55936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55983 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 3]
def baseStart_55983 : Nat := 118140960795 + 55983 * 2 ^ 59
def prefixEnd_55983 : Nat := 4983230072969 + 3 ^ 40 * 55983 * 2
def baseEnd_55983 : Nat := 28746187480759699955045

theorem tailTrace_55983 : CollatzResearch.WordTrace tailWord_55983 prefixEnd_55983 28746187480759699955045 := by
  unfold tailWord_55983
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041867756190626980308603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1361245170793751320205735 2041867756190626980308603)
  ·
    refine ⟨3062801634285940470462905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041867756190626980308603 3062801634285940470462905)
    ·
      refine ⟨2297101225714455352847179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3062801634285940470462905 2297101225714455352847179)
      ·
        refine ⟨3445651838571683029270769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297101225714455352847179 3445651838571683029270769)
        ·
          refine ⟨2584238878928762271953077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3445651838571683029270769 2584238878928762271953077)
          ·
            refine ⟨242272394899571462995601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2584238878928762271953077 242272394899571462995601)
            ·
              refine ⟨181704296174678597246701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242272394899571462995601 181704296174678597246701)
              ·
                refine ⟨68139111065504473967513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181704296174678597246701 68139111065504473967513)
                ·
                  refine ⟨51104333299128355475635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68139111065504473967513 51104333299128355475635)
                  ·
                    refine ⟨76656499948692533213453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51104333299128355475635 76656499948692533213453)
                    ·
                      refine ⟨28746187480759699955045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 76656499948692533213453 28746187480759699955045)
                      ·
                        rfl

theorem cell23_55983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 3].length) (baseStart_55983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55983 prefixEnd_55983 := by exact prefixLift 55983
  have htrace : WordTrace (prefixWord ++ tailWord_55983) baseStart_55983 baseEnd_55983 := by
    simpa [prefixWord, tailWord_55983, baseEnd_55983] using wordTrace_append hprefix tailTrace_55983
  have hstable : (prefixWord ++ tailWord_55983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55983).length < 2 ^ (prefixWord ++ tailWord_55983).sum := by decide
  have hdescent : baseEnd_55983 < baseStart_55983 := by decide
  rcases family_descends (prefixWord ++ tailWord_55983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55990 : List Nat := [5, 1, 3, 1, 2, 1, 3, 7]
def baseStart_55990 : Nat := 118140960795 + 55990 * 2 ^ 59
def prefixEnd_55990 : Nat := 4983230072969 + 3 ^ 40 * 55990 * 2
def baseEnd_55990 : Nat := 1064806735012636021019

theorem tailTrace_55990 : CollatzResearch.WordTrace tailWord_55990 prefixEnd_55990 1064806735012636021019 := by
  unfold tailWord_55990
  simp only [CollatzResearch.WordTrace]
  refine ⟨127632691697829198488339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1361415378110178117208949 127632691697829198488339)
  ·
    refine ⟨191449037546743797732509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127632691697829198488339 191449037546743797732509)
    ·
      refine ⟨71793389080028924149691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191449037546743797732509 71793389080028924149691)
      ·
        refine ⟨107690083620043386224537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71793389080028924149691 107690083620043386224537)
        ·
          refine ⟨80767562715032539668403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107690083620043386224537 80767562715032539668403)
          ·
            refine ⟨121151344072548809502605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80767562715032539668403 121151344072548809502605)
            ·
              refine ⟨45431754027205803563477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121151344072548809502605 45431754027205803563477)
              ·
                refine ⟨1064806735012636021019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45431754027205803563477 1064806735012636021019)
                ·
                  rfl

theorem cell23_55990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_55990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55990 prefixEnd_55990 := by exact prefixLift 55990
  have htrace : WordTrace (prefixWord ++ tailWord_55990) baseStart_55990 baseEnd_55990 := by
    simpa [prefixWord, tailWord_55990, baseEnd_55990] using wordTrace_append hprefix tailTrace_55990
  have hstable : (prefixWord ++ tailWord_55990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55990).length < 2 ^ (prefixWord ++ tailWord_55990).sum := by decide
  have hdescent : baseEnd_55990 < baseStart_55990 := by decide
  rcases family_descends (prefixWord ++ tailWord_55990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55993 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 1, 3, 2]
def baseStart_55993 : Nat := 118140960795 + 55993 * 2 ^ 59
def prefixEnd_55993 : Nat := 4983230072969 + 3 ^ 40 * 55993 * 2
def baseEnd_55993 : Nat := 28751322287304660829999

theorem tailTrace_55993 : CollatzResearch.WordTrace tailWord_55993 prefixEnd_55993 28751322287304660829999 := by
  unfold tailWord_55993
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042232486154398688172633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1361488324102932458781755 2042232486154398688172633)
  ·
    refine ⟨1531674364615799016129475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2042232486154398688172633 1531674364615799016129475)
    ·
      refine ⟨2297511546923698524194213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531674364615799016129475 2297511546923698524194213)
      ·
        refine ⟨430783415048193473286415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2297511546923698524194213 430783415048193473286415)
        ·
          refine ⟨646175122572290209929623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430783415048193473286415 646175122572290209929623)
          ·
            refine ⟨969262683858435314894435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646175122572290209929623 969262683858435314894435)
            ·
              refine ⟨1453894025787652972341653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969262683858435314894435 1453894025787652972341653)
              ·
                refine ⟨68151282458796233078515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1453894025787652972341653 68151282458796233078515)
                ·
                  refine ⟨102226923688194349617773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68151282458796233078515 102226923688194349617773)
                  ·
                    refine ⟨38335096383072881106665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102226923688194349617773 38335096383072881106665)
                    ·
                      refine ⟨28751322287304660829999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38335096383072881106665 28751322287304660829999)
                      ·
                        rfl

theorem cell23_55993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_55993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55993 prefixEnd_55993 := by exact prefixLift 55993
  have htrace : WordTrace (prefixWord ++ tailWord_55993) baseStart_55993 baseEnd_55993 := by
    simpa [prefixWord, tailWord_55993, baseEnd_55993] using wordTrace_append hprefix tailTrace_55993
  have hstable : (prefixWord ++ tailWord_55993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55993).length < 2 ^ (prefixWord ++ tailWord_55993).sum := by decide
  have hdescent : baseEnd_55993 < baseStart_55993 := by decide
  rcases family_descends (prefixWord ++ tailWord_55993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56001 : List Nat := [1, 2, 6, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_56001 : Nat := 118140960795 + 56001 * 2 ^ 59
def prefixEnd_56001 : Nat := 4983230072969 + 3 ^ 40 * 56001 * 2
def baseEnd_56001 : Nat := 28755430132540629529963

theorem tailTrace_56001 : CollatzResearch.WordTrace tailWord_56001 prefixEnd_56001 28755430132540629529963 := by
  unfold tailWord_56001
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042524270125416054463857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1361682846750277369642571 2042524270125416054463857)
  ·
    refine ⟨1531893202594062040847893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2042524270125416054463857 1531893202594062040847893)
    ·
      refine ⟨71807493871596658164745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1531893202594062040847893 71807493871596658164745)
      ·
        refine ⟨53855620403697493623559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71807493871596658164745 53855620403697493623559)
        ·
          refine ⟨80783430605546240435339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53855620403697493623559 80783430605546240435339)
          ·
            refine ⟨121175145908319360653009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80783430605546240435339 121175145908319360653009)
            ·
              refine ⟨90881359431239520489757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121175145908319360653009 90881359431239520489757)
              ·
                refine ⟨34080509786714820183659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90881359431239520489757 34080509786714820183659)
                ·
                  refine ⟨51120764680072230275489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34080509786714820183659 51120764680072230275489)
                  ·
                    refine ⟨38340573510054172706617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51120764680072230275489 38340573510054172706617)
                    ·
                      refine ⟨28755430132540629529963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38340573510054172706617 28755430132540629529963)
                      ·
                        rfl

theorem cell23_56001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_56001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56001 prefixEnd_56001 := by exact prefixLift 56001
  have htrace : WordTrace (prefixWord ++ tailWord_56001) baseStart_56001 baseEnd_56001 := by
    simpa [prefixWord, tailWord_56001, baseEnd_56001] using wordTrace_append hprefix tailTrace_56001
  have hstable : (prefixWord ++ tailWord_56001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56001).length < 2 ^ (prefixWord ++ tailWord_56001).sum := by decide
  have hdescent : baseEnd_56001 < baseStart_56001 := by decide
  rcases family_descends (prefixWord ++ tailWord_56001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56010 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_56010 : Nat := 118140960795 + 56010 * 2 ^ 59
def prefixEnd_56010 : Nat := 4983230072969 + 3 ^ 40 * 56010 * 2
def baseEnd_56010 : Nat := 28760051458431094317421

theorem tailTrace_56010 : CollatzResearch.WordTrace tailWord_56010 prefixEnd_56010 28760051458431094317421 := by
  unfold tailWord_56010
  simp only [CollatzResearch.WordTrace]
  refine ⟨510713131773202647885371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1361901684728540394360989 510713131773202647885371)
  ·
    refine ⟨766069697659803971828057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 510713131773202647885371 766069697659803971828057)
    ·
      refine ⟨574552273244852978871043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766069697659803971828057 574552273244852978871043)
      ·
        refine ⟨861828409867279468306565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574552273244852978871043 861828409867279468306565)
        ·
          refine ⟨161592826850114900307481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 861828409867279468306565 161592826850114900307481)
          ·
            refine ⟨121194620137586175230611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161592826850114900307481 121194620137586175230611)
            ·
              refine ⟨181791930206379262845917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121194620137586175230611 181791930206379262845917)
              ·
                refine ⟨68171973827392223567219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181791930206379262845917 68171973827392223567219)
                ·
                  refine ⟨102257960741088335350829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68171973827392223567219 102257960741088335350829)
                  ·
                    refine ⟨38346735277908125756561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102257960741088335350829 38346735277908125756561)
                    ·
                      refine ⟨28760051458431094317421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38346735277908125756561 28760051458431094317421)
                      ·
                        rfl

theorem cell23_56010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_56010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56010 prefixEnd_56010 := by exact prefixLift 56010
  have htrace : WordTrace (prefixWord ++ tailWord_56010) baseStart_56010 baseEnd_56010 := by
    simpa [prefixWord, tailWord_56010, baseEnd_56010] using wordTrace_append hprefix tailTrace_56010
  have hstable : (prefixWord ++ tailWord_56010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56010).length < 2 ^ (prefixWord ++ tailWord_56010).sum := by decide
  have hdescent : baseEnd_56010 < baseStart_56010 := by decide
  rcases family_descends (prefixWord ++ tailWord_56010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56036 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_56036 : Nat := 118140960795 + 56036 * 2 ^ 59
def prefixEnd_56036 : Nat := 4983230072969 + 3 ^ 40 * 56036 * 2
def baseEnd_56036 : Nat := 28773401955447992592301

theorem tailTrace_56036 : CollatzResearch.WordTrace tailWord_56036 prefixEnd_56036 28773401955447992592301 := by
  unfold tailWord_56036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021900412499308515993981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1362533883332411354658641 1021900412499308515993981)
  ·
    refine ⟨383212654687240693497743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1021900412499308515993981 383212654687240693497743)
    ·
      refine ⟨574818982030861040246615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383212654687240693497743 574818982030861040246615)
      ·
        refine ⟨862228473046291560369923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574818982030861040246615 862228473046291560369923)
        ·
          refine ⟨1293342709569437340554885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862228473046291560369923 1293342709569437340554885)
          ·
            refine ⟨242501758044269501354041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1293342709569437340554885 242501758044269501354041)
            ·
              refine ⟨181876318533202126015531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242501758044269501354041 181876318533202126015531)
              ·
                refine ⟨272814477799803189023297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181876318533202126015531 272814477799803189023297)
                ·
                  refine ⟨204610858349852391767473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272814477799803189023297 204610858349852391767473)
                  ·
                    refine ⟨153458143762389293825605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204610858349852391767473 153458143762389293825605)
                    ·
                      refine ⟨28773401955447992592301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 153458143762389293825605 28773401955447992592301)
                      ·
                        rfl

theorem cell23_56036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_56036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56036 prefixEnd_56036 := by exact prefixLift 56036
  have htrace : WordTrace (prefixWord ++ tailWord_56036) baseStart_56036 baseEnd_56036 := by
    simpa [prefixWord, tailWord_56036, baseEnd_56036] using wordTrace_append hprefix tailTrace_56036
  have hstable : (prefixWord ++ tailWord_56036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56036).length < 2 ^ (prefixWord ++ tailWord_56036).sum := by decide
  have hdescent : baseEnd_56036 < baseStart_56036 := by decide
  rcases family_descends (prefixWord ++ tailWord_56036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56046 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_56046 : Nat := 118140960795 + 56046 * 2 ^ 59
def prefixEnd_56046 : Nat := 4983230072969 + 3 ^ 40 * 56046 * 2
def baseEnd_56046 : Nat := 3197615195776994829695

theorem tailTrace_56046 : CollatzResearch.WordTrace tailWord_56046 prefixEnd_56046 3197615195776994829695 := by
  unfold tailWord_56046
  simp only [CollatzResearch.WordTrace]
  refine ⟨255520694370298592481499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1362777036641592493234661 255520694370298592481499)
  ·
    refine ⟨383281041555447888722249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255520694370298592481499 383281041555447888722249)
    ·
      refine ⟨287460781166585916541687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383281041555447888722249 287460781166585916541687)
      ·
        refine ⟨431191171749878874812531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287460781166585916541687 431191171749878874812531)
        ·
          refine ⟨646786757624818312218797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431191171749878874812531 646786757624818312218797)
          ·
            refine ⟨242545034109306867082049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 646786757624818312218797 242545034109306867082049)
            ·
              refine ⟨181908775581980150311537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242545034109306867082049 181908775581980150311537)
              ·
                refine ⟨136431581686485112733653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181908775581980150311537 136431581686485112733653)
                ·
                  refine ⟨3197615195776994829695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 136431581686485112733653 3197615195776994829695)
                  ·
                    rfl

theorem cell23_56046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_56046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56046 prefixEnd_56046 := by exact prefixLift 56046
  have htrace : WordTrace (prefixWord ++ tailWord_56046) baseStart_56046 baseEnd_56046 := by
    simpa [prefixWord, tailWord_56046, baseEnd_56046] using wordTrace_append hprefix tailTrace_56046
  have hstable : (prefixWord ++ tailWord_56046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56046).length < 2 ^ (prefixWord ++ tailWord_56046).sum := by decide
  have hdescent : baseEnd_56046 < baseStart_56046 := by decide
  rcases family_descends (prefixWord ++ tailWord_56046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56069 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_56069 : Nat := 118140960795 + 56069 * 2 ^ 59
def prefixEnd_56069 : Nat := 4983230072969 + 3 ^ 40 * 56069 * 2
def baseEnd_56069 : Nat := 28790346817046363479649

theorem tailTrace_56069 : CollatzResearch.WordTrace tailWord_56069 prefixEnd_56069 28790346817046363479649 := by
  unfold tailWord_56069
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045004433879063667939261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1363336289252709111959507 2045004433879063667939261)
  ·
    refine ⟨766876662704648875477223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2045004433879063667939261 766876662704648875477223)
    ·
      refine ⟨1150314994056973313215835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766876662704648875477223 1150314994056973313215835)
      ·
        refine ⟨1725472491085459969823753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150314994056973313215835 1725472491085459969823753)
        ·
          refine ⟨1294104368314094977367815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1725472491085459969823753 1294104368314094977367815)
          ·
            refine ⟨1941156552471142466051723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294104368314094977367815 1941156552471142466051723)
            ·
              refine ⟨2911734828706713699077585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941156552471142466051723 2911734828706713699077585)
              ·
                refine ⟨2183801121530035274308189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911734828706713699077585 2183801121530035274308189)
                ·
                  refine ⟨818925420573763227865571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2183801121530035274308189 818925420573763227865571)
                  ·
                    refine ⟨1228388130860644841798357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 818925420573763227865571 1228388130860644841798357)
                    ·
                      refine ⟨28790346817046363479649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1228388130860644841798357 28790346817046363479649)
                      ·
                        rfl

theorem cell23_56069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_56069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56069 prefixEnd_56069 := by exact prefixLift 56069
  have htrace : WordTrace (prefixWord ++ tailWord_56069) baseStart_56069 baseEnd_56069 := by
    simpa [prefixWord, tailWord_56069, baseEnd_56069] using wordTrace_append hprefix tailTrace_56069
  have hstable : (prefixWord ++ tailWord_56069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56069).length < 2 ^ (prefixWord ++ tailWord_56069).sum := by decide
  have hdescent : baseEnd_56069 < baseStart_56069 := by decide
  rcases family_descends (prefixWord ++ tailWord_56069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56089 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 2, 8]
def baseStart_56089 : Nat := 118140960795 + 56089 * 2 ^ 59
def prefixEnd_56089 : Nat := 4983230072969 + 3 ^ 40 * 56089 * 2
def baseEnd_56089 : Nat := 9600205476712095076519

theorem tailTrace_56089 : CollatzResearch.WordTrace tailWord_56089 prefixEnd_56089 9600205476712095076519 := by
  unfold tailWord_56089
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045733893806607083667321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1363822595871071389111547 2045733893806607083667321)
  ·
    refine ⟨1534300420354955312750491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2045733893806607083667321 1534300420354955312750491)
    ·
      refine ⟨2301450630532432969125737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534300420354955312750491 2301450630532432969125737)
      ·
        refine ⟨1726087972899324726844303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2301450630532432969125737 1726087972899324726844303)
        ·
          refine ⟨2589131959348987090266455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726087972899324726844303 2589131959348987090266455)
          ·
            refine ⟨3883697939023480635399683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589131959348987090266455 3883697939023480635399683)
            ·
              refine ⟨5825546908535220953099525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883697939023480635399683 5825546908535220953099525)
              ·
                refine ⟨1092290045350353928706161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5825546908535220953099525 1092290045350353928706161)
                ·
                  refine ⟨819217534012765446529621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092290045350353928706161 819217534012765446529621)
                  ·
                    refine ⟨9600205476712095076519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 819217534012765446529621 9600205476712095076519)
                    ·
                      rfl

theorem cell23_56089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_56089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56089 prefixEnd_56089 := by exact prefixLift 56089
  have htrace : WordTrace (prefixWord ++ tailWord_56089) baseStart_56089 baseEnd_56089 := by
    simpa [prefixWord, tailWord_56089, baseEnd_56089] using wordTrace_append hprefix tailTrace_56089
  have hstable : (prefixWord ++ tailWord_56089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56089).length < 2 ^ (prefixWord ++ tailWord_56089).sum := by decide
  have hdescent : baseEnd_56089 < baseStart_56089 := by decide
  rcases family_descends (prefixWord ++ tailWord_56089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56110 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_56110 : Nat := 118140960795 + 56110 * 2 ^ 59
def prefixEnd_56110 : Nat := 4983230072969 + 3 ^ 40 * 56110 * 2
def baseEnd_56110 : Nat := 9603799841293567688987

theorem tailTrace_56110 : CollatzResearch.WordTrace tailWord_56110 prefixEnd_56110 9603799841293567688987 := by
  unfold tailWord_56110
  simp only [CollatzResearch.WordTrace]
  refine ⟨255812478341315958772723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1364333217820351780121189 255812478341315958772723)
  ·
    refine ⟨383718717511973938159085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255812478341315958772723 383718717511973938159085)
    ·
      refine ⟨143894519066990226809657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383718717511973938159085 143894519066990226809657)
      ·
        refine ⟨107920889300242670107243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143894519066990226809657 107920889300242670107243)
        ·
          refine ⟨161881333950364005160865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107920889300242670107243 161881333950364005160865)
          ·
            refine ⟨121411000462773003870649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161881333950364005160865 121411000462773003870649)
            ·
              refine ⟨91058250347079752902987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121411000462773003870649 91058250347079752902987)
              ·
                refine ⟨136587375520619629354481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91058250347079752902987 136587375520619629354481)
                ·
                  refine ⟨102440531640464722015861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136587375520619629354481 102440531640464722015861)
                  ·
                    refine ⟨9603799841293567688987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102440531640464722015861 9603799841293567688987)
                    ·
                      rfl

theorem cell23_56110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_56110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56110 prefixEnd_56110 := by exact prefixLift 56110
  have htrace : WordTrace (prefixWord ++ tailWord_56110) baseStart_56110 baseEnd_56110 := by
    simpa [prefixWord, tailWord_56110, baseEnd_56110] using wordTrace_append hprefix tailTrace_56110
  have hstable : (prefixWord ++ tailWord_56110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56110).length < 2 ^ (prefixWord ++ tailWord_56110).sum := by decide
  have hdescent : baseEnd_56110 < baseStart_56110 := by decide
  rcases family_descends (prefixWord ++ tailWord_56110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56113 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_56113 : Nat := 118140960795 + 56113 * 2 ^ 59
def prefixEnd_56113 : Nat := 4983230072969 + 3 ^ 40 * 56113 * 2
def baseEnd_56113 : Nat := 28812939965844191329447

theorem tailTrace_56113 : CollatzResearch.WordTrace tailWord_56113 prefixEnd_56113 28812939965844191329447 := by
  unfold tailWord_56113
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046609245719659182540993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1364406163813106121693995 2046609245719659182540993)
  ·
    refine ⟨1534956934289744386905745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2046609245719659182540993 1534956934289744386905745)
    ·
      refine ⟨1151217700717308290179309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1534956934289744386905745 1151217700717308290179309)
      ·
        refine ⟨431706637768990608817241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1151217700717308290179309 431706637768990608817241)
        ·
          refine ⟨323779978326742956612931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431706637768990608817241 323779978326742956612931)
          ·
            refine ⟨485669967490114434919397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323779978326742956612931 485669967490114434919397)
            ·
              refine ⟨91063118904396456547387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485669967490114434919397 91063118904396456547387)
              ·
                refine ⟨136594678356594684821081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91063118904396456547387 136594678356594684821081)
                ·
                  refine ⟨102446008767446013615811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136594678356594684821081 102446008767446013615811)
                  ·
                    refine ⟨153669013151169020423717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102446008767446013615811 153669013151169020423717)
                    ·
                      refine ⟨28812939965844191329447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 153669013151169020423717 28812939965844191329447)
                      ·
                        rfl

theorem cell23_56113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_56113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56113 prefixEnd_56113 := by exact prefixLift 56113
  have htrace : WordTrace (prefixWord ++ tailWord_56113) baseStart_56113 baseEnd_56113 := by
    simpa [prefixWord, tailWord_56113, baseEnd_56113] using wordTrace_append hprefix tailTrace_56113
  have hstable : (prefixWord ++ tailWord_56113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56113).length < 2 ^ (prefixWord ++ tailWord_56113).sum := by decide
  have hdescent : baseEnd_56113 < baseStart_56113 := by decide
  rcases family_descends (prefixWord ++ tailWord_56113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56174 : List Nat := [4, 1, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_56174 : Nat := 118140960795 + 56174 * 2 ^ 59
def prefixEnd_56174 : Nat := 4983230072969 + 3 ^ 40 * 56174 * 2
def baseEnd_56174 : Nat := 9614754095256150888889

theorem tailTrace_56174 : CollatzResearch.WordTrace tailWord_56174 prefixEnd_56174 9614754095256150888889 := by
  unfold tailWord_56174
  simp only [CollatzResearch.WordTrace]
  refine ⟨256104262312333325063947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1365889398999111067007717 256104262312333325063947)
  ·
    refine ⟨384156393468499987595921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256104262312333325063947 384156393468499987595921)
    ·
      refine ⟨288117295101374990696941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384156393468499987595921 288117295101374990696941)
      ·
        refine ⟨108043985663015621511353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288117295101374990696941 108043985663015621511353)
        ·
          refine ⟨81032989247261716133515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108043985663015621511353 81032989247261716133515)
          ·
            refine ⟨121549483870892574200273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81032989247261716133515 121549483870892574200273)
            ·
              refine ⟨91162112903169430650205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121549483870892574200273 91162112903169430650205)
              ·
                refine ⟨34185792338688536493827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91162112903169430650205 34185792338688536493827)
                ·
                  refine ⟨51278688508032804740741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34185792338688536493827 51278688508032804740741)
                  ·
                    refine ⟨9614754095256150888889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51278688508032804740741 9614754095256150888889)
                    ·
                      rfl

theorem cell23_56174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_56174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56174 prefixEnd_56174 := by exact prefixLift 56174
  have htrace : WordTrace (prefixWord ++ tailWord_56174) baseStart_56174 baseEnd_56174 := by
    simpa [prefixWord, tailWord_56174, baseEnd_56174] using wordTrace_append hprefix tailTrace_56174
  have hstable : (prefixWord ++ tailWord_56174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56174).length < 2 ^ (prefixWord ++ tailWord_56174).sum := by decide
  have hdescent : baseEnd_56174 < baseStart_56174 := by decide
  rcases family_descends (prefixWord ++ tailWord_56174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56197 : List Nat := [1, 3, 1, 1, 3, 3, 2, 4, 1, 1, 3]
def baseStart_56197 : Nat := 118140960795 + 56197 * 2 ^ 59
def prefixEnd_56197 : Nat := 4983230072969 + 3 ^ 40 * 56197 * 2
def baseEnd_56197 : Nat := 28856072340821862679061

theorem tailTrace_56197 : CollatzResearch.WordTrace tailWord_56197 prefixEnd_56197 28856072340821862679061 := by
  unfold tailWord_56197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049672977415341528598845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1366448651610227685732563 2049672977415341528598845)
  ·
    refine ⟨768627366530753073224567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2049672977415341528598845 768627366530753073224567)
    ·
      refine ⟨1152941049796129609836851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768627366530753073224567 1152941049796129609836851)
      ·
        refine ⟨1729411574694194414755277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152941049796129609836851 1729411574694194414755277)
        ·
          refine ⟨648529340510322905533229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1729411574694194414755277 648529340510322905533229)
          ·
            refine ⟨243198502691371089574961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 648529340510322905533229 243198502691371089574961)
            ·
              refine ⟨182398877018528317181221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243198502691371089574961 182398877018528317181221)
              ·
                refine ⟨34199789440974059471479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182398877018528317181221 34199789440974059471479)
                ·
                  refine ⟨51299684161461089207219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34199789440974059471479 51299684161461089207219)
                  ·
                    refine ⟨76949526242191633810829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51299684161461089207219 76949526242191633810829)
                    ·
                      refine ⟨28856072340821862679061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 76949526242191633810829 28856072340821862679061)
                      ·
                        rfl

theorem cell23_56197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_56197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56197 prefixEnd_56197 := by exact prefixLift 56197
  have htrace : WordTrace (prefixWord ++ tailWord_56197) baseStart_56197 baseEnd_56197 := by
    simpa [prefixWord, tailWord_56197, baseEnd_56197] using wordTrace_append hprefix tailTrace_56197
  have hstable : (prefixWord ++ tailWord_56197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56197).length < 2 ^ (prefixWord ++ tailWord_56197).sum := by decide
  have hdescent : baseEnd_56197 < baseStart_56197 := by decide
  rcases family_descends (prefixWord ++ tailWord_56197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56213 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_56213 : Nat := 118140960795 + 56213 * 2 ^ 59
def prefixEnd_56213 : Nat := 4983230072969 + 3 ^ 40 * 56213 * 2
def baseEnd_56213 : Nat := 9621429343764600026329

theorem tailTrace_56213 : CollatzResearch.WordTrace tailWord_56213 prefixEnd_56213 9621429343764600026329 := by
  unfold tailWord_56213
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050256545357376261181293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1366837696904917507454195 2050256545357376261181293)
  ·
    refine ⟨768846204509016097942985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2050256545357376261181293 768846204509016097942985)
    ·
      refine ⟨576634653381762073457239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 768846204509016097942985 576634653381762073457239)
      ·
        refine ⟨864951980072643110185859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576634653381762073457239 864951980072643110185859)
        ·
          refine ⟨1297427970108964665278789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864951980072643110185859 1297427970108964665278789)
          ·
            refine ⟨243267744395430874739773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1297427970108964665278789 243267744395430874739773)
            ·
              refine ⟨91225404148286578027415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243267744395430874739773 91225404148286578027415)
              ·
                refine ⟨136838106222429867041123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91225404148286578027415 136838106222429867041123)
                ·
                  refine ⟨205257159333644800561685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136838106222429867041123 205257159333644800561685)
                  ·
                    refine ⟨9621429343764600026329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205257159333644800561685 9621429343764600026329)
                    ·
                      rfl

theorem cell23_56213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_56213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56213 prefixEnd_56213 := by exact prefixLift 56213
  have htrace : WordTrace (prefixWord ++ tailWord_56213) baseStart_56213 baseEnd_56213 := by
    simpa [prefixWord, tailWord_56213, baseEnd_56213] using wordTrace_append hprefix tailTrace_56213
  have hstable : (prefixWord ++ tailWord_56213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56213).length < 2 ^ (prefixWord ++ tailWord_56213).sum := by decide
  have hdescent : baseEnd_56213 < baseStart_56213 := by decide
  rcases family_descends (prefixWord ++ tailWord_56213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56231 : List Nat := [1, 1, 6, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_56231 : Nat := 118140960795 + 56231 * 2 ^ 59
def prefixEnd_56231 : Nat := 4983230072969 + 3 ^ 40 * 56231 * 2
def baseEnd_56231 : Nat := 28873530683074729653905

theorem tailTrace_56231 : CollatzResearch.WordTrace tailWord_56231 prefixEnd_56231 28873530683074729653905 := by
  unfold tailWord_56231
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050913059292165335336547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1367275372861443556891031 2050913059292165335336547)
  ·
    refine ⟨3076369588938248003004821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2050913059292165335336547 3076369588938248003004821)
    ·
      refine ⟨144204824481480375140851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3076369588938248003004821 144204824481480375140851)
      ·
        refine ⟨216307236722220562711277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144204824481480375140851 216307236722220562711277)
        ·
          refine ⟨81115213770832711016729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216307236722220562711277 81115213770832711016729)
          ·
            refine ⟨60836410328124533262547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81115213770832711016729 60836410328124533262547)
            ·
              refine ⟨91254615492186799893821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60836410328124533262547 91254615492186799893821)
              ·
                refine ⟨34220480809570049960183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91254615492186799893821 34220480809570049960183)
                ·
                  refine ⟨51330721214355074940275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34220480809570049960183 51330721214355074940275)
                  ·
                    refine ⟨76996081821532612410413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51330721214355074940275 76996081821532612410413)
                    ·
                      refine ⟨28873530683074729653905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 76996081821532612410413 28873530683074729653905)
                      ·
                        rfl

theorem cell23_56231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_56231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56231 prefixEnd_56231 := by exact prefixLift 56231
  have htrace : WordTrace (prefixWord ++ tailWord_56231) baseStart_56231 baseEnd_56231 := by
    simpa [prefixWord, tailWord_56231, baseEnd_56231] using wordTrace_append hprefix tailTrace_56231
  have hstable : (prefixWord ++ tailWord_56231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56231).length < 2 ^ (prefixWord ++ tailWord_56231).sum := by decide
  have hdescent : baseEnd_56231 < baseStart_56231 := by decide
  rcases family_descends (prefixWord ++ tailWord_56231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56264 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 2, 4]
def baseStart_56264 : Nat := 118140960795 + 56264 * 2 ^ 59
def prefixEnd_56264 : Nat := 4983230072969 + 3 ^ 40 * 56264 * 2
def baseEnd_56264 : Nat := 9630158514891033513751

theorem tailTrace_56264 : CollatzResearch.WordTrace tailWord_56264 prefixEnd_56264 9630158514891033513751 := by
  unfold tailWord_56264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026058334086305985643923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1368077778781741314191897 1026058334086305985643923)
  ·
    refine ⟨1539087501129458978465885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1026058334086305985643923 1539087501129458978465885)
    ·
      refine ⟨577157812923547116924707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1539087501129458978465885 577157812923547116924707)
      ·
        refine ⟨865736719385320675387061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577157812923547116924707 865736719385320675387061)
        ·
          refine ⟨81162817442373813317537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 865736719385320675387061 81162817442373813317537)
          ·
            refine ⟨60872113081780359988153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81162817442373813317537 60872113081780359988153)
            ·
              refine ⟨45654084811335269991115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60872113081780359988153 45654084811335269991115)
              ·
                refine ⟨68481127217002904986673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45654084811335269991115 68481127217002904986673)
                ·
                  refine ⟨51360845412752178740005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68481127217002904986673 51360845412752178740005)
                  ·
                    refine ⟨9630158514891033513751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51360845412752178740005 9630158514891033513751)
                    ·
                      rfl

theorem cell23_56264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_56264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56264 prefixEnd_56264 := by exact prefixLift 56264
  have htrace : WordTrace (prefixWord ++ tailWord_56264) baseStart_56264 baseEnd_56264 := by
    simpa [prefixWord, tailWord_56264, baseEnd_56264] using wordTrace_append hprefix tailTrace_56264
  have hstable : (prefixWord ++ tailWord_56264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56264).length < 2 ^ (prefixWord ++ tailWord_56264).sum := by decide
  have hdescent : baseEnd_56264 < baseStart_56264 := by decide
  rcases family_descends (prefixWord ++ tailWord_56264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56274 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_56274 : Nat := 118140960795 + 56274 * 2 ^ 59
def prefixEnd_56274 : Nat := 4983230072969 + 3 ^ 40 * 56274 * 2
def baseEnd_56274 : Nat := 28895610351218061416207

theorem tailTrace_56274 : CollatzResearch.WordTrace tailWord_56274 prefixEnd_56274 28895610351218061416207 := by
  unfold tailWord_56274
  simp only [CollatzResearch.WordTrace]
  refine ⟨513120349534095919787969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1368320932090922452767917 513120349534095919787969)
  ·
    refine ⟨384840262150571939840977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 513120349534095919787969 384840262150571939840977)
    ·
      refine ⟨288630196612928954880733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384840262150571939840977 288630196612928954880733)
      ·
        refine ⟨108236323729848358080275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288630196612928954880733 108236323729848358080275)
        ·
          refine ⟨162354485594772537120413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108236323729848358080275 162354485594772537120413)
          ·
            refine ⟨60882932098039701420155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162354485594772537120413 60882932098039701420155)
            ·
              refine ⟨91324398147059552130233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60882932098039701420155 91324398147059552130233)
              ·
                refine ⟨68493298610294664097675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91324398147059552130233 68493298610294664097675)
                ·
                  refine ⟨102739947915441996146513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68493298610294664097675 102739947915441996146513)
                  ·
                    refine ⟨77054960936581497109885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102739947915441996146513 77054960936581497109885)
                    ·
                      refine ⟨28895610351218061416207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 77054960936581497109885 28895610351218061416207)
                      ·
                        rfl

theorem cell23_56274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_56274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56274 prefixEnd_56274 := by exact prefixLift 56274
  have htrace : WordTrace (prefixWord ++ tailWord_56274) baseStart_56274 baseEnd_56274 := by
    simpa [prefixWord, tailWord_56274, baseEnd_56274] using wordTrace_append hprefix tailTrace_56274
  have hstable : (prefixWord ++ tailWord_56274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56274).length < 2 ^ (prefixWord ++ tailWord_56274).sum := by decide
  have hdescent : baseEnd_56274 < baseStart_56274 := by decide
  rcases family_descends (prefixWord ++ tailWord_56274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56310 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_56310 : Nat := 118140960795 + 56310 * 2 ^ 59
def prefixEnd_56310 : Nat := 4983230072969 + 3 ^ 40 * 56310 * 2
def baseEnd_56310 : Nat := 28914095654779920566041

theorem tailTrace_56310 : CollatzResearch.WordTrace tailWord_56310 prefixEnd_56310 28914095654779920566041 := by
  unfold tailWord_56310
  simp only [CollatzResearch.WordTrace]
  refine ⟨128362151625372614216399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1369196284003974551641589 128362151625372614216399)
  ·
    refine ⟨192543227438058921324599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128362151625372614216399 192543227438058921324599)
    ·
      refine ⟨288814841157088381986899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192543227438058921324599 288814841157088381986899)
      ·
        refine ⟨433222261735632572980349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288814841157088381986899 433222261735632572980349)
        ·
          refine ⟨162458348150862214867631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433222261735632572980349 162458348150862214867631)
          ·
            refine ⟨243687522226293322301447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162458348150862214867631 243687522226293322301447)
            ·
              refine ⟨365531283339439983452171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243687522226293322301447 365531283339439983452171)
              ·
                refine ⟨548296925009159975178257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365531283339439983452171 548296925009159975178257)
                ·
                  refine ⟨411222693756869981383693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548296925009159975178257 411222693756869981383693)
                  ·
                    refine ⟨154208510158826243018885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411222693756869981383693 154208510158826243018885)
                    ·
                      refine ⟨28914095654779920566041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 154208510158826243018885 28914095654779920566041)
                      ·
                        rfl

theorem cell23_56310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_56310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56310 prefixEnd_56310 := by exact prefixLift 56310
  have htrace : WordTrace (prefixWord ++ tailWord_56310) baseStart_56310 baseEnd_56310 := by
    simpa [prefixWord, tailWord_56310, baseEnd_56310] using wordTrace_append hprefix tailTrace_56310
  have hstable : (prefixWord ++ tailWord_56310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56310).length < 2 ^ (prefixWord ++ tailWord_56310).sum := by decide
  have hdescent : baseEnd_56310 < baseStart_56310 := by decide
  rcases family_descends (prefixWord ++ tailWord_56310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56313 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 3]
def baseStart_56313 : Nat := 118140960795 + 56313 * 2 ^ 59
def prefixEnd_56313 : Nat := 4983230072969 + 3 ^ 40 * 56313 * 2
def baseEnd_56313 : Nat := 28915636096743408828527

theorem tailTrace_56313 : CollatzResearch.WordTrace tailWord_56313 prefixEnd_56313 28915636096743408828527 := by
  unfold tailWord_56313
  simp only [CollatzResearch.WordTrace]
  refine ⟨2053903844995093339821593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1369269229996728893214395 2053903844995093339821593)
  ·
    refine ⟨1540427883746320004866195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2053903844995093339821593 1540427883746320004866195)
    ·
      refine ⟨2310641825619480007299293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1540427883746320004866195 2310641825619480007299293)
      ·
        refine ⟨866490684607305002737235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2310641825619480007299293 866490684607305002737235)
        ·
          refine ⟨1299736026910957504105853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866490684607305002737235 1299736026910957504105853)
          ·
            refine ⟨487401010091609064039695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1299736026910957504105853 487401010091609064039695)
            ·
              refine ⟨731101515137413596059543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487401010091609064039695 731101515137413596059543)
              ·
                refine ⟨1096652272706120394089315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731101515137413596059543 1096652272706120394089315)
                ·
                  refine ⟨1644978409059180591133973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096652272706120394089315 1644978409059180591133973)
                  ·
                    refine ⟨77108362924649090209405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1644978409059180591133973 77108362924649090209405)
                    ·
                      refine ⟨28915636096743408828527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 77108362924649090209405 28915636096743408828527)
                      ·
                        rfl

theorem cell23_56313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_56313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56313 prefixEnd_56313 := by exact prefixLift 56313
  have htrace : WordTrace (prefixWord ++ tailWord_56313) baseStart_56313 baseEnd_56313 := by
    simpa [prefixWord, tailWord_56313, baseEnd_56313] using wordTrace_append hprefix tailTrace_56313
  have hstable : (prefixWord ++ tailWord_56313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56313).length < 2 ^ (prefixWord ++ tailWord_56313).sum := by decide
  have hdescent : baseEnd_56313 < baseStart_56313 := by decide
  rcases family_descends (prefixWord ++ tailWord_56313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56327 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_56327 : Nat := 118140960795 + 56327 * 2 ^ 59
def prefixEnd_56327 : Nat := 4983230072969 + 3 ^ 40 * 56327 * 2
def baseEnd_56327 : Nat := 28922824825906354053463

theorem tailTrace_56327 : CollatzResearch.WordTrace tailWord_56327 prefixEnd_56327 28922824825906354053463 := by
  unfold tailWord_56327
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054414466944373730831235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1369609644629582487220823 2054414466944373730831235)
  ·
    refine ⟨3081621700416560596246853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2054414466944373730831235 3081621700416560596246853)
    ·
      refine ⟨577804068828105111796285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3081621700416560596246853 577804068828105111796285)
      ·
        refine ⟨216676525810539416923607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577804068828105111796285 216676525810539416923607)
        ·
          refine ⟨325014788715809125385411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216676525810539416923607 325014788715809125385411)
          ·
            refine ⟨487522183073713688078117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325014788715809125385411 487522183073713688078117)
            ·
              refine ⟨91410409326321316514647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 487522183073713688078117 91410409326321316514647)
              ·
                refine ⟨137115613989481974771971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91410409326321316514647 137115613989481974771971)
                ·
                  refine ⟨205673420984222962157957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137115613989481974771971 205673420984222962157957)
                  ·
                    refine ⟨38563766434541805404617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205673420984222962157957 38563766434541805404617)
                    ·
                      refine ⟨28922824825906354053463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38563766434541805404617 28922824825906354053463)
                      ·
                        rfl

theorem cell23_56327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_56327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56327 prefixEnd_56327 := by exact prefixLift 56327
  have htrace : WordTrace (prefixWord ++ tailWord_56327) baseStart_56327 baseEnd_56327 := by
    simpa [prefixWord, tailWord_56327, baseEnd_56327] using wordTrace_append hprefix tailTrace_56327
  have hstable : (prefixWord ++ tailWord_56327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56327).length < 2 ^ (prefixWord ++ tailWord_56327).sum := by decide
  have hdescent : baseEnd_56327 < baseStart_56327 := by decide
  rcases family_descends (prefixWord ++ tailWord_56327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56348 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_56348 : Nat := 118140960795 + 56348 * 2 ^ 59
def prefixEnd_56348 : Nat := 4983230072969 + 3 ^ 40 * 56348 * 2
def baseEnd_56348 : Nat := 28933607919650771890867

theorem tailTrace_56348 : CollatzResearch.WordTrace tailWord_56348 prefixEnd_56348 28933607919650771890867 := by
  unfold tailWord_56348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027590199934147158672849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1370120266578862878230465 1027590199934147158672849)
  ·
    refine ⟨770692649950610369004637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1027590199934147158672849 770692649950610369004637)
    ·
      refine ⟨289009743731478888376739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 770692649950610369004637 289009743731478888376739)
      ·
        refine ⟨433514615597218332565109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289009743731478888376739 433514615597218332565109)
        ·
          refine ⟨40641995212239218677979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 433514615597218332565109 40641995212239218677979)
          ·
            refine ⟨60962992818358828016969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40641995212239218677979 60962992818358828016969)
            ·
              refine ⟨45722244613769121012727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60962992818358828016969 45722244613769121012727)
              ·
                refine ⟨68583366920653681519091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45722244613769121012727 68583366920653681519091)
                ·
                  refine ⟨102875050380980522278637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68583366920653681519091 102875050380980522278637)
                  ·
                    refine ⟨38578143892867695854489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102875050380980522278637 38578143892867695854489)
                    ·
                      refine ⟨28933607919650771890867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38578143892867695854489 28933607919650771890867)
                      ·
                        rfl

theorem cell23_56348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_56348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56348 prefixEnd_56348 := by exact prefixLift 56348
  have htrace : WordTrace (prefixWord ++ tailWord_56348) baseStart_56348 baseEnd_56348 := by
    simpa [prefixWord, tailWord_56348, baseEnd_56348] using wordTrace_append hprefix tailTrace_56348
  have hstable : (prefixWord ++ tailWord_56348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56348).length < 2 ^ (prefixWord ++ tailWord_56348).sum := by decide
  have hdescent : baseEnd_56348 < baseStart_56348 := by decide
  rcases family_descends (prefixWord ++ tailWord_56348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56363 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 4, 5]
def baseStart_56363 : Nat := 118140960795 + 56363 * 2 ^ 59
def prefixEnd_56363 : Nat := 4983230072969 + 3 ^ 40 * 56363 * 2
def baseEnd_56363 : Nat := 9647103376489404401099

theorem tailTrace_56363 : CollatzResearch.WordTrace tailWord_56363 prefixEnd_56363 9647103376489404401099 := by
  unfold tailWord_56363
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055727494813951879141743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1370484996542634586094495 2055727494813951879141743)
  ·
    refine ⟨3083591242220927818712615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2055727494813951879141743 3083591242220927818712615)
    ·
      refine ⟨4625386863331391728068923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083591242220927818712615 4625386863331391728068923)
      ·
        refine ⟨6938080294997087592103385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4625386863331391728068923 6938080294997087592103385)
        ·
          refine ⟨5203560221247815694077539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6938080294997087592103385 5203560221247815694077539)
          ·
            refine ⟨7805340331871723541116309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203560221247815694077539 7805340331871723541116309)
            ·
              refine ⟨365875328056487040989827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7805340331871723541116309 365875328056487040989827)
              ·
                refine ⟨548812992084730561484741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365875328056487040989827 548812992084730561484741)
                ·
                  refine ⟨102902436015886980278389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548812992084730561484741 102902436015886980278389)
                  ·
                    refine ⟨9647103376489404401099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102902436015886980278389 9647103376489404401099)
                    ·
                      rfl

theorem cell23_56363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 5].length) (baseStart_56363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56363 prefixEnd_56363 := by exact prefixLift 56363
  have htrace : WordTrace (prefixWord ++ tailWord_56363) baseStart_56363 baseEnd_56363 := by
    simpa [prefixWord, tailWord_56363, baseEnd_56363] using wordTrace_append hprefix tailTrace_56363
  have hstable : (prefixWord ++ tailWord_56363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56363).length < 2 ^ (prefixWord ++ tailWord_56363).sum := by decide
  have hdescent : baseEnd_56363 < baseStart_56363 := by decide
  rcases family_descends (prefixWord ++ tailWord_56363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56373 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_56373 : Nat := 118140960795 + 56373 * 2 ^ 59
def prefixEnd_56373 : Nat := 4983230072969 + 3 ^ 40 * 56373 * 2
def baseEnd_56373 : Nat := 28946444936013174078251

theorem tailTrace_56373 : CollatzResearch.WordTrace tailWord_56373 prefixEnd_56373 28946444936013174078251 := by
  unfold tailWord_56373
  simp only [CollatzResearch.WordTrace]
  refine ⟨2056092224777723587005773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1370728149851815724670515 2056092224777723587005773)
  ·
    refine ⟨771034584291646345127165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2056092224777723587005773 771034584291646345127165)
    ·
      refine ⟨289137969109367379422687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 771034584291646345127165 289137969109367379422687)
      ·
        refine ⟨433706953664051069134031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289137969109367379422687 433706953664051069134031)
        ·
          refine ⟨650560430496076603701047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433706953664051069134031 650560430496076603701047)
          ·
            refine ⟨975840645744114905551571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650560430496076603701047 975840645744114905551571)
            ·
              refine ⟨1463760968616172358327357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975840645744114905551571 1463760968616172358327357)
              ·
                refine ⟨548910363231064634372759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1463760968616172358327357 548910363231064634372759)
                ·
                  refine ⟨823365544846596951559139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548910363231064634372759 823365544846596951559139)
                  ·
                    refine ⟨1235048317269895427338709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 823365544846596951559139 1235048317269895427338709)
                    ·
                      refine ⟨28946444936013174078251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1235048317269895427338709 28946444936013174078251)
                      ·
                        rfl

theorem cell23_56373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_56373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56373 prefixEnd_56373 := by exact prefixLift 56373
  have htrace : WordTrace (prefixWord ++ tailWord_56373) baseStart_56373 baseEnd_56373 := by
    simpa [prefixWord, tailWord_56373, baseEnd_56373] using wordTrace_append hprefix tailTrace_56373
  have hstable : (prefixWord ++ tailWord_56373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56373).length < 2 ^ (prefixWord ++ tailWord_56373).sum := by decide
  have hdescent : baseEnd_56373 < baseStart_56373 := by decide
  rcases family_descends (prefixWord ++ tailWord_56373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56400 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 1, 6, 2]
def baseStart_56400 : Nat := 118140960795 + 56400 * 2 ^ 59
def prefixEnd_56400 : Nat := 4983230072969 + 3 ^ 40 * 56400 * 2
def baseEnd_56400 : Nat := 28960308913684568440627

theorem tailTrace_56400 : CollatzResearch.WordTrace tailWord_56400 prefixEnd_56400 28960308913684568440627 := by
  unfold tailWord_56400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028538497839953599119327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1371384663786604798825769 1028538497839953599119327)
  ·
    refine ⟨1542807746759930398678991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028538497839953599119327 1542807746759930398678991)
    ·
      refine ⟨2314211620139895598018487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542807746759930398678991 2314211620139895598018487)
      ·
        refine ⟨3471317430209843397027731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314211620139895598018487 3471317430209843397027731)
        ·
          refine ⟨5206976145314765095541597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471317430209843397027731 5206976145314765095541597)
          ·
            refine ⟨1952616054493036910828099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5206976145314765095541597 1952616054493036910828099)
            ·
              refine ⟨2928924081739555366242149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952616054493036910828099 2928924081739555366242149)
              ·
                refine ⟨549173265326166631170403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2928924081739555366242149 549173265326166631170403)
                ·
                  refine ⟨823759897989249946755605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549173265326166631170403 823759897989249946755605)
                  ·
                    refine ⟨38613745218246091254169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 823759897989249946755605 38613745218246091254169)
                    ·
                      refine ⟨28960308913684568440627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38613745218246091254169 28960308913684568440627)
                      ·
                        rfl

theorem cell23_56400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 6, 2].length) (baseStart_56400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56400 prefixEnd_56400 := by exact prefixLift 56400
  have htrace : WordTrace (prefixWord ++ tailWord_56400) baseStart_56400 baseEnd_56400 := by
    simpa [prefixWord, tailWord_56400, baseEnd_56400] using wordTrace_append hprefix tailTrace_56400
  have hstable : (prefixWord ++ tailWord_56400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56400).length < 2 ^ (prefixWord ++ tailWord_56400).sum := by decide
  have hdescent : baseEnd_56400 < baseStart_56400 := by decide
  rcases family_descends (prefixWord ++ tailWord_56400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56414 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_56414 : Nat := 118140960795 + 56414 * 2 ^ 59
def prefixEnd_56414 : Nat := 4983230072969 + 3 ^ 40 * 56414 * 2
def baseEnd_56414 : Nat := 9655832547615837888521

theorem tailTrace_56414 : CollatzResearch.WordTrace tailWord_56414 prefixEnd_56414 9655832547615837888521 := by
  unfold tailWord_56414
  simp only [CollatzResearch.WordTrace]
  refine ⟨257198452203648448656037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1371725078419458392832197 257198452203648448656037)
  ·
    refine ⟨48224709788184084123007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257198452203648448656037 48224709788184084123007)
    ·
      refine ⟨72337064682276126184511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48224709788184084123007 72337064682276126184511)
      ·
        refine ⟨108505597023414189276767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72337064682276126184511 108505597023414189276767)
        ·
          refine ⟨162758395535121283915151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108505597023414189276767 162758395535121283915151)
          ·
            refine ⟨244137593302681925872727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162758395535121283915151 244137593302681925872727)
            ·
              refine ⟨366206389954022888809091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244137593302681925872727 366206389954022888809091)
              ·
                refine ⟨549309584931034333213637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366206389954022888809091 549309584931034333213637)
                ·
                  refine ⟨102995547174568937477557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549309584931034333213637 102995547174568937477557)
                  ·
                    refine ⟨9655832547615837888521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102995547174568937477557 9655832547615837888521)
                    ·
                      rfl

theorem cell23_56414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_56414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56414 prefixEnd_56414 := by exact prefixLift 56414
  have htrace : WordTrace (prefixWord ++ tailWord_56414) baseStart_56414 baseEnd_56414 := by
    simpa [prefixWord, tailWord_56414, baseEnd_56414] using wordTrace_append hprefix tailTrace_56414
  have hstable : (prefixWord ++ tailWord_56414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56414).length < 2 ^ (prefixWord ++ tailWord_56414).sum := by decide
  have hdescent : baseEnd_56414 < baseStart_56414 := by decide
  rcases family_descends (prefixWord ++ tailWord_56414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56443 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6]
def baseStart_56443 : Nat := 118140960795 + 56443 * 2 ^ 59
def prefixEnd_56443 : Nat := 4983230072969 + 3 ^ 40 * 56443 * 2
def baseEnd_56443 : Nat := 28982388581827900202929

theorem tailTrace_56443 : CollatzResearch.WordTrace tailWord_56443 prefixEnd_56443 28982388581827900202929 := by
  unfold tailWord_56443
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058645334524125542053983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1372430223016083694702655 2058645334524125542053983)
  ·
    refine ⟨3087968001786188313080975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2058645334524125542053983 3087968001786188313080975)
    ·
      refine ⟨4631952002679282469621463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3087968001786188313080975 4631952002679282469621463)
      ·
        refine ⟨6947928004018923704432195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4631952002679282469621463 6947928004018923704432195)
        ·
          refine ⟨10421892006028385556648293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6947928004018923704432195 10421892006028385556648293)
          ·
            refine ⟨1954104751130322291871555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10421892006028385556648293 1954104751130322291871555)
            ·
              refine ⟨2931157126695483437807333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954104751130322291871555 2931157126695483437807333)
              ·
                refine ⟨549591961255403144588875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2931157126695483437807333 549591961255403144588875)
                ·
                  refine ⟨824387941883104716883313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549591961255403144588875 824387941883104716883313)
                  ·
                    refine ⟨618290956412328537662485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 824387941883104716883313 618290956412328537662485)
                    ·
                      refine ⟨28982388581827900202929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 618290956412328537662485 28982388581827900202929)
                      ·
                        rfl

theorem cell23_56443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_56443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56443 prefixEnd_56443 := by exact prefixLift 56443
  have htrace : WordTrace (prefixWord ++ tailWord_56443) baseStart_56443 baseEnd_56443 := by
    simpa [prefixWord, tailWord_56443, baseEnd_56443] using wordTrace_append hprefix tailTrace_56443
  have hstable : (prefixWord ++ tailWord_56443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56443).length < 2 ^ (prefixWord ++ tailWord_56443).sum := by decide
  have hdescent : baseEnd_56443 < baseStart_56443 := by decide
  rcases family_descends (prefixWord ++ tailWord_56443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56478 : List Nat := [4, 3, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_56478 : Nat := 118140960795 + 56478 * 2 ^ 59
def prefixEnd_56478 : Nat := 4983230072969 + 3 ^ 40 * 56478 * 2
def baseEnd_56478 : Nat := 9666786801578421088423

theorem tailTrace_56478 : CollatzResearch.WordTrace tailWord_56478 prefixEnd_56478 9666786801578421088423 := by
  unfold tailWord_56478
  simp only [CollatzResearch.WordTrace]
  refine ⟨257490236174665814947261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1373281259598217679718725 257490236174665814947261)
  ·
    refine ⟨96558838565499680605223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257490236174665814947261 96558838565499680605223)
    ·
      refine ⟨144838257848249520907835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96558838565499680605223 144838257848249520907835)
      ·
        refine ⟨217257386772374281361753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144838257848249520907835 217257386772374281361753)
        ·
          refine ⟨162943040079280711021315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217257386772374281361753 162943040079280711021315)
          ·
            refine ⟨244414560118921066531973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162943040079280711021315 244414560118921066531973)
            ·
              refine ⟨45827730022297699974745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244414560118921066531973 45827730022297699974745)
              ·
                refine ⟨34370797516723274981059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45827730022297699974745 34370797516723274981059)
                ·
                  refine ⟨51556196275084912471589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34370797516723274981059 51556196275084912471589)
                  ·
                    refine ⟨9666786801578421088423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51556196275084912471589 9666786801578421088423)
                    ·
                      rfl

theorem cell23_56478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_56478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56478 prefixEnd_56478 := by exact prefixLift 56478
  have htrace : WordTrace (prefixWord ++ tailWord_56478) baseStart_56478 baseEnd_56478 := by
    simpa [prefixWord, tailWord_56478, baseEnd_56478] using wordTrace_append hprefix tailTrace_56478
  have hstable : (prefixWord ++ tailWord_56478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56478).length < 2 ^ (prefixWord ++ tailWord_56478).sum := by decide
  have hdescent : baseEnd_56478 < baseStart_56478 := by decide
  rcases family_descends (prefixWord ++ tailWord_56478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56487 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 3, 5]
def baseStart_56487 : Nat := 118140960795 + 56487 * 2 ^ 59
def prefixEnd_56487 : Nat := 4983230072969 + 3 ^ 40 * 56487 * 2
def baseEnd_56487 : Nat := 9668327243541909350909

theorem tailTrace_56487 : CollatzResearch.WordTrace tailWord_56487 prefixEnd_56487 9668327243541909350909 := by
  unfold tailWord_56487
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060250146364721056655715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1373500097576480704437143 2060250146364721056655715)
  ·
    refine ⟨3090375219547081584983573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060250146364721056655715 3090375219547081584983573)
    ·
      refine ⟨144861338416269449296105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3090375219547081584983573 144861338416269449296105)
      ·
        refine ⟨108646003812202086972079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144861338416269449296105 108646003812202086972079)
        ·
          refine ⟨162969005718303130458119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108646003812202086972079 162969005718303130458119)
          ·
            refine ⟨244453508577454695687179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162969005718303130458119 244453508577454695687179)
            ·
              refine ⟨366680262866182043530769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244453508577454695687179 366680262866182043530769)
              ·
                refine ⟨275010197149636532648077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366680262866182043530769 275010197149636532648077)
                ·
                  refine ⟨103128823931113699743029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275010197149636532648077 103128823931113699743029)
                  ·
                    refine ⟨9668327243541909350909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103128823931113699743029 9668327243541909350909)
                    ·
                      rfl

theorem cell23_56487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_56487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56487 prefixEnd_56487 := by exact prefixLift 56487
  have htrace : WordTrace (prefixWord ++ tailWord_56487) baseStart_56487 baseEnd_56487 := by
    simpa [prefixWord, tailWord_56487, baseEnd_56487] using wordTrace_append hprefix tailTrace_56487
  have hstable : (prefixWord ++ tailWord_56487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56487).length < 2 ^ (prefixWord ++ tailWord_56487).sum := by decide
  have hdescent : baseEnd_56487 < baseStart_56487 := by decide
  rcases family_descends (prefixWord ++ tailWord_56487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56530 : List Nat := [3, 2, 2, 2, 1, 1, 12]
def baseStart_56530 : Nat := 118140960795 + 56530 * 2 ^ 59
def prefixEnd_56530 : Nat := 4983230072969 + 3 ^ 40 * 56530 * 2
def baseEnd_56530 : Nat := 358358782700852590309

theorem tailTrace_56530 : CollatzResearch.WordTrace tailWord_56530 prefixEnd_56530 358358782700852590309 := by
  unfold tailWord_56530
  simp only [CollatzResearch.WordTrace]
  refine ⟨515454621302234850117761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1374545656805959600314029 515454621302234850117761)
  ·
    refine ⟨386590965976676137588321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 515454621302234850117761 386590965976676137588321)
    ·
      refine ⟨289943224482507103191241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386590965976676137588321 289943224482507103191241)
      ·
        refine ⟨217457418361880327393431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289943224482507103191241 217457418361880327393431)
        ·
          refine ⟨326186127542820491090147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217457418361880327393431 326186127542820491090147)
          ·
            refine ⟨489279191314230736635221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326186127542820491090147 489279191314230736635221)
            ·
              refine ⟨358358782700852590309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 489279191314230736635221 358358782700852590309)
              ·
                rfl

theorem cell23_56530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 12].length) (baseStart_56530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56530 prefixEnd_56530 := by exact prefixLift 56530
  have htrace : WordTrace (prefixWord ++ tailWord_56530) baseStart_56530 baseEnd_56530 := by
    simpa [prefixWord, tailWord_56530, baseEnd_56530] using wordTrace_append hprefix tailTrace_56530
  have hstable : (prefixWord ++ tailWord_56530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56530).length < 2 ^ (prefixWord ++ tailWord_56530).sum := by decide
  have hdescent : baseEnd_56530 < baseStart_56530 := by decide
  rcases family_descends (prefixWord ++ tailWord_56530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56551 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 1, 6]
def baseStart_56551 : Nat := 118140960795 + 56551 * 2 ^ 59
def prefixEnd_56551 : Nat := 4983230072969 + 3 ^ 40 * 56551 * 2
def baseEnd_56551 : Nat := 9679281497504492550811

theorem tailTrace_56551 : CollatzResearch.WordTrace tailWord_56551 prefixEnd_56551 9679281497504492550811 := by
  unfold tailWord_56551
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062584418132859986985507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1375056278755239991323671 2062584418132859986985507)
  ·
    refine ⟨3093876627199289980478261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2062584418132859986985507 3093876627199289980478261)
    ·
      refine ⟨290050933799933435669837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3093876627199289980478261 290050933799933435669837)
      ·
        refine ⟨108769100174975038376189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290050933799933435669837 108769100174975038376189)
        ·
          refine ⟨40788412565615639391071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108769100174975038376189 40788412565615639391071)
          ·
            refine ⟨61182618848423459086607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40788412565615639391071 61182618848423459086607)
            ·
              refine ⟨91773928272635188629911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61182618848423459086607 91773928272635188629911)
              ·
                refine ⟨137660892408952782944867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91773928272635188629911 137660892408952782944867)
                ·
                  refine ⟨206491338613429174417301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137660892408952782944867 206491338613429174417301)
                  ·
                    refine ⟨9679281497504492550811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 206491338613429174417301 9679281497504492550811)
                    ·
                      rfl

theorem cell23_56551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_56551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56551 prefixEnd_56551 := by exact prefixLift 56551
  have htrace : WordTrace (prefixWord ++ tailWord_56551) baseStart_56551 baseEnd_56551 := by
    simpa [prefixWord, tailWord_56551, baseEnd_56551] using wordTrace_append hprefix tailTrace_56551
  have hstable : (prefixWord ++ tailWord_56551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56551).length < 2 ^ (prefixWord ++ tailWord_56551).sum := by decide
  have hdescent : baseEnd_56551 < baseStart_56551 := by decide
  rcases family_descends (prefixWord ++ tailWord_56551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56554 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_56554 : Nat := 118140960795 + 56554 * 2 ^ 59
def prefixEnd_56554 : Nat := 4983230072969 + 3 ^ 40 * 56554 * 2
def baseEnd_56554 : Nat := 29039384934476965914919

theorem tailTrace_56554 : CollatzResearch.WordTrace tailWord_56554 prefixEnd_56554 29039384934476965914919 := by
  unfold tailWord_56554
  simp only [CollatzResearch.WordTrace]
  refine ⟨515673459280497874836179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1375129224747994332896477 515673459280497874836179)
  ·
    refine ⟨773510188920746812254269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 515673459280497874836179 773510188920746812254269)
    ·
      refine ⟨290066320845280054595351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 773510188920746812254269 290066320845280054595351)
      ·
        refine ⟨435099481267920081893027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290066320845280054595351 435099481267920081893027)
        ·
          refine ⟨652649221901880122839541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435099481267920081893027 652649221901880122839541)
          ·
            refine ⟨61185864553301261516207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 652649221901880122839541 61185864553301261516207)
            ·
              refine ⟨91778796829951892274311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61185864553301261516207 91778796829951892274311)
              ·
                refine ⟨137668195244927838411467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91778796829951892274311 137668195244927838411467)
                ·
                  refine ⟨206502292867391757617201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137668195244927838411467 206502292867391757617201)
                  ·
                    refine ⟨154876719650543818212901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206502292867391757617201 154876719650543818212901)
                    ·
                      refine ⟨29039384934476965914919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 154876719650543818212901 29039384934476965914919)
                      ·
                        rfl

theorem cell23_56554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_56554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56554 prefixEnd_56554 := by exact prefixLift 56554
  have htrace : WordTrace (prefixWord ++ tailWord_56554) baseStart_56554 baseEnd_56554 := by
    simpa [prefixWord, tailWord_56554, baseEnd_56554] using wordTrace_append hprefix tailTrace_56554
  have hstable : (prefixWord ++ tailWord_56554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56554).length < 2 ^ (prefixWord ++ tailWord_56554).sum := by decide
  have hdescent : baseEnd_56554 < baseStart_56554 := by decide
  rcases family_descends (prefixWord ++ tailWord_56554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56570 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_56570 : Nat := 118140960795 + 56570 * 2 ^ 59
def prefixEnd_56570 : Nat := 4983230072969 + 3 ^ 40 * 56570 * 2
def baseEnd_56570 : Nat := 29047600624948903314845

theorem tailTrace_56570 : CollatzResearch.WordTrace tailWord_56570 prefixEnd_56570 29047600624948903314845 := by
  unfold tailWord_56570
  simp only [CollatzResearch.WordTrace]
  refine ⟨515819351266006557981791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1375518270042684154618109 515819351266006557981791)
  ·
    refine ⟨773729026899009836972687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 515819351266006557981791 773729026899009836972687)
    ·
      refine ⟨1160593540348514755459031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773729026899009836972687 1160593540348514755459031)
      ·
        refine ⟨1740890310522772133188547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160593540348514755459031 1740890310522772133188547)
        ·
          refine ⟨2611335465784158199782821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740890310522772133188547 2611335465784158199782821)
          ·
            refine ⟨489625399834529662459279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2611335465784158199782821 489625399834529662459279)
            ·
              refine ⟨734438099751794493688919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489625399834529662459279 734438099751794493688919)
              ·
                refine ⟨1101657149627691740533379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734438099751794493688919 1101657149627691740533379)
                ·
                  refine ⟨1652485724441537610800069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101657149627691740533379 1652485724441537610800069)
                  ·
                    refine ⟨309841073332788302025013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1652485724441537610800069 309841073332788302025013)
                    ·
                      refine ⟨29047600624948903314845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 309841073332788302025013 29047600624948903314845)
                      ·
                        rfl

theorem cell23_56570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_56570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56570 prefixEnd_56570 := by exact prefixLift 56570
  have htrace : WordTrace (prefixWord ++ tailWord_56570) baseStart_56570 baseEnd_56570 := by
    simpa [prefixWord, tailWord_56570, baseEnd_56570] using wordTrace_append hprefix tailTrace_56570
  have hstable : (prefixWord ++ tailWord_56570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56570).length < 2 ^ (prefixWord ++ tailWord_56570).sum := by decide
  have hdescent : baseEnd_56570 < baseStart_56570 := by decide
  rcases family_descends (prefixWord ++ tailWord_56570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56618 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_56618 : Nat := 118140960795 + 56618 * 2 ^ 59
def prefixEnd_56618 : Nat := 4983230072969 + 3 ^ 40 * 56618 * 2
def baseEnd_56618 : Nat := 29072247696364715514625

theorem tailTrace_56618 : CollatzResearch.WordTrace tailWord_56618 prefixEnd_56618 29072247696364715514625 := by
  unfold tailWord_56618
  simp only [CollatzResearch.WordTrace]
  refine ⟨516257027222532607418627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1376685405926753619783005 516257027222532607418627)
  ·
    refine ⟨774385540833798911127941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516257027222532607418627 774385540833798911127941)
    ·
      refine ⟨145197288906337295836489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 774385540833798911127941 145197288906337295836489)
      ·
        refine ⟨108897966679752971877367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145197288906337295836489 108897966679752971877367)
        ·
          refine ⟨163346950019629457816051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108897966679752971877367 163346950019629457816051)
          ·
            refine ⟨245020425029444186724077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163346950019629457816051 245020425029444186724077)
            ·
              refine ⟨91882659386041570021529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245020425029444186724077 91882659386041570021529)
              ·
                refine ⟨68911994539531177516147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91882659386041570021529 68911994539531177516147)
                ·
                  refine ⟨103367991809296766274221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68911994539531177516147 103367991809296766274221)
                  ·
                    refine ⟨38762996928486287352833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103367991809296766274221 38762996928486287352833)
                    ·
                      refine ⟨29072247696364715514625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38762996928486287352833 29072247696364715514625)
                      ·
                        rfl

theorem cell23_56618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_56618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56618 prefixEnd_56618 := by exact prefixLift 56618
  have htrace : WordTrace (prefixWord ++ tailWord_56618) baseStart_56618 baseEnd_56618 := by
    simpa [prefixWord, tailWord_56618, baseEnd_56618] using wordTrace_append hprefix tailTrace_56618
  have hstable : (prefixWord ++ tailWord_56618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56618).length < 2 ^ (prefixWord ++ tailWord_56618).sum := by decide
  have hdescent : baseEnd_56618 < baseStart_56618 := by decide
  rcases family_descends (prefixWord ++ tailWord_56618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56620 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 9]
def baseStart_56620 : Nat := 118140960795 + 56620 * 2 ^ 59
def prefixEnd_56620 : Nat := 4983230072969 + 3 ^ 40 * 56620 * 2
def baseEnd_56620 : Nat := 3230363850852634187735

theorem tailTrace_56620 : CollatzResearch.WordTrace tailWord_56620 prefixEnd_56620 3230363850852634187735 := by
  unfold tailWord_56620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032550527441442385623657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1376734036588589847498209 1032550527441442385623657)
  ·
    refine ⟨774412895581081789217743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1032550527441442385623657 774412895581081789217743)
    ·
      refine ⟨1161619343371622683826615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774412895581081789217743 1161619343371622683826615)
      ·
        refine ⟨1742429015057434025739923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161619343371622683826615 1742429015057434025739923)
        ·
          refine ⟨2613643522586151038609885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742429015057434025739923 2613643522586151038609885)
          ·
            refine ⟨980116320969806639478707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2613643522586151038609885 980116320969806639478707)
            ·
              refine ⟨1470174481454709959218061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980116320969806639478707 1470174481454709959218061)
              ·
                refine ⟨551315430545516234706773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470174481454709959218061 551315430545516234706773)
                ·
                  refine ⟨3230363850852634187735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 551315430545516234706773 3230363850852634187735)
                  ·
                    rfl

theorem cell23_56620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_56620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56620 prefixEnd_56620 := by exact prefixLift 56620
  have htrace : WordTrace (prefixWord ++ tailWord_56620) baseStart_56620 baseEnd_56620 := by
    simpa [prefixWord, tailWord_56620, baseEnd_56620] using wordTrace_append hprefix tailTrace_56620
  have hstable : (prefixWord ++ tailWord_56620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56620).length < 2 ^ (prefixWord ++ tailWord_56620).sum := by decide
  have hdescent : baseEnd_56620 < baseStart_56620 := by decide
  rcases family_descends (prefixWord ++ tailWord_56620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56654 : List Nat := [4, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_56654 : Nat := 118140960795 + 56654 * 2 ^ 59
def prefixEnd_56654 : Nat := 4983230072969 + 3 ^ 40 * 56654 * 2
def baseEnd_56654 : Nat := 3232303666658508296051

theorem tailTrace_56654 : CollatzResearch.WordTrace tailWord_56654 prefixEnd_56654 3232303666658508296051 := by
  unfold tailWord_56654
  simp only [CollatzResearch.WordTrace]
  refine ⟨258292642094963572248127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1377560757839805718656677 258292642094963572248127)
  ·
    refine ⟨387438963142445358372191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258292642094963572248127 387438963142445358372191)
    ·
      refine ⟨581158444713668037558287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387438963142445358372191 581158444713668037558287)
      ·
        refine ⟨871737667070502056337431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581158444713668037558287 871737667070502056337431)
        ·
          refine ⟨1307606500605753084506147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871737667070502056337431 1307606500605753084506147)
          ·
            refine ⟨1961409750908629626759221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307606500605753084506147 1961409750908629626759221)
            ·
              refine ⟨183882164147684027508677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1961409750908629626759221 183882164147684027508677)
              ·
                refine ⟨34477905777690755157877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183882164147684027508677 34477905777690755157877)
                ·
                  refine ⟨3232303666658508296051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34477905777690755157877 3232303666658508296051)
                  ·
                    rfl

theorem cell23_56654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_56654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56654 prefixEnd_56654 := by exact prefixLift 56654
  have htrace : WordTrace (prefixWord ++ tailWord_56654) baseStart_56654 baseEnd_56654 := by
    simpa [prefixWord, tailWord_56654, baseEnd_56654] using wordTrace_append hprefix tailTrace_56654
  have hstable : (prefixWord ++ tailWord_56654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56654).length < 2 ^ (prefixWord ++ tailWord_56654).sum := by decide
  have hdescent : baseEnd_56654 < baseStart_56654 := by decide
  rcases family_descends (prefixWord ++ tailWord_56654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56684 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_56684 : Nat := 118140960795 + 56684 * 2 ^ 59
def prefixEnd_56684 : Nat := 4983230072969 + 3 ^ 40 * 56684 * 2
def baseEnd_56684 : Nat := 9702045806520485763107

theorem tailTrace_56684 : CollatzResearch.WordTrace tailWord_56684 prefixEnd_56684 9702045806520485763107 := by
  unfold tailWord_56684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033717663325511850788553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1378290217767349134384737 1033717663325511850788553)
  ·
    refine ⟨775288247494133888091415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1033717663325511850788553 775288247494133888091415)
    ·
      refine ⟨1162932371241200832137123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775288247494133888091415 1162932371241200832137123)
      ·
        refine ⟨1744398556861801248205685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162932371241200832137123 1744398556861801248205685)
        ·
          refine ⟨163537364705793867019283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1744398556861801248205685 163537364705793867019283)
          ·
            refine ⟨245306047058690800528925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163537364705793867019283 245306047058690800528925)
            ·
              refine ⟨91989767647009050198347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245306047058690800528925 91989767647009050198347)
              ·
                refine ⟨137984651470513575297521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91989767647009050198347 137984651470513575297521)
                ·
                  refine ⟨103488488602885181473141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137984651470513575297521 103488488602885181473141)
                  ·
                    refine ⟨9702045806520485763107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103488488602885181473141 9702045806520485763107)
                    ·
                      rfl

theorem cell23_56684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_56684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56684 prefixEnd_56684 := by exact prefixLift 56684
  have htrace : WordTrace (prefixWord ++ tailWord_56684) baseStart_56684 baseEnd_56684 := by
    simpa [prefixWord, tailWord_56684, baseEnd_56684] using wordTrace_append hprefix tailTrace_56684
  have hstable : (prefixWord ++ tailWord_56684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56684).length < 2 ^ (prefixWord ++ tailWord_56684).sum := by decide
  have hdescent : baseEnd_56684 < baseStart_56684 := by decide
  rcases family_descends (prefixWord ++ tailWord_56684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56687 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_56687 : Nat := 118140960795 + 56687 * 2 ^ 59
def prefixEnd_56687 : Nat := 4983230072969 + 3 ^ 40 * 56687 * 2
def baseEnd_56687 : Nat := 29107677861524945551807

theorem tailTrace_56687 : CollatzResearch.WordTrace tailWord_56687 prefixEnd_56687 29107677861524945551807 := by
  unfold tailWord_56687
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067544745640155213936315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1378363163760103475957543 2067544745640155213936315)
  ·
    refine ⟨3101317118460232820904473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2067544745640155213936315 3101317118460232820904473)
    ·
      refine ⟨2325987838845174615678355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3101317118460232820904473 2325987838845174615678355)
      ·
        refine ⟨3488981758267761923517533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325987838845174615678355 3488981758267761923517533)
        ·
          refine ⟨1308368159350410721319075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3488981758267761923517533 1308368159350410721319075)
          ·
            refine ⟨1962552239025616081978613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308368159350410721319075 1962552239025616081978613)
            ·
              refine ⟨183989272408651507685495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1962552239025616081978613 183989272408651507685495)
              ·
                refine ⟨275983908612977261528243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183989272408651507685495 275983908612977261528243)
                ·
                  refine ⟨413975862919465892292365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275983908612977261528243 413975862919465892292365)
                  ·
                    refine ⟨155240948594799709609637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413975862919465892292365 155240948594799709609637)
                    ·
                      refine ⟨29107677861524945551807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 155240948594799709609637 29107677861524945551807)
                      ·
                        rfl

theorem cell23_56687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_56687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56687 prefixEnd_56687 := by exact prefixLift 56687
  have htrace : WordTrace (prefixWord ++ tailWord_56687) baseStart_56687 baseEnd_56687 := by
    simpa [prefixWord, tailWord_56687, baseEnd_56687] using wordTrace_append hprefix tailTrace_56687
  have hstable : (prefixWord ++ tailWord_56687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56687).length < 2 ^ (prefixWord ++ tailWord_56687).sum := by decide
  have hdescent : baseEnd_56687 < baseStart_56687 := by decide
  rcases family_descends (prefixWord ++ tailWord_56687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56771 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 3]
def baseStart_56771 : Nat := 118140960795 + 56771 * 2 ^ 59
def prefixEnd_56771 : Nat := 4983230072969 + 3 ^ 40 * 56771 * 2
def baseEnd_56771 : Nat := 29150810236502616901421

theorem tailTrace_56771 : CollatzResearch.WordTrace tailWord_56771 prefixEnd_56771 29150810236502616901421 := by
  unfold tailWord_56771
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070608477335837559994167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1380405651557225039996111 2070608477335837559994167)
  ·
    refine ⟨3105912716003756339991251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2070608477335837559994167 3105912716003756339991251)
    ·
      refine ⟨4658869074005634509986877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105912716003756339991251 4658869074005634509986877)
      ·
        refine ⟨1747075902752112941245079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4658869074005634509986877 1747075902752112941245079)
        ·
          refine ⟨2620613854128169411867619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747075902752112941245079 2620613854128169411867619)
          ·
            refine ⟨3930920781192254117801429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620613854128169411867619 3930920781192254117801429)
            ·
              refine ⟨92130955809193455885971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3930920781192254117801429 92130955809193455885971)
              ·
                refine ⟨138196433713790183828957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92130955809193455885971 138196433713790183828957)
                ·
                  refine ⟨51823662642671318935859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138196433713790183828957 51823662642671318935859)
                  ·
                    refine ⟨77735493964006978403789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51823662642671318935859 77735493964006978403789)
                    ·
                      refine ⟨29150810236502616901421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 77735493964006978403789 29150810236502616901421)
                      ·
                        rfl

theorem cell23_56771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_56771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56771 prefixEnd_56771 := by exact prefixLift 56771
  have htrace : WordTrace (prefixWord ++ tailWord_56771) baseStart_56771 baseEnd_56771 := by
    simpa [prefixWord, tailWord_56771, baseEnd_56771] using wordTrace_append hprefix tailTrace_56771
  have hstable : (prefixWord ++ tailWord_56771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56771).length < 2 ^ (prefixWord ++ tailWord_56771).sum := by decide
  have hdescent : baseEnd_56771 < baseStart_56771 := by decide
  rcases family_descends (prefixWord ++ tailWord_56771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56777 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_56777 : Nat := 118140960795 + 56777 * 2 ^ 59
def prefixEnd_56777 : Nat := 4983230072969 + 3 ^ 40 * 56777 * 2
def baseEnd_56777 : Nat := 29153891120429593426393

theorem tailTrace_56777 : CollatzResearch.WordTrace tailWord_56777 prefixEnd_56777 29153891120429593426393 := by
  unfold tailWord_56777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070827315314100584712585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1380551543542733723141723 2070827315314100584712585)
  ·
    refine ⟨1553120486485575438534439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2070827315314100584712585 1553120486485575438534439)
    ·
      refine ⟨2329680729728363157801659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553120486485575438534439 2329680729728363157801659)
      ·
        refine ⟨3494521094592544736702489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2329680729728363157801659 3494521094592544736702489)
        ·
          refine ⟨2620890820944408552526867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3494521094592544736702489 2620890820944408552526867)
          ·
            refine ⟨3931336231416612828790301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620890820944408552526867 3931336231416612828790301)
            ·
              refine ⟨1474251086781229810796363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3931336231416612828790301 1474251086781229810796363)
              ·
                refine ⟨2211376630171844716194545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474251086781229810796363 2211376630171844716194545)
                ·
                  refine ⟨1658532472628883537145909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2211376630171844716194545 1658532472628883537145909)
                  ·
                    refine ⟨155487419308957831607429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1658532472628883537145909 155487419308957831607429)
                    ·
                      refine ⟨29153891120429593426393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 155487419308957831607429 29153891120429593426393)
                      ·
                        rfl

theorem cell23_56777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_56777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56777 prefixEnd_56777 := by exact prefixLift 56777
  have htrace : WordTrace (prefixWord ++ tailWord_56777) baseStart_56777 baseEnd_56777 := by
    simpa [prefixWord, tailWord_56777, baseEnd_56777] using wordTrace_append hprefix tailTrace_56777
  have hstable : (prefixWord ++ tailWord_56777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56777).length < 2 ^ (prefixWord ++ tailWord_56777).sum := by decide
  have hdescent : baseEnd_56777 < baseStart_56777 := by decide
  rcases family_descends (prefixWord ++ tailWord_56777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56804 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_56804 : Nat := 118140960795 + 56804 * 2 ^ 59
def prefixEnd_56804 : Nat := 4983230072969 + 3 ^ 40 * 56804 * 2
def baseEnd_56804 : Nat := 9722585032700329262923

theorem tailTrace_56804 : CollatzResearch.WordTrace tailWord_56804 prefixEnd_56804 9722585032700329262923 := by
  unfold tailWord_56804
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035906043108142097972733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1381208057477522797296977 1035906043108142097972733)
  ·
    refine ⟨388464766165553286739775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1035906043108142097972733 388464766165553286739775)
    ·
      refine ⟨582697149248329930109663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388464766165553286739775 582697149248329930109663)
      ·
        refine ⟨874045723872494895164495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582697149248329930109663 874045723872494895164495)
        ·
          refine ⟨1311068585808742342746743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874045723872494895164495 1311068585808742342746743)
          ·
            refine ⟨1966602878713113514120115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311068585808742342746743 1966602878713113514120115)
            ·
              refine ⟨2949904318069670271180173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966602878713113514120115 2949904318069670271180173)
              ·
                refine ⟨1106214119276126351692565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2949904318069670271180173 1106214119276126351692565)
                ·
                  refine ⟨51853786841068422735589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1106214119276126351692565 51853786841068422735589)
                  ·
                    refine ⟨9722585032700329262923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51853786841068422735589 9722585032700329262923)
                    ·
                      rfl

theorem cell23_56804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_56804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56804 prefixEnd_56804 := by exact prefixLift 56804
  have htrace : WordTrace (prefixWord ++ tailWord_56804) baseStart_56804 baseEnd_56804 := by
    simpa [prefixWord, tailWord_56804, baseEnd_56804] using wordTrace_append hprefix tailTrace_56804
  have hstable : (prefixWord ++ tailWord_56804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56804).length < 2 ^ (prefixWord ++ tailWord_56804).sum := by decide
  have hdescent : baseEnd_56804 < baseStart_56804 := by decide
  rcases family_descends (prefixWord ++ tailWord_56804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56811 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 7, 2, 2]
def baseStart_56811 : Nat := 118140960795 + 56811 * 2 ^ 59
def prefixEnd_56811 : Nat := 4983230072969 + 3 ^ 40 * 56811 * 2
def baseEnd_56811 : Nat := 29171349462682460401237

theorem tailTrace_56811 : CollatzResearch.WordTrace tailWord_56811 prefixEnd_56811 29171349462682460401237 := by
  unfold tailWord_56811
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072067397190924391450287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1381378264793949594300191 2072067397190924391450287)
  ·
    refine ⟨3108101095786386587175431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2072067397190924391450287 3108101095786386587175431)
    ·
      refine ⟨4662151643679579880763147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108101095786386587175431 4662151643679579880763147)
      ·
        refine ⟨6993227465519369821144721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662151643679579880763147 6993227465519369821144721)
        ·
          refine ⟨5244920599139527365858541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6993227465519369821144721 5244920599139527365858541)
          ·
            refine ⟨1966845224677322762196953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5244920599139527365858541 1966845224677322762196953)
            ·
              refine ⟨1475133918507992071647715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966845224677322762196953 1475133918507992071647715)
              ·
                refine ⟨2212700877761988107471573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475133918507992071647715 2212700877761988107471573)
                ·
                  refine ⟨51860176822546596268865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2212700877761988107471573 51860176822546596268865)
                  ·
                    refine ⟨38895132616909947201649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51860176822546596268865 38895132616909947201649)
                    ·
                      refine ⟨29171349462682460401237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 38895132616909947201649 29171349462682460401237)
                      ·
                        rfl

theorem cell23_56811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 2, 2].length) (baseStart_56811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56811 prefixEnd_56811 := by exact prefixLift 56811
  have htrace : WordTrace (prefixWord ++ tailWord_56811) baseStart_56811 baseEnd_56811 := by
    simpa [prefixWord, tailWord_56811, baseEnd_56811] using wordTrace_append hprefix tailTrace_56811
  have hstable : (prefixWord ++ tailWord_56811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56811).length < 2 ^ (prefixWord ++ tailWord_56811).sum := by decide
  have hdescent : baseEnd_56811 < baseStart_56811 := by decide
  rcases family_descends (prefixWord ++ tailWord_56811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56817 : List Nat := [1, 2, 2, 2, 3, 13]
def baseStart_56817 : Nat := 118140960795 + 56817 * 2 ^ 59
def prefixEnd_56817 : Nat := 4983230072969 + 3 ^ 40 * 56817 * 2
def baseEnd_56817 : Nat := 120059384142425666363

theorem tailTrace_56817 : CollatzResearch.WordTrace tailWord_56817 prefixEnd_56817 120059384142425666363 := by
  unfold tailWord_56817
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072286235169187416168705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1381524156779458277445803 2072286235169187416168705)
  ·
    refine ⟨1554214676376890562126529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2072286235169187416168705 1554214676376890562126529)
    ·
      refine ⟨1165661007282667921594897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1554214676376890562126529 1165661007282667921594897)
      ·
        refine ⟨874245755462000941196173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1165661007282667921594897 874245755462000941196173)
        ·
          refine ⟨327842158298250352948565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874245755462000941196173 327842158298250352948565)
          ·
            refine ⟨120059384142425666363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 327842158298250352948565 120059384142425666363)
            ·
              rfl

theorem cell23_56817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 13].length) (baseStart_56817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56817 prefixEnd_56817 := by exact prefixLift 56817
  have htrace : WordTrace (prefixWord ++ tailWord_56817) baseStart_56817 baseEnd_56817 := by
    simpa [prefixWord, tailWord_56817, baseEnd_56817] using wordTrace_append hprefix tailTrace_56817
  have hstable : (prefixWord ++ tailWord_56817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56817).length < 2 ^ (prefixWord ++ tailWord_56817).sum := by decide
  have hdescent : baseEnd_56817 < baseStart_56817 := by decide
  rcases family_descends (prefixWord ++ tailWord_56817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56822 : List Nat := [5, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_56822 : Nat := 118140960795 + 56822 * 2 ^ 59
def prefixEnd_56822 : Nat := 4983230072969 + 3 ^ 40 * 56822 * 2
def baseEnd_56822 : Nat := 29176997749881917363687

theorem tailTrace_56822 : CollatzResearch.WordTrace tailWord_56822 prefixEnd_56822 29176997749881917363687 := by
  unfold tailWord_56822
  simp only [CollatzResearch.WordTrace]
  refine ⟨129529287509442079381295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1381645733434048846733813 129529287509442079381295)
  ·
    refine ⟨194293931264163119071943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129529287509442079381295 194293931264163119071943)
    ·
      refine ⟨291440896896244678607915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194293931264163119071943 291440896896244678607915)
      ·
        refine ⟨437161345344367017911873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291440896896244678607915 437161345344367017911873)
        ·
          refine ⟨327871009008275263433905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437161345344367017911873 327871009008275263433905)
          ·
            refine ⟨245903256756206447575429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327871009008275263433905 245903256756206447575429)
            ·
              refine ⟨46106860641788708920393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245903256756206447575429 46106860641788708920393)
              ·
                refine ⟨34580145481341531690295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46106860641788708920393 34580145481341531690295)
                ·
                  refine ⟨51870218222012297535443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34580145481341531690295 51870218222012297535443)
                  ·
                    refine ⟨77805327333018446303165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51870218222012297535443 77805327333018446303165)
                    ·
                      refine ⟨29176997749881917363687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 77805327333018446303165 29176997749881917363687)
                      ·
                        rfl

theorem cell23_56822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_56822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56822 prefixEnd_56822 := by exact prefixLift 56822
  have htrace : WordTrace (prefixWord ++ tailWord_56822) baseStart_56822 baseEnd_56822 := by
    simpa [prefixWord, tailWord_56822, baseEnd_56822] using wordTrace_append hprefix tailTrace_56822
  have hstable : (prefixWord ++ tailWord_56822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56822).length < 2 ^ (prefixWord ++ tailWord_56822).sum := by decide
  have hdescent : baseEnd_56822 < baseStart_56822 := by decide
  rcases family_descends (prefixWord ++ tailWord_56822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56847 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 9]
def baseStart_56847 : Nat := 118140960795 + 56847 * 2 ^ 59
def prefixEnd_56847 : Nat := 4983230072969 + 3 ^ 40 * 56847 * 2
def baseEnd_56847 : Nat := 9729944922081439850357

theorem tailTrace_56847 : CollatzResearch.WordTrace tailWord_56847 prefixEnd_56847 9729944922081439850357 := by
  unfold tailWord_56847
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073380425060502539760795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1382253616707001693173863 2073380425060502539760795)
  ·
    refine ⟨3110070637590753809641193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2073380425060502539760795 3110070637590753809641193)
    ·
      refine ⟨2332552978193065357230895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3110070637590753809641193 2332552978193065357230895)
      ·
        refine ⟨3498829467289598035846343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332552978193065357230895 3498829467289598035846343)
        ·
          refine ⟨5248244200934397053769515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498829467289598035846343 5248244200934397053769515)
          ·
            refine ⟨7872366301401595580654273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248244200934397053769515 7872366301401595580654273)
            ·
              refine ⟨5904274726051196685490705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7872366301401595580654273 5904274726051196685490705)
              ·
                refine ⟨4428206044538397514118029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904274726051196685490705 4428206044538397514118029)
                ·
                  refine ⟨1660577266701899067794261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4428206044538397514118029 1660577266701899067794261)
                  ·
                    refine ⟨9729944922081439850357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1660577266701899067794261 9729944922081439850357)
                    ·
                      rfl

theorem cell23_56847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_56847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56847 prefixEnd_56847 := by exact prefixLift 56847
  have htrace : WordTrace (prefixWord ++ tailWord_56847) baseStart_56847 baseEnd_56847 := by
    simpa [prefixWord, tailWord_56847, baseEnd_56847] using wordTrace_append hprefix tailTrace_56847
  have hstable : (prefixWord ++ tailWord_56847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56847).length < 2 ^ (prefixWord ++ tailWord_56847).sum := by decide
  have hdescent : baseEnd_56847 < baseStart_56847 := by decide
  rcases family_descends (prefixWord ++ tailWord_56847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56861 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_56861 : Nat := 118140960795 + 56861 * 2 ^ 59
def prefixEnd_56861 : Nat := 4983230072969 + 3 ^ 40 * 56861 * 2
def baseEnd_56861 : Nat := 29197023495407264776007

theorem tailTrace_56861 : CollatzResearch.WordTrace tailWord_56861 prefixEnd_56861 29197023495407264776007 := by
  unfold tailWord_56861
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073891047009782930770437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1382594031339855287180291 2073891047009782930770437)
  ·
    refine ⟨388854571314334299519457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2073891047009782930770437 388854571314334299519457)
    ·
      refine ⟨291640928485750724639593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388854571314334299519457 291640928485750724639593)
      ·
        refine ⟨218730696364313043479695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291640928485750724639593 218730696364313043479695)
        ·
          refine ⟨328096044546469565219543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218730696364313043479695 328096044546469565219543)
          ·
            refine ⟨492144066819704347829315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328096044546469565219543 492144066819704347829315)
            ·
              refine ⟨738216100229556521743973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492144066819704347829315 738216100229556521743973)
              ·
                refine ⟨138415518793041847826995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738216100229556521743973 138415518793041847826995)
                ·
                  refine ⟨207623278189562771740493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138415518793041847826995 207623278189562771740493)
                  ·
                    refine ⟨77858729321086039402685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207623278189562771740493 77858729321086039402685)
                    ·
                      refine ⟨29197023495407264776007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 77858729321086039402685 29197023495407264776007)
                      ·
                        rfl

theorem cell23_56861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_56861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56861 prefixEnd_56861 := by exact prefixLift 56861
  have htrace : WordTrace (prefixWord ++ tailWord_56861) baseStart_56861 baseEnd_56861 := by
    simpa [prefixWord, tailWord_56861, baseEnd_56861] using wordTrace_append hprefix tailTrace_56861
  have hstable : (prefixWord ++ tailWord_56861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56861).length < 2 ^ (prefixWord ++ tailWord_56861).sum := by decide
  have hdescent : baseEnd_56861 < baseStart_56861 := by decide
  rcases family_descends (prefixWord ++ tailWord_56861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56865 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_56865 : Nat := 118140960795 + 56865 * 2 ^ 59
def prefixEnd_56865 : Nat := 4983230072969 + 3 ^ 40 * 56865 * 2
def baseEnd_56865 : Nat := 29199077418025249125989

theorem tailTrace_56865 : CollatzResearch.WordTrace tailWord_56865 prefixEnd_56865 29199077418025249125989 := by
  unfold tailWord_56865
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074036938995291613916049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1382691292663527742610699 2074036938995291613916049)
  ·
    refine ⟨1555527704246468710437037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2074036938995291613916049 1555527704246468710437037)
    ·
      refine ⟨583322889092425766413889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1555527704246468710437037 583322889092425766413889)
      ·
        refine ⟨437492166819319324810417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583322889092425766413889 437492166819319324810417)
        ·
          refine ⟨328119125114489493607813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437492166819319324810417 328119125114489493607813)
          ·
            refine ⟨61522335958966780051465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328119125114489493607813 61522335958966780051465)
            ·
              refine ⟨46141751969225085038599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61522335958966780051465 46141751969225085038599)
              ·
                refine ⟨69212627953837627557899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46141751969225085038599 69212627953837627557899)
                ·
                  refine ⟨103818941930756441336849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69212627953837627557899 103818941930756441336849)
                  ·
                    refine ⟨77864206448067331002637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103818941930756441336849 77864206448067331002637)
                    ·
                      refine ⟨29199077418025249125989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 77864206448067331002637 29199077418025249125989)
                      ·
                        rfl

theorem cell23_56865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_56865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56865 prefixEnd_56865 := by exact prefixLift 56865
  have htrace : WordTrace (prefixWord ++ tailWord_56865) baseStart_56865 baseEnd_56865 := by
    simpa [prefixWord, tailWord_56865, baseEnd_56865] using wordTrace_append hprefix tailTrace_56865
  have hstable : (prefixWord ++ tailWord_56865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56865).length < 2 ^ (prefixWord ++ tailWord_56865).sum := by decide
  have hdescent : baseEnd_56865 < baseStart_56865 := by decide
  rcases family_descends (prefixWord ++ tailWord_56865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56872 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 2, 4]
def baseStart_56872 : Nat := 118140960795 + 56872 * 2 ^ 59
def prefixEnd_56872 : Nat := 4983230072969 + 3 ^ 40 * 56872 * 2
def baseEnd_56872 : Nat := 9734223927535573912819

theorem tailTrace_56872 : CollatzResearch.WordTrace tailWord_56872 prefixEnd_56872 9734223927535573912819 := by
  unfold tailWord_56872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037146124984965904710435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1382861499979954539613913 1037146124984965904710435)
  ·
    refine ⟨1555719187477448857065653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1037146124984965904710435 1555719187477448857065653)
    ·
      refine ⟨145848673826010830349905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1555719187477448857065653 145848673826010830349905)
      ·
        refine ⟨109386505369508122762429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145848673826010830349905 109386505369508122762429)
        ·
          refine ⟨41019939513565546035911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109386505369508122762429 41019939513565546035911)
          ·
            refine ⟨61529909270348319053867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41019939513565546035911 61529909270348319053867)
            ·
              refine ⟨92294863905522478580801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61529909270348319053867 92294863905522478580801)
              ·
                refine ⟨69221147929141858935601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92294863905522478580801 69221147929141858935601)
                ·
                  refine ⟨51915860946856394201701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69221147929141858935601 51915860946856394201701)
                  ·
                    refine ⟨9734223927535573912819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51915860946856394201701 9734223927535573912819)
                    ·
                      rfl

theorem cell23_56872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_56872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56872 prefixEnd_56872 := by exact prefixLift 56872
  have htrace : WordTrace (prefixWord ++ tailWord_56872) baseStart_56872 baseEnd_56872 := by
    simpa [prefixWord, tailWord_56872, baseEnd_56872] using wordTrace_append hprefix tailTrace_56872
  have hstable : (prefixWord ++ tailWord_56872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56872).length < 2 ^ (prefixWord ++ tailWord_56872).sum := by decide
  have hdescent : baseEnd_56872 < baseStart_56872 := by decide
  rcases family_descends (prefixWord ++ tailWord_56872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56895 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 2, 1, 3]
def baseStart_56895 : Nat := 118140960795 + 56895 * 2 ^ 59
def prefixEnd_56895 : Nat := 4983230072969 + 3 ^ 40 * 56895 * 2
def baseEnd_56895 : Nat := 29214481837660131750851

theorem tailTrace_56895 : CollatzResearch.WordTrace tailWord_56895 prefixEnd_56895 29214481837660131750851 := by
  unfold tailWord_56895
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075131128886606737508139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1383420752591071158338759 2075131128886606737508139)
  ·
    refine ⟨3112696693329910106262209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2075131128886606737508139 3112696693329910106262209)
    ·
      refine ⟨2334522519997432579696657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3112696693329910106262209 2334522519997432579696657)
      ·
        refine ⟨1750891889998074434772493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2334522519997432579696657 1750891889998074434772493)
        ·
          refine ⟨656584458749277913039685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1750891889998074434772493 656584458749277913039685)
          ·
            refine ⟨123109586015489608694941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656584458749277913039685 123109586015489608694941)
            ·
              refine ⟨46166094755808603260603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123109586015489608694941 46166094755808603260603)
              ·
                refine ⟨69249142133712904890905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46166094755808603260603 69249142133712904890905)
                ·
                  refine ⟨51936856600284678668179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69249142133712904890905 51936856600284678668179)
                  ·
                    refine ⟨77905284900427018002269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51936856600284678668179 77905284900427018002269)
                    ·
                      refine ⟨29214481837660131750851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 77905284900427018002269 29214481837660131750851)
                      ·
                        rfl

theorem cell23_56895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_56895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56895 prefixEnd_56895 := by exact prefixLift 56895
  have htrace : WordTrace (prefixWord ++ tailWord_56895) baseStart_56895 baseEnd_56895 := by
    simpa [prefixWord, tailWord_56895, baseEnd_56895] using wordTrace_append hprefix tailTrace_56895
  have hstable : (prefixWord ++ tailWord_56895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56895).length < 2 ^ (prefixWord ++ tailWord_56895).sum := by decide
  have hdescent : baseEnd_56895 < baseStart_56895 := by decide
  rcases family_descends (prefixWord ++ tailWord_56895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56902 : List Nat := [6, 1, 1, 1, 4, 1, 2, 7]
def baseStart_56902 : Nat := 118140960795 + 56902 * 2 ^ 59
def prefixEnd_56902 : Nat := 4983230072969 + 3 ^ 40 * 56902 * 2
def baseEnd_56902 : Nat := 1082150970453392754197

theorem tailTrace_56902 : CollatzResearch.WordTrace tailWord_56902 prefixEnd_56902 1082150970453392754197 := by
  unfold tailWord_56902
  simp only [CollatzResearch.WordTrace]
  refine ⟨64855826245663966656655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1383590959907497955341973 64855826245663966656655)
  ·
    refine ⟨97283739368495949984983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64855826245663966656655 97283739368495949984983)
    ·
      refine ⟨145925609052743924977475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97283739368495949984983 145925609052743924977475)
      ·
        refine ⟨218888413579115887466213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145925609052743924977475 218888413579115887466213)
        ·
          refine ⟨41041577546084228899915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218888413579115887466213 41041577546084228899915)
          ·
            refine ⟨61562366319126343349873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41041577546084228899915 61562366319126343349873)
            ·
              refine ⟨46171774739344757512405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61562366319126343349873 46171774739344757512405)
              ·
                refine ⟨1082150970453392754197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46171774739344757512405 1082150970453392754197)
                ·
                  rfl

theorem cell23_56902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_56902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56902 prefixEnd_56902 := by exact prefixLift 56902
  have htrace : WordTrace (prefixWord ++ tailWord_56902) baseStart_56902 baseEnd_56902 := by
    simpa [prefixWord, tailWord_56902, baseEnd_56902] using wordTrace_append hprefix tailTrace_56902
  have hstable : (prefixWord ++ tailWord_56902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56902).length < 2 ^ (prefixWord ++ tailWord_56902).sum := by decide
  have hdescent : baseEnd_56902 < baseStart_56902 := by decide
  rcases family_descends (prefixWord ++ tailWord_56902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56954 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_56954 : Nat := 118140960795 + 56954 * 2 ^ 59
def prefixEnd_56954 : Nat := 4983230072969 + 3 ^ 40 * 56954 * 2
def baseEnd_56954 : Nat := 9748259065425133637693

theorem tailTrace_56954 : CollatzResearch.WordTrace tailWord_56954 prefixEnd_56954 9748259065425133637693 := by
  unfold tailWord_56954
  simp only [CollatzResearch.WordTrace]
  refine ⟨519320758918214953476479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1384855357115239875937277 519320758918214953476479)
  ·
    refine ⟨778981138377322430214719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 519320758918214953476479 778981138377322430214719)
    ·
      refine ⟨1168471707565983645322079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778981138377322430214719 1168471707565983645322079)
      ·
        refine ⟨1752707561348975467983119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168471707565983645322079 1752707561348975467983119)
        ·
          refine ⟨2629061342023463201974679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752707561348975467983119 2629061342023463201974679)
          ·
            refine ⟨3943592013035194802962019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629061342023463201974679 3943592013035194802962019)
            ·
              refine ⟨5915388019552792204443029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943592013035194802962019 5915388019552792204443029)
              ·
                refine ⟨277283813416537134583267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5915388019552792204443029 277283813416537134583267)
                ·
                  refine ⟨415925720124805701874901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277283813416537134583267 415925720124805701874901)
                  ·
                    refine ⟨9748259065425133637693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 415925720124805701874901 9748259065425133637693)
                    ·
                      rfl

theorem cell23_56954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_56954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56954 prefixEnd_56954 := by exact prefixLift 56954
  have htrace : WordTrace (prefixWord ++ tailWord_56954) baseStart_56954 baseEnd_56954 := by
    simpa [prefixWord, tailWord_56954, baseEnd_56954] using wordTrace_append hprefix tailTrace_56954
  have hstable : (prefixWord ++ tailWord_56954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56954).length < 2 ^ (prefixWord ++ tailWord_56954).sum := by decide
  have hdescent : baseEnd_56954 < baseStart_56954 := by decide
  rcases family_descends (prefixWord ++ tailWord_56954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56971 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 2, 5]
def baseStart_56971 : Nat := 118140960795 + 56971 * 2 ^ 59
def prefixEnd_56971 : Nat := 4983230072969 + 3 ^ 40 * 56971 * 2
def baseEnd_56971 : Nat := 9751168789133944800167

theorem tailTrace_56971 : CollatzResearch.WordTrace tailWord_56971 prefixEnd_56971 9751168789133944800167 := by
  unfold tailWord_56971
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077903076611271717274767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1385268717740847811516511 2077903076611271717274767)
  ·
    refine ⟨3116854614916907575912151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2077903076611271717274767 3116854614916907575912151)
    ·
      refine ⟨4675281922375361363868227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116854614916907575912151 4675281922375361363868227)
      ·
        refine ⟨7012922883563042045802341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4675281922375361363868227 7012922883563042045802341)
        ·
          refine ⟨1314923040668070383587939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7012922883563042045802341 1314923040668070383587939)
          ·
            refine ⟨1972384561002105575381909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314923040668070383587939 1972384561002105575381909)
            ·
              refine ⟨92455526296973698846027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1972384561002105575381909 92455526296973698846027)
              ·
                refine ⟨138683289445460548269041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92455526296973698846027 138683289445460548269041)
                ·
                  refine ⟨104012467084095411201781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138683289445460548269041 104012467084095411201781)
                  ·
                    refine ⟨9751168789133944800167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104012467084095411201781 9751168789133944800167)
                    ·
                      rfl

theorem cell23_56971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 5].length) (baseStart_56971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_56971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_56971 prefixEnd_56971 := by exact prefixLift 56971
  have htrace : WordTrace (prefixWord ++ tailWord_56971) baseStart_56971 baseEnd_56971 := by
    simpa [prefixWord, tailWord_56971, baseEnd_56971] using wordTrace_append hprefix tailTrace_56971
  have hstable : (prefixWord ++ tailWord_56971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56971).length < 2 ^ (prefixWord ++ tailWord_56971).sum := by decide
  have hdescent : baseEnd_56971 < baseStart_56971 := by decide
  rcases family_descends (prefixWord ++ tailWord_56971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57011 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 3]
def baseStart_57011 : Nat := 118140960795 + 57011 * 2 ^ 59
def prefixEnd_57011 : Nat := 4983230072969 + 3 ^ 40 * 57011 * 2
def baseEnd_57011 : Nat := 29274045593581677900317

theorem tailTrace_57011 : CollatzResearch.WordTrace tailWord_57011 prefixEnd_57011 29274045593581677900317 := by
  unfold tailWord_57011
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079361996466358548730887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1386241330977572365820591 2079361996466358548730887)
  ·
    refine ⟨3119042994699537823096331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2079361996466358548730887 3119042994699537823096331)
    ·
      refine ⟨4678564492049306734644497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119042994699537823096331 4678564492049306734644497)
      ·
        refine ⟨3508923369036980050983373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4678564492049306734644497 3508923369036980050983373)
        ·
          refine ⟨1315846263388867519118765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3508923369036980050983373 1315846263388867519118765)
          ·
            refine ⟨493442348770825319669537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1315846263388867519118765 493442348770825319669537)
            ·
              refine ⟨370081761578118989752153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493442348770825319669537 370081761578118989752153)
              ·
                refine ⟨277561321183589242314115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370081761578118989752153 277561321183589242314115)
                ·
                  refine ⟨416341981775383863471173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277561321183589242314115 416341981775383863471173)
                  ·
                    refine ⟨78064121582884474400845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416341981775383863471173 78064121582884474400845)
                    ·
                      refine ⟨29274045593581677900317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 78064121582884474400845 29274045593581677900317)
                      ·
                        rfl

theorem cell23_57011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_57011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57011 prefixEnd_57011 := by exact prefixLift 57011
  have htrace : WordTrace (prefixWord ++ tailWord_57011) baseStart_57011 baseEnd_57011 := by
    simpa [prefixWord, tailWord_57011, baseEnd_57011] using wordTrace_append hprefix tailTrace_57011
  have hstable : (prefixWord ++ tailWord_57011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57011).length < 2 ^ (prefixWord ++ tailWord_57011).sum := by decide
  have hdescent : baseEnd_57011 < baseStart_57011 := by decide
  rcases family_descends (prefixWord ++ tailWord_57011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57018 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_57018 : Nat := 118140960795 + 57018 * 2 ^ 59
def prefixEnd_57018 : Nat := 4983230072969 + 3 ^ 40 * 57018 * 2
def baseEnd_57018 : Nat := 9759213319387716837595

theorem tailTrace_57018 : CollatzResearch.WordTrace tailWord_57018 prefixEnd_57018 9759213319387716837595 := by
  unfold tailWord_57018
  simp only [CollatzResearch.WordTrace]
  refine ⟨519904326860249686058927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1386411538293999162823805 519904326860249686058927)
  ·
    refine ⟨779856490290374529088391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 519904326860249686058927 779856490290374529088391)
    ·
      refine ⟨1169784735435561793632587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779856490290374529088391 1169784735435561793632587)
      ·
        refine ⟨1754677103153342690448881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169784735435561793632587 1754677103153342690448881)
        ·
          refine ⟨1316007827365007017836661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1754677103153342690448881 1316007827365007017836661)
          ·
            refine ⟨123375733815469407922187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1316007827365007017836661 123375733815469407922187)
            ·
              refine ⟨185063600723204111883281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123375733815469407922187 185063600723204111883281)
              ·
                refine ⟨138797700542403083912461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185063600723204111883281 138797700542403083912461)
                ·
                  refine ⟨52049137703401156467173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138797700542403083912461 52049137703401156467173)
                  ·
                    refine ⟨9759213319387716837595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52049137703401156467173 9759213319387716837595)
                    ·
                      rfl

theorem cell23_57018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_57018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57018 prefixEnd_57018 := by exact prefixLift 57018
  have htrace : WordTrace (prefixWord ++ tailWord_57018) baseStart_57018 baseEnd_57018 := by
    simpa [prefixWord, tailWord_57018, baseEnd_57018] using wordTrace_append hprefix tailTrace_57018
  have hstable : (prefixWord ++ tailWord_57018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57018).length < 2 ^ (prefixWord ++ tailWord_57018).sum := by decide
  have hdescent : baseEnd_57018 < baseStart_57018 := by decide
  rcases family_descends (prefixWord ++ tailWord_57018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57028 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_57028 : Nat := 118140960795 + 57028 * 2 ^ 59
def prefixEnd_57028 : Nat := 4983230072969 + 3 ^ 40 * 57028 * 2
def baseEnd_57028 : Nat := 29282774764708111387739

theorem tailTrace_57028 : CollatzResearch.WordTrace tailWord_57028 prefixEnd_57028 29282774764708111387739 := by
  unfold tailWord_57028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039991018702385226049869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1386654691603180301399825 1039991018702385226049869)
  ·
    refine ⟨389996632013394459768701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1039991018702385226049869 389996632013394459768701)
    ·
      refine ⟨146248737005022922413263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389996632013394459768701 146248737005022922413263)
      ·
        refine ⟨219373105507534383619895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146248737005022922413263 219373105507534383619895)
        ·
          refine ⟨329059658261301575429843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219373105507534383619895 329059658261301575429843)
          ·
            refine ⟨493589487391952363144765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329059658261301575429843 493589487391952363144765)
            ·
              refine ⟨185096057771982136179287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493589487391952363144765 185096057771982136179287)
              ·
                refine ⟨277644086657973204268931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185096057771982136179287 277644086657973204268931)
                ·
                  refine ⟨416466129986959806403397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277644086657973204268931 416466129986959806403397)
                  ·
                    refine ⟨78087399372554963700637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416466129986959806403397 78087399372554963700637)
                    ·
                      refine ⟨29282774764708111387739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 78087399372554963700637 29282774764708111387739)
                      ·
                        rfl

theorem cell23_57028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_57028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57028 prefixEnd_57028 := by exact prefixLift 57028
  have htrace : WordTrace (prefixWord ++ tailWord_57028) baseStart_57028 baseEnd_57028 := by
    simpa [prefixWord, tailWord_57028, baseEnd_57028] using wordTrace_append hprefix tailTrace_57028
  have hstable : (prefixWord ++ tailWord_57028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57028).length < 2 ^ (prefixWord ++ tailWord_57028).sum := by decide
  have hdescent : baseEnd_57028 < baseStart_57028 := by decide
  rcases family_descends (prefixWord ++ tailWord_57028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57052 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_57052 : Nat := 118140960795 + 57052 * 2 ^ 59
def prefixEnd_57052 : Nat := 4983230072969 + 3 ^ 40 * 57052 * 2
def baseEnd_57052 : Nat := 9765032766805339162543

theorem tailTrace_57052 : CollatzResearch.WordTrace tailWord_57052 prefixEnd_57052 9765032766805339162543 := by
  unfold tailWord_57052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040428694658911275486705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1387238259545215033982273 1040428694658911275486705)
  ·
    refine ⟨780321520994183456615029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1040428694658911275486705 780321520994183456615029)
    ·
      refine ⟨73155142593204699057659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 780321520994183456615029 73155142593204699057659)
      ·
        refine ⟨109732713889807048586489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73155142593204699057659 109732713889807048586489)
        ·
          refine ⟨82299535417355286439867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109732713889807048586489 82299535417355286439867)
          ·
            refine ⟨123449303126032929659801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82299535417355286439867 123449303126032929659801)
            ·
              refine ⟨92586977344524697244851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123449303126032929659801 92586977344524697244851)
              ·
                refine ⟨138880466016787045867277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92586977344524697244851 138880466016787045867277)
                ·
                  refine ⟨52080174756295142200229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138880466016787045867277 52080174756295142200229)
                  ·
                    refine ⟨9765032766805339162543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52080174756295142200229 9765032766805339162543)
                    ·
                      rfl

theorem cell23_57052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_57052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57052 prefixEnd_57052 := by exact prefixLift 57052
  have htrace : WordTrace (prefixWord ++ tailWord_57052) baseStart_57052 baseEnd_57052 := by
    simpa [prefixWord, tailWord_57052, baseEnd_57052] using wordTrace_append hprefix tailTrace_57052
  have hstable : (prefixWord ++ tailWord_57052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57052).length < 2 ^ (prefixWord ++ tailWord_57052).sum := by decide
  have hdescent : baseEnd_57052 < baseStart_57052 := by decide
  rcases family_descends (prefixWord ++ tailWord_57052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57068 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 1, 5, 2]
def baseStart_57068 : Nat := 118140960795 + 57068 * 2 ^ 59
def prefixEnd_57068 : Nat := 4983230072969 + 3 ^ 40 * 57068 * 2
def baseEnd_57068 : Nat := 29303313990887954887555

theorem tailTrace_57068 : CollatzResearch.WordTrace tailWord_57068 prefixEnd_57068 29303313990887954887555 := by
  unfold tailWord_57068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040720478629928641777929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1387627304839904855703905 1040720478629928641777929)
  ·
    refine ⟨780540358972446481333447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1040720478629928641777929 780540358972446481333447)
    ·
      refine ⟨1170810538458669722000171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780540358972446481333447 1170810538458669722000171)
      ·
        refine ⟨1756215807688004583000257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170810538458669722000171 1756215807688004583000257)
        ·
          refine ⟨1317161855766003437250193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756215807688004583000257 1317161855766003437250193)
          ·
            refine ⟨987871391824502577937645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317161855766003437250193 987871391824502577937645)
            ·
              refine ⟨370451771934188466726617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 987871391824502577937645 370451771934188466726617)
              ·
                refine ⟨277838828950641350044963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370451771934188466726617 277838828950641350044963)
                ·
                  refine ⟨416758243425962025067445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277838828950641350044963 416758243425962025067445)
                  ·
                    refine ⟨39071085321183939850073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 416758243425962025067445 39071085321183939850073)
                    ·
                      refine ⟨29303313990887954887555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 39071085321183939850073 29303313990887954887555)
                      ·
                        rfl

theorem cell23_57068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_57068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57068 prefixEnd_57068 := by exact prefixLift 57068
  have htrace : WordTrace (prefixWord ++ tailWord_57068) baseStart_57068 baseEnd_57068 := by
    simpa [prefixWord, tailWord_57068, baseEnd_57068] using wordTrace_append hprefix tailTrace_57068
  have hstable : (prefixWord ++ tailWord_57068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57068).length < 2 ^ (prefixWord ++ tailWord_57068).sum := by decide
  have hdescent : baseEnd_57068 < baseStart_57068 := by decide
  rcases family_descends (prefixWord ++ tailWord_57068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57086 : List Nat := [4, 2, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_57086 : Nat := 118140960795 + 57086 * 2 ^ 59
def prefixEnd_57086 : Nat := 4983230072969 + 3 ^ 40 * 57086 * 2
def baseEnd_57086 : Nat := 9770852214222961487491

theorem tailTrace_57086 : CollatzResearch.WordTrace tailWord_57086 prefixEnd_57086 9770852214222961487491 := by
  unfold tailWord_57086
  simp only [CollatzResearch.WordTrace]
  refine ⟨260262183899330794713889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1388064980796430905140741 260262183899330794713889)
  ·
    refine ⟨195196637924498096035417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260262183899330794713889 195196637924498096035417)
    ·
      refine ⟨146397478443373572026563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195196637924498096035417 146397478443373572026563)
      ·
        refine ⟨219596217665060358039845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146397478443373572026563 219596217665060358039845)
        ·
          refine ⟨41174290812198817132471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219596217665060358039845 41174290812198817132471)
          ·
            refine ⟨61761436218298225698707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41174290812198817132471 61761436218298225698707)
            ·
              refine ⟨92642154327447338548061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61761436218298225698707 92642154327447338548061)
              ·
                refine ⟨34740807872792751955523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92642154327447338548061 34740807872792751955523)
                ·
                  refine ⟨52111211809189127933285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34740807872792751955523 52111211809189127933285)
                  ·
                    refine ⟨9770852214222961487491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52111211809189127933285 9770852214222961487491)
                    ·
                      rfl

theorem cell23_57086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_57086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57086 prefixEnd_57086 := by exact prefixLift 57086
  have htrace : WordTrace (prefixWord ++ tailWord_57086) baseStart_57086 baseEnd_57086 := by
    simpa [prefixWord, tailWord_57086, baseEnd_57086] using wordTrace_append hprefix tailTrace_57086
  have hstable : (prefixWord ++ tailWord_57086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57086).length < 2 ^ (prefixWord ++ tailWord_57086).sum := by decide
  have hdescent : baseEnd_57086 < baseStart_57086 := by decide
  rcases family_descends (prefixWord ++ tailWord_57086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57091 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 1, 6]
def baseStart_57091 : Nat := 118140960795 + 57091 * 2 ^ 59
def prefixEnd_57091 : Nat := 4983230072969 + 3 ^ 40 * 57091 * 2
def baseEnd_57091 : Nat := 9771708015313788299983

theorem tailTrace_57091 : CollatzResearch.WordTrace tailWord_57091 prefixEnd_57091 9771708015313788299983 := by
  unfold tailWord_57091
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082279836176532211643127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1388186557451021474428751 2082279836176532211643127)
  ·
    refine ⟨3123419754264798317464691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082279836176532211643127 3123419754264798317464691)
    ·
      refine ⟨4685129631397197476197037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123419754264798317464691 4685129631397197476197037)
      ·
        refine ⟨1756923611773949053573889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4685129631397197476197037 1756923611773949053573889)
        ·
          refine ⟨1317692708830461790180417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756923611773949053573889 1317692708830461790180417)
          ·
            refine ⟨988269531622846342635313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317692708830461790180417 988269531622846342635313)
            ·
              refine ⟨741202148717134756976485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988269531622846342635313 741202148717134756976485)
              ·
                refine ⟨138975402884462766933091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741202148717134756976485 138975402884462766933091)
                ·
                  refine ⟨208463104326694150399637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138975402884462766933091 208463104326694150399637)
                  ·
                    refine ⟨9771708015313788299983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208463104326694150399637 9771708015313788299983)
                    ·
                      rfl

theorem cell23_57091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 6].length) (baseStart_57091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57091 prefixEnd_57091 := by exact prefixLift 57091
  have htrace : WordTrace (prefixWord ++ tailWord_57091) baseStart_57091 baseEnd_57091 := by
    simpa [prefixWord, tailWord_57091, baseEnd_57091] using wordTrace_append hprefix tailTrace_57091
  have hstable : (prefixWord ++ tailWord_57091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57091).length < 2 ^ (prefixWord ++ tailWord_57091).sum := by decide
  have hdescent : baseEnd_57091 < baseStart_57091 := by decide
  rcases family_descends (prefixWord ++ tailWord_57091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57109 : List Nat := [1, 3, 2, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_57109 : Nat := 118140960795 + 57109 * 2 ^ 59
def prefixEnd_57109 : Nat := 4983230072969 + 3 ^ 40 * 57109 * 2
def baseEnd_57109 : Nat := 29324366697722294474867

theorem tailTrace_57109 : CollatzResearch.WordTrace tailWord_57109 prefixEnd_57109 29324366697722294474867 := by
  unfold tailWord_57109
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082936350111321285798381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1388624233407547523865587 2082936350111321285798381)
  ·
    refine ⟨781101131291745482174393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2082936350111321285798381 781101131291745482174393)
    ·
      refine ⟨585825848468809111630795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 781101131291745482174393 585825848468809111630795)
      ·
        refine ⟨878738772703213667446193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585825848468809111630795 878738772703213667446193)
        ·
          refine ⟨659054079527410250584645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878738772703213667446193 659054079527410250584645)
          ·
            refine ⟨123572639911389421984621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 659054079527410250584645 123572639911389421984621)
            ·
              refine ⟨46339739966771033244233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123572639911389421984621 46339739966771033244233)
              ·
                refine ⟨34754804975078274933175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46339739966771033244233 34754804975078274933175)
                ·
                  refine ⟨52132207462617412399763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34754804975078274933175 52132207462617412399763)
                  ·
                    refine ⟨78198311193926118599645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52132207462617412399763 78198311193926118599645)
                    ·
                      refine ⟨29324366697722294474867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 78198311193926118599645 29324366697722294474867)
                      ·
                        rfl

theorem cell23_57109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_57109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57109 prefixEnd_57109 := by exact prefixLift 57109
  have htrace : WordTrace (prefixWord ++ tailWord_57109) baseStart_57109 baseEnd_57109 := by
    simpa [prefixWord, tailWord_57109, baseEnd_57109] using wordTrace_append hprefix tailTrace_57109
  have hstable : (prefixWord ++ tailWord_57109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57109).length < 2 ^ (prefixWord ++ tailWord_57109).sum := by decide
  have hdescent : baseEnd_57109 < baseStart_57109 := by decide
  rcases family_descends (prefixWord ++ tailWord_57109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57121 : List Nat := [1, 2, 3, 2, 1, 3, 1, 10]
def baseStart_57121 : Nat := 118140960795 + 57121 * 2 ^ 59
def prefixEnd_57121 : Nat := 4983230072969 + 3 ^ 40 * 57121 * 2
def baseEnd_57121 : Nat := 1086315869095416574993

theorem tailTrace_57121 : CollatzResearch.WordTrace tailWord_57121 prefixEnd_57121 1086315869095416574993 := by
  unfold tailWord_57121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083374026067847335235217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1388916017378564890156811 2083374026067847335235217)
  ·
    refine ⟨1562530519550885501426413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2083374026067847335235217 1562530519550885501426413)
    ·
      refine ⟨585948944831582063034905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1562530519550885501426413 585948944831582063034905)
      ·
        refine ⟨439461708623686547276179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585948944831582063034905 439461708623686547276179)
        ·
          refine ⟨659192562935529820914269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439461708623686547276179 659192562935529820914269)
          ·
            refine ⟨247197211100823682842851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 659192562935529820914269 247197211100823682842851)
            ·
              refine ⟨370795816651235524264277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247197211100823682842851 370795816651235524264277)
              ·
                refine ⟨1086315869095416574993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 370795816651235524264277 1086315869095416574993)
                ·
                  rfl

theorem cell23_57121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 10].length) (baseStart_57121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57121 prefixEnd_57121 := by exact prefixLift 57121
  have htrace : WordTrace (prefixWord ++ tailWord_57121) baseStart_57121 baseEnd_57121 := by
    simpa [prefixWord, tailWord_57121, baseEnd_57121] using wordTrace_append hprefix tailTrace_57121
  have hstable : (prefixWord ++ tailWord_57121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57121).length < 2 ^ (prefixWord ++ tailWord_57121).sum := by decide
  have hdescent : baseEnd_57121 < baseStart_57121 := by decide
  rcases family_descends (prefixWord ++ tailWord_57121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57125 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_57125 : Nat := 118140960795 + 57125 * 2 ^ 59
def prefixEnd_57125 : Nat := 4983230072969 + 3 ^ 40 * 57125 * 2
def baseEnd_57125 : Nat := 9777527462731410624931

theorem tailTrace_57125 : CollatzResearch.WordTrace tailWord_57125 prefixEnd_57125 9777527462731410624931 := by
  unfold tailWord_57125
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083519918053356018380829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1389013278702237345587219 2083519918053356018380829)
  ·
    refine ⟨781319969270008506892811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2083519918053356018380829 781319969270008506892811)
    ·
      refine ⟨1171979953905012760339217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781319969270008506892811 1171979953905012760339217)
      ·
        refine ⟨878984965428759570254413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171979953905012760339217 878984965428759570254413)
        ·
          refine ⟨329619362035784838845405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878984965428759570254413 329619362035784838845405)
          ·
            refine ⟨123607260763419314567027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329619362035784838845405 123607260763419314567027)
            ·
              refine ⟨185410891145128971850541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123607260763419314567027 185410891145128971850541)
              ·
                refine ⟨69529084179423364443953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185410891145128971850541 69529084179423364443953)
                ·
                  refine ⟨52146813134567523332965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69529084179423364443953 52146813134567523332965)
                  ·
                    refine ⟨9777527462731410624931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52146813134567523332965 9777527462731410624931)
                    ·
                      rfl

theorem cell23_57125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_57125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57125 prefixEnd_57125 := by exact prefixLift 57125
  have htrace : WordTrace (prefixWord ++ tailWord_57125) baseStart_57125 baseEnd_57125 := by
    simpa [prefixWord, tailWord_57125, baseEnd_57125] using wordTrace_append hprefix tailTrace_57125
  have hstable : (prefixWord ++ tailWord_57125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57125).length < 2 ^ (prefixWord ++ tailWord_57125).sum := by decide
  have hdescent : baseEnd_57125 < baseStart_57125 := by decide
  rcases family_descends (prefixWord ++ tailWord_57125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57128 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_57128 : Nat := 118140960795 + 57128 * 2 ^ 59
def prefixEnd_57128 : Nat := 4983230072969 + 3 ^ 40 * 57128 * 2
def baseEnd_57128 : Nat := 29334122830157720137279

theorem tailTrace_57128 : CollatzResearch.WordTrace tailWord_57128 prefixEnd_57128 29334122830157720137279 := by
  unfold tailWord_57128
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041814668521243765370019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1389086224694991687160025 1041814668521243765370019)
  ·
    refine ⟨1562722002781865648055029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1041814668521243765370019 1562722002781865648055029)
    ·
      refine ⟨146505187760799904505159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1562722002781865648055029 146505187760799904505159)
      ·
        refine ⟨219757781641199856757739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146505187760799904505159 219757781641199856757739)
        ·
          refine ⟨329636672461799785136609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219757781641199856757739 329636672461799785136609)
          ·
            refine ⟨247227504346349838852457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329636672461799785136609 247227504346349838852457)
            ·
              refine ⟨185420628259762379139343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247227504346349838852457 185420628259762379139343)
              ·
                refine ⟨278130942389643568709015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185420628259762379139343 278130942389643568709015)
                ·
                  refine ⟨417196413584465353063523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278130942389643568709015 417196413584465353063523)
                  ·
                    refine ⟨625794620376698029595285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 417196413584465353063523 625794620376698029595285)
                    ·
                      refine ⟨29334122830157720137279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 625794620376698029595285 29334122830157720137279)
                      ·
                        rfl

theorem cell23_57128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_57128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57128 prefixEnd_57128 := by exact prefixLift 57128
  have htrace : WordTrace (prefixWord ++ tailWord_57128) baseStart_57128 baseEnd_57128 := by
    simpa [prefixWord, tailWord_57128, baseEnd_57128] using wordTrace_append hprefix tailTrace_57128
  have hstable : (prefixWord ++ tailWord_57128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57128).length < 2 ^ (prefixWord ++ tailWord_57128).sum := by decide
  have hdescent : baseEnd_57128 < baseStart_57128 := by decide
  rcases family_descends (prefixWord ++ tailWord_57128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57148 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_57148 : Nat := 118140960795 + 57148 * 2 ^ 59
def prefixEnd_57148 : Nat := 4983230072969 + 3 ^ 40 * 57148 * 2
def baseEnd_57148 : Nat := 29344392443247641887187

theorem tailTrace_57148 : CollatzResearch.WordTrace tailWord_57148 prefixEnd_57148 29344392443247641887187 := by
  unfold tailWord_57148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042179398485015473234049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1389572531313353964312065 1042179398485015473234049)
  ·
    refine ⟨781634548863761604925537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1042179398485015473234049 781634548863761604925537)
    ·
      refine ⟨586225911647821203694153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 781634548863761604925537 586225911647821203694153)
      ·
        refine ⟨439669433735865902770615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586225911647821203694153 439669433735865902770615)
        ·
          refine ⟨659504150603798854155923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439669433735865902770615 659504150603798854155923)
          ·
            refine ⟨989256225905698281233885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659504150603798854155923 989256225905698281233885)
            ·
              refine ⟨370971084714636855462707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 989256225905698281233885 370971084714636855462707)
              ·
                refine ⟨556456627071955283194061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370971084714636855462707 556456627071955283194061)
                ·
                  refine ⟨208671235151983231197773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556456627071955283194061 208671235151983231197773)
                  ·
                    refine ⟨78251713181993711699165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208671235151983231197773 78251713181993711699165)
                    ·
                      refine ⟨29344392443247641887187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 78251713181993711699165 29344392443247641887187)
                      ·
                        rfl

theorem cell23_57148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_57148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57148 prefixEnd_57148 := by exact prefixLift 57148
  have htrace : WordTrace (prefixWord ++ tailWord_57148) baseStart_57148 baseEnd_57148 := by
    simpa [prefixWord, tailWord_57148, baseEnd_57148] using wordTrace_append hprefix tailTrace_57148
  have hstable : (prefixWord ++ tailWord_57148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57148).length < 2 ^ (prefixWord ++ tailWord_57148).sum := by decide
  have hdescent : baseEnd_57148 < baseStart_57148 := by decide
  rcases family_descends (prefixWord ++ tailWord_57148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57192 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_57192 : Nat := 118140960795 + 57192 * 2 ^ 59
def prefixEnd_57192 : Nat := 4983230072969 + 3 ^ 40 * 57192 * 2
def baseEnd_57192 : Nat := 29366985592045469736985

theorem tailTrace_57192 : CollatzResearch.WordTrace tailWord_57192 prefixEnd_57192 29366985592045469736985 := by
  unfold tailWord_57192
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042981804405313230534915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1390642405873750974046553 1042981804405313230534915)
  ·
    refine ⟨1564472706607969845802373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042981804405313230534915 1564472706607969845802373)
    ·
      refine ⟨293338632488994346087945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1564472706607969845802373 293338632488994346087945)
      ·
        refine ⟨220003974366745759565959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293338632488994346087945 220003974366745759565959)
        ·
          refine ⟨330005961550118639348939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220003974366745759565959 330005961550118639348939)
          ·
            refine ⟨495008942325177959023409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330005961550118639348939 495008942325177959023409)
            ·
              refine ⟨371256706743883469267557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495008942325177959023409 371256706743883469267557)
              ·
                refine ⟨69610632514478150487667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371256706743883469267557 69610632514478150487667)
                ·
                  refine ⟨104415948771717225731501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69610632514478150487667 104415948771717225731501)
                  ·
                    refine ⟨39155980789393959649313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104415948771717225731501 39155980789393959649313)
                    ·
                      refine ⟨29366985592045469736985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 39155980789393959649313 29366985592045469736985)
                      ·
                        rfl

theorem cell23_57192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_57192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57192 prefixEnd_57192 := by exact prefixLift 57192
  have htrace : WordTrace (prefixWord ++ tailWord_57192) baseStart_57192 baseEnd_57192 := by
    simpa [prefixWord, tailWord_57192, baseEnd_57192] using wordTrace_append hprefix tailTrace_57192
  have hstable : (prefixWord ++ tailWord_57192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57192).length < 2 ^ (prefixWord ++ tailWord_57192).sum := by decide
  have hdescent : baseEnd_57192 < baseStart_57192 := by decide
  rcases family_descends (prefixWord ++ tailWord_57192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57211 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 11]
def baseStart_57211 : Nat := 118140960795 + 57211 * 2 ^ 59
def prefixEnd_57211 : Nat := 4983230072969 + 3 ^ 40 * 57211 * 2
def baseEnd_57211 : Nat := 3264082413831210599933

theorem tailTrace_57211 : CollatzResearch.WordTrace tailWord_57211 prefixEnd_57211 3264082413831210599933 := by
  unfold tailWord_57211
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086656595741792706011487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1391104397161195137340991 2086656595741792706011487)
  ·
    refine ⟨3129984893612689059017231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2086656595741792706011487 3129984893612689059017231)
    ·
      refine ⟨4694977340419033588525847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129984893612689059017231 4694977340419033588525847)
      ·
        refine ⟨7042466010628550382788771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694977340419033588525847 7042466010628550382788771)
        ·
          refine ⟨10563699015942825574183157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042466010628550382788771 10563699015942825574183157)
          ·
            refine ⟨990346782744639897579671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10563699015942825574183157 990346782744639897579671)
            ·
              refine ⟨1485520174116959846369507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990346782744639897579671 1485520174116959846369507)
              ·
                refine ⟨2228280261175439769554261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485520174116959846369507 2228280261175439769554261)
                ·
                  refine ⟨3264082413831210599933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 2228280261175439769554261 3264082413831210599933)
                  ·
                    rfl

theorem cell23_57211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 11].length) (baseStart_57211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57211 prefixEnd_57211 := by exact prefixLift 57211
  have htrace : WordTrace (prefixWord ++ tailWord_57211) baseStart_57211 baseEnd_57211 := by
    simpa [prefixWord, tailWord_57211, baseEnd_57211] using wordTrace_append hprefix tailTrace_57211
  have hstable : (prefixWord ++ tailWord_57211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57211).length < 2 ^ (prefixWord ++ tailWord_57211).sum := by decide
  have hdescent : baseEnd_57211 < baseStart_57211 := by decide
  rcases family_descends (prefixWord ++ tailWord_57211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57295 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 1, 6, 2]
def baseStart_57295 : Nat := 118140960795 + 57295 * 2 ^ 59
def prefixEnd_57295 : Nat := 4983230072969 + 3 ^ 40 * 57295 * 2
def baseEnd_57295 : Nat := 29419874099458566749011

theorem tailTrace_57295 : CollatzResearch.WordTrace tailWord_57295 prefixEnd_57295 29419874099458566749011 := by
  unfold tailWord_57295
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089720327437475052069339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1393146884958316701379559 2089720327437475052069339)
  ·
    refine ⟨3134580491156212578104009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2089720327437475052069339 3134580491156212578104009)
    ·
      refine ⟨2350935368367159433578007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3134580491156212578104009 2350935368367159433578007)
      ·
        refine ⟨3526403052550739150367011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2350935368367159433578007 3526403052550739150367011)
        ·
          refine ⟨5289604578826108725550517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526403052550739150367011 5289604578826108725550517)
          ·
            refine ⟨495900429264947693020361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5289604578826108725550517 495900429264947693020361)
            ·
              refine ⟨371925321948710769765271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495900429264947693020361 371925321948710769765271)
              ·
                refine ⟨557887982923066154647907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371925321948710769765271 557887982923066154647907)
                ·
                  refine ⟨836831974384599231971861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557887982923066154647907 836831974384599231971861)
                  ·
                    refine ⟨39226498799278088998681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 836831974384599231971861 39226498799278088998681)
                    ·
                      refine ⟨29419874099458566749011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 39226498799278088998681 29419874099458566749011)
                      ·
                        rfl

theorem cell23_57295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6, 2].length) (baseStart_57295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57295 prefixEnd_57295 := by exact prefixLift 57295
  have htrace : WordTrace (prefixWord ++ tailWord_57295) baseStart_57295 baseEnd_57295 := by
    simpa [prefixWord, tailWord_57295, baseEnd_57295] using wordTrace_append hprefix tailTrace_57295
  have hstable : (prefixWord ++ tailWord_57295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57295).length < 2 ^ (prefixWord ++ tailWord_57295).sum := by decide
  have hdescent : baseEnd_57295 < baseStart_57295 := by decide
  rcases family_descends (prefixWord ++ tailWord_57295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57339 : List Nat := [1, 1, 1, 1, 1, 3, 8, 2, 1, 4]
def baseStart_57339 : Nat := 118140960795 + 57339 * 2 ^ 59
def prefixEnd_57339 : Nat := 4983230072969 + 3 ^ 40 * 57339 * 2
def baseEnd_57339 : Nat := 9814155749418798199603

theorem tailTrace_57339 : CollatzResearch.WordTrace tailWord_57339 prefixEnd_57339 9814155749418798199603 := by
  unfold tailWord_57339
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091325139278070566671071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1394216759518713711114047 2091325139278070566671071)
  ·
    refine ⟨3136987708917105850006607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2091325139278070566671071 3136987708917105850006607)
    ·
      refine ⟨4705481563375658775009911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136987708917105850006607 4705481563375658775009911)
      ·
        refine ⟨7058222345063488162514867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705481563375658775009911 7058222345063488162514867)
        ·
          refine ⟨10587333517595232243772301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7058222345063488162514867 10587333517595232243772301)
          ·
            refine ⟨3970250069098212091414613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10587333517595232243772301 3970250069098212091414613)
            ·
              refine ⟨46526367997244672946265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3970250069098212091414613 46526367997244672946265)
              ·
                refine ⟨34894775997933504709699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46526367997244672946265 34894775997933504709699)
                ·
                  refine ⟨52342163996900257064549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34894775997933504709699 52342163996900257064549)
                  ·
                    refine ⟨9814155749418798199603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52342163996900257064549 9814155749418798199603)
                    ·
                      rfl

theorem cell23_57339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 4].length) (baseStart_57339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57339 prefixEnd_57339 := by exact prefixLift 57339
  have htrace : WordTrace (prefixWord ++ tailWord_57339) baseStart_57339 baseEnd_57339 := by
    simpa [prefixWord, tailWord_57339, baseEnd_57339] using wordTrace_append hprefix tailTrace_57339
  have hstable : (prefixWord ++ tailWord_57339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57339).length < 2 ^ (prefixWord ++ tailWord_57339).sum := by decide
  have hdescent : baseEnd_57339 < baseStart_57339 := by decide
  rcases family_descends (prefixWord ++ tailWord_57339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57415 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_57415 : Nat := 118140960795 + 57415 * 2 ^ 59
def prefixEnd_57415 : Nat := 4983230072969 + 3 ^ 40 * 57415 * 2
def baseEnd_57415 : Nat := 29481491777998097248459

theorem tailTrace_57415 : CollatzResearch.WordTrace tailWord_57415 prefixEnd_57415 29481491777998097248459 := by
  unfold tailWord_57415
  simp only [CollatzResearch.WordTrace]
  refine ⟨2094097087002735546437699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1396064724668490364291799 2094097087002735546437699)
  ·
    refine ⟨3141145630504103319656549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2094097087002735546437699 3141145630504103319656549)
    ·
      refine ⟨588964805719519372435603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3141145630504103319656549 588964805719519372435603)
      ·
        refine ⟨883447208579279058653405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588964805719519372435603 883447208579279058653405)
        ·
          refine ⟨331292703217229646995027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 883447208579279058653405 331292703217229646995027)
          ·
            refine ⟨496939054825844470492541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331292703217229646995027 496939054825844470492541)
            ·
              refine ⟨186352145559691676434703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496939054825844470492541 186352145559691676434703)
              ·
                refine ⟨279528218339537514652055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186352145559691676434703 279528218339537514652055)
                ·
                  refine ⟨419292327509306271978083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279528218339537514652055 419292327509306271978083)
                  ·
                    refine ⟨628938491263959407967125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419292327509306271978083 628938491263959407967125)
                    ·
                      refine ⟨29481491777998097248459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 628938491263959407967125 29481491777998097248459)
                      ·
                        rfl

theorem cell23_57415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_57415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57415 prefixEnd_57415 := by exact prefixLift 57415
  have htrace : WordTrace (prefixWord ++ tailWord_57415) baseStart_57415 baseEnd_57415 := by
    simpa [prefixWord, tailWord_57415, baseEnd_57415] using wordTrace_append hprefix tailTrace_57415
  have hstable : (prefixWord ++ tailWord_57415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57415).length < 2 ^ (prefixWord ++ tailWord_57415).sum := by decide
  have hdescent : baseEnd_57415 < baseStart_57415 := by decide
  rcases family_descends (prefixWord ++ tailWord_57415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57430 : List Nat := [5, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_57430 : Nat := 118140960795 + 57430 * 2 ^ 59
def prefixEnd_57430 : Nat := 4983230072969 + 3 ^ 40 * 57430 * 2
def baseEnd_57430 : Nat := 29489193987815538560891

theorem tailTrace_57430 : CollatzResearch.WordTrace tailWord_57430 prefixEnd_57430 29489193987815538560891 := by
  unfold tailWord_57430
  simp only [CollatzResearch.WordTrace]
  refine ⟨130915261371774569264609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1396429454632262072155829 130915261371774569264609)
  ·
    refine ⟨98186446028830926948457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130915261371774569264609 98186446028830926948457)
    ·
      refine ⟨73639834521623195211343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98186446028830926948457 73639834521623195211343)
      ·
        refine ⟨110459751782434792817015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73639834521623195211343 110459751782434792817015)
        ·
          refine ⟨165689627673652189225523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110459751782434792817015 165689627673652189225523)
          ·
            refine ⟨248534441510478283838285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165689627673652189225523 248534441510478283838285)
            ·
              refine ⟨93200415566429356439357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248534441510478283838285 93200415566429356439357)
              ·
                refine ⟨34950155837411008664759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93200415566429356439357 34950155837411008664759)
                ·
                  refine ⟨52425233756116512997139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34950155837411008664759 52425233756116512997139)
                  ·
                    refine ⟨78637850634174769495709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52425233756116512997139 78637850634174769495709)
                    ·
                      refine ⟨29489193987815538560891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 78637850634174769495709 29489193987815538560891)
                      ·
                        rfl

theorem cell23_57430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_57430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57430 prefixEnd_57430 := by exact prefixLift 57430
  have htrace : WordTrace (prefixWord ++ tailWord_57430) baseStart_57430 baseEnd_57430 := by
    simpa [prefixWord, tailWord_57430, baseEnd_57430] using wordTrace_append hprefix tailTrace_57430
  have hstable : (prefixWord ++ tailWord_57430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57430).length < 2 ^ (prefixWord ++ tailWord_57430).sum := by decide
  have hdescent : baseEnd_57430 < baseStart_57430 := by decide
  rcases family_descends (prefixWord ++ tailWord_57430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57473 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_57473 : Nat := 118140960795 + 57473 * 2 ^ 59
def prefixEnd_57473 : Nat := 4983230072969 + 3 ^ 40 * 57473 * 2
def baseEnd_57473 : Nat := 29511273655958870323193

theorem tailTrace_57473 : CollatzResearch.WordTrace tailWord_57473 prefixEnd_57473 29511273655958870323193 := by
  unfold tailWord_57473
  simp only [CollatzResearch.WordTrace]
  refine ⟨2096212520792611452049073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1397475013861740968032715 2096212520792611452049073)
  ·
    refine ⟨1572159390594458589036805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2096212520792611452049073 1572159390594458589036805)
    ·
      refine ⟨294779885736460985444401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1572159390594458589036805 294779885736460985444401)
      ·
        refine ⟨221084914302345739083301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294779885736460985444401 221084914302345739083301)
        ·
          refine ⟨41453421431689826078119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221084914302345739083301 41453421431689826078119)
          ·
            refine ⟨62180132147534739117179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41453421431689826078119 62180132147534739117179)
            ·
              refine ⟨93270198221302108675769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62180132147534739117179 93270198221302108675769)
              ·
                refine ⟨69952648665976581506827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93270198221302108675769 69952648665976581506827)
                ·
                  refine ⟨104928972998964872260241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69952648665976581506827 104928972998964872260241)
                  ·
                    refine ⟨78696729749223654195181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104928972998964872260241 78696729749223654195181)
                    ·
                      refine ⟨29511273655958870323193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 78696729749223654195181 29511273655958870323193)
                      ·
                        rfl

theorem cell23_57473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_57473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57473 prefixEnd_57473 := by exact prefixLift 57473
  have htrace : WordTrace (prefixWord ++ tailWord_57473) baseStart_57473 baseEnd_57473 := by
    simpa [prefixWord, tailWord_57473, baseEnd_57473] using wordTrace_append hprefix tailTrace_57473
  have hstable : (prefixWord ++ tailWord_57473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57473).length < 2 ^ (prefixWord ++ tailWord_57473).sum := by decide
  have hdescent : baseEnd_57473 < baseStart_57473 := by decide
  rcases family_descends (prefixWord ++ tailWord_57473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57522 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_57522 : Nat := 118140960795 + 57522 * 2 ^ 59
def prefixEnd_57522 : Nat := 4983230072969 + 3 ^ 40 * 57522 * 2
def baseEnd_57522 : Nat := 29536434208029178610467

theorem tailTrace_57522 : CollatzResearch.WordTrace tailWord_57522 prefixEnd_57522 29536434208029178610467 := by
  unfold tailWord_57522
  simp only [CollatzResearch.WordTrace]
  refine ⟨524499924403773205145705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1398666465076728547055213 524499924403773205145705)
  ·
    refine ⟨393374943302829903859279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 524499924403773205145705 393374943302829903859279)
    ·
      refine ⟨590062414954244855788919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393374943302829903859279 590062414954244855788919)
      ·
        refine ⟨885093622431367283683379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590062414954244855788919 885093622431367283683379)
        ·
          refine ⟨1327640433647050925525069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885093622431367283683379 1327640433647050925525069)
          ·
            refine ⟨497865162617644097071901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1327640433647050925525069 497865162617644097071901)
            ·
              refine ⟨186699435981616536401963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497865162617644097071901 186699435981616536401963)
              ·
                refine ⟨280049153972424804602945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186699435981616536401963 280049153972424804602945)
                ·
                  refine ⟨210036865479318603452209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280049153972424804602945 210036865479318603452209)
                  ·
                    refine ⟨157527649109488952589157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210036865479318603452209 157527649109488952589157)
                    ·
                      refine ⟨29536434208029178610467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 157527649109488952589157 29536434208029178610467)
                      ·
                        rfl

theorem cell23_57522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_57522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57522 prefixEnd_57522 := by exact prefixLift 57522
  have htrace : WordTrace (prefixWord ++ tailWord_57522) baseStart_57522 baseEnd_57522 := by
    simpa [prefixWord, tailWord_57522, baseEnd_57522] using wordTrace_append hprefix tailTrace_57522
  have hstable : (prefixWord ++ tailWord_57522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57522).length < 2 ^ (prefixWord ++ tailWord_57522).sum := by decide
  have hdescent : baseEnd_57522 < baseStart_57522 := by decide
  rcases family_descends (prefixWord ++ tailWord_57522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57562 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_57562 : Nat := 118140960795 + 57562 * 2 ^ 59
def prefixEnd_57562 : Nat := 4983230072969 + 3 ^ 40 * 57562 * 2
def baseEnd_57562 : Nat := 9852324478069674036761

theorem tailTrace_57562 : CollatzResearch.WordTrace tailWord_57562 prefixEnd_57562 9852324478069674036761 := by
  unfold tailWord_57562
  simp only [CollatzResearch.WordTrace]
  refine ⟨524864654367544913009735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1399639078313453101359293 524864654367544913009735)
  ·
    refine ⟨787296981551317369514603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524864654367544913009735 787296981551317369514603)
    ·
      refine ⟨1180945472326976054271905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787296981551317369514603 1180945472326976054271905)
      ·
        refine ⟨885709104245232040703929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1180945472326976054271905 885709104245232040703929)
        ·
          refine ⟨664281828183924030527947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885709104245232040703929 664281828183924030527947)
          ·
            refine ⟨996422742275886045791921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664281828183924030527947 996422742275886045791921)
            ·
              refine ⟨747317056706914534343941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996422742275886045791921 747317056706914534343941)
              ·
                refine ⟨140121948132546475189489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747317056706914534343941 140121948132546475189489)
                ·
                  refine ⟨105091461099409856392117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140121948132546475189489 105091461099409856392117)
                  ·
                    refine ⟨9852324478069674036761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105091461099409856392117 9852324478069674036761)
                    ·
                      rfl

theorem cell23_57562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_57562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57562 prefixEnd_57562 := by exact prefixLift 57562
  have htrace : WordTrace (prefixWord ++ tailWord_57562) baseStart_57562 baseEnd_57562 := by
    simpa [prefixWord, tailWord_57562, baseEnd_57562] using wordTrace_append hprefix tailTrace_57562
  have hstable : (prefixWord ++ tailWord_57562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57562).length < 2 ^ (prefixWord ++ tailWord_57562).sum := by decide
  have hdescent : baseEnd_57562 < baseStart_57562 := by decide
  rcases family_descends (prefixWord ++ tailWord_57562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57676 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 2, 3, 2]
def baseStart_57676 : Nat := 118140960795 + 57676 * 2 ^ 59
def prefixEnd_57676 : Nat := 4983230072969 + 3 ^ 40 * 57676 * 2
def baseEnd_57676 : Nat := 29615510228821576084759

theorem tailTrace_57676 : CollatzResearch.WordTrace tailWord_57676 prefixEnd_57676 29615510228821576084759 := by
  unfold tailWord_57676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051808269528588560844441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1402411026038118081125921 1051808269528588560844441)
  ·
    refine ⟨788856202146441420633331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1051808269528588560844441 788856202146441420633331)
    ·
      refine ⟨1183284303219662130949997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788856202146441420633331 1183284303219662130949997)
      ·
        refine ⟨443731613707373299106249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1183284303219662130949997 443731613707373299106249)
        ·
          refine ⟨332798710280529974329687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443731613707373299106249 332798710280529974329687)
          ·
            refine ⟨499198065420794961494531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332798710280529974329687 499198065420794961494531)
            ·
              refine ⟨748797098131192442241797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499198065420794961494531 748797098131192442241797)
              ·
                refine ⟨140399455899598582920337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748797098131192442241797 140399455899598582920337)
                ·
                  refine ⟨105299591924698937190253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140399455899598582920337 105299591924698937190253)
                  ·
                    refine ⟨39487346971762101446345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105299591924698937190253 39487346971762101446345)
                    ·
                      refine ⟨29615510228821576084759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 39487346971762101446345 29615510228821576084759)
                      ·
                        rfl

theorem cell23_57676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_57676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57676 prefixEnd_57676 := by exact prefixLift 57676
  have htrace : WordTrace (prefixWord ++ tailWord_57676) baseStart_57676 baseEnd_57676 := by
    simpa [prefixWord, tailWord_57676, baseEnd_57676] using wordTrace_append hprefix tailTrace_57676
  have hstable : (prefixWord ++ tailWord_57676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57676).length < 2 ^ (prefixWord ++ tailWord_57676).sum := by decide
  have hdescent : baseEnd_57676 < baseStart_57676 := by decide
  rcases family_descends (prefixWord ++ tailWord_57676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57689 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 2, 6, 2]
def baseStart_57689 : Nat := 118140960795 + 57689 * 2 ^ 59
def prefixEnd_57689 : Nat := 4983230072969 + 3 ^ 40 * 57689 * 2
def baseEnd_57689 : Nat := 29622185477330025222199

theorem tailTrace_57689 : CollatzResearch.WordTrace tailWord_57689 prefixEnd_57689 29622185477330025222199 := by
  unfold tailWord_57689
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104090688010080341912121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1402727125340053561274747 2104090688010080341912121)
  ·
    refine ⟨1578068016007560256434091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2104090688010080341912121 1578068016007560256434091)
    ·
      refine ⟨2367102024011340384651137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578068016007560256434091 2367102024011340384651137)
      ·
        refine ⟨1775326518008505288488353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2367102024011340384651137 1775326518008505288488353)
        ·
          refine ⟨1331494888506378966366265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775326518008505288488353 1331494888506378966366265)
          ·
            refine ⟨998621166379784224774699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331494888506378966366265 998621166379784224774699)
            ·
              refine ⟨1497931749569676337162049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998621166379784224774699 1497931749569676337162049)
              ·
                refine ⟨1123448812177257252871537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497931749569676337162049 1123448812177257252871537)
                ·
                  refine ⟨842586609132942939653653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1123448812177257252871537 842586609132942939653653)
                  ·
                    refine ⟨39496247303106700296265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 842586609132942939653653 39496247303106700296265)
                    ·
                      refine ⟨29622185477330025222199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 39496247303106700296265 29622185477330025222199)
                      ·
                        rfl

theorem cell23_57689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_57689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57689 prefixEnd_57689 := by exact prefixLift 57689
  have htrace : WordTrace (prefixWord ++ tailWord_57689) baseStart_57689 baseEnd_57689 := by
    simpa [prefixWord, tailWord_57689, baseEnd_57689] using wordTrace_append hprefix tailTrace_57689
  have hstable : (prefixWord ++ tailWord_57689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57689).length < 2 ^ (prefixWord ++ tailWord_57689).sum := by decide
  have hdescent : baseEnd_57689 < baseStart_57689 := by decide
  rcases family_descends (prefixWord ++ tailWord_57689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57699 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 1, 6]
def baseStart_57699 : Nat := 118140960795 + 57699 * 2 ^ 59
def prefixEnd_57699 : Nat := 4983230072969 + 3 ^ 40 * 57699 * 2
def baseEnd_57699 : Nat := 9875773427958328699051

theorem tailTrace_57699 : CollatzResearch.WordTrace tailWord_57699 prefixEnd_57699 9875773427958328699051 := by
  unfold tailWord_57699
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104455417973852049776151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1402970278649234699850767 2104455417973852049776151)
  ·
    refine ⟨3156683126960778074664227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104455417973852049776151 3156683126960778074664227)
    ·
      refine ⟨4735024690441167111996341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3156683126960778074664227 4735024690441167111996341)
      ·
        refine ⟨443908564728859416749657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4735024690441167111996341 443908564728859416749657)
        ·
          refine ⟨332931423546644562562243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443908564728859416749657 332931423546644562562243)
          ·
            refine ⟨499397135319966843843365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332931423546644562562243 499397135319966843843365)
            ·
              refine ⟨93636962872493783220631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499397135319966843843365 93636962872493783220631)
              ·
                refine ⟨140455444308740674830947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93636962872493783220631 140455444308740674830947)
                ·
                  refine ⟨210683166463111012246421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140455444308740674830947 210683166463111012246421)
                  ·
                    refine ⟨9875773427958328699051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 210683166463111012246421 9875773427958328699051)
                    ·
                      rfl

theorem cell23_57699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 6].length) (baseStart_57699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57699 prefixEnd_57699 := by exact prefixLift 57699
  have htrace : WordTrace (prefixWord ++ tailWord_57699) baseStart_57699 baseEnd_57699 := by
    simpa [prefixWord, tailWord_57699, baseEnd_57699] using wordTrace_append hprefix tailTrace_57699
  have hstable : (prefixWord ++ tailWord_57699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57699).length < 2 ^ (prefixWord ++ tailWord_57699).sum := by decide
  have hdescent : baseEnd_57699 < baseStart_57699 := by decide
  rcases family_descends (prefixWord ++ tailWord_57699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57706 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_57706 : Nat := 118140960795 + 57706 * 2 ^ 59
def prefixEnd_57706 : Nat := 4983230072969 + 3 ^ 40 * 57706 * 2
def baseEnd_57706 : Nat := 29630914648456458709621

theorem tailTrace_57706 : CollatzResearch.WordTrace tailWord_57706 prefixEnd_57706 29630914648456458709621 := by
  unfold tailWord_57706
  simp only [CollatzResearch.WordTrace]
  refine ⟨526177682237123061320243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1403140485965661496853981 526177682237123061320243)
  ·
    refine ⟨789266523355684591980365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 526177682237123061320243 789266523355684591980365)
    ·
      refine ⟨295974946258381721992637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 789266523355684591980365 295974946258381721992637)
      ·
        refine ⟨110990604846893145747239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295974946258381721992637 110990604846893145747239)
        ·
          refine ⟨166485907270339718620859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110990604846893145747239 166485907270339718620859)
          ·
            refine ⟨249728860905509577931289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166485907270339718620859 249728860905509577931289)
            ·
              refine ⟨187296645679132183448467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249728860905509577931289 187296645679132183448467)
              ·
                refine ⟨280944968518698275172701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187296645679132183448467 280944968518698275172701)
                ·
                  refine ⟨105354363194511853189763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280944968518698275172701 105354363194511853189763)
                  ·
                    refine ⟨158031544791767779784645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105354363194511853189763 158031544791767779784645)
                    ·
                      refine ⟨29630914648456458709621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 158031544791767779784645 29630914648456458709621)
                      ·
                        rfl

theorem cell23_57706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_57706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57706 prefixEnd_57706 := by exact prefixLift 57706
  have htrace : WordTrace (prefixWord ++ tailWord_57706) baseStart_57706 baseEnd_57706 := by
    simpa [prefixWord, tailWord_57706, baseEnd_57706] using wordTrace_append hprefix tailTrace_57706
  have hstable : (prefixWord ++ tailWord_57706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57706).length < 2 ^ (prefixWord ++ tailWord_57706).sum := by decide
  have hdescent : baseEnd_57706 < baseStart_57706 := by decide
  rcases family_descends (prefixWord ++ tailWord_57706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57723 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 1, 1, 4]
def baseStart_57723 : Nat := 118140960795 + 57723 * 2 ^ 59
def prefixEnd_57723 : Nat := 4983230072969 + 3 ^ 40 * 57723 * 2
def baseEnd_57723 : Nat := 29639643819582892197043

theorem tailTrace_57723 : CollatzResearch.WordTrace tailWord_57723 prefixEnd_57723 29639643819582892197043 := by
  unfold tailWord_57723
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105330769886904148649823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1403553846591269432433215 2105330769886904148649823)
  ·
    refine ⟨3157996154830356222974735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2105330769886904148649823 3157996154830356222974735)
    ·
      refine ⟨4736994232245534334462103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157996154830356222974735 4736994232245534334462103)
      ·
        refine ⟨7105491348368301501693155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736994232245534334462103 7105491348368301501693155)
        ·
          refine ⟨10658237022552452252539733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105491348368301501693155 10658237022552452252539733)
          ·
            refine ⟨62450607554018274917225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 10658237022552452252539733 62450607554018274917225)
            ·
              refine ⟨46837955665513706187919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62450607554018274917225 46837955665513706187919)
              ·
                refine ⟨70256933498270559281879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46837955665513706187919 70256933498270559281879)
                ·
                  refine ⟨105385400247405838922819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70256933498270559281879 105385400247405838922819)
                  ·
                    refine ⟨158078100371108758384229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105385400247405838922819 158078100371108758384229)
                    ·
                      refine ⟨29639643819582892197043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 158078100371108758384229 29639643819582892197043)
                      ·
                        rfl

theorem cell23_57723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 1, 4].length) (baseStart_57723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57723 prefixEnd_57723 := by exact prefixLift 57723
  have htrace : WordTrace (prefixWord ++ tailWord_57723) baseStart_57723 baseEnd_57723 := by
    simpa [prefixWord, tailWord_57723, baseEnd_57723] using wordTrace_append hprefix tailTrace_57723
  have hstable : (prefixWord ++ tailWord_57723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57723).length < 2 ^ (prefixWord ++ tailWord_57723).sum := by decide
  have hdescent : baseEnd_57723 < baseStart_57723 := by decide
  rcases family_descends (prefixWord ++ tailWord_57723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57729 : List Nat := [1, 2, 4, 3, 1, 2, 10]
def baseStart_57729 : Nat := 118140960795 + 57729 * 2 ^ 59
def prefixEnd_57729 : Nat := 4983230072969 + 3 ^ 40 * 57729 * 2
def baseEnd_57729 : Nat := 365959564240862576815

theorem tailTrace_57729 : CollatzResearch.WordTrace tailWord_57729 prefixEnd_57729 365959564240862576815 := by
  unfold tailWord_57729
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105549607865167173368241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1403699738576778115578827 2105549607865167173368241)
  ·
    refine ⟨1579162205898875380026181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2105549607865167173368241 1579162205898875380026181)
    ·
      refine ⟨296092913606039133754909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1579162205898875380026181 296092913606039133754909)
      ·
        refine ⟨111034842602264675158091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296092913606039133754909 111034842602264675158091)
        ·
          refine ⟨166552263903397012737137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111034842602264675158091 166552263903397012737137)
          ·
            refine ⟨124914197927547759552853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166552263903397012737137 124914197927547759552853)
            ·
              refine ⟨365959564240862576815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 124914197927547759552853 365959564240862576815)
              ·
                rfl

theorem cell23_57729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 10].length) (baseStart_57729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57729 prefixEnd_57729 := by exact prefixLift 57729
  have htrace : WordTrace (prefixWord ++ tailWord_57729) baseStart_57729 baseEnd_57729 := by
    simpa [prefixWord, tailWord_57729, baseEnd_57729] using wordTrace_append hprefix tailTrace_57729
  have hstable : (prefixWord ++ tailWord_57729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57729).length < 2 ^ (prefixWord ++ tailWord_57729).sum := by decide
  have hdescent : baseEnd_57729 < baseStart_57729 := by decide
  rcases family_descends (prefixWord ++ tailWord_57729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57740 : List Nat := [2, 2, 1, 2, 1, 4, 2, 4, 1, 2, 2]
def baseStart_57740 : Nat := 118140960795 + 57740 * 2 ^ 59
def prefixEnd_57740 : Nat := 4983230072969 + 3 ^ 40 * 57740 * 2
def baseEnd_57740 : Nat := 29648372990709325684465

theorem tailTrace_57740 : CollatzResearch.WordTrace tailWord_57740 prefixEnd_57740 29648372990709325684465 := by
  unfold tailWord_57740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052975405412658026009337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1403967207216877368012449 1052975405412658026009337)
  ·
    refine ⟨789731554059493519507003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1052975405412658026009337 789731554059493519507003)
    ·
      refine ⟨1184597331089240279260505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789731554059493519507003 1184597331089240279260505)
      ·
        refine ⟨888447998316930209445379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184597331089240279260505 888447998316930209445379)
        ·
          refine ⟨1332671997475395314168069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888447998316930209445379 1332671997475395314168069)
          ·
            refine ⟨249875999526636621406513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1332671997475395314168069 249875999526636621406513)
            ·
              refine ⟨187406999644977466054885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249875999526636621406513 187406999644977466054885)
              ·
                refine ⟨35138812433433274885291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187406999644977466054885 35138812433433274885291)
                ·
                  refine ⟨52708218650149912327937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35138812433433274885291 52708218650149912327937)
                  ·
                    refine ⟨39531163987612434245953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52708218650149912327937 39531163987612434245953)
                    ·
                      refine ⟨29648372990709325684465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 39531163987612434245953 29648372990709325684465)
                      ·
                        rfl

theorem cell23_57740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_57740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57740 prefixEnd_57740 := by exact prefixLift 57740
  have htrace : WordTrace (prefixWord ++ tailWord_57740) baseStart_57740 baseEnd_57740 := by
    simpa [prefixWord, tailWord_57740, baseEnd_57740] using wordTrace_append hprefix tailTrace_57740
  have hstable : (prefixWord ++ tailWord_57740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57740).length < 2 ^ (prefixWord ++ tailWord_57740).sum := by decide
  have hdescent : baseEnd_57740 < baseStart_57740 := by decide
  rcases family_descends (prefixWord ++ tailWord_57740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57780 : List Nat := [2, 5, 2, 2, 2, 1, 9]
def baseStart_57780 : Nat := 118140960795 + 57780 * 2 ^ 59
def prefixEnd_57780 : Nat := 4983230072969 + 3 ^ 40 * 57780 * 2
def baseEnd_57780 : Nat := 366282866875174928201

theorem tailTrace_57780 : CollatzResearch.WordTrace tailWord_57780 prefixEnd_57780 366282866875174928201 := by
  unfold tailWord_57780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053704865340201441737397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1404939820453601922316529 1053704865340201441737397)
  ·
    refine ⟨98784831125643885162881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1053704865340201441737397 98784831125643885162881)
    ·
      refine ⟨74088623344232913872161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98784831125643885162881 74088623344232913872161)
      ·
        refine ⟨55566467508174685404121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74088623344232913872161 55566467508174685404121)
        ·
          refine ⟨41674850631131014053091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55566467508174685404121 41674850631131014053091)
          ·
            refine ⟨62512275946696521079637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41674850631131014053091 62512275946696521079637)
            ·
              refine ⟨366282866875174928201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 62512275946696521079637 366282866875174928201)
              ·
                rfl

theorem cell23_57780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 9].length) (baseStart_57780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57780 prefixEnd_57780 := by exact prefixLift 57780
  have htrace : WordTrace (prefixWord ++ tailWord_57780) baseStart_57780 baseEnd_57780 := by
    simpa [prefixWord, tailWord_57780, baseEnd_57780] using wordTrace_append hprefix tailTrace_57780
  have hstable : (prefixWord ++ tailWord_57780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57780).length < 2 ^ (prefixWord ++ tailWord_57780).sum := by decide
  have hdescent : baseEnd_57780 < baseStart_57780 := by decide
  rcases family_descends (prefixWord ++ tailWord_57780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57783 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 1, 3, 2]
def baseStart_57783 : Nat := 118140960795 + 57783 * 2 ^ 59
def prefixEnd_57783 : Nat := 4983230072969 + 3 ^ 40 * 57783 * 2
def baseEnd_57783 : Nat := 29670452658852657446767

theorem tailTrace_57783 : CollatzResearch.WordTrace tailWord_57783 prefixEnd_57783 29670452658852657446767 := by
  unfold tailWord_57783
  simp only [CollatzResearch.WordTrace]
  refine ⟨2107519149669534395834003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1405012766446356263889335 2107519149669534395834003)
  ·
    refine ⟨3161278724504301593751005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2107519149669534395834003 3161278724504301593751005)
    ·
      refine ⟨1185479521689113097656627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3161278724504301593751005 1185479521689113097656627)
      ·
        refine ⟨1778219282533669646484941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185479521689113097656627 1778219282533669646484941)
        ·
          refine ⟨666832230950126117431853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1778219282533669646484941 666832230950126117431853)
          ·
            refine ⟨250062086606297294036945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666832230950126117431853 250062086606297294036945)
            ·
              refine ⟨187546564954722970527709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250062086606297294036945 187546564954722970527709)
              ·
                refine ⟨70329961858021113947891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187546564954722970527709 70329961858021113947891)
                ·
                  refine ⟨105494942787031670921837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70329961858021113947891 105494942787031670921837)
                  ·
                    refine ⟨39560603545136876595689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105494942787031670921837 39560603545136876595689)
                    ·
                      refine ⟨29670452658852657446767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 39560603545136876595689 29670452658852657446767)
                      ·
                        rfl

theorem cell23_57783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_57783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57783 prefixEnd_57783 := by exact prefixLift 57783
  have htrace : WordTrace (prefixWord ++ tailWord_57783) baseStart_57783 baseEnd_57783 := by
    simpa [prefixWord, tailWord_57783, baseEnd_57783] using wordTrace_append hprefix tailTrace_57783
  have hstable : (prefixWord ++ tailWord_57783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57783).length < 2 ^ (prefixWord ++ tailWord_57783).sum := by decide
  have hdescent : baseEnd_57783 < baseStart_57783 := by decide
  rcases family_descends (prefixWord ++ tailWord_57783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57809 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_57809 : Nat := 118140960795 + 57809 * 2 ^ 59
def prefixEnd_57809 : Nat := 4983230072969 + 3 ^ 40 * 57809 * 2
def baseEnd_57809 : Nat := 29683803155869555721647

theorem tailTrace_57809 : CollatzResearch.WordTrace tailWord_57809 prefixEnd_57809 29683803155869555721647 := by
  unfold tailWord_57809
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108467447575340836280481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1405644965050227224186987 2108467447575340836280481)
  ·
    refine ⟨1581350585681505627210361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2108467447575340836280481 1581350585681505627210361)
    ·
      refine ⟨1186012939261129220407771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1581350585681505627210361 1186012939261129220407771)
      ·
        refine ⟨1779019408891693830611657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186012939261129220407771 1779019408891693830611657)
        ·
          refine ⟨1334264556668770372958743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1779019408891693830611657 1334264556668770372958743)
          ·
            refine ⟨2001396835003155559438115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334264556668770372958743 2001396835003155559438115)
            ·
              refine ⟨3002095252504733339157173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001396835003155559438115 3002095252504733339157173)
              ·
                refine ⟨281446429922318750545985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3002095252504733339157173 281446429922318750545985)
                ·
                  refine ⟨211084822441739062909489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281446429922318750545985 211084822441739062909489)
                  ·
                    refine ⟨158313616831304297182117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211084822441739062909489 158313616831304297182117)
                    ·
                      refine ⟨29683803155869555721647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 158313616831304297182117 29683803155869555721647)
                      ·
                        rfl

theorem cell23_57809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_57809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57809 prefixEnd_57809 := by exact prefixLift 57809
  have htrace : WordTrace (prefixWord ++ tailWord_57809) baseStart_57809 baseEnd_57809 := by
    simpa [prefixWord, tailWord_57809, baseEnd_57809] using wordTrace_append hprefix tailTrace_57809
  have hstable : (prefixWord ++ tailWord_57809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57809).length < 2 ^ (prefixWord ++ tailWord_57809).sum := by decide
  have hdescent : baseEnd_57809 < baseStart_57809 := by decide
  rcases family_descends (prefixWord ++ tailWord_57809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57836 : List Nat := [2, 2, 1, 1, 2, 1, 4, 5, 5]
def baseStart_57836 : Nat := 118140960795 + 57836 * 2 ^ 59
def prefixEnd_57836 : Nat := 4983230072969 + 3 ^ 40 * 57836 * 2
def baseEnd_57836 : Nat := 3299740792615661120447

theorem tailTrace_57836 : CollatzResearch.WordTrace tailWord_57836 prefixEnd_57836 3299740792615661120447 := by
  unfold tailWord_57836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054726109238762223756681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1406301478985016298342241 1054726109238762223756681)
  ·
    refine ⟨791044581929071667817511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1054726109238762223756681 791044581929071667817511)
    ·
      refine ⟨1186566872893607501726267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791044581929071667817511 1186566872893607501726267)
      ·
        refine ⟨1779850309340411252589401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186566872893607501726267 1779850309340411252589401)
        ·
          refine ⟨1334887732005308439442051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1779850309340411252589401 1334887732005308439442051)
          ·
            refine ⟨2002331598007962659163077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334887732005308439442051 2002331598007962659163077)
            ·
              refine ⟨375437174626492998593077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2002331598007962659163077 375437174626492998593077)
              ·
                refine ⟨35197235121233718618101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375437174626492998593077 35197235121233718618101)
                ·
                  refine ⟨3299740792615661120447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35197235121233718618101 3299740792615661120447)
                  ·
                    rfl

theorem cell23_57836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_57836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57836 prefixEnd_57836 := by exact prefixLift 57836
  have htrace : WordTrace (prefixWord ++ tailWord_57836) baseStart_57836 baseEnd_57836 := by
    simpa [prefixWord, tailWord_57836, baseEnd_57836] using wordTrace_append hprefix tailTrace_57836
  have hstable : (prefixWord ++ tailWord_57836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57836).length < 2 ^ (prefixWord ++ tailWord_57836).sum := by decide
  have hdescent : baseEnd_57836 < baseStart_57836 := by decide
  rcases family_descends (prefixWord ++ tailWord_57836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57859 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5]
def baseStart_57859 : Nat := 118140960795 + 57859 * 2 ^ 59
def prefixEnd_57859 : Nat := 4983230072969 + 3 ^ 40 * 57859 * 2
def baseEnd_57859 : Nat := 29709477188594360096417

theorem tailTrace_57859 : CollatzResearch.WordTrace tailWord_57859 prefixEnd_57859 29709477188594360096417 := by
  unfold tailWord_57859
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110291097394199375600631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1406860731596132917067087 2110291097394199375600631)
  ·
    refine ⟨3165436646091299063400947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110291097394199375600631 3165436646091299063400947)
    ·
      refine ⟨4748154969136948595101421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165436646091299063400947 4748154969136948595101421)
      ·
        refine ⟨1780558113426355723163033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4748154969136948595101421 1780558113426355723163033)
        ·
          refine ⟨1335418585069766792372275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780558113426355723163033 1335418585069766792372275)
          ·
            refine ⟨2003127877604650188558413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335418585069766792372275 2003127877604650188558413)
            ·
              refine ⟨751172954101743820709405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2003127877604650188558413 751172954101743820709405)
              ·
                refine ⟨281689857788153932766027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 751172954101743820709405 281689857788153932766027)
                ·
                  refine ⟨422534786682230899149041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281689857788153932766027 422534786682230899149041)
                  ·
                    refine ⟨316901090011673174361781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 422534786682230899149041 316901090011673174361781)
                    ·
                      refine ⟨29709477188594360096417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 316901090011673174361781 29709477188594360096417)
                      ·
                        rfl

theorem cell23_57859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_57859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57859 prefixEnd_57859 := by exact prefixLift 57859
  have htrace : WordTrace (prefixWord ++ tailWord_57859) baseStart_57859 baseEnd_57859 := by
    simpa [prefixWord, tailWord_57859, baseEnd_57859] using wordTrace_append hprefix tailTrace_57859
  have hstable : (prefixWord ++ tailWord_57859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57859).length < 2 ^ (prefixWord ++ tailWord_57859).sum := by decide
  have hdescent : baseEnd_57859 < baseStart_57859 := by decide
  rcases family_descends (prefixWord ++ tailWord_57859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57863 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_57863 : Nat := 118140960795 + 57863 * 2 ^ 59
def prefixEnd_57863 : Nat := 4983230072969 + 3 ^ 40 * 57863 * 2
def baseEnd_57863 : Nat := 29711531111212344446399

theorem tailTrace_57863 : CollatzResearch.WordTrace tailWord_57863 prefixEnd_57863 29711531111212344446399 := by
  unfold tailWord_57863
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110436989379708058746243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1406957992919805372497495 2110436989379708058746243)
  ·
    refine ⟨3165655484069562088119365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110436989379708058746243 3165655484069562088119365)
    ·
      refine ⟨593560403263042891522381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3165655484069562088119365 593560403263042891522381)
      ·
        refine ⟨222585151223641084320893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593560403263042891522381 222585151223641084320893)
        ·
          refine ⟨83469431708865406620335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222585151223641084320893 83469431708865406620335)
          ·
            refine ⟨125204147563298109930503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83469431708865406620335 125204147563298109930503)
            ·
              refine ⟨187806221344947164895755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125204147563298109930503 187806221344947164895755)
              ·
                refine ⟨281709332017420747343633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187806221344947164895755 281709332017420747343633)
                ·
                  refine ⟨211281999013065560507725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281709332017420747343633 211281999013065560507725)
                  ·
                    refine ⟨79230749629899585190397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211281999013065560507725 79230749629899585190397)
                    ·
                      refine ⟨29711531111212344446399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 79230749629899585190397 29711531111212344446399)
                      ·
                        rfl

theorem cell23_57863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_57863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57863 prefixEnd_57863 := by exact prefixLift 57863
  have htrace : WordTrace (prefixWord ++ tailWord_57863) baseStart_57863 baseEnd_57863 := by
    simpa [prefixWord, tailWord_57863, baseEnd_57863] using wordTrace_append hprefix tailTrace_57863
  have hstable : (prefixWord ++ tailWord_57863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57863).length < 2 ^ (prefixWord ++ tailWord_57863).sum := by decide
  have hdescent : baseEnd_57863 < baseStart_57863 := by decide
  rcases family_descends (prefixWord ++ tailWord_57863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57899 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4]
def baseStart_57899 : Nat := 118140960795 + 57899 * 2 ^ 59
def prefixEnd_57899 : Nat := 4983230072969 + 3 ^ 40 * 57899 * 2
def baseEnd_57899 : Nat := 29730016414774203596233

theorem tailTrace_57899 : CollatzResearch.WordTrace tailWord_57899 prefixEnd_57899 29730016414774203596233 := by
  unfold tailWord_57899
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111750017249286207056751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1407833344832857471371167 2111750017249286207056751)
  ·
    refine ⟨3167625025873929310585127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111750017249286207056751 3167625025873929310585127)
    ·
      refine ⟨4751437538810893965877691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167625025873929310585127 4751437538810893965877691)
      ·
        refine ⟨7127156308216340948816537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4751437538810893965877691 7127156308216340948816537)
        ·
          refine ⟨5345367231162255711612403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7127156308216340948816537 5345367231162255711612403)
          ·
            refine ⟨8018050846743383567418605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345367231162255711612403 8018050846743383567418605)
            ·
              refine ⟨3006769067528768837781977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8018050846743383567418605 3006769067528768837781977)
              ·
                refine ⟨2255076800646576628336483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006769067528768837781977 2255076800646576628336483)
                ·
                  refine ⟨3382615200969864942504725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255076800646576628336483 3382615200969864942504725)
                  ·
                    refine ⟨158560087545462419179909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3382615200969864942504725 158560087545462419179909)
                    ·
                      refine ⟨29730016414774203596233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 158560087545462419179909 29730016414774203596233)
                      ·
                        rfl

theorem cell23_57899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_57899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57899 prefixEnd_57899 := by exact prefixLift 57899
  have htrace : WordTrace (prefixWord ++ tailWord_57899) baseStart_57899 baseEnd_57899 := by
    simpa [prefixWord, tailWord_57899, baseEnd_57899] using wordTrace_append hprefix tailTrace_57899
  have hstable : (prefixWord ++ tailWord_57899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57899).length < 2 ^ (prefixWord ++ tailWord_57899).sum := by decide
  have hdescent : baseEnd_57899 < baseStart_57899 := by decide
  rcases family_descends (prefixWord ++ tailWord_57899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57913 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 3, 4]
def baseStart_57913 : Nat := 118140960795 + 57913 * 2 ^ 59
def prefixEnd_57913 : Nat := 4983230072969 + 3 ^ 40 * 57913 * 2
def baseEnd_57913 : Nat := 9912401714645716273723

theorem tailTrace_57913 : CollatzResearch.WordTrace tailWord_57913 prefixEnd_57913 9912401714645716273723 := by
  unfold tailWord_57913
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112260639198566598066393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1408173759465711065377595 2112260639198566598066393)
  ·
    refine ⟨1584195479398924948549795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2112260639198566598066393 1584195479398924948549795)
    ·
      refine ⟨2376293219098387422824693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584195479398924948549795 2376293219098387422824693)
      ·
        refine ⟨222777489290473820889815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2376293219098387422824693 222777489290473820889815)
        ·
          refine ⟨334166233935710731334723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222777489290473820889815 334166233935710731334723)
          ·
            refine ⟨501249350903566097002085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334166233935710731334723 501249350903566097002085)
            ·
              refine ⟨93984253294418643187891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 501249350903566097002085 93984253294418643187891)
              ·
                refine ⟨140976379941627964781837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93984253294418643187891 140976379941627964781837)
                ·
                  refine ⟨52866142478110486793189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140976379941627964781837 52866142478110486793189)
                  ·
                    refine ⟨9912401714645716273723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52866142478110486793189 9912401714645716273723)
                    ·
                      rfl

theorem cell23_57913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_57913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57913 prefixEnd_57913 := by exact prefixLift 57913
  have htrace : WordTrace (prefixWord ++ tailWord_57913) baseStart_57913 baseEnd_57913 := by
    simpa [prefixWord, tailWord_57913, baseEnd_57913] using wordTrace_append hprefix tailTrace_57913
  have hstable : (prefixWord ++ tailWord_57913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57913).length < 2 ^ (prefixWord ++ tailWord_57913).sum := by decide
  have hdescent : baseEnd_57913 < baseStart_57913 := by decide
  rcases family_descends (prefixWord ++ tailWord_57913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57976 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_57976 : Nat := 118140960795 + 57976 * 2 ^ 59
def prefixEnd_57976 : Nat := 4983230072969 + 3 ^ 40 * 57976 * 2
def baseEnd_57976 : Nat := 29769554425170402333379

theorem tailTrace_57976 : CollatzResearch.WordTrace tailWord_57976 prefixEnd_57976 29769554425170402333379 := by
  unfold tailWord_57976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057279218985164178804891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1409705625313552238406521 1057279218985164178804891)
  ·
    refine ⟨1585918828477746268207337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057279218985164178804891 1585918828477746268207337)
    ·
      refine ⟨1189439121358309701155503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1585918828477746268207337 1189439121358309701155503)
      ·
        refine ⟨1784158682037464551733255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189439121358309701155503 1784158682037464551733255)
        ·
          refine ⟨2676238023056196827599883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784158682037464551733255 2676238023056196827599883)
          ·
            refine ⟨4014357034584295241399825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676238023056196827599883 4014357034584295241399825)
            ·
              refine ⟨3010767775938221431049869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014357034584295241399825 3010767775938221431049869)
              ·
                refine ⟨1129037915976833036643701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3010767775938221431049869 1129037915976833036643701)
                ·
                  refine ⟨105847304622828097185347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1129037915976833036643701 105847304622828097185347)
                  ·
                    refine ⟨158770956934242145778021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105847304622828097185347 158770956934242145778021)
                    ·
                      refine ⟨29769554425170402333379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 158770956934242145778021 29769554425170402333379)
                      ·
                        rfl

theorem cell23_57976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_57976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_57976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_57976 prefixEnd_57976 := by exact prefixLift 57976
  have htrace : WordTrace (prefixWord ++ tailWord_57976) baseStart_57976 baseEnd_57976 := by
    simpa [prefixWord, tailWord_57976, baseEnd_57976] using wordTrace_append hprefix tailTrace_57976
  have hstable : (prefixWord ++ tailWord_57976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57976).length < 2 ^ (prefixWord ++ tailWord_57976).sum := by decide
  have hdescent : baseEnd_57976 < baseStart_57976 := by decide
  rcases family_descends (prefixWord ++ tailWord_57976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58013 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_58013 : Nat := 118140960795 + 58013 * 2 ^ 59
def prefixEnd_58013 : Nat := 4983230072969 + 3 ^ 40 * 58013 * 2
def baseEnd_58013 : Nat := 29788553209386757570709

theorem tailTrace_58013 : CollatzResearch.WordTrace tailWord_58013 prefixEnd_58013 29788553209386757570709 := by
  unfold tailWord_58013
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115907938836283676706693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1410605292557522451137795 2115907938836283676706693)
  ·
    refine ⟨396732738531803189382505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2115907938836283676706693 396732738531803189382505)
    ·
      refine ⟨297549553898852392036879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396732738531803189382505 297549553898852392036879)
      ·
        refine ⟨446324330848278588055319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297549553898852392036879 446324330848278588055319)
        ·
          refine ⟨669486496272417882082979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446324330848278588055319 669486496272417882082979)
          ·
            refine ⟨1004229744408626823124469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669486496272417882082979 1004229744408626823124469)
            ·
              refine ⟨94146538538308764667919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1004229744408626823124469 94146538538308764667919)
              ·
                refine ⟨141219807807463147001879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94146538538308764667919 141219807807463147001879)
                ·
                  refine ⟨211829711711194720502819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141219807807463147001879 211829711711194720502819)
                  ·
                    refine ⟨317744567566792080754229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211829711711194720502819 317744567566792080754229)
                    ·
                      refine ⟨29788553209386757570709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 317744567566792080754229 29788553209386757570709)
                      ·
                        rfl

theorem cell23_58013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_58013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58013 prefixEnd_58013 := by exact prefixLift 58013
  have htrace : WordTrace (prefixWord ++ tailWord_58013) baseStart_58013 baseEnd_58013 := by
    simpa [prefixWord, tailWord_58013, baseEnd_58013] using wordTrace_append hprefix tailTrace_58013
  have hstable : (prefixWord ++ tailWord_58013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58013).length < 2 ^ (prefixWord ++ tailWord_58013).sum := by decide
  have hdescent : baseEnd_58013 < baseStart_58013 := by decide
  rcases family_descends (prefixWord ++ tailWord_58013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58016 : List Nat := [2, 1, 1, 4, 4, 11]
def baseStart_58016 : Nat := 118140960795 + 58016 * 2 ^ 59
def prefixEnd_58016 : Nat := 4983230072969 + 3 ^ 40 * 58016 * 2
def baseEnd_58016 : Nat := 122592977989095661865

theorem tailTrace_58016 : CollatzResearch.WordTrace tailWord_58016 prefixEnd_58016 122592977989095661865 := by
  unfold tailWord_58016
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058008678912707594532951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1410678238550276792710601 1058008678912707594532951)
  ·
    refine ⟨1587013018369061391799427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1058008678912707594532951 1587013018369061391799427)
    ·
      refine ⟨2380519527553592087699141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587013018369061391799427 2380519527553592087699141)
      ·
        refine ⟨446347411416298516443589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2380519527553592087699141 446347411416298516443589)
        ·
          refine ⟨83690139640555971833173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446347411416298516443589 83690139640555971833173)
          ·
            refine ⟨122592977989095661865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 83690139640555971833173 122592977989095661865)
            ·
              rfl

theorem cell23_58016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 11].length) (baseStart_58016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58016 prefixEnd_58016 := by exact prefixLift 58016
  have htrace : WordTrace (prefixWord ++ tailWord_58016) baseStart_58016 baseEnd_58016 := by
    simpa [prefixWord, tailWord_58016, baseEnd_58016] using wordTrace_append hprefix tailTrace_58016
  have hstable : (prefixWord ++ tailWord_58016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58016).length < 2 ^ (prefixWord ++ tailWord_58016).sum := by decide
  have hdescent : baseEnd_58016 < baseStart_58016 := by decide
  rcases family_descends (prefixWord ++ tailWord_58016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58020 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_58020 : Nat := 118140960795 + 58020 * 2 ^ 59
def prefixEnd_58020 : Nat := 4983230072969 + 3 ^ 40 * 58020 * 2
def baseEnd_58020 : Nat := 9930715857989410061059

theorem tailTrace_58020 : CollatzResearch.WordTrace tailWord_58020 prefixEnd_58020 9930715857989410061059 := by
  unfold tailWord_58020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058081624905461936105757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1410775499873949248141009 1058081624905461936105757)
  ·
    refine ⟨396780609339548226039659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1058081624905461936105757 396780609339548226039659)
    ·
      refine ⟨595170914009322339059489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396780609339548226039659 595170914009322339059489)
      ·
        refine ⟨446378185506991754294617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595170914009322339059489 446378185506991754294617)
        ·
          refine ⟨334783639130243815720963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446378185506991754294617 334783639130243815720963)
          ·
            refine ⟨502175458695365723581445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334783639130243815720963 502175458695365723581445)
            ·
              refine ⟨94157898505381073171521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502175458695365723581445 94157898505381073171521)
              ·
                refine ⟨70618423879035804878641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94157898505381073171521 70618423879035804878641)
                ·
                  refine ⟨52963817909276853658981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70618423879035804878641 52963817909276853658981)
                  ·
                    refine ⟨9930715857989410061059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52963817909276853658981 9930715857989410061059)
                    ·
                      rfl

theorem cell23_58020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_58020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58020 prefixEnd_58020 := by exact prefixLift 58020
  have htrace : WordTrace (prefixWord ++ tailWord_58020) baseStart_58020 baseEnd_58020 := by
    simpa [prefixWord, tailWord_58020, baseEnd_58020] using wordTrace_append hprefix tailTrace_58020
  have hstable : (prefixWord ++ tailWord_58020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58020).length < 2 ^ (prefixWord ++ tailWord_58020).sum := by decide
  have hdescent : baseEnd_58020 < baseStart_58020 := by decide
  rcases family_descends (prefixWord ++ tailWord_58020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58043 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 3]
def baseStart_58043 : Nat := 118140960795 + 58043 * 2 ^ 59
def prefixEnd_58043 : Nat := 4983230072969 + 3 ^ 40 * 58043 * 2
def baseEnd_58043 : Nat := 29803957629021640195571

theorem tailTrace_58043 : CollatzResearch.WordTrace tailWord_58043 prefixEnd_58043 29803957629021640195571 := by
  unfold tailWord_58043
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117002128727598800298783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1411334752485065866865855 2117002128727598800298783)
  ·
    refine ⟨3175503193091398200448175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2117002128727598800298783 3175503193091398200448175)
    ·
      refine ⟨4763254789637097300672263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3175503193091398200448175 4763254789637097300672263)
      ·
        refine ⟨7144882184455645951008395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763254789637097300672263 7144882184455645951008395)
        ·
          refine ⟨10717323276683468926512593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7144882184455645951008395 10717323276683468926512593)
          ·
            refine ⟨8037992457512601694884445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10717323276683468926512593 8037992457512601694884445)
            ·
              refine ⟨3014247171567225635581667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8037992457512601694884445 3014247171567225635581667)
              ·
                refine ⟨4521370757350838453372501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014247171567225635581667 4521370757350838453372501)
                ·
                  refine ⟨52984813562705138125459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4521370757350838453372501 52984813562705138125459)
                  ·
                    refine ⟨79477220344057707188189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52984813562705138125459 79477220344057707188189)
                    ·
                      refine ⟨29803957629021640195571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 79477220344057707188189 29803957629021640195571)
                      ·
                        rfl

theorem cell23_58043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 3].length) (baseStart_58043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58043 prefixEnd_58043 := by exact prefixLift 58043
  have htrace : WordTrace (prefixWord ++ tailWord_58043) baseStart_58043 baseEnd_58043 := by
    simpa [prefixWord, tailWord_58043, baseEnd_58043] using wordTrace_append hprefix tailTrace_58043
  have hstable : (prefixWord ++ tailWord_58043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58043).length < 2 ^ (prefixWord ++ tailWord_58043).sum := by decide
  have hdescent : baseEnd_58043 < baseStart_58043 := by decide
  rcases family_descends (prefixWord ++ tailWord_58043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58060 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_58060 : Nat := 118140960795 + 58060 * 2 ^ 59
def prefixEnd_58060 : Nat := 4983230072969 + 3 ^ 40 * 58060 * 2
def baseEnd_58060 : Nat := 29812686800148073682993

theorem tailTrace_58060 : CollatzResearch.WordTrace tailWord_58060 prefixEnd_58060 29812686800148073682993 := by
  unfold tailWord_58060
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058811084833005351833817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1411748113110673802445089 1058811084833005351833817)
  ·
    refine ⟨794108313624754013875363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1058811084833005351833817 794108313624754013875363)
    ·
      refine ⟨1191162470437131020813045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794108313624754013875363 1191162470437131020813045)
      ·
        refine ⟨111671481603481033201223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1191162470437131020813045 111671481603481033201223)
        ·
          refine ⟨167507222405221549801835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111671481603481033201223 167507222405221549801835)
          ·
            refine ⟨251260833607832324702753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167507222405221549801835 251260833607832324702753)
            ·
              refine ⟨188445625205874243527065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251260833607832324702753 188445625205874243527065)
              ·
                refine ⟨141334218904405682645299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188445625205874243527065 141334218904405682645299)
                ·
                  refine ⟨212001328356608523967949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141334218904405682645299 212001328356608523967949)
                  ·
                    refine ⟨79500498133728196487981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212001328356608523967949 79500498133728196487981)
                    ·
                      refine ⟨29812686800148073682993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 79500498133728196487981 29812686800148073682993)
                      ·
                        rfl

theorem cell23_58060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_58060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58060 prefixEnd_58060 := by exact prefixLift 58060
  have htrace : WordTrace (prefixWord ++ tailWord_58060) baseStart_58060 baseEnd_58060 := by
    simpa [prefixWord, tailWord_58060, baseEnd_58060] using wordTrace_append hprefix tailTrace_58060
  have hstable : (prefixWord ++ tailWord_58060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58060).length < 2 ^ (prefixWord ++ tailWord_58060).sum := by decide
  have hdescent : baseEnd_58060 < baseStart_58060 := by decide
  rcases family_descends (prefixWord ++ tailWord_58060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58061 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_58061 : Nat := 118140960795 + 58061 * 2 ^ 59
def prefixEnd_58061 : Nat := 4983230072969 + 3 ^ 40 * 58061 * 2
def baseEnd_58061 : Nat := 29813200280802569770489

theorem tailTrace_58061 : CollatzResearch.WordTrace tailWord_58061 prefixEnd_58061 29813200280802569770489 := by
  unfold tailWord_58061
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117658642662387874454037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1411772428441591916302691 2117658642662387874454037)
  ·
    refine ⟨99265248874799431615033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2117658642662387874454037 99265248874799431615033)
    ·
      refine ⟨74448936656099573711275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99265248874799431615033 74448936656099573711275)
      ·
        refine ⟨111673404984149360566913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74448936656099573711275 111673404984149360566913)
        ·
          refine ⟨83755053738112020425185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111673404984149360566913 83755053738112020425185)
          ·
            refine ⟨62816290303584015318889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83755053738112020425185 62816290303584015318889)
            ·
              refine ⟨47112217727688011489167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62816290303584015318889 47112217727688011489167)
              ·
                refine ⟨70668326591532017233751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47112217727688011489167 70668326591532017233751)
                ·
                  refine ⟨106002489887298025850627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70668326591532017233751 106002489887298025850627)
                  ·
                    refine ⟨159003734830947038775941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106002489887298025850627 159003734830947038775941)
                    ·
                      refine ⟨29813200280802569770489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 159003734830947038775941 29813200280802569770489)
                      ·
                        rfl

theorem cell23_58061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_58061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58061 prefixEnd_58061 := by exact prefixLift 58061
  have htrace : WordTrace (prefixWord ++ tailWord_58061) baseStart_58061 baseEnd_58061 := by
    simpa [prefixWord, tailWord_58061, baseEnd_58061] using wordTrace_append hprefix tailTrace_58061
  have hstable : (prefixWord ++ tailWord_58061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58061).length < 2 ^ (prefixWord ++ tailWord_58061).sum := by decide
  have hdescent : baseEnd_58061 < baseStart_58061 := by decide
  rcases family_descends (prefixWord ++ tailWord_58061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
