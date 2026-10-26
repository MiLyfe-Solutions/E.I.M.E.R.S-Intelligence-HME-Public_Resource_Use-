import V185TrunkScan23Chunk0530

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3139519 : List Nat := [1, 1, 2, 2, 2, 1, 3, 6, 1, 4]
def baseStart_3139519 : Nat := 118140960795 + 3139519 * 2 ^ 59
def prefixEnd_3139519 : Nat := 4983230072969 + 3 ^ 40 * 3139519 * 2
def baseEnd_3139519 : Nat := 537360756974335783724707

theorem tailTrace_3139519 : CollatzResearch.WordTrace tailWord_3139519 prefixEnd_3139519 537360756974335783724707 := by
  unfold tailWord_3139519
  simp only [CollatzResearch.WordTrace]
  refine ⟨114507665113066325002269611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76338443408710883334846407 114507665113066325002269611)
  ·
    refine ⟨171761497669599487503404417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114507665113066325002269611 171761497669599487503404417)
    ·
      refine ⟨128821123252199615627553313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171761497669599487503404417 128821123252199615627553313)
      ·
        refine ⟨96615842439149711720664985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128821123252199615627553313 96615842439149711720664985)
        ·
          refine ⟨72461881829362283790498739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96615842439149711720664985 72461881829362283790498739)
          ·
            refine ⟨108692822744043425685748109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72461881829362283790498739 108692822744043425685748109)
            ·
              refine ⟨40759808529016284632155541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108692822744043425685748109 40759808529016284632155541)
              ·
                refine ⟨1910616024797638342132291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40759808529016284632155541 1910616024797638342132291)
                ·
                  refine ⟨2865924037196457513198437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910616024797638342132291 2865924037196457513198437)
                  ·
                    refine ⟨537360756974335783724707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2865924037196457513198437 537360756974335783724707)
                    ·
                      rfl

theorem cell23_3139519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 4].length) (baseStart_3139519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139519 prefixEnd_3139519 := by exact prefixLift 3139519
  have htrace : WordTrace (prefixWord ++ tailWord_3139519) baseStart_3139519 baseEnd_3139519 := by
    simpa [prefixWord, tailWord_3139519, baseEnd_3139519] using wordTrace_append hprefix tailTrace_3139519
  have hstable : (prefixWord ++ tailWord_3139519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139519).length < 2 ^ (prefixWord ++ tailWord_3139519).sum := by decide
  have hdescent : baseEnd_3139519 < baseStart_3139519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139535 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_3139535 : Nat := 118140960795 + 3139535 * 2 ^ 59
def prefixEnd_3139535 : Nat := 4983230072969 + 3 ^ 40 * 3139535 * 2
def baseEnd_3139535 : Nat := 1612090486613479288574047

theorem tailTrace_3139535 : CollatzResearch.WordTrace tailWord_3139535 prefixEnd_3139535 1612090486613479288574047 := by
  unfold tailWord_3139535
  simp only [CollatzResearch.WordTrace]
  refine ⟨114508248681008359734852059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76338832454005573156568039 114508248681008359734852059)
  ·
    refine ⟨171762373021512539602278089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114508248681008359734852059 171762373021512539602278089)
    ·
      refine ⟨128821779766134404701708567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171762373021512539602278089 128821779766134404701708567)
      ·
        refine ⟨193232669649201607052562851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128821779766134404701708567 193232669649201607052562851)
        ·
          refine ⟨289849004473802410578844277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193232669649201607052562851 289849004473802410578844277)
          ·
            refine ⟨27173344169418975991766651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 289849004473802410578844277 27173344169418975991766651)
            ·
              refine ⟨40760016254128463987649977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27173344169418975991766651 40760016254128463987649977)
              ·
                refine ⟨30570012190596347990737483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40760016254128463987649977 30570012190596347990737483)
                ·
                  refine ⟨45855018285894521986106225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30570012190596347990737483 45855018285894521986106225)
                  ·
                    refine ⟨34391263714420891489579669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45855018285894521986106225 34391263714420891489579669)
                    ·
                      refine ⟨1612090486613479288574047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34391263714420891489579669 1612090486613479288574047)
                      ·
                        rfl

theorem cell23_3139535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_3139535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139535 prefixEnd_3139535 := by exact prefixLift 3139535
  have htrace : WordTrace (prefixWord ++ tailWord_3139535) baseStart_3139535 baseEnd_3139535 := by
    simpa [prefixWord, tailWord_3139535, baseEnd_3139535] using wordTrace_append hprefix tailTrace_3139535
  have hstable : (prefixWord ++ tailWord_3139535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139535).length < 2 ^ (prefixWord ++ tailWord_3139535).sum := by decide
  have hdescent : baseEnd_3139535 < baseStart_3139535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139576 : List Nat := [2, 1, 2, 1, 1, 3, 2, 6, 1, 1, 3]
def baseStart_3139576 : Nat := 118140960795 + 3139576 * 2 ^ 59
def prefixEnd_3139576 : Nat := 4983230072969 + 3 ^ 40 * 3139576 * 2
def baseEnd_3139576 : Nat := 1612111539320313628161359

theorem tailTrace_3139576 : CollatzResearch.WordTrace tailWord_3139576 prefixEnd_3139576 1612111539320313628161359 := by
  unfold tailWord_3139576
  simp only [CollatzResearch.WordTrace]
  refine ⟨57254872036929911868547291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76339829382573215824729721 57254872036929911868547291)
  ·
    refine ⟨85882308055394867802820937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57254872036929911868547291 85882308055394867802820937)
    ·
      refine ⟨64411731041546150852115703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85882308055394867802820937 64411731041546150852115703)
      ·
        refine ⟨96617596562319226278173555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64411731041546150852115703 96617596562319226278173555)
        ·
          refine ⟨144926394843478839417260333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96617596562319226278173555 144926394843478839417260333)
          ·
            refine ⟨54347398066304564781472625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144926394843478839417260333 54347398066304564781472625)
            ·
              refine ⟨40760548549728423586104469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54347398066304564781472625 40760548549728423586104469)
              ·
                refine ⟨1910650713268519855598647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40760548549728423586104469 1910650713268519855598647)
                ·
                  refine ⟨2865976069902779783397971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910650713268519855598647 2865976069902779783397971)
                  ·
                    refine ⟨4298964104854169675096957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2865976069902779783397971 4298964104854169675096957)
                    ·
                      refine ⟨1612111539320313628161359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298964104854169675096957 1612111539320313628161359)
                      ·
                        rfl

theorem cell23_3139576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_3139576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139576 prefixEnd_3139576 := by exact prefixLift 3139576
  have htrace : WordTrace (prefixWord ++ tailWord_3139576) baseStart_3139576 baseEnd_3139576 := by
    simpa [prefixWord, tailWord_3139576, baseEnd_3139576] using wordTrace_append hprefix tailTrace_3139576
  have hstable : (prefixWord ++ tailWord_3139576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139576).length < 2 ^ (prefixWord ++ tailWord_3139576).sum := by decide
  have hdescent : baseEnd_3139576 < baseStart_3139576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139592 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 1, 6]
def baseStart_3139592 : Nat := 118140960795 + 3139592 * 2 ^ 59
def prefixEnd_3139592 : Nat := 4983230072969 + 3 ^ 40 * 3139592 * 2
def baseEnd_3139592 : Nat := 537373251670261855187095

theorem tailTrace_3139592 : CollatzResearch.WordTrace tailWord_3139592 prefixEnd_3139592 537373251670261855187095 := by
  unfold tailWord_3139592
  simp only [CollatzResearch.WordTrace]
  refine ⟨57255163820900929234838515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76340218427867905646451353 57255163820900929234838515)
  ·
    refine ⟨85882745731351393852257773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57255163820900929234838515 85882745731351393852257773)
    ·
      refine ⟨32206029649256772694596665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85882745731351393852257773 32206029649256772694596665)
      ·
        refine ⟨24154522236942579520947499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32206029649256772694596665 24154522236942579520947499)
        ·
          refine ⟨36231783355413869281421249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24154522236942579520947499 36231783355413869281421249)
          ·
            refine ⟨27173837516560401961065937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36231783355413869281421249 27173837516560401961065937)
            ·
              refine ⟨20380378137420301470799453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27173837516560401961065937 20380378137420301470799453)
              ·
                refine ⟨7642641801532613051549795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20380378137420301470799453 7642641801532613051549795)
                ·
                  refine ⟨11463962702298919577324693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7642641801532613051549795 11463962702298919577324693)
                  ·
                    refine ⟨537373251670261855187095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11463962702298919577324693 537373251670261855187095)
                    ·
                      rfl

theorem cell23_3139592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_3139592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139592 prefixEnd_3139592 := by exact prefixLift 3139592
  have htrace : WordTrace (prefixWord ++ tailWord_3139592) baseStart_3139592 baseEnd_3139592 := by
    simpa [prefixWord, tailWord_3139592, baseEnd_3139592] using wordTrace_append hprefix tailTrace_3139592
  have hstable : (prefixWord ++ tailWord_3139592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139592).length < 2 ^ (prefixWord ++ tailWord_3139592).sum := by decide
  have hdescent : baseEnd_3139592 < baseStart_3139592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139626 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3139626 : Nat := 118140960795 + 3139626 * 2 ^ 59
def prefixEnd_3139626 : Nat := 4983230072969 + 3 ^ 40 * 3139626 * 2
def baseEnd_3139626 : Nat := 537379071117679477512043

theorem tailTrace_3139626 : CollatzResearch.WordTrace tailWord_3139626 prefixEnd_3139626 537379071117679477512043 := by
  unfold tailWord_3139626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28627891930919670569103683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76341045149119121517609821 28627891930919670569103683)
  ·
    refine ⟨42941837896379505853655525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28627891930919670569103683 42941837896379505853655525)
    ·
      refine ⟨8051594605571157347560411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42941837896379505853655525 8051594605571157347560411)
      ·
        refine ⟨12077391908356736021340617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8051594605571157347560411 12077391908356736021340617)
        ·
          refine ⟨9058043931267552016005463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12077391908356736021340617 9058043931267552016005463)
          ·
            refine ⟨13587065896901328024008195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058043931267552016005463 13587065896901328024008195)
            ·
              refine ⟨20380598845351992036012293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13587065896901328024008195 20380598845351992036012293)
              ·
                refine ⟨3821362283503498506752305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20380598845351992036012293 3821362283503498506752305)
                ·
                  refine ⟨2866021712627623880064229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3821362283503498506752305 2866021712627623880064229)
                  ·
                    refine ⟨537379071117679477512043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2866021712627623880064229 537379071117679477512043)
                    ·
                      rfl

theorem cell23_3139626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3139626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139626 prefixEnd_3139626 := by exact prefixLift 3139626
  have htrace : WordTrace (prefixWord ++ tailWord_3139626) baseStart_3139626 baseEnd_3139626 := by
    simpa [prefixWord, tailWord_3139626, baseEnd_3139626] using wordTrace_append hprefix tailTrace_3139626
  have hstable : (prefixWord ++ tailWord_3139626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139626).length < 2 ^ (prefixWord ++ tailWord_3139626).sum := by decide
  have hdescent : baseEnd_3139626 < baseStart_3139626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139670 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3139670 : Nat := 118140960795 + 3139670 * 2 ^ 59
def prefixEnd_3139670 : Nat := 4983230072969 + 3 ^ 40 * 3139670 * 2
def baseEnd_3139670 : Nat := 1612159806501836260385927

theorem tailTrace_3139670 : CollatzResearch.WordTrace tailWord_3139670 prefixEnd_3139670 1612159806501836260385927 := by
  unfold tailWord_3139670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157073283469954861938529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76342115023679518527344309 7157073283469954861938529)
  ·
    refine ⟨5367804962602466146453897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7157073283469954861938529 5367804962602466146453897)
    ·
      refine ⟨4025853721951849609840423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5367804962602466146453897 4025853721951849609840423)
      ·
        refine ⟨6038780582927774414760635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025853721951849609840423 6038780582927774414760635)
        ·
          refine ⟨9058170874391661622140953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038780582927774414760635 9058170874391661622140953)
          ·
            refine ⟨6793628155793746216605715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058170874391661622140953 6793628155793746216605715)
            ·
              refine ⟨10190442233690619324908573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793628155793746216605715 10190442233690619324908573)
              ·
                refine ⟨3821415837633982246840715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10190442233690619324908573 3821415837633982246840715)
                ·
                  refine ⟨5732123756450973370261073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821415837633982246840715 5732123756450973370261073)
                  ·
                    refine ⟨4299092817338230027695805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732123756450973370261073 4299092817338230027695805)
                    ·
                      refine ⟨1612159806501836260385927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299092817338230027695805 1612159806501836260385927)
                      ·
                        rfl

theorem cell23_3139670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3139670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139670 prefixEnd_3139670 := by exact prefixLift 3139670
  have htrace : WordTrace (prefixWord ++ tailWord_3139670) baseStart_3139670 baseEnd_3139670 := by
    simpa [prefixWord, tailWord_3139670, baseEnd_3139670] using wordTrace_append hprefix tailTrace_3139670
  have hstable : (prefixWord ++ tailWord_3139670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139670).length < 2 ^ (prefixWord ++ tailWord_3139670).sum := by decide
  have hdescent : baseEnd_3139670 < baseStart_3139670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139726 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3139726 : Nat := 118140960795 + 3139726 * 2 ^ 59
def prefixEnd_3139726 : Nat := 4983230072969 + 3 ^ 40 * 3139726 * 2
def baseEnd_3139726 : Nat := 1612188561418488041285669

theorem tailTrace_3139726 : CollatzResearch.WordTrace tailWord_3139726 prefixEnd_3139726 1612188561418488041285669 := by
  unfold tailWord_3139726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314401877914549919381879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76343476682210932903370021 14314401877914549919381879)
  ·
    refine ⟨21471602816871824879072819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14314401877914549919381879 21471602816871824879072819)
    ·
      refine ⟨32207404225307737318609229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21471602816871824879072819 32207404225307737318609229)
      ·
        refine ⟨12077776584490401494478461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32207404225307737318609229 12077776584490401494478461)
        ·
          refine ⟨4529166219183900560429423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12077776584490401494478461 4529166219183900560429423)
          ·
            refine ⟨6793749328775850840644135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529166219183900560429423 6793749328775850840644135)
            ·
              refine ⟨10190623993163776260966203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793749328775850840644135 10190623993163776260966203)
              ·
                refine ⟨15285935989745664391449305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190623993163776260966203 15285935989745664391449305)
                ·
                  refine ⟨11464451992309248293586979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15285935989745664391449305 11464451992309248293586979)
                  ·
                    refine ⟨17196677988463872440380469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11464451992309248293586979 17196677988463872440380469)
                    ·
                      refine ⟨1612188561418488041285669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17196677988463872440380469 1612188561418488041285669)
                      ·
                        rfl

theorem cell23_3139726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3139726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139726 prefixEnd_3139726 := by exact prefixLift 3139726
  have htrace : WordTrace (prefixWord ++ tailWord_3139726) baseStart_3139726 baseEnd_3139726 := by
    simpa [prefixWord, tailWord_3139726, baseEnd_3139726] using wordTrace_append hprefix tailTrace_3139726
  have hstable : (prefixWord ++ tailWord_3139726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139726).length < 2 ^ (prefixWord ++ tailWord_3139726).sum := by decide
  have hdescent : baseEnd_3139726 < baseStart_3139726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139746 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 7]
def baseStart_3139746 : Nat := 118140960795 + 3139746 * 2 ^ 59
def prefixEnd_3139746 : Nat := 4983230072969 + 3 ^ 40 * 3139746 * 2
def baseEnd_3139746 : Nat := 179133203447953107003953

theorem tailTrace_3139746 : CollatzResearch.WordTrace tailWord_3139746 prefixEnd_3139746 179133203447953107003953 := by
  unfold tailWord_3139746
  simp only [CollatzResearch.WordTrace]
  refine ⟨28628986120810985692695773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76343962988829295180522061 28628986120810985692695773)
  ·
    refine ⟨10735869795304119634760915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28628986120810985692695773 10735869795304119634760915)
    ·
      refine ⟨16103804692956179452141373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10735869795304119634760915 16103804692956179452141373)
      ·
        refine ⟨6038926759858567294553015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16103804692956179452141373 6038926759858567294553015)
        ·
          refine ⟨9058390139787850941829523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038926759858567294553015 9058390139787850941829523)
          ·
            refine ⟨13587585209681776412744285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058390139787850941829523 13587585209681776412744285)
            ·
              refine ⟨5095344453630666154779107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13587585209681776412744285 5095344453630666154779107)
              ·
                refine ⟨7643016680445999232168661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095344453630666154779107 7643016680445999232168661)
                ·
                  refine ⟨179133203447953107003953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7643016680445999232168661 179133203447953107003953)
                  ·
                    rfl

theorem cell23_3139746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_3139746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139746 prefixEnd_3139746 := by exact prefixLift 3139746
  have htrace : WordTrace (prefixWord ++ tailWord_3139746) baseStart_3139746 baseEnd_3139746 := by
    simpa [prefixWord, tailWord_3139746, baseEnd_3139746] using wordTrace_append hprefix tailTrace_3139746
  have hstable : (prefixWord ++ tailWord_3139746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139746).length < 2 ^ (prefixWord ++ tailWord_3139746).sum := by decide
  have hdescent : baseEnd_3139746 < baseStart_3139746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139757 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_3139757 : Nat := 118140960795 + 3139757 * 2 ^ 59
def prefixEnd_3139757 : Nat := 4983230072969 + 3 ^ 40 * 3139757 * 2
def baseEnd_3139757 : Nat := 1612204479318777419998027

theorem tailTrace_3139757 : CollatzResearch.WordTrace tailWord_3139757 prefixEnd_3139757 1612204479318777419998027 := by
  unfold tailWord_3139757
  simp only [CollatzResearch.WordTrace]
  refine ⟨114516345686204091649433525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76344230457469394432955683 114516345686204091649433525)
  ·
    refine ⟨10735907408081633592134393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114516345686204091649433525 10735907408081633592134393)
    ·
      refine ⟨8051930556061225194100795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10735907408081633592134393 8051930556061225194100795)
      ·
        refine ⟨12077895834091837791151193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8051930556061225194100795 12077895834091837791151193)
        ·
          refine ⟨9058421875568878343363395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12077895834091837791151193 9058421875568878343363395)
          ·
            refine ⟨13587632813353317515045093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058421875568878343363395 13587632813353317515045093)
            ·
              refine ⟨2547681152503747034070955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13587632813353317515045093 2547681152503747034070955)
              ·
                refine ⟨3821521728755620551106433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547681152503747034070955 3821521728755620551106433)
                ·
                  refine ⟨2866141296566715413329825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3821521728755620551106433 2866141296566715413329825)
                  ·
                    refine ⟨2149605972425036559997369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866141296566715413329825 2149605972425036559997369)
                    ·
                      refine ⟨1612204479318777419998027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149605972425036559997369 1612204479318777419998027)
                      ·
                        rfl

theorem cell23_3139757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_3139757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139757 prefixEnd_3139757 := by exact prefixLift 3139757
  have htrace : WordTrace (prefixWord ++ tailWord_3139757) baseStart_3139757 baseEnd_3139757 := by
    simpa [prefixWord, tailWord_3139757, baseEnd_3139757] using wordTrace_append hprefix tailTrace_3139757
  have hstable : (prefixWord ++ tailWord_3139757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139757).length < 2 ^ (prefixWord ++ tailWord_3139757).sum := by decide
  have hdescent : baseEnd_3139757 < baseStart_3139757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139776 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 2, 5]
def baseStart_3139776 : Nat := 118140960795 + 3139776 * 2 ^ 59
def prefixEnd_3139776 : Nat := 4983230072969 + 3 ^ 40 * 3139776 * 2
def baseEnd_3139776 : Nat := 537404745150404281886813

theorem tailTrace_3139776 : CollatzResearch.WordTrace tailWord_3139776 prefixEnd_3139776 537404745150404281886813 := by
  unfold tailWord_3139776
  simp only [CollatzResearch.WordTrace]
  refine ⟨57258519336567628947187591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76344692448756838596250121 57258519336567628947187591)
  ·
    refine ⟨85887779004851443420781387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57258519336567628947187591 85887779004851443420781387)
    ·
      refine ⟨128831668507277165131172081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85887779004851443420781387 128831668507277165131172081)
      ·
        refine ⟨96623751380457873848379061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128831668507277165131172081 96623751380457873848379061)
        ·
          refine ⟨9058476691917925673285537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96623751380457873848379061 9058476691917925673285537)
          ·
            refine ⟨6793857518938444254964153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058476691917925673285537 6793857518938444254964153)
            ·
              refine ⟨5095393139203833191223115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6793857518938444254964153 5095393139203833191223115)
              ·
                refine ⟨7643089708805749786834673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095393139203833191223115 7643089708805749786834673)
                ·
                  refine ⟨5732317281604312340126005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7643089708805749786834673 5732317281604312340126005)
                  ·
                    refine ⟨537404745150404281886813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5732317281604312340126005 537404745150404281886813)
                    ·
                      rfl

theorem cell23_3139776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_3139776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139776 prefixEnd_3139776 := by exact prefixLift 3139776
  have htrace : WordTrace (prefixWord ++ tailWord_3139776) baseStart_3139776 baseEnd_3139776 := by
    simpa [prefixWord, tailWord_3139776, baseEnd_3139776] using wordTrace_append hprefix tailTrace_3139776
  have hstable : (prefixWord ++ tailWord_3139776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139776).length < 2 ^ (prefixWord ++ tailWord_3139776).sum := by decide
  have hdescent : baseEnd_3139776 < baseStart_3139776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139797 : List Nat := [1, 3, 2, 4, 3, 1, 2, 2, 5]
def baseStart_3139797 : Nat := 118140960795 + 3139797 * 2 ^ 59
def prefixEnd_3139797 : Nat := 4983230072969 + 3 ^ 40 * 3139797 * 2
def baseEnd_3139797 : Nat := 179136113171661918166427

theorem tailTrace_3139797 : CollatzResearch.WordTrace tailWord_3139797 prefixEnd_3139797 179136113171661918166427 := by
  unfold tailWord_3139797
  simp only [CollatzResearch.WordTrace]
  refine ⟨114517804606059178480889645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76345203070706118987259763 114517804606059178480889645)
  ·
    refine ⟨42944176727272191930333617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114517804606059178480889645 42944176727272191930333617)
    ·
      refine ⟨32208132545454143947750213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42944176727272191930333617 32208132545454143947750213)
      ·
        refine ⟨6039024852272651990203165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32208132545454143947750213 6039024852272651990203165)
        ·
          refine ⟨2264634319602244496326187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6039024852272651990203165 2264634319602244496326187)
          ·
            refine ⟨3396951479403366744489281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264634319602244496326187 3396951479403366744489281)
            ·
              refine ⟨2547713609552525058366961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396951479403366744489281 2547713609552525058366961)
              ·
                refine ⟨1910785207164393793775221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547713609552525058366961 1910785207164393793775221)
                ·
                  refine ⟨179136113171661918166427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910785207164393793775221 179136113171661918166427)
                  ·
                    rfl

theorem cell23_3139797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_3139797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139797 prefixEnd_3139797 := by exact prefixLift 3139797
  have htrace : WordTrace (prefixWord ++ tailWord_3139797) baseStart_3139797 baseEnd_3139797 := by
    simpa [prefixWord, tailWord_3139797, baseEnd_3139797] using wordTrace_append hprefix tailTrace_3139797
  have hstable : (prefixWord ++ tailWord_3139797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139797).length < 2 ^ (prefixWord ++ tailWord_3139797).sum := by decide
  have hdescent : baseEnd_3139797 < baseStart_3139797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139799 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_3139799 : Nat := 118140960795 + 3139799 * 2 ^ 59
def prefixEnd_3139799 : Nat := 4983230072969 + 3 ^ 40 * 3139799 * 2
def baseEnd_3139799 : Nat := 1612226045506266255672833

theorem tailTrace_3139799 : CollatzResearch.WordTrace tailWord_3139799 prefixEnd_3139799 1612226045506266255672833 := by
  unfold tailWord_3139799
  simp only [CollatzResearch.WordTrace]
  refine ⟨114517877552051932822462451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76345251701367955214974967 114517877552051932822462451)
  ·
    refine ⟨171776816328077899233693677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114517877552051932822462451 171776816328077899233693677)
    ·
      refine ⟨64416306123029212212635129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171776816328077899233693677 64416306123029212212635129)
      ·
        refine ⟨48312229592271909159476347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64416306123029212212635129 48312229592271909159476347)
        ·
          refine ⟨72468344388407863739214521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48312229592271909159476347 72468344388407863739214521)
          ·
            refine ⟨54351258291305897804410891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72468344388407863739214521 54351258291305897804410891)
            ·
              refine ⟨81526887436958846706616337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54351258291305897804410891 81526887436958846706616337)
              ·
                refine ⟨61145165577719135029962253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81526887436958846706616337 61145165577719135029962253)
                ·
                  refine ⟨22929437091644675636235845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61145165577719135029962253 22929437091644675636235845)
                  ·
                    refine ⟨4299269454683376681794221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22929437091644675636235845 4299269454683376681794221)
                    ·
                      refine ⟨1612226045506266255672833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299269454683376681794221 1612226045506266255672833)
                      ·
                        rfl

theorem cell23_3139799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_3139799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139799 prefixEnd_3139799 := by exact prefixLift 3139799
  have htrace : WordTrace (prefixWord ++ tailWord_3139799) baseStart_3139799 baseEnd_3139799 := by
    simpa [prefixWord, tailWord_3139799, baseEnd_3139799] using wordTrace_append hprefix tailTrace_3139799
  have hstable : (prefixWord ++ tailWord_3139799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139799).length < 2 ^ (prefixWord ++ tailWord_3139799).sum := by decide
  have hdescent : baseEnd_3139799 < baseStart_3139799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139813 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 2, 4, 2]
def baseStart_3139813 : Nat := 118140960795 + 3139813 * 2 ^ 59
def prefixEnd_3139813 : Nat := 4983230072969 + 3 ^ 40 * 3139813 * 2
def baseEnd_3139813 : Nat := 1612233234235429200897769

theorem tailTrace_3139813 : CollatzResearch.WordTrace tailWord_3139813 prefixEnd_3139813 1612233234235429200897769 := by
  unfold tailWord_3139813
  simp only [CollatzResearch.WordTrace]
  refine ⟨114518388174001213213472093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76345592116000808808981395 114518388174001213213472093)
  ·
    refine ⟨42944395565250454955052035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114518388174001213213472093 42944395565250454955052035)
    ·
      refine ⟨64416593347875682432578053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42944395565250454955052035 64416593347875682432578053)
      ·
        refine ⟨12078111252726690456108385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64416593347875682432578053 12078111252726690456108385)
        ·
          refine ⟨9058583439545017842081289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12078111252726690456108385 9058583439545017842081289)
          ·
            refine ⟨6793937579658763381560967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058583439545017842081289 6793937579658763381560967)
            ·
              refine ⟨10190906369488145072341451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793937579658763381560967 10190906369488145072341451)
              ·
                refine ⟨15286359554232217608512177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190906369488145072341451 15286359554232217608512177)
                ·
                  refine ⟨11464769665674163206384133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15286359554232217608512177 11464769665674163206384133)
                  ·
                    refine ⟨2149644312313905601197025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11464769665674163206384133 2149644312313905601197025)
                    ·
                      refine ⟨1612233234235429200897769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149644312313905601197025 1612233234235429200897769)
                      ·
                        rfl

theorem cell23_3139813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_3139813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139813 prefixEnd_3139813 := by exact prefixLift 3139813
  have htrace : WordTrace (prefixWord ++ tailWord_3139813) baseStart_3139813 baseEnd_3139813 := by
    simpa [prefixWord, tailWord_3139813, baseEnd_3139813] using wordTrace_append hprefix tailTrace_3139813
  have hstable : (prefixWord ++ tailWord_3139813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139813).length < 2 ^ (prefixWord ++ tailWord_3139813).sum := by decide
  have hdescent : baseEnd_3139813 < baseStart_3139813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139819 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 6]
def baseStart_3139819 : Nat := 118140960795 + 3139819 * 2 ^ 59
def prefixEnd_3139819 : Nat := 4983230072969 + 3 ^ 40 * 3139819 * 2
def baseEnd_3139819 : Nat := 179137368346595130824749

theorem tailTrace_3139819 : CollatzResearch.WordTrace tailWord_3139819 prefixEnd_3139819 179137368346595130824749 := by
  unfold tailWord_3139819
  simp only [CollatzResearch.WordTrace]
  refine ⟨114518607011979476238190511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76345738007986317492127007 114518607011979476238190511)
  ·
    refine ⟨171777910517969214357285767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114518607011979476238190511 171777910517969214357285767)
    ·
      refine ⟨257666865776953821535928651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171777910517969214357285767 257666865776953821535928651)
      ·
        refine ⟨386500298665430732303892977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257666865776953821535928651 386500298665430732303892977)
        ·
          refine ⟨289875223999073049227919733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386500298665430732303892977 289875223999073049227919733)
          ·
            refine ⟨27175802249913098365117475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 289875223999073049227919733 27175802249913098365117475)
            ·
              refine ⟨40763703374869647547676213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27175802249913098365117475 40763703374869647547676213)
              ·
                refine ⟨3821597191394029457594645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40763703374869647547676213 3821597191394029457594645)
                ·
                  refine ⟨179137368346595130824749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3821597191394029457594645 179137368346595130824749)
                  ·
                    rfl

theorem cell23_3139819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 6].length) (baseStart_3139819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139819 prefixEnd_3139819 := by exact prefixLift 3139819
  have htrace : WordTrace (prefixWord ++ tailWord_3139819) baseStart_3139819 baseEnd_3139819 := by
    simpa [prefixWord, tailWord_3139819, baseEnd_3139819] using wordTrace_append hprefix tailTrace_3139819
  have hstable : (prefixWord ++ tailWord_3139819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139819).length < 2 ^ (prefixWord ++ tailWord_3139819).sum := by decide
  have hdescent : baseEnd_3139819 < baseStart_3139819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139863 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3139863 : Nat := 118140960795 + 3139863 * 2 ^ 59
def prefixEnd_3139863 : Nat := 4983230072969 + 3 ^ 40 * 3139863 * 2
def baseEnd_3139863 : Nat := 1612258908268154005272539

theorem tailTrace_3139863 : CollatzResearch.WordTrace tailWord_3139863 prefixEnd_3139863 1612258908268154005272539 := by
  unfold tailWord_3139863
  simp only [CollatzResearch.WordTrace]
  refine ⟨114520211823820071752792243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76346807882546714501861495 114520211823820071752792243)
  ·
    refine ⟨171780317735730107629188365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114520211823820071752792243 171780317735730107629188365)
    ·
      refine ⟨64417619150898790360945637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171780317735730107629188365 64417619150898790360945637)
      ·
        refine ⟨12078303590793523192677307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64417619150898790360945637 12078303590793523192677307)
        ·
          refine ⟨18117455386190284789015961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12078303590793523192677307 18117455386190284789015961)
          ·
            refine ⟨13588091539642713591761971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18117455386190284789015961 13588091539642713591761971)
            ·
              refine ⟨20382137309464070387642957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13588091539642713591761971 20382137309464070387642957)
              ·
                refine ⟨7643301491049026395366109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20382137309464070387642957 7643301491049026395366109)
                ·
                  refine ⟨2866238059143384898262291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7643301491049026395366109 2866238059143384898262291)
                  ·
                    refine ⟨4299357088715077347393437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2866238059143384898262291 4299357088715077347393437)
                    ·
                      refine ⟨1612258908268154005272539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299357088715077347393437 1612258908268154005272539)
                      ·
                        rfl

theorem cell23_3139863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3139863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139863 prefixEnd_3139863 := by exact prefixLift 3139863
  have htrace : WordTrace (prefixWord ++ tailWord_3139863) baseStart_3139863 baseEnd_3139863 := by
    simpa [prefixWord, tailWord_3139863, baseEnd_3139863] using wordTrace_append hprefix tailTrace_3139863
  have hstable : (prefixWord ++ tailWord_3139863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139863).length < 2 ^ (prefixWord ++ tailWord_3139863).sum := by decide
  have hdescent : baseEnd_3139863 < baseStart_3139863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139896 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 4, 4]
def baseStart_3139896 : Nat := 118140960795 + 3139896 * 2 ^ 59
def prefixEnd_3139896 : Nat := 4983230072969 + 3 ^ 40 * 3139896 * 2
def baseEnd_3139896 : Nat := 537425284376584125386629

theorem tailTrace_3139896 : CollatzResearch.WordTrace tailWord_3139896 prefixEnd_3139896 537425284376584125386629 := by
  unfold tailWord_3139896
  simp only [CollatzResearch.WordTrace]
  refine ⟨57260707716350259194371771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76347610288467012259162361 57260707716350259194371771)
  ·
    refine ⟨85891061574525388791557657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57260707716350259194371771 85891061574525388791557657)
    ·
      refine ⟨64418296180894041593668243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85891061574525388791557657 64418296180894041593668243)
      ·
        refine ⟨96627444271341062390502365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64418296180894041593668243 96627444271341062390502365)
        ·
          refine ⟨36235291601752898396438387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96627444271341062390502365 36235291601752898396438387)
          ·
            refine ⟨54352937402629347594657581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36235291601752898396438387 54352937402629347594657581)
            ·
              refine ⟨20382351525986005347996593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54352937402629347594657581 20382351525986005347996593)
              ·
                refine ⟨15286763644489504010997445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20382351525986005347996593 15286763644489504010997445)
                ·
                  refine ⟨2866268183341782002062021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15286763644489504010997445 2866268183341782002062021)
                  ·
                    refine ⟨537425284376584125386629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2866268183341782002062021 537425284376584125386629)
                    ·
                      rfl

theorem cell23_3139896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_3139896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139896 prefixEnd_3139896 := by exact prefixLift 3139896
  have htrace : WordTrace (prefixWord ++ tailWord_3139896) baseStart_3139896 baseEnd_3139896 := by
    simpa [prefixWord, tailWord_3139896, baseEnd_3139896] using wordTrace_append hprefix tailTrace_3139896
  have hstable : (prefixWord ++ tailWord_3139896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139896).length < 2 ^ (prefixWord ++ tailWord_3139896).sum := by decide
  have hdescent : baseEnd_3139896 < baseStart_3139896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139897 : List Nat := [1, 2, 1, 6, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3139897 : Nat := 118140960795 + 3139897 * 2 ^ 59
def prefixEnd_3139897 : Nat := 4983230072969 + 3 ^ 40 * 3139897 * 2
def baseEnd_3139897 : Nat := 1612276366610406872247383

theorem tailTrace_3139897 : CollatzResearch.WordTrace tailWord_3139897 prefixEnd_3139897 1612276366610406872247383 := by
  unfold tailWord_3139897
  simp only [CollatzResearch.WordTrace]
  refine ⟨114521451905696895559529945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76347634603797930373019963 114521451905696895559529945)
  ·
    refine ⟨85891088929272671669647459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114521451905696895559529945 85891088929272671669647459)
    ·
      refine ⟨128836633393909007504471189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85891088929272671669647459 128836633393909007504471189)
      ·
        refine ⟨6039217190339484726772087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128836633393909007504471189 6039217190339484726772087)
        ·
          refine ⟨9058825785509227090158131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6039217190339484726772087 9058825785509227090158131)
          ·
            refine ⟨13588238678263840635237197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058825785509227090158131 13588238678263840635237197)
            ·
              refine ⟨5095589504348940238213949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13588238678263840635237197 5095589504348940238213949)
              ·
                refine ⟨1910846064130852589330231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5095589504348940238213949 1910846064130852589330231)
                ·
                  refine ⟨2866269096196278883995347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910846064130852589330231 2866269096196278883995347)
                  ·
                    refine ⟨4299403644294418325993021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2866269096196278883995347 4299403644294418325993021)
                    ·
                      refine ⟨1612276366610406872247383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299403644294418325993021 1612276366610406872247383)
                      ·
                        rfl

theorem cell23_3139897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3139897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139897 prefixEnd_3139897 := by exact prefixLift 3139897
  have htrace : WordTrace (prefixWord ++ tailWord_3139897) baseStart_3139897 baseEnd_3139897 := by
    simpa [prefixWord, tailWord_3139897, baseEnd_3139897] using wordTrace_append hprefix tailTrace_3139897
  have hstable : (prefixWord ++ tailWord_3139897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139897).length < 2 ^ (prefixWord ++ tailWord_3139897).sum := by decide
  have hdescent : baseEnd_3139897 < baseStart_3139897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139920 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 3, 2, 2]
def baseStart_3139920 : Nat := 118140960795 + 3139920 * 2 ^ 59
def prefixEnd_3139920 : Nat := 4983230072969 + 3 ^ 40 * 3139920 * 2
def baseEnd_3139920 : Nat := 1612288176665460282259777

theorem tailTrace_3139920 : CollatzResearch.WordTrace tailWord_3139920 prefixEnd_3139920 1612288176665460282259777 := by
  unfold tailWord_3139920
  simp only [CollatzResearch.WordTrace]
  refine ⟨57261145392306785243808607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76348193856409046991744809 57261145392306785243808607)
  ·
    refine ⟨85891718088460177865712911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57261145392306785243808607 85891718088460177865712911)
    ·
      refine ⟨128837577132690266798569367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85891718088460177865712911 128837577132690266798569367)
      ·
        refine ⟨193256365699035400197854051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128837577132690266798569367 193256365699035400197854051)
        ·
          refine ⟨289884548548553100296781077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193256365699035400197854051 289884548548553100296781077)
          ·
            refine ⟨13588338213213426576411613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 289884548548553100296781077 13588338213213426576411613)
            ·
              refine ⟨5095626829955034966154355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13588338213213426576411613 5095626829955034966154355)
              ·
                refine ⟨7643440244932552449231533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095626829955034966154355 7643440244932552449231533)
                ·
                  refine ⟨2866290091849707168461825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7643440244932552449231533 2866290091849707168461825)
                  ·
                    refine ⟨2149717568887280376346369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866290091849707168461825 2149717568887280376346369)
                    ·
                      refine ⟨1612288176665460282259777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149717568887280376346369 1612288176665460282259777)
                      ·
                        rfl

theorem cell23_3139920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 2, 2].length) (baseStart_3139920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139920 prefixEnd_3139920 := by exact prefixLift 3139920
  have htrace : WordTrace (prefixWord ++ tailWord_3139920) baseStart_3139920 baseEnd_3139920 := by
    simpa [prefixWord, tailWord_3139920, baseEnd_3139920] using wordTrace_append hprefix tailTrace_3139920
  have hstable : (prefixWord ++ tailWord_3139920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139920).length < 2 ^ (prefixWord ++ tailWord_3139920).sum := by decide
  have hdescent : baseEnd_3139920 < baseStart_3139920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139929 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_3139929 : Nat := 118140960795 + 3139929 * 2 ^ 59
def prefixEnd_3139929 : Nat := 4983230072969 + 3 ^ 40 * 3139929 * 2
def baseEnd_3139929 : Nat := 1612292797991350747047235

theorem tailTrace_3139929 : CollatzResearch.WordTrace tailWord_3139929 prefixEnd_3139929 1612292797991350747047235 := by
  unfold tailWord_3139929
  simp only [CollatzResearch.WordTrace]
  refine ⟨114522619041580965024694841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76348412694387310016463227 114522619041580965024694841)
  ·
    refine ⟨85891964281185723768521131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114522619041580965024694841 85891964281185723768521131)
    ·
      refine ⟨128837946421778585652781697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85891964281185723768521131 128837946421778585652781697)
      ·
        refine ⟨96628459816333939239586273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128837946421778585652781697 96628459816333939239586273)
        ·
          refine ⟨72471344862250454429689705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96628459816333939239586273 72471344862250454429689705)
          ·
            refine ⟨54353508646687840822267279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72471344862250454429689705 54353508646687840822267279)
            ·
              refine ⟨81530262970031761233400919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54353508646687840822267279 81530262970031761233400919)
              ·
                refine ⟨122295394455047641850101379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81530262970031761233400919 122295394455047641850101379)
                ·
                  refine ⟨183443091682571462775152069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122295394455047641850101379 183443091682571462775152069)
                  ·
                    refine ⟨34395579690482149270341013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183443091682571462775152069 34395579690482149270341013)
                    ·
                      refine ⟨1612292797991350747047235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34395579690482149270341013 1612292797991350747047235)
                      ·
                        rfl

theorem cell23_3139929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3139929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139929 prefixEnd_3139929 := by exact prefixLift 3139929
  have htrace : WordTrace (prefixWord ++ tailWord_3139929) baseStart_3139929 baseEnd_3139929 := by
    simpa [prefixWord, tailWord_3139929, baseEnd_3139929] using wordTrace_append hprefix tailTrace_3139929
  have hstable : (prefixWord ++ tailWord_3139929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139929).length < 2 ^ (prefixWord ++ tailWord_3139929).sum := by decide
  have hdescent : baseEnd_3139929 < baseStart_3139929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139934 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3139934 : Nat := 118140960795 + 3139934 * 2 ^ 59
def prefixEnd_3139934 : Nat := 4983230072969 + 3 ^ 40 * 3139934 * 2
def baseEnd_3139934 : Nat := 537431788464874409161571

theorem tailTrace_3139934 : CollatzResearch.WordTrace tailWord_3139934 prefixEnd_3139934 537431788464874409161571 := by
  unfold tailWord_3139934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14315350175820356359828357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76348534271041900585751237 14315350175820356359828357)
  ·
    refine ⟨2684128157966316817467817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14315350175820356359828357 2684128157966316817467817)
    ·
      refine ⟨2013096118474737613100863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2684128157966316817467817 2013096118474737613100863)
      ·
        refine ⟨3019644177712106419651295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013096118474737613100863 3019644177712106419651295)
        ·
          refine ⟨4529466266568159629476943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019644177712106419651295 4529466266568159629476943)
          ·
            refine ⟨6794199399852239444215415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529466266568159629476943 6794199399852239444215415)
            ·
              refine ⟨10191299099778359166323123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794199399852239444215415 10191299099778359166323123)
              ·
                refine ⟨15286948649667538749484685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10191299099778359166323123 15286948649667538749484685)
                ·
                  refine ⟨5732605743625327031056757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15286948649667538749484685 5732605743625327031056757)
                  ·
                    refine ⟨537431788464874409161571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5732605743625327031056757 537431788464874409161571)
                    ·
                      rfl

theorem cell23_3139934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3139934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139934 prefixEnd_3139934 := by exact prefixLift 3139934
  have htrace : WordTrace (prefixWord ++ tailWord_3139934) baseStart_3139934 baseEnd_3139934 := by
    simpa [prefixWord, tailWord_3139934, baseEnd_3139934] using wordTrace_append hprefix tailTrace_3139934
  have hstable : (prefixWord ++ tailWord_3139934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139934).length < 2 ^ (prefixWord ++ tailWord_3139934).sum := by decide
  have hdescent : baseEnd_3139934 < baseStart_3139934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139957 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_3139957 : Nat := 118140960795 + 3139957 * 2 ^ 59
def prefixEnd_3139957 : Nat := 4983230072969 + 3 ^ 40 * 3139957 * 2
def baseEnd_3139957 : Nat := 1612307175449676637497107

theorem tailTrace_3139957 : CollatzResearch.WordTrace tailWord_3139957 prefixEnd_3139957 1612307175449676637497107 := by
  unfold tailWord_3139957
  simp only [CollatzResearch.WordTrace]
  refine ⟨114523640285479525806714125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76349093523653017204476083 114523640285479525806714125)
  ·
    refine ⟨42946365107054822177517797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114523640285479525806714125 42946365107054822177517797)
    ·
      refine ⟨8052443457572779158284587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42946365107054822177517797 8052443457572779158284587)
      ·
        refine ⟨12078665186359168737426881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8052443457572779158284587 12078665186359168737426881)
        ·
          refine ⟨9058998889769376553070161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12078665186359168737426881 9058998889769376553070161)
          ·
            refine ⟨6794249167327032414802621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058998889769376553070161 6794249167327032414802621)
            ·
              refine ⟨2547843437747637155550983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6794249167327032414802621 2547843437747637155550983)
              ·
                refine ⟨3821765156621455733326475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547843437747637155550983 3821765156621455733326475)
                ·
                  refine ⟨5732647734932183599989713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821765156621455733326475 5732647734932183599989713)
                  ·
                    refine ⟨4299485801199137699992285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732647734932183599989713 4299485801199137699992285)
                    ·
                      refine ⟨1612307175449676637497107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299485801199137699992285 1612307175449676637497107)
                      ·
                        rfl

theorem cell23_3139957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_3139957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139957 prefixEnd_3139957 := by exact prefixLift 3139957
  have htrace : WordTrace (prefixWord ++ tailWord_3139957) baseStart_3139957 baseEnd_3139957 := by
    simpa [prefixWord, tailWord_3139957, baseEnd_3139957] using wordTrace_append hprefix tailTrace_3139957
  have hstable : (prefixWord ++ tailWord_3139957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139957).length < 2 ^ (prefixWord ++ tailWord_3139957).sum := by decide
  have hdescent : baseEnd_3139957 < baseStart_3139957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139971 : List Nat := [1, 1, 1, 3, 6, 2, 2, 2, 1, 2, 2]
def baseStart_3139971 : Nat := 118140960795 + 3139971 * 2 ^ 59
def prefixEnd_3139971 : Nat := 4983230072969 + 3 ^ 40 * 3139971 * 2
def baseEnd_3139971 : Nat := 1612314364178839582722043

theorem tailTrace_3139971 : CollatzResearch.WordTrace tailWord_3139971 prefixEnd_3139971 1612314364178839582722043 := by
  unfold tailWord_3139971
  simp only [CollatzResearch.WordTrace]
  refine ⟨114524150907428806197723767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76349433938285870798482511 114524150907428806197723767)
  ·
    refine ⟨171786226361143209296585651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114524150907428806197723767 171786226361143209296585651)
    ·
      refine ⟨257679339541714813944878477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171786226361143209296585651 257679339541714813944878477)
      ·
        refine ⟨96629752328143055229329429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257679339541714813944878477 96629752328143055229329429)
        ·
          refine ⟨4529519640381705713874817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96629752328143055229329429 4529519640381705713874817)
          ·
            refine ⟨3397139730286279285406113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4529519640381705713874817 3397139730286279285406113)
            ·
              refine ⟨2547854797714709464054585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3397139730286279285406113 2547854797714709464054585)
              ·
                refine ⟨1910891098286032098040939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547854797714709464054585 1910891098286032098040939)
                ·
                  refine ⟨2866336647429048147061409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910891098286032098040939 2866336647429048147061409)
                  ·
                    refine ⟨2149752485571786110296057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866336647429048147061409 2149752485571786110296057)
                    ·
                      refine ⟨1612314364178839582722043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149752485571786110296057 1612314364178839582722043)
                      ·
                        rfl

theorem cell23_3139971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_3139971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139971 prefixEnd_3139971 := by exact prefixLift 3139971
  have htrace : WordTrace (prefixWord ++ tailWord_3139971) baseStart_3139971 baseEnd_3139971 := by
    simpa [prefixWord, tailWord_3139971, baseEnd_3139971] using wordTrace_append hprefix tailTrace_3139971
  have hstable : (prefixWord ++ tailWord_3139971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139971).length < 2 ^ (prefixWord ++ tailWord_3139971).sum := by decide
  have hdescent : baseEnd_3139971 < baseStart_3139971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139976 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3139976 : Nat := 118140960795 + 3139976 * 2 ^ 59
def prefixEnd_3139976 : Nat := 4983230072969 + 3 ^ 40 * 3139976 * 2
def baseEnd_3139976 : Nat := 1612316931582112063159519

theorem tailTrace_3139976 : CollatzResearch.WordTrace tailWord_3139976 prefixEnd_3139976 1612316931582112063159519 := by
  unfold tailWord_3139976
  simp only [CollatzResearch.WordTrace]
  refine ⟨57262166636205346025827891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76349555514940461367770521 57262166636205346025827891)
  ·
    refine ⟨85893249954308019038741837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57262166636205346025827891 85893249954308019038741837)
    ·
      refine ⟨32209968732865507139528189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85893249954308019038741837 32209968732865507139528189)
      ·
        refine ⟨12078738274824565177323071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32209968732865507139528189 12078738274824565177323071)
        ·
          refine ⟨18118107412236847765984607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12078738274824565177323071 18118107412236847765984607)
          ·
            refine ⟨27177161118355271648976911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18118107412236847765984607 27177161118355271648976911)
            ·
              refine ⟨40765741677532907473465367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27177161118355271648976911 40765741677532907473465367)
              ·
                refine ⟨61148612516299361210198051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40765741677532907473465367 61148612516299361210198051)
                ·
                  refine ⟨91722918774449041815297077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61148612516299361210198051 91722918774449041815297077)
                  ·
                    refine ⟨8599023635104597670184101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91722918774449041815297077 8599023635104597670184101)
                    ·
                      refine ⟨1612316931582112063159519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8599023635104597670184101 1612316931582112063159519)
                      ·
                        rfl

theorem cell23_3139976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3139976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139976 prefixEnd_3139976 := by exact prefixLift 3139976
  have htrace : WordTrace (prefixWord ++ tailWord_3139976) baseStart_3139976 baseEnd_3139976 := by
    simpa [prefixWord, tailWord_3139976, baseEnd_3139976] using wordTrace_append hprefix tailTrace_3139976
  have hstable : (prefixWord ++ tailWord_3139976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139976).length < 2 ^ (prefixWord ++ tailWord_3139976).sum := by decide
  have hdescent : baseEnd_3139976 < baseStart_3139976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140044 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3140044 : Nat := 118140960795 + 3140044 * 2 ^ 59
def prefixEnd_3140044 : Nat := 4983230072969 + 3 ^ 40 * 3140044 * 2
def baseEnd_3140044 : Nat := 1612351848266617797109207

theorem tailTrace_3140044 : CollatzResearch.WordTrace tailWord_3140044 prefixEnd_3140044 1612351848266617797109207 := by
  unfold tailWord_3140044
  simp only [CollatzResearch.WordTrace]
  refine ⟨57263406718082169832565593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76351208957442893110087457 57263406718082169832565593)
  ·
    refine ⟨42947555038561627374424195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57263406718082169832565593 42947555038561627374424195)
    ·
      refine ⟨64421332557842441061636293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42947555038561627374424195 64421332557842441061636293)
      ·
        refine ⟨12078999854595457699056805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64421332557842441061636293 12078999854595457699056805)
        ·
          refine ⟨2264812472736648318573151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12078999854595457699056805 2264812472736648318573151)
          ·
            refine ⟨3397218709104972477859727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264812472736648318573151 3397218709104972477859727)
            ·
              refine ⟨5095828063657458716789591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397218709104972477859727 5095828063657458716789591)
              ·
                refine ⟨7643742095486188075184387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095828063657458716789591 7643742095486188075184387)
                ·
                  refine ⟨11465613143229282112776581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643742095486188075184387 11465613143229282112776581)
                  ·
                    refine ⟨2149802464355490396145609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11465613143229282112776581 2149802464355490396145609)
                    ·
                      refine ⟨1612351848266617797109207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149802464355490396145609 1612351848266617797109207)
                      ·
                        rfl

theorem cell23_3140044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3140044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140044 prefixEnd_3140044 := by exact prefixLift 3140044
  have htrace : WordTrace (prefixWord ++ tailWord_3140044) baseStart_3140044 baseEnd_3140044 := by
    simpa [prefixWord, tailWord_3140044, baseEnd_3140044] using wordTrace_append hprefix tailTrace_3140044
  have hstable : (prefixWord ++ tailWord_3140044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140044).length < 2 ^ (prefixWord ++ tailWord_3140044).sum := by decide
  have hdescent : baseEnd_3140044 < baseStart_3140044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140056 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3140056 : Nat := 118140960795 + 3140056 * 2 ^ 59
def prefixEnd_3140056 : Nat := 4983230072969 + 3 ^ 40 * 3140056 * 2
def baseEnd_3140056 : Nat := 1612358010034471750159151

theorem tailTrace_3140056 : CollatzResearch.WordTrace tailWord_3140056 prefixEnd_3140056 1612358010034471750159151 := by
  unfold tailWord_3140056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57263625556060432857284011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76351500741413910476378681 57263625556060432857284011)
  ·
    refine ⟨85895438334090649285926017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57263625556060432857284011 85895438334090649285926017)
    ·
      refine ⟨64421578750567986964444513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85895438334090649285926017 64421578750567986964444513)
      ·
        refine ⟨48316184062925990223333385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64421578750567986964444513 48316184062925990223333385)
        ·
          refine ⟨36237138047194492667500039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48316184062925990223333385 36237138047194492667500039)
          ·
            refine ⟨54355707070791739001250059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36237138047194492667500039 54355707070791739001250059)
            ·
              refine ⟨81533560606187608501875089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54355707070791739001250059 81533560606187608501875089)
              ·
                refine ⟨61150170454640706376406317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81533560606187608501875089 61150170454640706376406317)
                ·
                  refine ⟨22931313920490264891152369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61150170454640706376406317 22931313920490264891152369)
                  ·
                    refine ⟨17198485440367698668364277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22931313920490264891152369 17198485440367698668364277)
                    ·
                      refine ⟨1612358010034471750159151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17198485440367698668364277 1612358010034471750159151)
                      ·
                        rfl

theorem cell23_3140056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3140056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140056 prefixEnd_3140056 := by exact prefixLift 3140056
  have htrace : WordTrace (prefixWord ++ tailWord_3140056) baseStart_3140056 baseEnd_3140056 := by
    simpa [prefixWord, tailWord_3140056, baseEnd_3140056] using wordTrace_append hprefix tailTrace_3140056
  have hstable : (prefixWord ++ tailWord_3140056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140056).length < 2 ^ (prefixWord ++ tailWord_3140056).sum := by decide
  have hdescent : baseEnd_3140056 < baseStart_3140056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140067 : List Nat := [1, 1, 1, 6, 3, 2, 1, 3, 5]
def baseStart_3140067 : Nat := 118140960795 + 3140067 * 2 ^ 59
def prefixEnd_3140067 : Nat := 4983230072969 + 3 ^ 40 * 3140067 * 2
def baseEnd_3140067 : Nat := 179151517591296800791289

theorem tailTrace_3140067 : CollatzResearch.WordTrace tailWord_3140067 prefixEnd_3140067 179151517591296800791289 := by
  unfold tailWord_3140067
  simp only [CollatzResearch.WordTrace]
  refine ⟨114527652315081014593218455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76351768210054009728812303 114527652315081014593218455)
  ·
    refine ⟨171791478472621521889827683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114527652315081014593218455 171791478472621521889827683)
    ·
      refine ⟨257687217708932282834741525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171791478472621521889827683 257687217708932282834741525)
      ·
        refine ⟨12079088330106200757878509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257687217708932282834741525 12079088330106200757878509)
        ·
          refine ⟨4529658123789825284204441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12079088330106200757878509 4529658123789825284204441)
          ·
            refine ⟨3397243592842368963153331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4529658123789825284204441 3397243592842368963153331)
            ·
              refine ⟨5095865389263553444729997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397243592842368963153331 5095865389263553444729997)
              ·
                refine ⟨1910949520973832541773749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5095865389263553444729997 1910949520973832541773749)
                ·
                  refine ⟨179151517591296800791289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910949520973832541773749 179151517591296800791289)
                  ·
                    rfl

theorem cell23_3140067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 5].length) (baseStart_3140067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140067 prefixEnd_3140067 := by exact prefixLift 3140067
  have htrace : WordTrace (prefixWord ++ tailWord_3140067) baseStart_3140067 baseEnd_3140067 := by
    simpa [prefixWord, tailWord_3140067, baseEnd_3140067] using wordTrace_append hprefix tailTrace_3140067
  have hstable : (prefixWord ++ tailWord_3140067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140067).length < 2 ^ (prefixWord ++ tailWord_3140067).sum := by decide
  have hdescent : baseEnd_3140067 < baseStart_3140067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140083 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 4]
def baseStart_3140083 : Nat := 118140960795 + 3140083 * 2 ^ 59
def prefixEnd_3140083 : Nat := 4983230072969 + 3 ^ 40 * 3140083 * 2
def baseEnd_3140083 : Nat := 1612371874012143144521527

theorem tailTrace_3140083 : CollatzResearch.WordTrace tailWord_3140083 prefixEnd_3140083 1612371874012143144521527 := by
  unfold tailWord_3140083
  simp only [CollatzResearch.WordTrace]
  refine ⟨114528235883023049325800903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76352157255348699550533935 114528235883023049325800903)
  ·
    refine ⟨171792353824534573988701355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114528235883023049325800903 171792353824534573988701355)
    ·
      refine ⟨257688530736801860983052033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171792353824534573988701355 257688530736801860983052033)
      ·
        refine ⟨193266398052601395737289025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257688530736801860983052033 193266398052601395737289025)
        ·
          refine ⟨144949798539451046802966769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193266398052601395737289025 144949798539451046802966769)
          ·
            refine ⟨108712348904588285102225077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144949798539451046802966769 108712348904588285102225077)
            ·
              refine ⟨10191782709805151728333601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108712348904588285102225077 10191782709805151728333601)
              ·
                refine ⟨7643837032353863796250201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10191782709805151728333601 7643837032353863796250201)
                ·
                  refine ⟨5732877774265397847187651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7643837032353863796250201 5732877774265397847187651)
                  ·
                    refine ⟨8599316661398096770781477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5732877774265397847187651 8599316661398096770781477)
                    ·
                      refine ⟨1612371874012143144521527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8599316661398096770781477 1612371874012143144521527)
                      ·
                        rfl

theorem cell23_3140083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_3140083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140083 prefixEnd_3140083 := by exact prefixLift 3140083
  have htrace : WordTrace (prefixWord ++ tailWord_3140083) baseStart_3140083 baseEnd_3140083 := by
    simpa [prefixWord, tailWord_3140083, baseEnd_3140083] using wordTrace_append hprefix tailTrace_3140083
  have hstable : (prefixWord ++ tailWord_3140083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140083).length < 2 ^ (prefixWord ++ tailWord_3140083).sum := by decide
  have hdescent : baseEnd_3140083 < baseStart_3140083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140120 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3140120 : Nat := 118140960795 + 3140120 * 2 ^ 59
def prefixEnd_3140120 : Nat := 4983230072969 + 3 ^ 40 * 3140120 * 2
def baseEnd_3140120 : Nat := 1612390872796359499758857

theorem tailTrace_3140120 : CollatzResearch.WordTrace tailWord_3140120 prefixEnd_3140120 1612390872796359499758857 := by
  unfold tailWord_3140120
  simp only [CollatzResearch.WordTrace]
  refine ⟨57264792691944502322448907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76353056922592669763265209 57264792691944502322448907)
  ·
    refine ⟨85897189037916753483673361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57264792691944502322448907 85897189037916753483673361)
    ·
      refine ⟨64422891778437565112755021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85897189037916753483673361 64422891778437565112755021)
      ·
        refine ⟨24158584416914086917283133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64422891778437565112755021 24158584416914086917283133)
        ·
          refine ⟨9059469156342782593981175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24158584416914086917283133 9059469156342782593981175)
          ·
            refine ⟨13589203734514173890971763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9059469156342782593981175 13589203734514173890971763)
            ·
              refine ⟨20383805601771260836457645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13589203734514173890971763 20383805601771260836457645)
              ·
                refine ⟨7643927100664222813671617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20383805601771260836457645 7643927100664222813671617)
                ·
                  refine ⟨5732945325498167110253713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7643927100664222813671617 5732945325498167110253713)
                  ·
                    refine ⟨4299708994123625332690285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732945325498167110253713 4299708994123625332690285)
                    ·
                      refine ⟨1612390872796359499758857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299708994123625332690285 1612390872796359499758857)
                      ·
                        rfl

theorem cell23_3140120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3140120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140120 prefixEnd_3140120 := by exact prefixLift 3140120
  have htrace : WordTrace (prefixWord ++ tailWord_3140120) baseStart_3140120 baseEnd_3140120 := by
    simpa [prefixWord, tailWord_3140120, baseEnd_3140120] using wordTrace_append hprefix tailTrace_3140120
  have hstable : (prefixWord ++ tailWord_3140120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140120).length < 2 ^ (prefixWord ++ tailWord_3140120).sum := by decide
  have hdescent : baseEnd_3140120 < baseStart_3140120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140153 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 5, 5]
def baseStart_3140153 : Nat := 118140960795 + 3140153 * 2 ^ 59
def prefixEnd_3140153 : Nat := 4983230072969 + 3 ^ 40 * 3140153 * 2
def baseEnd_3140153 : Nat := 537469272552652623548735

theorem tailTrace_3140153 : CollatzResearch.WordTrace tailWord_3140153 prefixEnd_3140153 537469272552652623548735 := by
  unfold tailWord_3140153
  simp only [CollatzResearch.WordTrace]
  refine ⟨114530788992769451280849113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76353859328512967520566075 114530788992769451280849113)
  ·
    refine ⟨85898091744577088460636835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114530788992769451280849113 85898091744577088460636835)
    ·
      refine ⟨128847137616865632690955253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85898091744577088460636835 128847137616865632690955253)
      ·
        refine ⟨12079419151581153064777055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128847137616865632690955253 12079419151581153064777055)
        ·
          refine ⟨18119128727371729597165583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12079419151581153064777055 18119128727371729597165583)
          ·
            refine ⟨27178693091057594395748375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18119128727371729597165583 27178693091057594395748375)
            ·
              refine ⟨40768039636586391593622563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27178693091057594395748375 40768039636586391593622563)
              ·
                refine ⟨61152059454879587390433845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40768039636586391593622563 61152059454879587390433845)
                ·
                  refine ⟨5733005573894961317853173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61152059454879587390433845 5733005573894961317853173)
                  ·
                    refine ⟨537469272552652623548735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5733005573894961317853173 537469272552652623548735)
                    ·
                      rfl

theorem cell23_3140153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_3140153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140153 prefixEnd_3140153 := by exact prefixLift 3140153
  have htrace : WordTrace (prefixWord ++ tailWord_3140153) baseStart_3140153 baseEnd_3140153 := by
    simpa [prefixWord, tailWord_3140153, baseEnd_3140153] using wordTrace_append hprefix tailTrace_3140153
  have hstable : (prefixWord ++ tailWord_3140153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140153).length < 2 ^ (prefixWord ++ tailWord_3140153).sum := by decide
  have hdescent : baseEnd_3140153 < baseStart_3140153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140160 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 4, 3, 2]
def baseStart_3140160 : Nat := 118140960795 + 3140160 * 2 ^ 59
def prefixEnd_3140160 : Nat := 4983230072969 + 3 ^ 40 * 3140160 * 2
def baseEnd_3140160 : Nat := 1612411412022539343258673

theorem tailTrace_3140160 : CollatzResearch.WordTrace tailWord_3140160 prefixEnd_3140160 1612411412022539343258673 := by
  unfold tailWord_3140160
  simp only [CollatzResearch.WordTrace]
  refine ⟨57265522151872045738176967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76354029535829394317569289 57265522151872045738176967)
  ·
    refine ⟨85898283227808068607265451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57265522151872045738176967 85898283227808068607265451)
    ·
      refine ⟨128847424841712102910898177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85898283227808068607265451 128847424841712102910898177)
      ·
        refine ⟨96635568631284077183173633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128847424841712102910898177 96635568631284077183173633)
        ·
          refine ⟨72476676473463057887380225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96635568631284077183173633 72476676473463057887380225)
          ·
            refine ⟨54357507355097293415535169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72476676473463057887380225 54357507355097293415535169)
            ·
              refine ⟨40768130516322970061651377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54357507355097293415535169 40768130516322970061651377)
              ·
                refine ⟨30576097887242227546238533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40768130516322970061651377 30576097887242227546238533)
                ·
                  refine ⟨5733018353857917664919725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30576097887242227546238533 5733018353857917664919725)
                  ·
                    refine ⟨2149881882696719124344897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5733018353857917664919725 2149881882696719124344897)
                    ·
                      refine ⟨1612411412022539343258673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149881882696719124344897 1612411412022539343258673)
                      ·
                        rfl

theorem cell23_3140160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_3140160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140160 prefixEnd_3140160 := by exact prefixLift 3140160
  have htrace : WordTrace (prefixWord ++ tailWord_3140160) baseStart_3140160 baseEnd_3140160 := by
    simpa [prefixWord, tailWord_3140160, baseEnd_3140160] using wordTrace_append hprefix tailTrace_3140160
  have hstable : (prefixWord ++ tailWord_3140160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140160).length < 2 ^ (prefixWord ++ tailWord_3140160).sum := by decide
  have hdescent : baseEnd_3140160 < baseStart_3140160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140167 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_3140167 : Nat := 118140960795 + 3140167 * 2 ^ 59
def prefixEnd_3140167 : Nat := 4983230072969 + 3 ^ 40 * 3140167 * 2
def baseEnd_3140167 : Nat := 1612415006387120815871141

theorem tailTrace_3140167 : CollatzResearch.WordTrace tailWord_3140167 prefixEnd_3140167 1612415006387120815871141 := by
  unfold tailWord_3140167
  simp only [CollatzResearch.WordTrace]
  refine ⟨114531299614718731671858755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76354199743145821114572503 114531299614718731671858755)
  ·
    refine ⟨171796949422078097507788133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114531299614718731671858755 171796949422078097507788133)
    ·
      refine ⟨32211928016639643282710275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171796949422078097507788133 32211928016639643282710275)
      ·
        refine ⟨48317892024959464924065413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32211928016639643282710275 48317892024959464924065413)
        ·
          refine ⟨9059604754679899673262265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48317892024959464924065413 9059604754679899673262265)
          ·
            refine ⟨6794703566009924754946699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9059604754679899673262265 6794703566009924754946699)
            ·
              refine ⟨10192055349014887132420049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794703566009924754946699 10192055349014887132420049)
              ·
                refine ⟨7644041511761165349315037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10192055349014887132420049 7644041511761165349315037)
                ·
                  refine ⟨2866515566910437005993139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7644041511761165349315037 2866515566910437005993139)
                  ·
                    refine ⟨4299773350365655508989709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2866515566910437005993139 4299773350365655508989709)
                    ·
                      refine ⟨1612415006387120815871141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299773350365655508989709 1612415006387120815871141)
                      ·
                        rfl

theorem cell23_3140167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_3140167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140167 prefixEnd_3140167 := by exact prefixLift 3140167
  have htrace : WordTrace (prefixWord ++ tailWord_3140167) baseStart_3140167 baseEnd_3140167 := by
    simpa [prefixWord, tailWord_3140167, baseEnd_3140167] using wordTrace_append hprefix tailTrace_3140167
  have hstable : (prefixWord ++ tailWord_3140167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140167).length < 2 ^ (prefixWord ++ tailWord_3140167).sum := by decide
  have hdescent : baseEnd_3140167 < baseStart_3140167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140177 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 2, 3, 2]
def baseStart_3140177 : Nat := 118140960795 + 3140177 * 2 ^ 59
def prefixEnd_3140177 : Nat := 4983230072969 + 3 ^ 40 * 3140177 * 2
def baseEnd_3140177 : Nat := 1612420141193665776746095

theorem tailTrace_3140177 : CollatzResearch.WordTrace tailWord_3140177 prefixEnd_3140177 1612420141193665776746095 := by
  unfold tailWord_3140177
  simp only [CollatzResearch.WordTrace]
  refine ⟨114531664344682503379722785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76354442896455002253148523 114531664344682503379722785)
  ·
    refine ⟨85898748258511877534792089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114531664344682503379722785 85898748258511877534792089)
    ·
      refine ⟨64424061193883908151094067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85898748258511877534792089 64424061193883908151094067)
      ·
        refine ⟨96636091790825862226641101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64424061193883908151094067 96636091790825862226641101)
        ·
          refine ⟨36238534421559698334990413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96636091790825862226641101 36238534421559698334990413)
          ·
            refine ⟨13589450408084886875621405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36238534421559698334990413 13589450408084886875621405)
            ·
              refine ⟨5096043903031832578358027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13589450408084886875621405 5096043903031832578358027)
              ·
                refine ⟨7644065854547748867537041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096043903031832578358027 7644065854547748867537041)
                ·
                  refine ⟨5733049390910811650652781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7644065854547748867537041 5733049390910811650652781)
                  ·
                    refine ⟨2149893521591554368994793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5733049390910811650652781 2149893521591554368994793)
                    ·
                      refine ⟨1612420141193665776746095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149893521591554368994793 1612420141193665776746095)
                      ·
                        rfl

theorem cell23_3140177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_3140177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140177 prefixEnd_3140177 := by exact prefixLift 3140177
  have htrace : WordTrace (prefixWord ++ tailWord_3140177) baseStart_3140177 baseEnd_3140177 := by
    simpa [prefixWord, tailWord_3140177, baseEnd_3140177] using wordTrace_append hprefix tailTrace_3140177
  have hstable : (prefixWord ++ tailWord_3140177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140177).length < 2 ^ (prefixWord ++ tailWord_3140177).sum := by decide
  have hdescent : baseEnd_3140177 < baseStart_3140177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140183 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 1, 6]
def baseStart_3140183 : Nat := 118140960795 + 3140183 * 2 ^ 59
def prefixEnd_3140183 : Nat := 4983230072969 + 3 ^ 40 * 3140183 * 2
def baseEnd_3140183 : Nat := 537474407359197584423689

theorem tailTrace_3140183 : CollatzResearch.WordTrace tailWord_3140183 prefixEnd_3140183 537474407359197584423689 := by
  unfold tailWord_3140183
  simp only [CollatzResearch.WordTrace]
  refine ⟨114531883182660766404441203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76354588788440510936294135 114531883182660766404441203)
  ·
    refine ⟨171797824773991149606661805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114531883182660766404441203 171797824773991149606661805)
    ·
      refine ⟨64424184290246681102498177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171797824773991149606661805 64424184290246681102498177)
      ·
        refine ⟨48318138217685010826873633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64424184290246681102498177 48318138217685010826873633)
        ·
          refine ⟨36238603663263758120155225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48318138217685010826873633 36238603663263758120155225)
          ·
            refine ⟨27178952747447818590116419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36238603663263758120155225 27178952747447818590116419)
            ·
              refine ⟨40768429121171727885174629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27178952747447818590116419 40768429121171727885174629)
              ·
                refine ⟨7644080460219698978470243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40768429121171727885174629 7644080460219698978470243)
                ·
                  refine ⟨11466120690329548467705365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644080460219698978470243 11466120690329548467705365)
                  ·
                    refine ⟨537474407359197584423689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11466120690329548467705365 537474407359197584423689)
                    ·
                      rfl

theorem cell23_3140183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_3140183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140183 prefixEnd_3140183 := by exact prefixLift 3140183
  have htrace : WordTrace (prefixWord ++ tailWord_3140183) baseStart_3140183 baseEnd_3140183 := by
    simpa [prefixWord, tailWord_3140183, baseEnd_3140183] using wordTrace_append hprefix tailTrace_3140183
  have hstable : (prefixWord ++ tailWord_3140183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140183).length < 2 ^ (prefixWord ++ tailWord_3140183).sum := by decide
  have hdescent : baseEnd_3140183 < baseStart_3140183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140207 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 3, 2, 2]
def baseStart_3140207 : Nat := 118140960795 + 3140207 * 2 ^ 59
def prefixEnd_3140207 : Nat := 4983230072969 + 3 ^ 40 * 3140207 * 2
def baseEnd_3140207 : Nat := 1612435545613300659370957

theorem tailTrace_3140207 : CollatzResearch.WordTrace tailWord_3140207 prefixEnd_3140207 1612435545613300659370957 := by
  unfold tailWord_3140207
  simp only [CollatzResearch.WordTrace]
  refine ⟨114532758534573818503314875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76355172356382545668876583 114532758534573818503314875)
  ·
    refine ⟨171799137801860727754972313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114532758534573818503314875 171799137801860727754972313)
    ·
      refine ⟨128849353351395545816229235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171799137801860727754972313 128849353351395545816229235)
      ·
        refine ⟨193274030027093318724343853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128849353351395545816229235 193274030027093318724343853)
        ·
          refine ⟨72477761260159994521628945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193274030027093318724343853 72477761260159994521628945)
          ·
            refine ⟨54358320945119995891221709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72477761260159994521628945 54358320945119995891221709)
            ·
              refine ⟨20384370354419998459208141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54358320945119995891221709 20384370354419998459208141)
              ·
                refine ⟨7644138882907499422203053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20384370354419998459208141 7644138882907499422203053)
                ·
                  refine ⟨2866552081090312283326145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7644138882907499422203053 2866552081090312283326145)
                  ·
                    refine ⟨2149914060817734212494609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866552081090312283326145 2149914060817734212494609)
                    ·
                      refine ⟨1612435545613300659370957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149914060817734212494609 1612435545613300659370957)
                      ·
                        rfl

theorem cell23_3140207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 2, 2].length) (baseStart_3140207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140207 prefixEnd_3140207 := by exact prefixLift 3140207
  have htrace : WordTrace (prefixWord ++ tailWord_3140207) baseStart_3140207 baseEnd_3140207 := by
    simpa [prefixWord, tailWord_3140207, baseEnd_3140207] using wordTrace_append hprefix tailTrace_3140207
  have hstable : (prefixWord ++ tailWord_3140207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140207).length < 2 ^ (prefixWord ++ tailWord_3140207).sum := by decide
  have hdescent : baseEnd_3140207 < baseStart_3140207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140220 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_3140220 : Nat := 118140960795 + 3140220 * 2 ^ 59
def prefixEnd_3140220 : Nat := 4983230072969 + 3 ^ 40 * 3140220 * 2
def baseEnd_3140220 : Nat := 1612442220861809108508397

theorem tailTrace_3140220 : CollatzResearch.WordTrace tailWord_3140220 prefixEnd_3140220 1612442220861809108508397 := by
  unfold tailWord_3140220
  simp only [CollatzResearch.WordTrace]
  refine ⟨57266616341763360861769057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76355488455684481149025409 57266616341763360861769057)
  ·
    refine ⟨42949962256322520646326793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57266616341763360861769057 42949962256322520646326793)
    ·
      refine ⟨32212471692241890484745095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42949962256322520646326793 32212471692241890484745095)
      ·
        refine ⟨48318707538362835727117643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32212471692241890484745095 48318707538362835727117643)
        ·
          refine ⟨72478061307544253590676465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48318707538362835727117643 72478061307544253590676465)
          ·
            refine ⟨54358545980658190193007349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72478061307544253590676465 54358545980658190193007349)
            ·
              refine ⟨5096113685686705330594439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54358545980658190193007349 5096113685686705330594439)
              ·
                refine ⟨7644170528530057995891659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096113685686705330594439 7644170528530057995891659)
                ·
                  refine ⟨11466255792795086993837489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644170528530057995891659 11466255792795086993837489)
                  ·
                    refine ⟨8599691844596315245378117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11466255792795086993837489 8599691844596315245378117)
                    ·
                      refine ⟨1612442220861809108508397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8599691844596315245378117 1612442220861809108508397)
                      ·
                        rfl

theorem cell23_3140220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_3140220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140220 prefixEnd_3140220 := by exact prefixLift 3140220
  have htrace : WordTrace (prefixWord ++ tailWord_3140220) baseStart_3140220 baseEnd_3140220 := by
    simpa [prefixWord, tailWord_3140220, baseEnd_3140220] using wordTrace_append hprefix tailTrace_3140220
  have hstable : (prefixWord ++ tailWord_3140220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140220).length < 2 ^ (prefixWord ++ tailWord_3140220).sum := by decide
  have hdescent : baseEnd_3140220 < baseStart_3140220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140244 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3140244 : Nat := 118140960795 + 3140244 * 2 ^ 59
def prefixEnd_3140244 : Nat := 4983230072969 + 3 ^ 40 * 3140244 * 2
def baseEnd_3140244 : Nat := 1612454544397517014608287

theorem tailTrace_3140244 : CollatzResearch.WordTrace tailWord_3140244 prefixEnd_3140244 1612454544397517014608287 := by
  unfold tailWord_3140244
  simp only [CollatzResearch.WordTrace]
  refine ⟨57267054017719886911205893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76356072023626515881607857 57267054017719886911205893)
  ·
    refine ⟨10737572628322478795851105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57267054017719886911205893 10737572628322478795851105)
    ·
      refine ⟨8053179471241859096888329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10737572628322478795851105 8053179471241859096888329)
      ·
        refine ⟨6039884603431394322666247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8053179471241859096888329 6039884603431394322666247)
        ·
          refine ⟨9059826905147091483999371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6039884603431394322666247 9059826905147091483999371)
          ·
            refine ⟨13589740357720637225999057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9059826905147091483999371 13589740357720637225999057)
            ·
              refine ⟨10192305268290477919499293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13589740357720637225999057 10192305268290477919499293)
              ·
                refine ⟨3822114475608929219812235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10192305268290477919499293 3822114475608929219812235)
                ·
                  refine ⟨5733171713413393829718353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822114475608929219812235 5733171713413393829718353)
                  ·
                    refine ⟨4299878785060045372288765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733171713413393829718353 4299878785060045372288765)
                    ·
                      refine ⟨1612454544397517014608287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299878785060045372288765 1612454544397517014608287)
                      ·
                        rfl

theorem cell23_3140244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3140244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140244 prefixEnd_3140244 := by exact prefixLift 3140244
  have htrace : WordTrace (prefixWord ++ tailWord_3140244) baseStart_3140244 baseEnd_3140244 := by
    simpa [prefixWord, tailWord_3140244, baseEnd_3140244] using wordTrace_append hprefix tailTrace_3140244
  have hstable : (prefixWord ++ tailWord_3140244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140244).length < 2 ^ (prefixWord ++ tailWord_3140244).sum := by decide
  have hdescent : baseEnd_3140244 < baseStart_3140244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140278 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3140278 : Nat := 118140960795 + 3140278 * 2 ^ 59
def prefixEnd_3140278 : Nat := 4983230072969 + 3 ^ 40 * 3140278 * 2
def baseEnd_3140278 : Nat := 1612472002739769881583131

theorem tailTrace_3140278 : CollatzResearch.WordTrace tailWord_3140278 prefixEnd_3140278 1612472002739769881583131 := by
  unfold tailWord_3140278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158459257332287351821843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76356898744877731752766325 7158459257332287351821843)
  ·
    refine ⟨10737688885998431027732765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7158459257332287351821843 10737688885998431027732765)
    ·
      refine ⟨4026633332249411635399787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10737688885998431027732765 4026633332249411635399787)
      ·
        refine ⟨6039949998374117453099681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026633332249411635399787 6039949998374117453099681)
        ·
          refine ⟨4529962498780588089824761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6039949998374117453099681 4529962498780588089824761)
          ·
            refine ⟨3397471874085441067368571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4529962498780588089824761 3397471874085441067368571)
            ·
              refine ⟨5096207811128161601052857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397471874085441067368571 5096207811128161601052857)
              ·
                refine ⟨3822155858346121200789643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5096207811128161601052857 3822155858346121200789643)
                ·
                  refine ⟨5733233787519181801184465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822155858346121200789643 5733233787519181801184465)
                  ·
                    refine ⟨4299925340639386350888349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733233787519181801184465 4299925340639386350888349)
                    ·
                      refine ⟨1612472002739769881583131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4299925340639386350888349 1612472002739769881583131)
                      ·
                        rfl

theorem cell23_3140278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3140278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140278 prefixEnd_3140278 := by exact prefixLift 3140278
  have htrace : WordTrace (prefixWord ++ tailWord_3140278) baseStart_3140278 baseEnd_3140278 := by
    simpa [prefixWord, tailWord_3140278, baseEnd_3140278] using wordTrace_append hprefix tailTrace_3140278
  have hstable : (prefixWord ++ tailWord_3140278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140278).length < 2 ^ (prefixWord ++ tailWord_3140278).sum := by decide
  have hdescent : baseEnd_3140278 < baseStart_3140278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140354 : List Nat := [3, 4, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3140354 : Nat := 118140960795 + 3140354 * 2 ^ 59
def prefixEnd_3140354 : Nat := 4983230072969 + 3 ^ 40 * 3140354 * 2
def baseEnd_3140354 : Nat := 179167891918834620470309

theorem tailTrace_3140354 : CollatzResearch.WordTrace tailWord_3140354 prefixEnd_3140354 179167891918834620470309 := by
  unfold tailWord_3140354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28634530016260315652229029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76358746710027508405944077 28634530016260315652229029)
  ·
    refine ⟨5368974378048809184792943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28634530016260315652229029 5368974378048809184792943)
    ·
      refine ⟨8053461567073213777189415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5368974378048809184792943 8053461567073213777189415)
      ·
        refine ⟨12080192350609820665784123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8053461567073213777189415 12080192350609820665784123)
        ·
          refine ⟨18120288525914730998676185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12080192350609820665784123 18120288525914730998676185)
          ·
            refine ⟨13590216394436048249007139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18120288525914730998676185 13590216394436048249007139)
            ·
              refine ⟨20385324591654072373510709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13590216394436048249007139 20385324591654072373510709)
              ·
                refine ⟨1911124180467569285016629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20385324591654072373510709 1911124180467569285016629)
                ·
                  refine ⟨179167891918834620470309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1911124180467569285016629 179167891918834620470309)
                  ·
                    rfl

theorem cell23_3140354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3140354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140354 prefixEnd_3140354 := by exact prefixLift 3140354
  have htrace : WordTrace (prefixWord ++ tailWord_3140354) baseStart_3140354 baseEnd_3140354 := by
    simpa [prefixWord, tailWord_3140354, baseEnd_3140354] using wordTrace_append hprefix tailTrace_3140354
  have hstable : (prefixWord ++ tailWord_3140354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140354).length < 2 ^ (prefixWord ++ tailWord_3140354).sum := by decide
  have hdescent : baseEnd_3140354 < baseStart_3140354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140407 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_3140407 : Nat := 118140960795 + 3140407 * 2 ^ 59
def prefixEnd_3140407 : Nat := 4983230072969 + 3 ^ 40 * 3140407 * 2
def baseEnd_3140407 : Nat := 1612538241744199876870037

theorem tailTrace_3140407 : CollatzResearch.WordTrace tailWord_3140407 prefixEnd_3140407 1612538241744199876870037 := by
  unfold tailWord_3140407
  simp only [CollatzResearch.WordTrace]
  refine ⟨114540053133849252660595475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76360035422566168440396983 114540053133849252660595475)
  ·
    refine ⟨171810079700773878990893213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114540053133849252660595475 171810079700773878990893213)
    ·
      refine ⟨64428779887790204621584955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171810079700773878990893213 64428779887790204621584955)
      ·
        refine ⟨96643169831685306932377433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64428779887790204621584955 96643169831685306932377433)
        ·
          refine ⟨72482377373763980199283075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96643169831685306932377433 72482377373763980199283075)
          ·
            refine ⟨108723566060645970298924613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72482377373763980199283075 108723566060645970298924613)
            ·
              refine ⟨20385668636371119431048365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108723566060645970298924613 20385668636371119431048365)
              ·
                refine ⟨7644625738639169786643137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20385668636371119431048365 7644625738639169786643137)
                ·
                  refine ⟨5733469303979377339982353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7644625738639169786643137 5733469303979377339982353)
                  ·
                    refine ⟨4300101977984533004986765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733469303979377339982353 4300101977984533004986765)
                    ·
                      refine ⟨1612538241744199876870037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4300101977984533004986765 1612538241744199876870037)
                      ·
                        rfl

theorem cell23_3140407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_3140407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140407 prefixEnd_3140407 := by exact prefixLift 3140407
  have htrace : WordTrace (prefixWord ++ tailWord_3140407) baseStart_3140407 baseEnd_3140407 := by
    simpa [prefixWord, tailWord_3140407, baseEnd_3140407] using wordTrace_append hprefix tailTrace_3140407
  have hstable : (prefixWord ++ tailWord_3140407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140407).length < 2 ^ (prefixWord ++ tailWord_3140407).sum := by decide
  have hdescent : baseEnd_3140407 < baseStart_3140407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140430 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3140430 : Nat := 118140960795 + 3140430 * 2 ^ 59
def prefixEnd_3140430 : Nat := 4983230072969 + 3 ^ 40 * 3140430 * 2
def baseEnd_3140430 : Nat := 1612550051799253286882431

theorem tailTrace_3140430 : CollatzResearch.WordTrace tailWord_3140430 prefixEnd_3140430 1612550051799253286882431 := by
  unfold tailWord_3140430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14317611501595740948585343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76360594675177285059121829 14317611501595740948585343)
  ·
    refine ⟨21476417252393611422878015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14317611501595740948585343 21476417252393611422878015)
    ·
      refine ⟨32214625878590417134317023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21476417252393611422878015 32214625878590417134317023)
      ·
        refine ⟨48321938817885625701475535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32214625878590417134317023 48321938817885625701475535)
        ·
          refine ⟨72482908226828438552213303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48321938817885625701475535 72482908226828438552213303)
          ·
            refine ⟨108724362340242657828319955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72482908226828438552213303 108724362340242657828319955)
            ·
              refine ⟨163086543510363986742479933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108724362340242657828319955 163086543510363986742479933)
              ·
                refine ⟨61157453816386495028429975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163086543510363986742479933 61157453816386495028429975)
                ·
                  refine ⟨91736180724579742542644963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61157453816386495028429975 91736180724579742542644963)
                  ·
                    refine ⟨137604271086869613813967445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91736180724579742542644963 137604271086869613813967445)
                    ·
                      refine ⟨1612550051799253286882431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 137604271086869613813967445 1612550051799253286882431)
                      ·
                        rfl

theorem cell23_3140430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3140430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140430 prefixEnd_3140430 := by exact prefixLift 3140430
  have htrace : WordTrace (prefixWord ++ tailWord_3140430) baseStart_3140430 baseEnd_3140430 := by
    simpa [prefixWord, tailWord_3140430, baseEnd_3140430] using wordTrace_append hprefix tailTrace_3140430
  have hstable : (prefixWord ++ tailWord_3140430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140430).length < 2 ^ (prefixWord ++ tailWord_3140430).sum := by decide
  have hdescent : baseEnd_3140430 < baseStart_3140430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140444 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 6]
def baseStart_3140444 : Nat := 118140960795 + 3140444 * 2 ^ 59
def prefixEnd_3140444 : Nat := 4983230072969 + 3 ^ 40 * 3140444 * 2
def baseEnd_3140444 : Nat := 179173026725379581345263

theorem tailTrace_3140444 : CollatzResearch.WordTrace tailWord_3140444 prefixEnd_3140444 179173026725379581345263 := by
  unfold tailWord_3140444
  simp only [CollatzResearch.WordTrace]
  refine ⟨57270701317357603989846193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76360935089810138653128257 57270701317357603989846193)
  ·
    refine ⟨42953025988018202992384645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57270701317357603989846193 42953025988018202992384645)
    ·
      refine ⟨8053692372753413061072121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42953025988018202992384645 8053692372753413061072121)
      ·
        refine ⟨6040269279565059795804091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8053692372753413061072121 6040269279565059795804091)
        ·
          refine ⟨9060403919347589693706137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040269279565059795804091 9060403919347589693706137)
          ·
            refine ⟨6795302939510692270279603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9060403919347589693706137 6795302939510692270279603)
            ·
              refine ⟨10192954409266038405419405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795302939510692270279603 10192954409266038405419405)
              ·
                refine ⟨3822357903474764402032277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10192954409266038405419405 3822357903474764402032277)
                ·
                  refine ⟨179173026725379581345263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3822357903474764402032277 179173026725379581345263)
                  ·
                    rfl

theorem cell23_3140444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_3140444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140444 prefixEnd_3140444 := by exact prefixLift 3140444
  have htrace : WordTrace (prefixWord ++ tailWord_3140444) baseStart_3140444 baseEnd_3140444 := by
    simpa [prefixWord, tailWord_3140444, baseEnd_3140444] using wordTrace_append hprefix tailTrace_3140444
  have hstable : (prefixWord ++ tailWord_3140444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140444).length < 2 ^ (prefixWord ++ tailWord_3140444).sum := by decide
  have hdescent : baseEnd_3140444 < baseStart_3140444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140464 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 2, 3, 2]
def baseStart_3140464 : Nat := 118140960795 + 3140464 * 2 ^ 59
def prefixEnd_3140464 : Nat := 4983230072969 + 3 ^ 40 * 3140464 * 2
def baseEnd_3140464 : Nat := 1612567510141506153857275

theorem tailTrace_3140464 : CollatzResearch.WordTrace tailWord_3140464 prefixEnd_3140464 1612567510141506153857275 := by
  unfold tailWord_3140464
  simp only [CollatzResearch.WordTrace]
  refine ⟨57271066047321375697710223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76361421396428500930280297 57271066047321375697710223)
  ·
    refine ⟨85906599070982063546565335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57271066047321375697710223 85906599070982063546565335)
    ·
      refine ⟨128859898606473095319848003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85906599070982063546565335 128859898606473095319848003)
      ·
        refine ⟨193289847909709642979772005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128859898606473095319848003 193289847909709642979772005)
        ·
          refine ⟨36241846483070558058707251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193289847909709642979772005 36241846483070558058707251)
          ·
            refine ⟨54362769724605837088060877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36241846483070558058707251 54362769724605837088060877)
            ·
              refine ⟨20386038646727188908022829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54362769724605837088060877 20386038646727188908022829)
              ·
                refine ⟨7644764492522695840508561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20386038646727188908022829 7644764492522695840508561)
                ·
                  refine ⟨5733573369392021880381421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7644764492522695840508561 5733573369392021880381421)
                  ·
                    refine ⟨2150090013522008205143033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5733573369392021880381421 2150090013522008205143033)
                    ·
                      refine ⟨1612567510141506153857275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150090013522008205143033 1612567510141506153857275)
                      ·
                        rfl

theorem cell23_3140464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 3, 2].length) (baseStart_3140464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140464 prefixEnd_3140464 := by exact prefixLift 3140464
  have htrace : WordTrace (prefixWord ++ tailWord_3140464) baseStart_3140464 baseEnd_3140464 := by
    simpa [prefixWord, tailWord_3140464, baseEnd_3140464] using wordTrace_append hprefix tailTrace_3140464
  have hstable : (prefixWord ++ tailWord_3140464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140464).length < 2 ^ (prefixWord ++ tailWord_3140464).sum := by decide
  have hdescent : baseEnd_3140464 < baseStart_3140464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140488 : List Nat := [2, 1, 3, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_3140488 : Nat := 118140960795 + 3140488 * 2 ^ 59
def prefixEnd_3140488 : Nat := 4983230072969 + 3 ^ 40 * 3140488 * 2
def baseEnd_3140488 : Nat := 1612579833677214059957165

theorem tailTrace_3140488 : CollatzResearch.WordTrace tailWord_3140488 prefixEnd_3140488 1612579833677214059957165 := by
  unfold tailWord_3140488
  simp only [CollatzResearch.WordTrace]
  refine ⟨57271503723277901747147059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76362004964370535662862745 57271503723277901747147059)
  ·
    refine ⟨85907255584916852620720589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57271503723277901747147059 85907255584916852620720589)
    ·
      refine ⟨32215220844343819732770221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85907255584916852620720589 32215220844343819732770221)
      ·
        refine ⟨12080707816628932399788833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32215220844343819732770221 12080707816628932399788833)
        ·
          refine ⟨9060530862471699299841625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12080707816628932399788833 9060530862471699299841625)
          ·
            refine ⟨6795398146853774474881219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9060530862471699299841625 6795398146853774474881219)
            ·
              refine ⟨10193097220280661712321829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795398146853774474881219 10193097220280661712321829)
              ·
                refine ⟨1911205728802624071060343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10193097220280661712321829 1911205728802624071060343)
                ·
                  refine ⟨2866808593203936106590515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911205728802624071060343 2866808593203936106590515)
                  ·
                    refine ⟨4300212889805904159885773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2866808593203936106590515 4300212889805904159885773)
                    ·
                      refine ⟨1612579833677214059957165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4300212889805904159885773 1612579833677214059957165)
                      ·
                        rfl

theorem cell23_3140488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_3140488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140488 prefixEnd_3140488 := by exact prefixLift 3140488
  have htrace : WordTrace (prefixWord ++ tailWord_3140488) baseStart_3140488 baseEnd_3140488 := by
    simpa [prefixWord, tailWord_3140488, baseEnd_3140488] using wordTrace_append hprefix tailTrace_3140488
  have hstable : (prefixWord ++ tailWord_3140488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140488).length < 2 ^ (prefixWord ++ tailWord_3140488).sum := by decide
  have hdescent : baseEnd_3140488 < baseStart_3140488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140511 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 5, 2, 2]
def baseStart_3140511 : Nat := 118140960795 + 3140511 * 2 ^ 59
def prefixEnd_3140511 : Nat := 4983230072969 + 3 ^ 40 * 3140511 * 2
def baseEnd_3140511 : Nat := 1612591643732267469969559

theorem tailTrace_3140511 : CollatzResearch.WordTrace tailWord_3140511 prefixEnd_3140511 1612591643732267469969559 := by
  unfold tailWord_3140511
  simp only [CollatzResearch.WordTrace]
  refine ⟨114543846325472478422381387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76362564216981652281587591 114543846325472478422381387)
  ·
    refine ⟨171815769488208717633572081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114543846325472478422381387 171815769488208717633572081)
    ·
      refine ⟨128861827116156538225179061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171815769488208717633572081 128861827116156538225179061)
      ·
        refine ⟨12080796292139675458610537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128861827116156538225179061 12080796292139675458610537)
        ·
          refine ⟨9060597219104756593957903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12080796292139675458610537 9060597219104756593957903)
          ·
            refine ⟨13590895828657134890936855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9060597219104756593957903 13590895828657134890936855)
            ·
              refine ⟨20386343742985702336405283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13590895828657134890936855 20386343742985702336405283)
              ·
                refine ⟨30579515614478553504607925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20386343742985702336405283 30579515614478553504607925)
                ·
                  refine ⟨2866829588857364391056993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30579515614478553504607925 2866829588857364391056993)
                  ·
                    refine ⟨2150122191643023293292745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866829588857364391056993 2150122191643023293292745)
                    ·
                      refine ⟨1612591643732267469969559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150122191643023293292745 1612591643732267469969559)
                      ·
                        rfl

theorem cell23_3140511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_3140511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140511 prefixEnd_3140511 := by exact prefixLift 3140511
  have htrace : WordTrace (prefixWord ++ tailWord_3140511) baseStart_3140511 baseEnd_3140511 := by
    simpa [prefixWord, tailWord_3140511, baseEnd_3140511] using wordTrace_append hprefix tailTrace_3140511
  have hstable : (prefixWord ++ tailWord_3140511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140511).length < 2 ^ (prefixWord ++ tailWord_3140511).sum := by decide
  have hdescent : baseEnd_3140511 < baseStart_3140511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140525 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_3140525 : Nat := 118140960795 + 3140525 * 2 ^ 59
def prefixEnd_3140525 : Nat := 4983230072969 + 3 ^ 40 * 3140525 * 2
def baseEnd_3140525 : Nat := 537532944153810138398165

theorem tailTrace_3140525 : CollatzResearch.WordTrace tailWord_3140525 prefixEnd_3140525 537532944153810138398165 := by
  unfold tailWord_3140525
  simp only [CollatzResearch.WordTrace]
  refine ⟨114544356947421758813391029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76362904631614505875594019 114544356947421758813391029)
  ·
    refine ⟨10738533463820789888755409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114544356947421758813391029 10738533463820789888755409)
    ·
      refine ⟨8053900097865592416566557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10738533463820789888755409 8053900097865592416566557)
      ·
        refine ⟨3020212536699597156212459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8053900097865592416566557 3020212536699597156212459)
        ·
          refine ⟨4530318805049395734318689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020212536699597156212459 4530318805049395734318689)
          ·
            refine ⟨3397739103787046800739017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4530318805049395734318689 3397739103787046800739017)
            ·
              refine ⟨2548304327840285100554263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3397739103787046800739017 2548304327840285100554263)
              ·
                refine ⟨3822456491760427650831395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2548304327840285100554263 3822456491760427650831395)
                ·
                  refine ⟨5733684737640641476247093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822456491760427650831395 5733684737640641476247093)
                  ·
                    refine ⟨537532944153810138398165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5733684737640641476247093 537532944153810138398165)
                    ·
                      rfl

theorem cell23_3140525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_3140525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140525 prefixEnd_3140525 := by exact prefixLift 3140525
  have htrace : WordTrace (prefixWord ++ tailWord_3140525) baseStart_3140525 baseEnd_3140525 := by
    simpa [prefixWord, tailWord_3140525, baseEnd_3140525] using wordTrace_append hprefix tailTrace_3140525
  have hstable : (prefixWord ++ tailWord_3140525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140525).length < 2 ^ (prefixWord ++ tailWord_3140525).sum := by decide
  have hdescent : baseEnd_3140525 < baseStart_3140525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140527 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 3]
def baseStart_3140527 : Nat := 118140960795 + 3140527 * 2 ^ 59
def prefixEnd_3140527 : Nat := 4983230072969 + 3 ^ 40 * 3140527 * 2
def baseEnd_3140527 : Nat := 1612599859422739407369485

theorem tailTrace_3140527 : CollatzResearch.WordTrace tailWord_3140527 prefixEnd_3140527 1612599859422739407369485 := by
  unfold tailWord_3140527
  simp only [CollatzResearch.WordTrace]
  refine ⟨114544429893414513154963835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76362953262276342103309223 114544429893414513154963835)
  ·
    refine ⟨171816644840121769732445753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114544429893414513154963835 171816644840121769732445753)
    ·
      refine ⟨128862483630091327299334315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171816644840121769732445753 128862483630091327299334315)
      ·
        refine ⟨193293725445136990949001473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128862483630091327299334315 193293725445136990949001473)
        ·
          refine ⟨144970294083852743211751105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193293725445136990949001473 144970294083852743211751105)
          ·
            refine ⟨108727720562889557408813329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144970294083852743211751105 108727720562889557408813329)
            ·
              refine ⟨81545790422167168056609997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108727720562889557408813329 81545790422167168056609997)
              ·
                refine ⟨30579671408312688021228749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81545790422167168056609997 30579671408312688021228749)
                ·
                  refine ⟨11467376778117258007960781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30579671408312688021228749 11467376778117258007960781)
                  ·
                    refine ⟨4300266291793971752985293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11467376778117258007960781 4300266291793971752985293)
                    ·
                      refine ⟨1612599859422739407369485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4300266291793971752985293 1612599859422739407369485)
                      ·
                        rfl

theorem cell23_3140527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_3140527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140527 prefixEnd_3140527 := by exact prefixLift 3140527
  have htrace : WordTrace (prefixWord ++ tailWord_3140527) baseStart_3140527 baseEnd_3140527 := by
    simpa [prefixWord, tailWord_3140527, baseEnd_3140527] using wordTrace_append hprefix tailTrace_3140527
  have hstable : (prefixWord ++ tailWord_3140527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140527).length < 2 ^ (prefixWord ++ tailWord_3140527).sum := by decide
  have hdescent : baseEnd_3140527 < baseStart_3140527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140578 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3140578 : Nat := 118140960795 + 3140578 * 2 ^ 59
def prefixEnd_3140578 : Nat := 4983230072969 + 3 ^ 40 * 3140578 * 2
def baseEnd_3140578 : Nat := 1612626046936118707831751

theorem tailTrace_3140578 : CollatzResearch.WordTrace tailWord_3140578 prefixEnd_3140578 1612626046936118707831751 := by
  unfold tailWord_3140578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28636572504057437216267597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76364193344153165910046925 28636572504057437216267597)
  ·
    refine ⟨10738714689021538956100349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28636572504057437216267597 10738714689021538956100349)
    ·
      refine ⟨4027018008383077108537631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10738714689021538956100349 4027018008383077108537631)
      ·
        refine ⟨6040527012574615662806447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027018008383077108537631 6040527012574615662806447)
        ·
          refine ⟨9060790518861923494209671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040527012574615662806447 9060790518861923494209671)
          ·
            refine ⟨13591185778292885241314507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9060790518861923494209671 13591185778292885241314507)
            ·
              refine ⟨20386778667439327861971761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13591185778292885241314507 20386778667439327861971761)
              ·
                refine ⟨15290084000579495896478821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20386778667439327861971761 15290084000579495896478821)
                ·
                  refine ⟨2866890750108655480589779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15290084000579495896478821 2866890750108655480589779)
                  ·
                    refine ⟨4300336125162983220884669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2866890750108655480589779 4300336125162983220884669)
                    ·
                      refine ⟨1612626046936118707831751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4300336125162983220884669 1612626046936118707831751)
                      ·
                        rfl

theorem cell23_3140578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3140578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140578 prefixEnd_3140578 := by exact prefixLift 3140578
  have htrace : WordTrace (prefixWord ++ tailWord_3140578) baseStart_3140578 baseEnd_3140578 := by
    simpa [prefixWord, tailWord_3140578, baseEnd_3140578] using wordTrace_append hprefix tailTrace_3140578
  have hstable : (prefixWord ++ tailWord_3140578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140578).length < 2 ^ (prefixWord ++ tailWord_3140578).sum := by decide
  have hdescent : baseEnd_3140578 < baseStart_3140578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140587 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 3]
def baseStart_3140587 : Nat := 118140960795 + 3140587 * 2 ^ 59
def prefixEnd_3140587 : Nat := 4983230072969 + 3 ^ 40 * 3140587 * 2
def baseEnd_3140587 : Nat := 1612630668262009172619209

theorem tailTrace_3140587 : CollatzResearch.WordTrace tailWord_3140587 prefixEnd_3140587 1612630668262009172619209 := by
  unfold tailWord_3140587
  simp only [CollatzResearch.WordTrace]
  refine ⟨114546618273197143402148015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76364412182131428934765343 114546618273197143402148015)
  ·
    refine ⟨171819927409795715103222023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114546618273197143402148015 171819927409795715103222023)
    ·
      refine ⟨257729891114693572654833035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171819927409795715103222023 257729891114693572654833035)
      ·
        refine ⟨386594836672040358982249553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257729891114693572654833035 386594836672040358982249553)
        ·
          refine ⟨289946127504030269236687165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386594836672040358982249553 289946127504030269236687165)
          ·
            refine ⟨108729797814011350963757687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289946127504030269236687165 108729797814011350963757687)
            ·
              refine ⟨163094696721017026445636531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108729797814011350963757687 163094696721017026445636531)
              ·
                refine ⟨244642045081525539668454797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163094696721017026445636531 244642045081525539668454797)
                ·
                  refine ⟨91740766905572077375670549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244642045081525539668454797 91740766905572077375670549)
                  ·
                    refine ⟨4300348448698691126984557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91740766905572077375670549 4300348448698691126984557)
                    ·
                      refine ⟨1612630668262009172619209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4300348448698691126984557 1612630668262009172619209)
                      ·
                        rfl

theorem cell23_3140587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 3].length) (baseStart_3140587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140587 prefixEnd_3140587 := by exact prefixLift 3140587
  have htrace : WordTrace (prefixWord ++ tailWord_3140587) baseStart_3140587 baseEnd_3140587 := by
    simpa [prefixWord, tailWord_3140587, baseEnd_3140587] using wordTrace_append hprefix tailTrace_3140587
  have hstable : (prefixWord ++ tailWord_3140587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140587).length < 2 ^ (prefixWord ++ tailWord_3140587).sum := by decide
  have hdescent : baseEnd_3140587 < baseStart_3140587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140596 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3140596 : Nat := 118140960795 + 3140596 * 2 ^ 59
def prefixEnd_3140596 : Nat := 4983230072969 + 3 ^ 40 * 3140596 * 2
def baseEnd_3140596 : Nat := 1612635289587899637406669

theorem tailTrace_3140596 : CollatzResearch.WordTrace tailWord_3140596 prefixEnd_3140596 1612635289587899637406669 := by
  unfold tailWord_3140596
  simp only [CollatzResearch.WordTrace]
  refine ⟨57273473265082268969612821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76364631020109691959483761 57273473265082268969612821)
  ·
    refine ⟨2684694059300731357950601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57273473265082268969612821 2684694059300731357950601)
    ·
      refine ⟨2013520544475548518462951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2684694059300731357950601 2013520544475548518462951)
      ·
        refine ⟨3020280816713322777694427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013520544475548518462951 3020280816713322777694427)
        ·
          refine ⟨4530421225069984166541641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020280816713322777694427 4530421225069984166541641)
          ·
            refine ⟨3397815918802488124906231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4530421225069984166541641 3397815918802488124906231)
            ·
              refine ⟨5096723878203732187359347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397815918802488124906231 5096723878203732187359347)
              ·
                refine ⟨7645085817305598281039021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096723878203732187359347 7645085817305598281039021)
                ·
                  refine ⟨2866907181489599355389633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7645085817305598281039021 2866907181489599355389633)
                  ·
                    refine ⟨2150180386117199516542225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866907181489599355389633 2150180386117199516542225)
                    ·
                      refine ⟨1612635289587899637406669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150180386117199516542225 1612635289587899637406669)
                      ·
                        rfl

theorem cell23_3140596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3140596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140596 prefixEnd_3140596 := by exact prefixLift 3140596
  have htrace : WordTrace (prefixWord ++ tailWord_3140596) baseStart_3140596 baseEnd_3140596 := by
    simpa [prefixWord, tailWord_3140596, baseEnd_3140596] using wordTrace_append hprefix tailTrace_3140596
  have hstable : (prefixWord ++ tailWord_3140596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140596).length < 2 ^ (prefixWord ++ tailWord_3140596).sum := by decide
  have hdescent : baseEnd_3140596 < baseStart_3140596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140601 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 4, 2, 2]
def baseStart_3140601 : Nat := 118140960795 + 3140601 * 2 ^ 59
def prefixEnd_3140601 : Nat := 4983230072969 + 3 ^ 40 * 3140601 * 2
def baseEnd_3140601 : Nat := 1612637856991172117844145

theorem tailTrace_3140601 : CollatzResearch.WordTrace tailWord_3140601 prefixEnd_3140601 1612637856991172117844145 := by
  unfold tailWord_3140601
  simp only [CollatzResearch.WordTrace]
  refine ⟨114547128895146423793157657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76364752596764282528771771 114547128895146423793157657)
  ·
    refine ⟨85910346671359817844868243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114547128895146423793157657 85910346671359817844868243)
    ·
      refine ⟨128865520007039726767302365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85910346671359817844868243 128865520007039726767302365)
      ·
        refine ⟨48324570002639897537738387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128865520007039726767302365 48324570002639897537738387)
        ·
          refine ⟨72486855003959846306607581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48324570002639897537738387 72486855003959846306607581)
          ·
            refine ⟨27182570626484942364977843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72486855003959846306607581 27182570626484942364977843)
            ·
              refine ⟨40773855939727413547466765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27182570626484942364977843 40773855939727413547466765)
              ·
                refine ⟨15290195977397780080300037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40773855939727413547466765 15290195977397780080300037)
                ·
                  refine ⟨2866911745762083765056257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15290195977397780080300037 2866911745762083765056257)
                  ·
                    refine ⟨2150183809321562823792193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866911745762083765056257 2150183809321562823792193)
                    ·
                      refine ⟨1612637856991172117844145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150183809321562823792193 1612637856991172117844145)
                      ·
                        rfl

theorem cell23_3140601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_3140601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140601 prefixEnd_3140601 := by exact prefixLift 3140601
  have htrace : WordTrace (prefixWord ++ tailWord_3140601) baseStart_3140601 baseEnd_3140601 := by
    simpa [prefixWord, tailWord_3140601, baseEnd_3140601] using wordTrace_append hprefix tailTrace_3140601
  have hstable : (prefixWord ++ tailWord_3140601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140601).length < 2 ^ (prefixWord ++ tailWord_3140601).sum := by decide
  have hdescent : baseEnd_3140601 < baseStart_3140601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140664 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3140664 : Nat := 118140960795 + 3140664 * 2 ^ 59
def prefixEnd_3140664 : Nat := 4983230072969 + 3 ^ 40 * 3140664 * 2
def baseEnd_3140664 : Nat := 1612670206272405371356355

theorem tailTrace_3140664 : CollatzResearch.WordTrace tailWord_3140664 prefixEnd_3140664 1612670206272405371356355 := by
  unfold tailWord_3140664
  simp only [CollatzResearch.WordTrace]
  refine ⟨57274713346959092776350523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76366284462612123701800697 57274713346959092776350523)
  ·
    refine ⟨85912070020438639164525785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57274713346959092776350523 85912070020438639164525785)
    ·
      refine ⟨64434052515328979373394339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85912070020438639164525785 64434052515328979373394339)
      ·
        refine ⟨96651078772993469060091509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64434052515328979373394339 96651078772993469060091509)
        ·
          refine ⟨9061038634968137724383579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96651078772993469060091509 9061038634968137724383579)
          ·
            refine ⟨13591557952452206586575369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9061038634968137724383579 13591557952452206586575369)
            ·
              refine ⟨10193668464339154939931527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13591557952452206586575369 10193668464339154939931527)
              ·
                refine ⟨15290502696508732409897291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10193668464339154939931527 15290502696508732409897291)
                ·
                  refine ⟨22935754044763098614845937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15290502696508732409897291 22935754044763098614845937)
                  ·
                    refine ⟨17201815533572323961134453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22935754044763098614845937 17201815533572323961134453)
                    ·
                      refine ⟨1612670206272405371356355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17201815533572323961134453 1612670206272405371356355)
                      ·
                        rfl

theorem cell23_3140664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3140664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140664 prefixEnd_3140664 := by exact prefixLift 3140664
  have htrace : WordTrace (prefixWord ++ tailWord_3140664) baseStart_3140664 baseEnd_3140664 := by
    simpa [prefixWord, tailWord_3140664, baseEnd_3140664] using wordTrace_append hprefix tailTrace_3140664
  have hstable : (prefixWord ++ tailWord_3140664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140664).length < 2 ^ (prefixWord ++ tailWord_3140664).sum := by decide
  have hdescent : baseEnd_3140664 < baseStart_3140664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140687 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_3140687 : Nat := 118140960795 + 3140687 * 2 ^ 59
def prefixEnd_3140687 : Nat := 4983230072969 + 3 ^ 40 * 3140687 * 2
def baseEnd_3140687 : Nat := 1612682016327458781368749

theorem tailTrace_3140687 : CollatzResearch.WordTrace tailWord_3140687 prefixEnd_3140687 1612682016327458781368749 := by
  unfold tailWord_3140687
  simp only [CollatzResearch.WordTrace]
  refine ⟨114550265572834860480788315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76366843715223240320525543 114550265572834860480788315)
  ·
    refine ⟨171825398359252290721182473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114550265572834860480788315 171825398359252290721182473)
    ·
      refine ⟨128869048769439218040886855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171825398359252290721182473 128869048769439218040886855)
      ·
        refine ⟨193303573154158827061330283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128869048769439218040886855 193303573154158827061330283)
        ·
          refine ⟨289955359731238240591995425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193303573154158827061330283 289955359731238240591995425)
          ·
            refine ⟨217466519798428680443996569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289955359731238240591995425 217466519798428680443996569)
            ·
              refine ⟨163099889848821510332997427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217466519798428680443996569 163099889848821510332997427)
              ·
                refine ⟨244649834773232265499496141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163099889848821510332997427 244649834773232265499496141)
                ·
                  refine ⟨91743688039962099562311053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244649834773232265499496141 91743688039962099562311053)
                  ·
                    refine ⟨34403883014985787335866645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91743688039962099562311053 34403883014985787335866645)
                    ·
                      refine ⟨1612682016327458781368749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34403883014985787335866645 1612682016327458781368749)
                      ·
                        rfl

theorem cell23_3140687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_3140687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140687 prefixEnd_3140687 := by exact prefixLift 3140687
  have htrace : WordTrace (prefixWord ++ tailWord_3140687) baseStart_3140687 baseEnd_3140687 := by
    simpa [prefixWord, tailWord_3140687, baseEnd_3140687] using wordTrace_append hprefix tailTrace_3140687
  have hstable : (prefixWord ++ tailWord_3140687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140687).length < 2 ^ (prefixWord ++ tailWord_3140687).sum := by decide
  have hdescent : baseEnd_3140687 < baseStart_3140687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140718 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3140718 : Nat := 118140960795 + 3140718 * 2 ^ 59
def prefixEnd_3140718 : Nat := 4983230072969 + 3 ^ 40 * 3140718 * 2
def baseEnd_3140718 : Nat := 537565978075916053360369

theorem tailTrace_3140718 : CollatzResearch.WordTrace tailWord_3140718 prefixEnd_3140718 537565978075916053360369 := by
  unfold tailWord_3140718
  simp only [CollatzResearch.WordTrace]
  refine ⟨14318924529465319096895851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76367597490481701850111205 14318924529465319096895851)
  ·
    refine ⟨21478386794197978645343777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14318924529465319096895851 21478386794197978645343777)
    ·
      refine ⟨16108790095648483984007833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21478386794197978645343777 16108790095648483984007833)
      ·
        refine ⟨12081592571736362988005875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16108790095648483984007833 12081592571736362988005875)
        ·
          refine ⟨18122388857604544482008813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12081592571736362988005875 18122388857604544482008813)
          ·
            refine ⟨6795895821601704180753305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18122388857604544482008813 6795895821601704180753305)
            ·
              refine ⟨5096921866201278135564979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6795895821601704180753305 5096921866201278135564979)
              ·
                refine ⟨7645382799301917203347469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096921866201278135564979 7645382799301917203347469)
                ·
                  refine ⟨2867018549738218951255301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7645382799301917203347469 2867018549738218951255301)
                  ·
                    refine ⟨537565978075916053360369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2867018549738218951255301 537565978075916053360369)
                    ·
                      rfl

theorem cell23_3140718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3140718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140718 prefixEnd_3140718 := by exact prefixLift 3140718
  have htrace : WordTrace (prefixWord ++ tailWord_3140718) baseStart_3140718 baseEnd_3140718 := by
    simpa [prefixWord, tailWord_3140718, baseEnd_3140718] using wordTrace_append hprefix tailTrace_3140718
  have hstable : (prefixWord ++ tailWord_3140718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140718).length < 2 ^ (prefixWord ++ tailWord_3140718).sum := by decide
  have hdescent : baseEnd_3140718 < baseStart_3140718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140768 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 2, 3, 2]
def baseStart_3140768 : Nat := 118140960795 + 3140768 * 2 ^ 59
def prefixEnd_3140768 : Nat := 4983230072969 + 3 ^ 40 * 3140768 * 2
def baseEnd_3140768 : Nat := 1612723608260472964455877

theorem tailTrace_3140768 : CollatzResearch.WordTrace tailWord_3140768 prefixEnd_3140768 1612723608260472964455877 := by
  unfold tailWord_3140768
  simp only [CollatzResearch.WordTrace]
  refine ⟨57276609942770705657243479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76368813257027607542991305 57276609942770705657243479)
  ·
    refine ⟨85914914914156058485865219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57276609942770705657243479 85914914914156058485865219)
    ·
      refine ⟨128872372371234087728797829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85914914914156058485865219 128872372371234087728797829)
      ·
        refine ⟨24163569819606391449149593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128872372371234087728797829 24163569819606391449149593)
        ·
          refine ⟨18122677364704793586862195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24163569819606391449149593 18122677364704793586862195)
          ·
            refine ⟨27184016047057190380293293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18122677364704793586862195 27184016047057190380293293)
            ·
              refine ⟨10194006017646446392609985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27184016047057190380293293 10194006017646446392609985)
              ·
                refine ⟨7645504513234834794457489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10194006017646446392609985 7645504513234834794457489)
                ·
                  refine ⟨5734128384926126095843117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7645504513234834794457489 5734128384926126095843117)
                  ·
                    refine ⟨2150298144347297285941169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5734128384926126095843117 2150298144347297285941169)
                    ·
                      refine ⟨1612723608260472964455877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150298144347297285941169 1612723608260472964455877)
                      ·
                        rfl

theorem cell23_3140768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_3140768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140768 prefixEnd_3140768 := by exact prefixLift 3140768
  have htrace : WordTrace (prefixWord ++ tailWord_3140768) baseStart_3140768 baseEnd_3140768 := by
    simpa [prefixWord, tailWord_3140768, baseEnd_3140768] using wordTrace_append hprefix tailTrace_3140768
  have hstable : (prefixWord ++ tailWord_3140768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140768).length < 2 ^ (prefixWord ++ tailWord_3140768).sum := by decide
  have hdescent : baseEnd_3140768 < baseStart_3140768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140775 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3140775 : Nat := 118140960795 + 3140775 * 2 ^ 59
def prefixEnd_3140775 : Nat := 4983230072969 + 3 ^ 40 * 3140775 * 2
def baseEnd_3140775 : Nat := 1612727202625054437068345

theorem tailTrace_3140775 : CollatzResearch.WordTrace tailWord_3140775 prefixEnd_3140775 1612727202625054437068345 := by
  unfold tailWord_3140775
  simp only [CollatzResearch.WordTrace]
  refine ⟨114553475196516051509991779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76368983464344034339994519 114553475196516051509991779)
  ·
    refine ⟨171830212794774077264987669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114553475196516051509991779 171830212794774077264987669)
    ·
      refine ⟨8054541224755034871796297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 171830212794774077264987669 8054541224755034871796297)
      ·
        refine ⟨6040905918566276153847223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8054541224755034871796297 6040905918566276153847223)
        ·
          refine ⟨9061358877849414230770835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040905918566276153847223 9061358877849414230770835)
          ·
            refine ⟨13592038316774121346156253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9061358877849414230770835 13592038316774121346156253)
            ·
              refine ⟨5097014368790295504808595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13592038316774121346156253 5097014368790295504808595)
              ·
                refine ⟨7645521553185443257212893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5097014368790295504808595 7645521553185443257212893)
                ·
                  refine ⟨2867070582444541221454835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7645521553185443257212893 2867070582444541221454835)
                  ·
                    refine ⟨4300605873666811832182253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867070582444541221454835 4300605873666811832182253)
                    ·
                      refine ⟨1612727202625054437068345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4300605873666811832182253 1612727202625054437068345)
                      ·
                        rfl

theorem cell23_3140775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3140775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140775 prefixEnd_3140775 := by exact prefixLift 3140775
  have htrace : WordTrace (prefixWord ++ tailWord_3140775) baseStart_3140775 baseEnd_3140775 := by
    simpa [prefixWord, tailWord_3140775, baseEnd_3140775] using wordTrace_append hprefix tailTrace_3140775
  have hstable : (prefixWord ++ tailWord_3140775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140775).length < 2 ^ (prefixWord ++ tailWord_3140775).sum := by decide
  have hdescent : baseEnd_3140775 < baseStart_3140775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140798 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3140798 : Nat := 118140960795 + 3140798 * 2 ^ 59
def prefixEnd_3140798 : Nat := 4983230072969 + 3 ^ 40 * 3140798 * 2
def baseEnd_3140798 : Nat := 1612739012680107847080739

theorem tailTrace_3140798 : CollatzResearch.WordTrace tailWord_3140798 prefixEnd_3140798 1612739012680107847080739 := by
  unfold tailWord_3140798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319289259429090804759881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76369542716955150958719365 14319289259429090804759881)
  ·
    refine ⟨10739466944571818103569911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14319289259429090804759881 10739466944571818103569911)
    ·
      refine ⟨16109200416857727155354867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10739466944571818103569911 16109200416857727155354867)
      ·
        refine ⟨24163800625286590733032301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16109200416857727155354867 24163800625286590733032301)
        ·
          refine ⟨9061425234482471524887113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24163800625286590733032301 9061425234482471524887113)
          ·
            refine ⟨6796068925861853643665335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9061425234482471524887113 6796068925861853643665335)
            ·
              refine ⟨10194103388792780465498003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796068925861853643665335 10194103388792780465498003)
              ·
                refine ⟨15291155083189170698247005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10194103388792780465498003 15291155083189170698247005)
                ·
                  refine ⟨5734183156195939011842627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15291155083189170698247005 5734183156195939011842627)
                  ·
                    refine ⟨8601274734293908517763941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5734183156195939011842627 8601274734293908517763941)
                    ·
                      refine ⟨1612739012680107847080739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8601274734293908517763941 1612739012680107847080739)
                      ·
                        rfl

theorem cell23_3140798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3140798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140798 prefixEnd_3140798 := by exact prefixLift 3140798
  have htrace : WordTrace (prefixWord ++ tailWord_3140798) baseStart_3140798 baseEnd_3140798 := by
    simpa [prefixWord, tailWord_3140798, baseEnd_3140798] using wordTrace_append hprefix tailTrace_3140798
  have hstable : (prefixWord ++ tailWord_3140798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140798).length < 2 ^ (prefixWord ++ tailWord_3140798).sum := by decide
  have hdescent : baseEnd_3140798 < baseStart_3140798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140832 : List Nat := [2, 1, 1, 3, 1, 5, 1, 4, 1, 2, 2]
def baseStart_3140832 : Nat := 118140960795 + 3140832 * 2 ^ 59
def prefixEnd_3140832 : Nat := 4983230072969 + 3 ^ 40 * 3140832 * 2
def baseEnd_3140832 : Nat := 1612756471022360714055583

theorem tailTrace_3140832 : CollatzResearch.WordTrace tailWord_3140832 prefixEnd_3140832 1612756471022360714055583 := by
  unfold tailWord_3140832
  simp only [CollatzResearch.WordTrace]
  refine ⟨57277777078654775122408375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76370369438206366829877833 57277777078654775122408375)
  ·
    refine ⟨85916665617982162683612563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57277777078654775122408375 85916665617982162683612563)
    ·
      refine ⟨128874998426973244025418845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85916665617982162683612563 128874998426973244025418845)
      ·
        refine ⟨48328124410114966509532067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128874998426973244025418845 48328124410114966509532067)
        ·
          refine ⟨72492186615172449764298101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48328124410114966509532067 72492186615172449764298101)
          ·
            refine ⟨6796142495172417165402947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72492186615172449764298101 6796142495172417165402947)
            ·
              refine ⟨10194213742758625748104421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796142495172417165402947 10194213742758625748104421)
              ·
                refine ⟨1911415076767242327769579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10194213742758625748104421 1911415076767242327769579)
                ·
                  refine ⟨2867122615150863491654369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911415076767242327769579 2867122615150863491654369)
                  ·
                    refine ⟨2150341961363147618740777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867122615150863491654369 2150341961363147618740777)
                    ·
                      refine ⟨1612756471022360714055583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150341961363147618740777 1612756471022360714055583)
                      ·
                        rfl

theorem cell23_3140832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_3140832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140832 prefixEnd_3140832 := by exact prefixLift 3140832
  have htrace : WordTrace (prefixWord ++ tailWord_3140832) baseStart_3140832 baseEnd_3140832 := by
    simpa [prefixWord, tailWord_3140832, baseEnd_3140832] using wordTrace_append hprefix tailTrace_3140832
  have hstable : (prefixWord ++ tailWord_3140832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140832).length < 2 ^ (prefixWord ++ tailWord_3140832).sum := by decide
  have hdescent : baseEnd_3140832 < baseStart_3140832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140841 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 9, 2]
def baseStart_3140841 : Nat := 118140960795 + 3140841 * 2 ^ 59
def prefixEnd_3140841 : Nat := 4983230072969 + 3 ^ 40 * 3140841 * 2
def baseEnd_3140841 : Nat := 1612761092348251178843041

theorem tailTrace_3140841 : CollatzResearch.WordTrace tailWord_3140841 prefixEnd_3140841 1612761092348251178843041 := by
  unfold tailWord_3140841
  simp only [CollatzResearch.WordTrace]
  refine ⟨114555882414276944781894377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76370588276184629854596251 114555882414276944781894377)
  ·
    refine ⟨85916911810707708586420783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114555882414276944781894377 85916911810707708586420783)
    ·
      refine ⟨128875367716061562879631175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85916911810707708586420783 128875367716061562879631175)
      ·
        refine ⟨193313051574092344319446763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128875367716061562879631175 193313051574092344319446763)
        ·
          refine ⟨289969577361138516479170145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193313051574092344319446763 289969577361138516479170145)
          ·
            refine ⟨217477183020853887359377609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289969577361138516479170145 217477183020853887359377609)
            ·
              refine ⟨163107887265640415519533207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217477183020853887359377609 163107887265640415519533207)
              ·
                refine ⟨244661830898460623279299811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163107887265640415519533207 244661830898460623279299811)
                ·
                  refine ⟨366992746347690934918949717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244661830898460623279299811 366992746347690934918949717)
                  ·
                    refine ⟨2150348123131001571790721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 366992746347690934918949717 2150348123131001571790721)
                    ·
                      refine ⟨1612761092348251178843041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150348123131001571790721 1612761092348251178843041)
                      ·
                        rfl

theorem cell23_3140841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 9, 2].length) (baseStart_3140841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140841 prefixEnd_3140841 := by exact prefixLift 3140841
  have htrace : WordTrace (prefixWord ++ tailWord_3140841) baseStart_3140841 baseEnd_3140841 := by
    simpa [prefixWord, tailWord_3140841, baseEnd_3140841] using wordTrace_append hprefix tailTrace_3140841
  have hstable : (prefixWord ++ tailWord_3140841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140841).length < 2 ^ (prefixWord ++ tailWord_3140841).sum := by decide
  have hdescent : baseEnd_3140841 < baseStart_3140841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140858 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2]
def baseStart_3140858 : Nat := 118140960795 + 3140858 * 2 ^ 59
def prefixEnd_3140858 : Nat := 4983230072969 + 3 ^ 40 * 3140858 * 2
def baseEnd_3140858 : Nat := 1612769821519377612330463

theorem tailTrace_3140858 : CollatzResearch.WordTrace tailWord_3140858 prefixEnd_3140858 1612769821519377612330463 := by
  unfold tailWord_3140858
  simp only [CollatzResearch.WordTrace]
  refine ⟨28639125613803839171315807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76371001636810237790175485 28639125613803839171315807)
  ·
    refine ⟨42958688420705758756973711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28639125613803839171315807 42958688420705758756973711)
    ·
      refine ⟨64438032631058638135460567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42958688420705758756973711 64438032631058638135460567)
      ·
        refine ⟨96657048946587957203190851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64438032631058638135460567 96657048946587957203190851)
        ·
          refine ⟨144985573419881935804786277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96657048946587957203190851 144985573419881935804786277)
          ·
            refine ⟨27184795016227862963397427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144985573419881935804786277 27184795016227862963397427)
            ·
              refine ⟨40777192524341794445096141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27184795016227862963397427 40777192524341794445096141)
              ·
                refine ⟨15291447196628172916911053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40777192524341794445096141 15291447196628172916911053)
                ·
                  refine ⟨5734292698735564843841645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15291447196628172916911053 5734292698735564843841645)
                  ·
                    refine ⟨2150359762025836816440617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5734292698735564843841645 2150359762025836816440617)
                    ·
                      refine ⟨1612769821519377612330463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150359762025836816440617 1612769821519377612330463)
                      ·
                        rfl

theorem cell23_3140858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_3140858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140858 prefixEnd_3140858 := by exact prefixLift 3140858
  have htrace : WordTrace (prefixWord ++ tailWord_3140858) baseStart_3140858 baseEnd_3140858 := by
    simpa [prefixWord, tailWord_3140858, baseEnd_3140858] using wordTrace_append hprefix tailTrace_3140858
  have hstable : (prefixWord ++ tailWord_3140858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140858).length < 2 ^ (prefixWord ++ tailWord_3140858).sum := by decide
  have hdescent : baseEnd_3140858 < baseStart_3140858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140864 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 3, 8]
def baseStart_3140864 : Nat := 118140960795 + 3140864 * 2 ^ 59
def prefixEnd_3140864 : Nat := 4983230072969 + 3 ^ 40 * 3140864 * 2
def baseEnd_3140864 : Nat := 537590967467768196285145

theorem tailTrace_3140864 : CollatzResearch.WordTrace tailWord_3140864 prefixEnd_3140864 537590967467768196285145 := by
  unfold tailWord_3140864
  simp only [CollatzResearch.WordTrace]
  refine ⟨57278360646596809854990823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76371147528795746473321097 57278360646596809854990823)
  ·
    refine ⟨85917540969895214782486235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57278360646596809854990823 85917540969895214782486235)
    ·
      refine ⟨128876311454842822173729353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85917540969895214782486235 128876311454842822173729353)
      ·
        refine ⟨96657233591132116630297015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128876311454842822173729353 96657233591132116630297015)
        ·
          refine ⟨144985850386698174945445523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96657233591132116630297015 144985850386698174945445523)
          ·
            refine ⟨217478775580047262418168285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144985850386698174945445523 217478775580047262418168285)
            ·
              refine ⟨81554540842517723406813107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217478775580047262418168285 81554540842517723406813107)
              ·
                refine ⟨122331811263776585110219661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81554540842517723406813107 122331811263776585110219661)
                ·
                  refine ⟨45874429223916219416332373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122331811263776585110219661 45874429223916219416332373)
                  ·
                    refine ⟨537590967467768196285145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45874429223916219416332373 537590967467768196285145)
                    ·
                      rfl

theorem cell23_3140864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_3140864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140864 prefixEnd_3140864 := by exact prefixLift 3140864
  have htrace : WordTrace (prefixWord ++ tailWord_3140864) baseStart_3140864 baseEnd_3140864 := by
    simpa [prefixWord, tailWord_3140864, baseEnd_3140864] using wordTrace_append hprefix tailTrace_3140864
  have hstable : (prefixWord ++ tailWord_3140864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140864).length < 2 ^ (prefixWord ++ tailWord_3140864).sum := by decide
  have hdescent : baseEnd_3140864 < baseStart_3140864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140866 : List Nat := [3, 4, 1, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3140866 : Nat := 118140960795 + 3140866 * 2 ^ 59
def prefixEnd_3140866 : Nat := 4983230072969 + 3 ^ 40 * 3140866 * 2
def baseEnd_3140866 : Nat := 1612773929364613581030427

theorem tailTrace_3140866 : CollatzResearch.WordTrace tailWord_3140866 prefixEnd_3140866 1612773929364613581030427 := by
  unfold tailWord_3140866
  simp only [CollatzResearch.WordTrace]
  refine ⟨28639198559796593512888613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76371196159457582701036301 28639198559796593512888613)
  ·
    refine ⟨5369849729961861283666615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28639198559796593512888613 5369849729961861283666615)
    ·
      refine ⟨8054774594942791925499923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5369849729961861283666615 8054774594942791925499923)
      ·
        refine ⟨12082161892414187888249885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8054774594942791925499923 12082161892414187888249885)
        ·
          refine ⟨4530810709655320458093707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12082161892414187888249885 4530810709655320458093707)
          ·
            refine ⟨6796216064482980687140561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4530810709655320458093707 6796216064482980687140561)
            ·
              refine ⟨5097162048362235515355421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6796216064482980687140561 5097162048362235515355421)
              ·
                refine ⟨1911435768135838318258283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5097162048362235515355421 1911435768135838318258283)
                ·
                  refine ⟨2867153652203757477387425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911435768135838318258283 2867153652203757477387425)
                  ·
                    refine ⟨2150365239152818108040569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867153652203757477387425 2150365239152818108040569)
                    ·
                      refine ⟨1612773929364613581030427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150365239152818108040569 1612773929364613581030427)
                      ·
                        rfl

theorem cell23_3140866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3140866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140866 prefixEnd_3140866 := by exact prefixLift 3140866
  have htrace : WordTrace (prefixWord ++ tailWord_3140866) baseStart_3140866 baseEnd_3140866 := by
    simpa [prefixWord, tailWord_3140866, baseEnd_3140866] using wordTrace_append hprefix tailTrace_3140866
  have hstable : (prefixWord ++ tailWord_3140866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140866).length < 2 ^ (prefixWord ++ tailWord_3140866).sum := by decide
  have hdescent : baseEnd_3140866 < baseStart_3140866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140875 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 1, 3, 2]
def baseStart_3140875 : Nat := 118140960795 + 3140875 * 2 ^ 59
def prefixEnd_3140875 : Nat := 4983230072969 + 3 ^ 40 * 3140875 * 2
def baseEnd_3140875 : Nat := 1612778550690504045817885

theorem tailTrace_3140875 : CollatzResearch.WordTrace tailWord_3140875 prefixEnd_3140875 1612778550690504045817885 := by
  unfold tailWord_3140875
  simp only [CollatzResearch.WordTrace]
  refine ⟨114557122496153768588632079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76371414997435845725754719 114557122496153768588632079)
  ·
    refine ⟨171835683744230652882948119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114557122496153768588632079 171835683744230652882948119)
    ·
      refine ⟨257753525616345979324422179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171835683744230652882948119 257753525616345979324422179)
      ·
        refine ⟨386630288424518968986633269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257753525616345979324422179 386630288424518968986633269)
        ·
          refine ⟨36246589539798653342496869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 386630288424518968986633269 36246589539798653342496869)
          ·
            refine ⟨6796235538712247501718163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36246589539798653342496869 6796235538712247501718163)
            ·
              refine ⟨10194353308068371252577245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796235538712247501718163 10194353308068371252577245)
              ·
                refine ⟨3822882490525639219716467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10194353308068371252577245 3822882490525639219716467)
                ·
                  refine ⟨5734323735788458829574701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822882490525639219716467 5734323735788458829574701)
                  ·
                    refine ⟨2150371400920672061090513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5734323735788458829574701 2150371400920672061090513)
                    ·
                      refine ⟨1612778550690504045817885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150371400920672061090513 1612778550690504045817885)
                      ·
                        rfl

theorem cell23_3140875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 3, 2].length) (baseStart_3140875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140875 prefixEnd_3140875 := by exact prefixLift 3140875
  have htrace : WordTrace (prefixWord ++ tailWord_3140875) baseStart_3140875 baseEnd_3140875 := by
    simpa [prefixWord, tailWord_3140875, baseEnd_3140875] using wordTrace_append hprefix tailTrace_3140875
  have hstable : (prefixWord ++ tailWord_3140875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140875).length < 2 ^ (prefixWord ++ tailWord_3140875).sum := by decide
  have hdescent : baseEnd_3140875 < baseStart_3140875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140909 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3140909 : Nat := 118140960795 + 3140909 * 2 ^ 59
def prefixEnd_3140909 : Nat := 4983230072969 + 3 ^ 40 * 3140909 * 2
def baseEnd_3140909 : Nat := 1612796009032756912792729

theorem tailTrace_3140909 : CollatzResearch.WordTrace tailWord_3140909 prefixEnd_3140909 1612796009032756912792729 := by
  unfold tailWord_3140909
  simp only [CollatzResearch.WordTrace]
  refine ⟨114558362578030592395369781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76372241718687061596913187 114558362578030592395369781)
  ·
    refine ⟨10739846491690368037065917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114558362578030592395369781 10739846491690368037065917)
    ·
      refine ⟨4027442434383888013899719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10739846491690368037065917 4027442434383888013899719)
      ·
        refine ⟨6041163651575832020849579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027442434383888013899719 6041163651575832020849579)
        ·
          refine ⟨9061745477363748031274369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041163651575832020849579 9061745477363748031274369)
          ·
            refine ⟨6796309108022811023455777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9061745477363748031274369 6796309108022811023455777)
            ·
              refine ⟨5097231831017108267591833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6796309108022811023455777 5097231831017108267591833)
              ·
                refine ⟨3822923873262831200693875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097231831017108267591833 3822923873262831200693875)
                ·
                  refine ⟨5734385809894246801040813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822923873262831200693875 5734385809894246801040813)
                  ·
                    refine ⟨2150394678710342550390305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5734385809894246801040813 2150394678710342550390305)
                    ·
                      refine ⟨1612796009032756912792729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150394678710342550390305 1612796009032756912792729)
                      ·
                        rfl

theorem cell23_3140909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3140909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140909 prefixEnd_3140909 := by exact prefixLift 3140909
  have htrace : WordTrace (prefixWord ++ tailWord_3140909) baseStart_3140909 baseEnd_3140909 := by
    simpa [prefixWord, tailWord_3140909, baseEnd_3140909] using wordTrace_append hprefix tailTrace_3140909
  have hstable : (prefixWord ++ tailWord_3140909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140909).length < 2 ^ (prefixWord ++ tailWord_3140909).sum := by decide
  have hdescent : baseEnd_3140909 < baseStart_3140909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140925 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3140925 : Nat := 118140960795 + 3140925 * 2 ^ 59
def prefixEnd_3140925 : Nat := 4983230072969 + 3 ^ 40 * 3140925 * 2
def baseEnd_3140925 : Nat := 1612804224723228850192655

theorem tailTrace_3140925 : CollatzResearch.WordTrace tailWord_3140925 prefixEnd_3140925 1612804224723228850192655 := by
  unfold tailWord_3140925
  simp only [CollatzResearch.WordTrace]
  refine ⟨114558946145972627127952229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76372630763981751418634819 114558946145972627127952229)
  ·
    refine ⟨21479802402369867586491043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114558946145972627127952229 21479802402369867586491043)
    ·
      refine ⟨32219703603554801379736565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21479802402369867586491043 32219703603554801379736565)
      ·
        refine ⟨3020597212833262629350303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32219703603554801379736565 3020597212833262629350303)
        ·
          refine ⟨4530895819249893944025455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020597212833262629350303 4530895819249893944025455)
          ·
            refine ⟨6796343728874840916038183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4530895819249893944025455 6796343728874840916038183)
            ·
              refine ⟨10194515593312261374057275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796343728874840916038183 10194515593312261374057275)
              ·
                refine ⟨15291773389968392061085913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10194515593312261374057275 15291773389968392061085913)
                ·
                  refine ⟨11468830042476294045814435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15291773389968392061085913 11468830042476294045814435)
                  ·
                    refine ⟨17203245063714441068721653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11468830042476294045814435 17203245063714441068721653)
                    ·
                      refine ⟨1612804224723228850192655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17203245063714441068721653 1612804224723228850192655)
                      ·
                        rfl

theorem cell23_3140925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3140925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140925 prefixEnd_3140925 := by exact prefixLift 3140925
  have htrace : WordTrace (prefixWord ++ tailWord_3140925) baseStart_3140925 baseEnd_3140925 := by
    simpa [prefixWord, tailWord_3140925, baseEnd_3140925] using wordTrace_append hprefix tailTrace_3140925
  have hstable : (prefixWord ++ tailWord_3140925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140925).length < 2 ^ (prefixWord ++ tailWord_3140925).sum := by decide
  have hdescent : baseEnd_3140925 < baseStart_3140925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140945 : List Nat := [1, 2, 2, 1, 4, 1, 5, 2, 5]
def baseStart_3140945 : Nat := 118140960795 + 3140945 * 2 ^ 59
def prefixEnd_3140945 : Nat := 4983230072969 + 3 ^ 40 * 3140945 * 2
def baseEnd_3140945 : Nat := 179201610481813196882507

theorem tailTrace_3140945 : CollatzResearch.WordTrace tailWord_3140945 prefixEnd_3140945 179201610481813196882507 := by
  unfold tailWord_3140945
  simp only [CollatzResearch.WordTrace]
  refine ⟨114559675605900170543680289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76373117070600113695786859 114559675605900170543680289)
  ·
    refine ⟨85919756704425127907760217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114559675605900170543680289 85919756704425127907760217)
    ·
      refine ⟨64439817528318845930820163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85919756704425127907760217 64439817528318845930820163)
      ·
        refine ⟨96659726292478268896230245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64439817528318845930820163 96659726292478268896230245)
        ·
          refine ⟨18123698679839675418043171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96659726292478268896230245 18123698679839675418043171)
          ·
            refine ⟨27185548019759513127064757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18123698679839675418043171 27185548019759513127064757)
            ·
              refine ⟨2548645126852454355662321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27185548019759513127064757 2548645126852454355662321)
              ·
                refine ⟨1911483845139340766746741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2548645126852454355662321 1911483845139340766746741)
                ·
                  refine ⟨179201610481813196882507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1911483845139340766746741 179201610481813196882507)
                  ·
                    rfl

theorem cell23_3140945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 5].length) (baseStart_3140945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140945 prefixEnd_3140945 := by exact prefixLift 3140945
  have htrace : WordTrace (prefixWord ++ tailWord_3140945) baseStart_3140945 baseEnd_3140945 := by
    simpa [prefixWord, tailWord_3140945, baseEnd_3140945] using wordTrace_append hprefix tailTrace_3140945
  have hstable : (prefixWord ++ tailWord_3140945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140945).length < 2 ^ (prefixWord ++ tailWord_3140945).sum := by decide
  have hdescent : baseEnd_3140945 < baseStart_3140945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140950 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3140950 : Nat := 118140960795 + 3140950 * 2 ^ 59
def prefixEnd_3140950 : Nat := 4983230072969 + 3 ^ 40 * 3140950 * 2
def baseEnd_3140950 : Nat := 1612817061739591252380041

theorem tailTrace_3140950 : CollatzResearch.WordTrace tailWord_3140950 prefixEnd_3140950 1612817061739591252380041 := by
  unfold tailWord_3140950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7159991123180128524850769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76373238647254704265074869 7159991123180128524850769)
  ·
    refine ⟨5369993342385096393638077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7159991123180128524850769 5369993342385096393638077)
    ·
      refine ⟨2013747503394411147614279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5369993342385096393638077 2013747503394411147614279)
      ·
        refine ⟨3020621255091616721421419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013747503394411147614279 3020621255091616721421419)
        ·
          refine ⟨4530931882637425082132129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020621255091616721421419 4530931882637425082132129)
          ·
            refine ⟨3398198911978068811599097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4530931882637425082132129 3398198911978068811599097)
            ·
              refine ⟨2548649183983551608699323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398198911978068811599097 2548649183983551608699323)
              ·
                refine ⟨3822973775975327413048985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2548649183983551608699323 3822973775975327413048985)
                ·
                  refine ⟨2867230331981495559786739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3822973775975327413048985 2867230331981495559786739)
                  ·
                    refine ⟨4300845497972243339680109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867230331981495559786739 4300845497972243339680109)
                    ·
                      refine ⟨1612817061739591252380041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4300845497972243339680109 1612817061739591252380041)
                      ·
                        rfl

theorem cell23_3140950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3140950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140950 prefixEnd_3140950 := by exact prefixLift 3140950
  have htrace : WordTrace (prefixWord ++ tailWord_3140950) baseStart_3140950 baseEnd_3140950 := by
    simpa [prefixWord, tailWord_3140950, baseEnd_3140950] using wordTrace_append hprefix tailTrace_3140950
  have hstable : (prefixWord ++ tailWord_3140950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140950).length < 2 ^ (prefixWord ++ tailWord_3140950).sum := by decide
  have hdescent : baseEnd_3140950 < baseStart_3140950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140951 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3140951 : Nat := 118140960795 + 3140951 * 2 ^ 59
def prefixEnd_3140951 : Nat := 4983230072969 + 3 ^ 40 * 3140951 * 2
def baseEnd_3140951 : Nat := 1612817575220245748467535

theorem tailTrace_3140951 : CollatzResearch.WordTrace tailWord_3140951 prefixEnd_3140951 1612817575220245748467535 := by
  unfold tailWord_3140951
  simp only [CollatzResearch.WordTrace]
  refine ⟨114559894443878433568398707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76373262962585622378932471 114559894443878433568398707)
  ·
    refine ⟨171839841665817650352598061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114559894443878433568398707 171839841665817650352598061)
    ·
      refine ⟨64439940624681618882224273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171839841665817650352598061 64439940624681618882224273)
      ·
        refine ⟨48329955468511214161668205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64439940624681618882224273 48329955468511214161668205)
        ·
          refine ⟨18123733300691705310625577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48329955468511214161668205 18123733300691705310625577)
          ·
            refine ⟨13592799975518778982969183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18123733300691705310625577 13592799975518778982969183)
            ·
              refine ⟨20389199963278168474453775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13592799975518778982969183 20389199963278168474453775)
              ·
                refine ⟨30583799944917252711680663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20389199963278168474453775 30583799944917252711680663)
                ·
                  refine ⟨45875699917375879067520995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30583799944917252711680663 45875699917375879067520995)
                  ·
                    refine ⟨68813549876063818601281493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45875699917375879067520995 68813549876063818601281493)
                    ·
                      refine ⟨1612817575220245748467535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68813549876063818601281493 1612817575220245748467535)
                      ·
                        rfl

theorem cell23_3140951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3140951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140951 prefixEnd_3140951 := by exact prefixLift 3140951
  have htrace : WordTrace (prefixWord ++ tailWord_3140951) baseStart_3140951 baseEnd_3140951 := by
    simpa [prefixWord, tailWord_3140951, baseEnd_3140951] using wordTrace_append hprefix tailTrace_3140951
  have hstable : (prefixWord ++ tailWord_3140951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140951).length < 2 ^ (prefixWord ++ tailWord_3140951).sum := by decide
  have hdescent : baseEnd_3140951 < baseStart_3140951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140961 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3140961 : Nat := 118140960795 + 3140961 * 2 ^ 59
def prefixEnd_3140961 : Nat := 4983230072969 + 3 ^ 40 * 3140961 * 2
def baseEnd_3140961 : Nat := 1612822710026790709342489

theorem tailTrace_3140961 : CollatzResearch.WordTrace tailWord_3140961 prefixEnd_3140961 1612822710026790709342489 := by
  unfold tailWord_3140961
  simp only [CollatzResearch.WordTrace]
  refine ⟨114560259173842205276262737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76373506115894803517508491 114560259173842205276262737)
  ·
    refine ⟨85920194380381653957197053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114560259173842205276262737 85920194380381653957197053)
    ·
      refine ⟨32220072892643120233948895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85920194380381653957197053 32220072892643120233948895)
      ·
        refine ⟨48330109338964680350923343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32220072892643120233948895 48330109338964680350923343)
        ·
          refine ⟨72495164008447020526385015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48330109338964680350923343 72495164008447020526385015)
          ·
            refine ⟨108742746012670530789577523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72495164008447020526385015 108742746012670530789577523)
            ·
              refine ⟨163114119019005796184366285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108742746012670530789577523 163114119019005796184366285)
              ·
                refine ⟨61167794632127173569137357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163114119019005796184366285 61167794632127173569137357)
                ·
                  refine ⟨22937922987047690088426509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61167794632127173569137357 22937922987047690088426509)
                  ·
                    refine ⟨8601721120142883783159941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22937922987047690088426509 8601721120142883783159941)
                    ·
                      refine ⟨1612822710026790709342489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8601721120142883783159941 1612822710026790709342489)
                      ·
                        rfl

theorem cell23_3140961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3140961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3140961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3140961 prefixEnd_3140961 := by exact prefixLift 3140961
  have htrace : WordTrace (prefixWord ++ tailWord_3140961) baseStart_3140961 baseEnd_3140961 := by
    simpa [prefixWord, tailWord_3140961, baseEnd_3140961] using wordTrace_append hprefix tailTrace_3140961
  have hstable : (prefixWord ++ tailWord_3140961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140961).length < 2 ^ (prefixWord ++ tailWord_3140961).sum := by decide
  have hdescent : baseEnd_3140961 < baseStart_3140961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141012 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_3141012 : Nat := 118140960795 + 3141012 * 2 ^ 59
def prefixEnd_3141012 : Nat := 4983230072969 + 3 ^ 40 * 3141012 * 2
def baseEnd_3141012 : Nat := 1612848897540170009804755

theorem tailTrace_3141012 : CollatzResearch.WordTrace tailWord_3141012 prefixEnd_3141012 1612848897540170009804755 := by
  unfold tailWord_3141012
  simp only [CollatzResearch.WordTrace]
  refine ⟨57281059648328720493184645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76374746197771627324246193 57281059648328720493184645)
  ·
    refine ⟨10740198684061635092472121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57281059648328720493184645 10740198684061635092472121)
    ·
      refine ⟨8055149013046226319354091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10740198684061635092472121 8055149013046226319354091)
      ·
        refine ⟨12082723519569339479031137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055149013046226319354091 12082723519569339479031137)
        ·
          refine ⟨9062042639677004609273353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12082723519569339479031137 9062042639677004609273353)
          ·
            refine ⟨6796531979757753456955015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9062042639677004609273353 6796531979757753456955015)
            ·
              refine ⟨10194797969636630185432523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796531979757753456955015 10194797969636630185432523)
              ·
                refine ⟨15292196954454945278148785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10194797969636630185432523 15292196954454945278148785)
                ·
                  refine ⟨11469147715841208958611589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15292196954454945278148785 11469147715841208958611589)
                  ·
                    refine ⟨2150465196720226679739673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11469147715841208958611589 2150465196720226679739673)
                    ·
                      refine ⟨1612848897540170009804755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150465196720226679739673 1612848897540170009804755)
                      ·
                        rfl

theorem cell23_3141012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_3141012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141012 prefixEnd_3141012 := by exact prefixLift 3141012
  have htrace : WordTrace (prefixWord ++ tailWord_3141012) baseStart_3141012 baseEnd_3141012 := by
    simpa [prefixWord, tailWord_3141012, baseEnd_3141012] using wordTrace_append hprefix tailTrace_3141012
  have hstable : (prefixWord ++ tailWord_3141012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141012).length < 2 ^ (prefixWord ++ tailWord_3141012).sum := by decide
  have hdescent : baseEnd_3141012 < baseStart_3141012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141018 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 6]
def baseStart_3141018 : Nat := 118140960795 + 3141018 * 2 ^ 59
def prefixEnd_3141018 : Nat := 4983230072969 + 3 ^ 40 * 3141018 * 2
def baseEnd_3141018 : Nat := 179205775380455220703303

theorem tailTrace_3141018 : CollatzResearch.WordTrace tailWord_3141018 prefixEnd_3141018 179205775380455220703303 := by
  unfold tailWord_3141018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28640584533658926002771927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76374892089757136007391805 28640584533658926002771927)
  ·
    refine ⟨42960876800488389004157891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28640584533658926002771927 42960876800488389004157891)
    ·
      refine ⟨64441315200732583506236837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42960876800488389004157891 64441315200732583506236837)
      ·
        refine ⟨12082746600137359407419407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64441315200732583506236837 12082746600137359407419407)
        ·
          refine ⟨18124119900206039111129111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12082746600137359407419407 18124119900206039111129111)
          ·
            refine ⟨27186179850309058666693667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18124119900206039111129111 27186179850309058666693667)
            ·
              refine ⟨40779269775463588000040501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27186179850309058666693667 40779269775463588000040501)
              ·
                refine ⟨3823056541449711375003797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40779269775463588000040501 3823056541449711375003797)
                ·
                  refine ⟨179205775380455220703303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3823056541449711375003797 179205775380455220703303)
                  ·
                    rfl

theorem cell23_3141018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_3141018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141018 prefixEnd_3141018 := by exact prefixLift 3141018
  have htrace : WordTrace (prefixWord ++ tailWord_3141018) baseStart_3141018 baseEnd_3141018 := by
    simpa [prefixWord, tailWord_3141018, baseEnd_3141018] using wordTrace_append hprefix tailTrace_3141018
  have hstable : (prefixWord ++ tailWord_3141018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141018).length < 2 ^ (prefixWord ++ tailWord_3141018).sum := by decide
  have hdescent : baseEnd_3141018 < baseStart_3141018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141032 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3141032 : Nat := 118140960795 + 3141032 * 2 ^ 59
def prefixEnd_3141032 : Nat := 4983230072969 + 3 ^ 40 * 3141032 * 2
def baseEnd_3141032 : Nat := 1612859167153259931554663

theorem tailTrace_3141032 : CollatzResearch.WordTrace tailWord_3141032 prefixEnd_3141032 1612859167153259931554663 := by
  unfold tailWord_3141032
  simp only [CollatzResearch.WordTrace]
  refine ⟨57281424378292492201048675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76375232504389989601398233 57281424378292492201048675)
  ·
    refine ⟨85922136567438738301573013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57281424378292492201048675 85922136567438738301573013)
    ·
      refine ⟨4027600151598690857886235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85922136567438738301573013 4027600151598690857886235)
      ·
        refine ⟨6041400227398036286829353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027600151598690857886235 6041400227398036286829353)
        ·
          refine ⟨4531050170548527215122015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6041400227398036286829353 4531050170548527215122015)
          ·
            refine ⟨6796575255822790822683023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531050170548527215122015 6796575255822790822683023)
            ·
              refine ⟨10194862883734186234024535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796575255822790822683023 10194862883734186234024535)
              ·
                refine ⟨15292294325601279351036803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10194862883734186234024535 15292294325601279351036803)
                ·
                  refine ⟨22938441488401919026555205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15292294325601279351036803 22938441488401919026555205)
                  ·
                    refine ⟨4300957779075359817479101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22938441488401919026555205 4300957779075359817479101)
                    ·
                      refine ⟨1612859167153259931554663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4300957779075359817479101 1612859167153259931554663)
                      ·
                        rfl

theorem cell23_3141032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3141032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141032 prefixEnd_3141032 := by exact prefixLift 3141032
  have htrace : WordTrace (prefixWord ++ tailWord_3141032) baseStart_3141032 baseEnd_3141032 := by
    simpa [prefixWord, tailWord_3141032, baseEnd_3141032] using wordTrace_append hprefix tailTrace_3141032
  have hstable : (prefixWord ++ tailWord_3141032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141032).length < 2 ^ (prefixWord ++ tailWord_3141032).sum := by decide
  have hdescent : baseEnd_3141032 < baseStart_3141032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141052 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 6]
def baseStart_3141052 : Nat := 118140960795 + 3141052 * 2 ^ 59
def prefixEnd_3141052 : Nat := 4983230072969 + 3 ^ 40 * 3141052 * 2
def baseEnd_3141052 : Nat := 179207715196261094811619

theorem tailTrace_3141052 : CollatzResearch.WordTrace tailWord_3141052 prefixEnd_3141052 179207715196261094811619 := by
  unfold tailWord_3141052
  simp only [CollatzResearch.WordTrace]
  refine ⟨57281789108256263908912705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76375718811008351878550273 57281789108256263908912705)
  ·
    refine ⟨42961341831192197931684529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57281789108256263908912705 42961341831192197931684529)
    ·
      refine ⟨32221006373394148448763397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42961341831192197931684529 32221006373394148448763397)
      ·
        refine ⟨6041438695011402834143137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32221006373394148448763397 6041438695011402834143137)
        ·
          refine ⟨4531079021258552125607353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6041438695011402834143137 4531079021258552125607353)
          ·
            refine ⟨3398309265943914094205515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4531079021258552125607353 3398309265943914094205515)
            ·
              refine ⟨5097463898915871141308273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398309265943914094205515 5097463898915871141308273)
              ·
                refine ⟨3823097924186903355981205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097463898915871141308273 3823097924186903355981205)
                ·
                  refine ⟨179207715196261094811619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3823097924186903355981205 179207715196261094811619)
                  ·
                    rfl

theorem cell23_3141052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_3141052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141052 prefixEnd_3141052 := by exact prefixLift 3141052
  have htrace : WordTrace (prefixWord ++ tailWord_3141052) baseStart_3141052 baseEnd_3141052 := by
    simpa [prefixWord, tailWord_3141052, baseEnd_3141052] using wordTrace_append hprefix tailTrace_3141052
  have hstable : (prefixWord ++ tailWord_3141052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141052).length < 2 ^ (prefixWord ++ tailWord_3141052).sum := by decide
  have hdescent : baseEnd_3141052 < baseStart_3141052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141055 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 2, 3, 2]
def baseStart_3141055 : Nat := 118140960795 + 3141055 * 2 ^ 59
def prefixEnd_3141055 : Nat := 4983230072969 + 3 ^ 40 * 3141055 * 2
def baseEnd_3141055 : Nat := 1612870977208313341567057

theorem tailTrace_3141055 : CollatzResearch.WordTrace tailWord_3141055 prefixEnd_3141055 1612870977208313341567057 := by
  unfold tailWord_3141055
  simp only [CollatzResearch.WordTrace]
  refine ⟨114563687635501659330184619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76375791757001106220123079 114563687635501659330184619)
  ·
    refine ⟨171845531453252488995276929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114563687635501659330184619 171845531453252488995276929)
    ·
      refine ⟨128884148589939366746457697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171845531453252488995276929 128884148589939366746457697)
      ·
        refine ⟨96663111442454525059843273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128884148589939366746457697 96663111442454525059843273)
        ·
          refine ⟨72497333581840893794882455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96663111442454525059843273 72497333581840893794882455)
          ·
            refine ⟨108746000372761340692323683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72497333581840893794882455 108746000372761340692323683)
            ·
              refine ⟨163119000559142011038485525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108746000372761340692323683 163119000559142011038485525)
              ·
                refine ⟨7646203151209781767429009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163119000559142011038485525 7646203151209781767429009)
                ·
                  refine ⟨5734652363407336325571757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7646203151209781767429009 5734652363407336325571757)
                  ·
                    refine ⟨2150494636277751122089409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5734652363407336325571757 2150494636277751122089409)
                    ·
                      refine ⟨1612870977208313341567057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150494636277751122089409 1612870977208313341567057)
                      ·
                        rfl

theorem cell23_3141055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_3141055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141055 prefixEnd_3141055 := by exact prefixLift 3141055
  have htrace : WordTrace (prefixWord ++ tailWord_3141055) baseStart_3141055 baseEnd_3141055 := by
    simpa [prefixWord, tailWord_3141055, baseEnd_3141055] using wordTrace_append hprefix tailTrace_3141055
  have hstable : (prefixWord ++ tailWord_3141055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141055).length < 2 ^ (prefixWord ++ tailWord_3141055).sum := by decide
  have hdescent : baseEnd_3141055 < baseStart_3141055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141061 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_3141061 : Nat := 118140960795 + 3141061 * 2 ^ 59
def prefixEnd_3141061 : Nat := 4983230072969 + 3 ^ 40 * 3141061 * 2
def baseEnd_3141061 : Nat := 537624686030746772697343

theorem tailTrace_3141061 : CollatzResearch.WordTrace tailWord_3141061 prefixEnd_3141061 537624686030746772697343 := by
  unfold tailWord_3141061
  simp only [CollatzResearch.WordTrace]
  refine ⟨114563906473479922354903037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76375937648986614903268691 114563906473479922354903037)
  ·
    refine ⟨42961464927554970883088639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114563906473479922354903037 42961464927554970883088639)
    ·
      refine ⟨64442197391332456324632959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42961464927554970883088639 64442197391332456324632959)
      ·
        refine ⟨96663296086998684486949439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64442197391332456324632959 96663296086998684486949439)
        ·
          refine ⟨144994944130498026730424159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96663296086998684486949439 144994944130498026730424159)
          ·
            refine ⟨217492416195747040095636239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144994944130498026730424159 217492416195747040095636239)
            ·
              refine ⟨326238624293620560143454359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217492416195747040095636239 326238624293620560143454359)
              ·
                refine ⟨489357936440430840215181539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326238624293620560143454359 489357936440430840215181539)
                ·
                  refine ⟨734036904660646260322772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489357936440430840215181539 734036904660646260322772309)
                  ·
                    refine ⟨537624686030746772697343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 734036904660646260322772309 537624686030746772697343)
                    ·
                      rfl

theorem cell23_3141061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_3141061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141061 prefixEnd_3141061 := by exact prefixLift 3141061
  have htrace : WordTrace (prefixWord ++ tailWord_3141061) baseStart_3141061 baseEnd_3141061 := by
    simpa [prefixWord, tailWord_3141061, baseEnd_3141061] using wordTrace_append hprefix tailTrace_3141061
  have hstable : (prefixWord ++ tailWord_3141061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141061).length < 2 ^ (prefixWord ++ tailWord_3141061).sum := by decide
  have hdescent : baseEnd_3141061 < baseStart_3141061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141095 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 4, 4]
def baseStart_3141095 : Nat := 118140960795 + 3141095 * 2 ^ 59
def prefixEnd_3141095 : Nat := 4983230072969 + 3 ^ 40 * 3141095 * 2
def baseEnd_3141095 : Nat := 537630505478164395022291

theorem tailTrace_3141095 : CollatzResearch.WordTrace tailWord_3141095 prefixEnd_3141095 537630505478164395022291 := by
  unfold tailWord_3141095
  simp only [CollatzResearch.WordTrace]
  refine ⟨114565146555356746161640739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76376764370237830774427159 114565146555356746161640739)
  ·
    refine ⟨171847719833035119242461109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114565146555356746161640739 171847719833035119242461109)
    ·
      refine ⟨16110723734347042428980729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171847719833035119242461109 16110723734347042428980729)
      ·
        refine ⟨12083042800760281821735547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16110723734347042428980729 12083042800760281821735547)
        ·
          refine ⟨18124564201140422732603321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12083042800760281821735547 18124564201140422732603321)
          ·
            refine ⟨13593423150855317049452491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18124564201140422732603321 13593423150855317049452491)
            ·
              refine ⟨20390134726282975574178737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13593423150855317049452491 20390134726282975574178737)
              ·
                refine ⟨15292601044712231680634053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20390134726282975574178737 15292601044712231680634053)
                ·
                  refine ⟨2867362695883543440118885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15292601044712231680634053 2867362695883543440118885)
                  ·
                    refine ⟨537630505478164395022291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2867362695883543440118885 537630505478164395022291)
                    ·
                      rfl

theorem cell23_3141095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_3141095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141095 prefixEnd_3141095 := by exact prefixLift 3141095
  have htrace : WordTrace (prefixWord ++ tailWord_3141095) baseStart_3141095 baseEnd_3141095 := by
    simpa [prefixWord, tailWord_3141095, baseEnd_3141095] using wordTrace_append hprefix tailTrace_3141095
  have hstable : (prefixWord ++ tailWord_3141095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141095).length < 2 ^ (prefixWord ++ tailWord_3141095).sum := by decide
  have hdescent : baseEnd_3141095 < baseStart_3141095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141105 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_3141105 : Nat := 118140960795 + 3141105 * 2 ^ 59
def prefixEnd_3141105 : Nat := 4983230072969 + 3 ^ 40 * 3141105 * 2
def baseEnd_3141105 : Nat := 1612896651241038145941827

theorem tailTrace_3141105 : CollatzResearch.WordTrace tailWord_3141105 prefixEnd_3141105 1612896651241038145941827 := by
  unfold tailWord_3141105
  simp only [CollatzResearch.WordTrace]
  refine ⟨114565511285320517869504769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76377007523547011913003179 114565511285320517869504769)
  ·
    refine ⟨85924133463990388402128577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114565511285320517869504769 85924133463990388402128577)
    ·
      refine ⟨64443100097992791301596433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85924133463990388402128577 64443100097992791301596433)
      ·
        refine ⟨48332325073494593476197325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64443100097992791301596433 48332325073494593476197325)
        ·
          refine ⟨18124621902560472553573997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48332325073494593476197325 18124621902560472553573997)
          ·
            refine ⟨6796733213460177207590249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18124621902560472553573997 6796733213460177207590249)
            ·
              refine ⟨5097549910095132905692687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6796733213460177207590249 5097549910095132905692687)
              ·
                refine ⟨7646324865142699358539031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5097549910095132905692687 7646324865142699358539031)
                ·
                  refine ⟨11469487297714049037808547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7646324865142699358539031 11469487297714049037808547)
                  ·
                    refine ⟨17204230946571073556712821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11469487297714049037808547 17204230946571073556712821)
                    ·
                      refine ⟨1612896651241038145941827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17204230946571073556712821 1612896651241038145941827)
                      ·
                        rfl

theorem cell23_3141105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_3141105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141105 prefixEnd_3141105 := by exact prefixLift 3141105
  have htrace : WordTrace (prefixWord ++ tailWord_3141105) baseStart_3141105 baseEnd_3141105 := by
    simpa [prefixWord, tailWord_3141105, baseEnd_3141105] using wordTrace_append hprefix tailTrace_3141105
  have hstable : (prefixWord ++ tailWord_3141105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141105).length < 2 ^ (prefixWord ++ tailWord_3141105).sum := by decide
  have hdescent : baseEnd_3141105 < baseStart_3141105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141122 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3141122 : Nat := 118140960795 + 3141122 * 2 ^ 59
def prefixEnd_3141122 : Nat := 4983230072969 + 3 ^ 40 * 3141122 * 2
def baseEnd_3141122 : Nat := 1612905380412164579429249

theorem tailTrace_3141122 : CollatzResearch.WordTrace tailWord_3141122 prefixEnd_3141122 1612905380412164579429249 := by
  unfold tailWord_3141122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28641532831564732443218405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76377420884172619848582413 28641532831564732443218405)
  ·
    refine ⟨5370287405918387333103451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28641532831564732443218405 5370287405918387333103451)
    ·
      refine ⟨8055431108877580999655177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5370287405918387333103451 8055431108877580999655177)
      ·
        refine ⟨6041573331658185749741383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8055431108877580999655177 6041573331658185749741383)
        ·
          refine ⟨9062359997487278624612075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041573331658185749741383 9062359997487278624612075)
          ·
            refine ⟨13593539996230917936918113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062359997487278624612075 13593539996230917936918113)
            ·
              refine ⟨10195154997173188452688585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13593539996230917936918113 10195154997173188452688585)
              ·
                refine ⟨7646366247879891339516439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10195154997173188452688585 7646366247879891339516439)
                ·
                  refine ⟨11469549371819837009274659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7646366247879891339516439 11469549371819837009274659)
                  ·
                    refine ⟨17204324057729755513911989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11469549371819837009274659 17204324057729755513911989)
                    ·
                      refine ⟨1612905380412164579429249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17204324057729755513911989 1612905380412164579429249)
                      ·
                        rfl

theorem cell23_3141122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3141122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141122 prefixEnd_3141122 := by exact prefixLift 3141122
  have htrace : WordTrace (prefixWord ++ tailWord_3141122) baseStart_3141122 baseEnd_3141122 := by
    simpa [prefixWord, tailWord_3141122, baseEnd_3141122] using wordTrace_append hprefix tailTrace_3141122
  have hstable : (prefixWord ++ tailWord_3141122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141122).length < 2 ^ (prefixWord ++ tailWord_3141122).sum := by decide
  have hdescent : baseEnd_3141122 < baseStart_3141122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141133 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3141133 : Nat := 118140960795 + 3141133 * 2 ^ 59
def prefixEnd_3141133 : Nat := 4983230072969 + 3 ^ 40 * 3141133 * 2
def baseEnd_3141133 : Nat := 537637009566454678797233

theorem tailTrace_3141133 : CollatzResearch.WordTrace tailWord_3141133 prefixEnd_3141133 537637009566454678797233 := by
  unfold tailWord_3141133
  simp only [CollatzResearch.WordTrace]
  refine ⟨114566532529219078651524053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76377688352812719101016035 114566532529219078651524053)
  ·
    refine ⟨2685153106153572155895095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114566532529219078651524053 2685153106153572155895095)
    ·
      refine ⟨4027729659230358233842643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685153106153572155895095 4027729659230358233842643)
      ·
        refine ⟨6041594488845537350763965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027729659230358233842643 6041594488845537350763965)
        ·
          refine ⟨2265597933317076506536487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6041594488845537350763965 2265597933317076506536487)
          ·
            refine ⟨3398396899975614759804731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265597933317076506536487 3398396899975614759804731)
            ·
              refine ⟨5097595349963422139707097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398396899975614759804731 5097595349963422139707097)
              ·
                refine ⟨3823196512472566604780323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097595349963422139707097 3823196512472566604780323)
                ·
                  refine ⟨5734794768708849907170485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823196512472566604780323 5734794768708849907170485)
                  ·
                    refine ⟨537637009566454678797233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5734794768708849907170485 537637009566454678797233)
                    ·
                      rfl

theorem cell23_3141133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3141133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141133 prefixEnd_3141133 := by exact prefixLift 3141133
  have htrace : WordTrace (prefixWord ++ tailWord_3141133) baseStart_3141133 baseEnd_3141133 := by
    simpa [prefixWord, tailWord_3141133, baseEnd_3141133] using wordTrace_append hprefix tailTrace_3141133
  have hstable : (prefixWord ++ tailWord_3141133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141133).length < 2 ^ (prefixWord ++ tailWord_3141133).sum := by decide
  have hdescent : baseEnd_3141133 < baseStart_3141133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141152 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3141152 : Nat := 118140960795 + 3141152 * 2 ^ 59
def prefixEnd_3141152 : Nat := 4983230072969 + 3 ^ 40 * 3141152 * 2
def baseEnd_3141152 : Nat := 1612920784831799462054111

theorem tailTrace_3141152 : CollatzResearch.WordTrace tailWord_3141152 prefixEnd_3141152 1612920784831799462054111 := by
  unfold tailWord_3141152
  simp only [CollatzResearch.WordTrace]
  refine ⟨57283612758075122448232855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76378150344100163264310473 57283612758075122448232855)
  ·
    refine ⟨85925419137112683672349283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57283612758075122448232855 85925419137112683672349283)
    ·
      refine ⟨128888128705669025508523925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85925419137112683672349283 128888128705669025508523925)
      ·
        refine ⟨6041631033078235570712059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128888128705669025508523925 6041631033078235570712059)
        ·
          refine ⟨9062446549617353356068089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041631033078235570712059 9062446549617353356068089)
          ·
            refine ⟨6796834912213015017051067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9062446549617353356068089 6796834912213015017051067)
            ·
              refine ⟨10195252368319522525576601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796834912213015017051067 10195252368319522525576601)
              ·
                refine ⟨7646439276239641894182451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10195252368319522525576601 7646439276239641894182451)
                ·
                  refine ⟨11469658914359462841273677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7646439276239641894182451 11469658914359462841273677)
                  ·
                    refine ⟨4301122092884798565477629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11469658914359462841273677 4301122092884798565477629)
                    ·
                      refine ⟨1612920784831799462054111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4301122092884798565477629 1612920784831799462054111)
                      ·
                        rfl

theorem cell23_3141152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3141152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141152 prefixEnd_3141152 := by exact prefixLift 3141152
  have htrace : WordTrace (prefixWord ++ tailWord_3141152) baseStart_3141152 baseEnd_3141152 := by
    simpa [prefixWord, tailWord_3141152, baseEnd_3141152] using wordTrace_append hprefix tailTrace_3141152
  have hstable : (prefixWord ++ tailWord_3141152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141152).length < 2 ^ (prefixWord ++ tailWord_3141152).sum := by decide
  have hdescent : baseEnd_3141152 < baseStart_3141152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141168 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 2, 6]
def baseStart_3141168 : Nat := 118140960795 + 3141168 * 2 ^ 59
def prefixEnd_3141168 : Nat := 4983230072969 + 3 ^ 40 * 3141168 * 2
def baseEnd_3141168 : Nat := 537643000174090466484679

theorem tailTrace_3141168 : CollatzResearch.WordTrace tailWord_3141168 prefixEnd_3141168 537643000174090466484679 := by
  unfold tailWord_3141168
  simp only [CollatzResearch.WordTrace]
  refine ⟨57283904542046139814524079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76378539389394853086032105 57283904542046139814524079)
  ·
    refine ⟨85925856813069209721786119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57283904542046139814524079 85925856813069209721786119)
    ·
      refine ⟨128888785219603814582679179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85925856813069209721786119 128888785219603814582679179)
      ·
        refine ⟨193333177829405721874018769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128888785219603814582679179 193333177829405721874018769)
        ·
          refine ⟨144999883372054291405514077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193333177829405721874018769 144999883372054291405514077)
          ·
            refine ⟨54374956264520359277067779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144999883372054291405514077 54374956264520359277067779)
            ·
              refine ⟨81562434396780538915601669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54374956264520359277067779 81562434396780538915601669)
              ·
                refine ⟨15292956449396351046675313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81562434396780538915601669 15292956449396351046675313)
                ·
                  refine ⟨11469717337047263285006485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15292956449396351046675313 11469717337047263285006485)
                  ·
                    refine ⟨537643000174090466484679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11469717337047263285006485 537643000174090466484679)
                    ·
                      rfl

theorem cell23_3141168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_3141168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141168 prefixEnd_3141168 := by exact prefixLift 3141168
  have htrace : WordTrace (prefixWord ++ tailWord_3141168) baseStart_3141168 baseEnd_3141168 := by
    simpa [prefixWord, tailWord_3141168, baseEnd_3141168] using wordTrace_append hprefix tailTrace_3141168
  have hstable : (prefixWord ++ tailWord_3141168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141168).length < 2 ^ (prefixWord ++ tailWord_3141168).sum := by decide
  have hdescent : baseEnd_3141168 < baseStart_3141168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141185 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3141185 : Nat := 118140960795 + 3141185 * 2 ^ 59
def prefixEnd_3141185 : Nat := 4983230072969 + 3 ^ 40 * 3141185 * 2
def baseEnd_3141185 : Nat := 537645909897799277647153

theorem tailTrace_3141185 : CollatzResearch.WordTrace tailWord_3141185 prefixEnd_3141185 537645909897799277647153 := by
  unfold tailWord_3141185
  simp only [CollatzResearch.WordTrace]
  refine ⟨114568429125030691532417009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76378952750020461021611339 114568429125030691532417009)
  ·
    refine ⟨85926321843773018649312757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114568429125030691532417009 85926321843773018649312757)
    ·
      refine ⟨8055592672853720498373071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85926321843773018649312757 8055592672853720498373071)
      ·
        refine ⟨12083389009280580747559607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055592672853720498373071 12083389009280580747559607)
        ·
          refine ⟨18125083513920871121339411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12083389009280580747559607 18125083513920871121339411)
          ·
            refine ⟨27187625270881306682009117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18125083513920871121339411 27187625270881306682009117)
            ·
              refine ⟨10195359476580490005753419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27187625270881306682009117 10195359476580490005753419)
              ·
                refine ⟨15293039214870735008630129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10195359476580490005753419 15293039214870735008630129)
                ·
                  refine ⟨11469779411153051256472597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15293039214870735008630129 11469779411153051256472597)
                  ·
                    refine ⟨537645909897799277647153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11469779411153051256472597 537645909897799277647153)
                    ·
                      rfl

theorem cell23_3141185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3141185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141185 prefixEnd_3141185 := by exact prefixLift 3141185
  have htrace : WordTrace (prefixWord ++ tailWord_3141185) baseStart_3141185 baseEnd_3141185 := by
    simpa [prefixWord, tailWord_3141185, baseEnd_3141185] using wordTrace_append hprefix tailTrace_3141185
  have hstable : (prefixWord ++ tailWord_3141185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141185).length < 2 ^ (prefixWord ++ tailWord_3141185).sum := by decide
  have hdescent : baseEnd_3141185 < baseStart_3141185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141192 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_3141192 : Nat := 118140960795 + 3141192 * 2 ^ 59
def prefixEnd_3141192 : Nat := 4983230072969 + 3 ^ 40 * 3141192 * 2
def baseEnd_3141192 : Nat := 1612941324057979305553927

theorem tailTrace_3141192 : CollatzResearch.WordTrace tailWord_3141192 prefixEnd_3141192 1612941324057979305553927 := by
  unfold tailWord_3141192
  simp only [CollatzResearch.WordTrace]
  refine ⟨57284342218002665863960915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76379122957336887818614553 57284342218002665863960915)
  ·
    refine ⟨85926513327003998795941373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57284342218002665863960915 85926513327003998795941373)
    ·
      refine ⟨32222442497626499548478015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85926513327003998795941373 32222442497626499548478015)
      ·
        refine ⟨48333663746439749322717023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32222442497626499548478015 48333663746439749322717023)
        ·
          refine ⟨72500495619659623984075535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48333663746439749322717023 72500495619659623984075535)
          ·
            refine ⟨108750743429489435976113303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72500495619659623984075535 108750743429489435976113303)
            ·
              refine ⟨163126115144234153964169955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108750743429489435976113303 163126115144234153964169955)
              ·
                refine ⟨244689172716351230946254933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163126115144234153964169955 244689172716351230946254933)
                ·
                  refine ⟨2867451242769740987651425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 244689172716351230946254933 2867451242769740987651425)
                  ·
                    refine ⟨2150588432077305740738569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867451242769740987651425 2150588432077305740738569)
                    ·
                      refine ⟨1612941324057979305553927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150588432077305740738569 1612941324057979305553927)
                      ·
                        rfl

theorem cell23_3141192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_3141192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141192 prefixEnd_3141192 := by exact prefixLift 3141192
  have htrace : WordTrace (prefixWord ++ tailWord_3141192) baseStart_3141192 baseEnd_3141192 := by
    simpa [prefixWord, tailWord_3141192, baseEnd_3141192] using wordTrace_append hprefix tailTrace_3141192
  have hstable : (prefixWord ++ tailWord_3141192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141192).length < 2 ^ (prefixWord ++ tailWord_3141192).sum := by decide
  have hdescent : baseEnd_3141192 < baseStart_3141192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141208 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3141208 : Nat := 118140960795 + 3141208 * 2 ^ 59
def prefixEnd_3141208 : Nat := 4983230072969 + 3 ^ 40 * 3141208 * 2
def baseEnd_3141208 : Nat := 1612949539748451242953853

theorem tailTrace_3141208 : CollatzResearch.WordTrace tailWord_3141208 prefixEnd_3141208 1612949539748451242953853 := by
  unfold tailWord_3141208
  simp only [CollatzResearch.WordTrace]
  refine ⟨57284634001973683230252139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76379512002631577640336185 57284634001973683230252139)
  ·
    refine ⟨85926951002960524845378209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57284634001973683230252139 85926951002960524845378209)
    ·
      refine ⟨64445213252220393634033657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85926951002960524845378209 64445213252220393634033657)
      ·
        refine ⟨48333909939165295225525243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64445213252220393634033657 48333909939165295225525243)
        ·
          refine ⟨72500864908747942838287865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48333909939165295225525243 72500864908747942838287865)
          ·
            refine ⟨54375648681560957128715899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72500864908747942838287865 54375648681560957128715899)
            ·
              refine ⟨81563473022341435693073849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54375648681560957128715899 81563473022341435693073849)
              ·
                refine ⟨61172604766756076769805387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81563473022341435693073849 61172604766756076769805387)
                ·
                  refine ⟨91758907150134115154708081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61172604766756076769805387 91758907150134115154708081)
                  ·
                    refine ⟨68819180362600586366031061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91758907150134115154708081 68819180362600586366031061)
                    ·
                      refine ⟨1612949539748451242953853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68819180362600586366031061 1612949539748451242953853)
                      ·
                        rfl

theorem cell23_3141208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3141208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141208 prefixEnd_3141208 := by exact prefixLift 3141208
  have htrace : WordTrace (prefixWord ++ tailWord_3141208) baseStart_3141208 baseEnd_3141208 := by
    simpa [prefixWord, tailWord_3141208, baseEnd_3141208] using wordTrace_append hprefix tailTrace_3141208
  have hstable : (prefixWord ++ tailWord_3141208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141208).length < 2 ^ (prefixWord ++ tailWord_3141208).sum := by decide
  have hdescent : baseEnd_3141208 < baseStart_3141208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141213 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3141213 : Nat := 118140960795 + 3141213 * 2 ^ 59
def prefixEnd_3141213 : Nat := 4983230072969 + 3 ^ 40 * 3141213 * 2
def baseEnd_3141213 : Nat := 1612952107151723723391331

theorem tailTrace_3141213 : CollatzResearch.WordTrace tailWord_3141213 prefixEnd_3141213 1612952107151723723391331 := by
  unfold tailWord_3141213
  simp only [CollatzResearch.WordTrace]
  refine ⟨114569450368929252314436293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76379633579286168209624195 114569450368929252314436293)
  ·
    refine ⟨21481771944174234808956805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114569450368929252314436293 21481771944174234808956805)
    ·
      refine ⟨4027832239532669026679401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21481771944174234808956805 4027832239532669026679401)
      ·
        refine ⟨3020874179649501770009551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4027832239532669026679401 3020874179649501770009551)
        ·
          refine ⟨4531311269474252655014327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020874179649501770009551 4531311269474252655014327)
          ·
            refine ⟨6796966904211378982521491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531311269474252655014327 6796966904211378982521491)
            ·
              refine ⟨10195450356317068473782237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796966904211378982521491 10195450356317068473782237)
              ·
                refine ⟨3823293883618900677668339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10195450356317068473782237 3823293883618900677668339)
                ·
                  refine ⟨5734940825428351016502509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823293883618900677668339 5734940825428351016502509)
                  ·
                    refine ⟨2150602809535631631188441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5734940825428351016502509 2150602809535631631188441)
                    ·
                      refine ⟨1612952107151723723391331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150602809535631631188441 1612952107151723723391331)
                      ·
                        rfl

theorem cell23_3141213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3141213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141213 prefixEnd_3141213 := by exact prefixLift 3141213
  have htrace : WordTrace (prefixWord ++ tailWord_3141213) baseStart_3141213 baseEnd_3141213 := by
    simpa [prefixWord, tailWord_3141213, baseEnd_3141213] using wordTrace_append hprefix tailTrace_3141213
  have hstable : (prefixWord ++ tailWord_3141213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141213).length < 2 ^ (prefixWord ++ tailWord_3141213).sum := by decide
  have hdescent : baseEnd_3141213 < baseStart_3141213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141225 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 3]
def baseStart_3141225 : Nat := 118140960795 + 3141225 * 2 ^ 59
def prefixEnd_3141225 : Nat := 4983230072969 + 3 ^ 40 * 3141225 * 2
def baseEnd_3141225 : Nat := 1612958268919577676441275

theorem tailTrace_3141225 : CollatzResearch.WordTrace tailWord_3141225 prefixEnd_3141225 1612958268919577676441275 := by
  unfold tailWord_3141225
  simp only [CollatzResearch.WordTrace]
  refine ⟨114569888044885778363873129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76379925363257185575915419 114569888044885778363873129)
  ·
    refine ⟨85927416033664333772904847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114569888044885778363873129 85927416033664333772904847)
    ·
      refine ⟨128891124050496500659357271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85927416033664333772904847 128891124050496500659357271)
      ·
        refine ⟨193336686075744750989035907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128891124050496500659357271 193336686075744750989035907)
        ·
          refine ⟨290005029113617126483553861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193336686075744750989035907 290005029113617126483553861)
          ·
            refine ⟨54375942958803211215666349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290005029113617126483553861 54375942958803211215666349)
            ·
              refine ⟨20390978609551204205874881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54375942958803211215666349 20390978609551204205874881)
              ·
                refine ⟨15293233957163403154406161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20390978609551204205874881 15293233957163403154406161)
                ·
                  refine ⟨11469925467872552365804621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15293233957163403154406161 11469925467872552365804621)
                  ·
                    refine ⟨4301222050452207137176733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11469925467872552365804621 4301222050452207137176733)
                    ·
                      refine ⟨1612958268919577676441275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4301222050452207137176733 1612958268919577676441275)
                      ·
                        rfl

theorem cell23_3141225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_3141225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141225 prefixEnd_3141225 := by exact prefixLift 3141225
  have htrace : WordTrace (prefixWord ++ tailWord_3141225) baseStart_3141225 baseEnd_3141225 := by
    simpa [prefixWord, tailWord_3141225, baseEnd_3141225] using wordTrace_append hprefix tailTrace_3141225
  have hstable : (prefixWord ++ tailWord_3141225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141225).length < 2 ^ (prefixWord ++ tailWord_3141225).sum := by decide
  have hdescent : baseEnd_3141225 < baseStart_3141225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141226 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_3141226 : Nat := 118140960795 + 3141226 * 2 ^ 59
def prefixEnd_3141226 : Nat := 4983230072969 + 3 ^ 40 * 3141226 * 2
def baseEnd_3141226 : Nat := 1612958782400232172528771

theorem tailTrace_3141226 : CollatzResearch.WordTrace tailWord_3141226 prefixEnd_3141226 1612958782400232172528771 := by
  unfold tailWord_3141226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28642481129470538883664883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76379949678588103689773021 28642481129470538883664883)
  ·
    refine ⟨42963721694205808325497325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28642481129470538883664883 42963721694205808325497325)
    ·
      refine ⟨16111395635327178122061497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42963721694205808325497325 16111395635327178122061497)
      ·
        refine ⟨12083546726495383591546123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16111395635327178122061497 12083546726495383591546123)
        ·
          refine ⟨18125320089743075387319185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12083546726495383591546123 18125320089743075387319185)
          ·
            refine ⟨13593990067307306540489389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18125320089743075387319185 13593990067307306540489389)
            ·
              refine ⟨5097746275240239952683521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13593990067307306540489389 5097746275240239952683521)
              ·
                refine ⟨3823309706430179964512641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097746275240239952683521 3823309706430179964512641)
                ·
                  refine ⟨2867482279822634973384481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823309706430179964512641 2867482279822634973384481)
                  ·
                    refine ⟨2150611709866976230038361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867482279822634973384481 2150611709866976230038361)
                    ·
                      refine ⟨1612958782400232172528771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150611709866976230038361 1612958782400232172528771)
                      ·
                        rfl

theorem cell23_3141226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_3141226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141226 prefixEnd_3141226 := by exact prefixLift 3141226
  have htrace : WordTrace (prefixWord ++ tailWord_3141226) baseStart_3141226 baseEnd_3141226 := by
    simpa [prefixWord, tailWord_3141226, baseEnd_3141226] using wordTrace_append hprefix tailTrace_3141226
  have hstable : (prefixWord ++ tailWord_3141226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141226).length < 2 ^ (prefixWord ++ tailWord_3141226).sum := by decide
  have hdescent : baseEnd_3141226 < baseStart_3141226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141232 : List Nat := [2, 1, 1, 1, 6, 1, 2, 4, 5]
def baseStart_3141232 : Nat := 118140960795 + 3141232 * 2 ^ 59
def prefixEnd_3141232 : Nat := 4983230072969 + 3 ^ 40 * 3141232 * 2
def baseEnd_3141232 : Nat := 179217984809351016561527

theorem tailTrace_3141232 : CollatzResearch.WordTrace tailWord_3141232 prefixEnd_3141232 179217984809351016561527 := by
  unfold tailWord_3141232
  simp only [CollatzResearch.WordTrace]
  refine ⟨57285071677930209279688975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76380095570573612372918633 57285071677930209279688975)
  ·
    refine ⟨85927607516895313919533463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57285071677930209279688975 85927607516895313919533463)
    ·
      refine ⟨128891411275342970879300195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85927607516895313919533463 128891411275342970879300195)
      ·
        refine ⟨193337116913014456318950293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128891411275342970879300195 193337116913014456318950293)
        ·
          refine ⟨9062677355297552639950795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193337116913014456318950293 9062677355297552639950795)
          ·
            refine ⟨13594016032946328959926193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062677355297552639950795 13594016032946328959926193)
            ·
              refine ⟨10195512024709746719944645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13594016032946328959926193 10195512024709746719944645)
              ·
                refine ⟨1911658504633077509989621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10195512024709746719944645 1911658504633077509989621)
                ·
                  refine ⟨179217984809351016561527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1911658504633077509989621 179217984809351016561527)
                  ·
                    rfl

theorem cell23_3141232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 5].length) (baseStart_3141232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141232 prefixEnd_3141232 := by exact prefixLift 3141232
  have htrace : WordTrace (prefixWord ++ tailWord_3141232) baseStart_3141232 baseEnd_3141232 := by
    simpa [prefixWord, tailWord_3141232, baseEnd_3141232] using wordTrace_append hprefix tailTrace_3141232
  have hstable : (prefixWord ++ tailWord_3141232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141232).length < 2 ^ (prefixWord ++ tailWord_3141232).sum := by decide
  have hdescent : baseEnd_3141232 < baseStart_3141232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141245 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_3141245 : Nat := 118140960795 + 3141245 * 2 ^ 59
def prefixEnd_3141245 : Nat := 4983230072969 + 3 ^ 40 * 3141245 * 2
def baseEnd_3141245 : Nat := 537656179510889199397061

theorem tailTrace_3141245 : CollatzResearch.WordTrace tailWord_3141245 prefixEnd_3141245 537656179510889199397061 := by
  unfold tailWord_3141245
  simp only [CollatzResearch.WordTrace]
  refine ⟨114570617504813321779601189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76380411669875547853067459 114570617504813321779601189)
  ·
    refine ⟨21481990782152497833675223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114570617504813321779601189 21481990782152497833675223)
    ·
      refine ⟨32222986173228746750512835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21481990782152497833675223 32222986173228746750512835)
      ·
        refine ⟨48334479259843120125769253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32222986173228746750512835 48334479259843120125769253)
        ·
          refine ⟨9062714861220585023581735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48334479259843120125769253 9062714861220585023581735)
          ·
            refine ⟨13594072291830877535372603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062714861220585023581735 13594072291830877535372603)
            ·
              refine ⟨20391108437746316303058905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13594072291830877535372603 20391108437746316303058905)
              ·
                refine ⟨15293331328309737227294179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20391108437746316303058905 15293331328309737227294179)
                ·
                  refine ⟨22939996992464605840941269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15293331328309737227294179 22939996992464605840941269)
                  ·
                    refine ⟨537656179510889199397061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22939996992464605840941269 537656179510889199397061)
                    ·
                      rfl

theorem cell23_3141245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_3141245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141245 prefixEnd_3141245 := by exact prefixLift 3141245
  have htrace : WordTrace (prefixWord ++ tailWord_3141245) baseStart_3141245 baseEnd_3141245 := by
    simpa [prefixWord, tailWord_3141245, baseEnd_3141245] using wordTrace_append hprefix tailTrace_3141245
  have hstable : (prefixWord ++ tailWord_3141245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141245).length < 2 ^ (prefixWord ++ tailWord_3141245).sum := by decide
  have hdescent : baseEnd_3141245 < baseStart_3141245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141266 : List Nat := [3, 2, 3, 1, 3, 2, 1, 3, 5]
def baseStart_3141266 : Nat := 118140960795 + 3141266 * 2 ^ 59
def prefixEnd_3141266 : Nat := 4983230072969 + 3 ^ 40 * 3141266 * 2
def baseEnd_3141266 : Nat := 179219924625156890669843

theorem tailTrace_3141266 : CollatzResearch.WordTrace tailWord_3141266 prefixEnd_3141266 179219924625156890669843 := by
  unfold tailWord_3141266
  simp only [CollatzResearch.WordTrace]
  refine ⟨28642845859434310591528913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76380922291824828244077101 28642845859434310591528913)
  ·
    refine ⟨21482134394575732943646685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28642845859434310591528913 21482134394575732943646685)
    ·
      refine ⟨8055800397965899853867507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21482134394575732943646685 8055800397965899853867507)
      ·
        refine ⟨12083700596948849780801261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055800397965899853867507 12083700596948849780801261)
        ·
          refine ⟨4531387723855818667800473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12083700596948849780801261 4531387723855818667800473)
          ·
            refine ⟨3398540792891864000850355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4531387723855818667800473 3398540792891864000850355)
            ·
              refine ⟨5097811189337796001275533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398540792891864000850355 5097811189337796001275533)
              ·
                refine ⟨1911679196001673500478325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5097811189337796001275533 1911679196001673500478325)
                ·
                  refine ⟨179219924625156890669843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1911679196001673500478325 179219924625156890669843)
                  ·
                    rfl

theorem cell23_3141266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_3141266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141266 prefixEnd_3141266 := by exact prefixLift 3141266
  have htrace : WordTrace (prefixWord ++ tailWord_3141266) baseStart_3141266 baseEnd_3141266 := by
    simpa [prefixWord, tailWord_3141266, baseEnd_3141266] using wordTrace_append hprefix tailTrace_3141266
  have hstable : (prefixWord ++ tailWord_3141266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141266).length < 2 ^ (prefixWord ++ tailWord_3141266).sum := by decide
  have hdescent : baseEnd_3141266 < baseStart_3141266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141279 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 2, 5]
def baseStart_3141279 : Nat := 118140960795 + 3141279 * 2 ^ 59
def prefixEnd_3141279 : Nat := 4983230072969 + 3 ^ 40 * 3141279 * 2
def baseEnd_3141279 : Nat := 537661998958306821722009

theorem tailTrace_3141279 : CollatzResearch.WordTrace tailWord_3141279 prefixEnd_3141279 537661998958306821722009 := by
  unfold tailWord_3141279
  simp only [CollatzResearch.WordTrace]
  refine ⟨114571857586690145586338891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76381238391126763724225927 114571857586690145586338891)
  ·
    refine ⟨171857786380035218379508337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114571857586690145586338891 171857786380035218379508337)
    ·
      refine ⟨128893339785026413784631253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171857786380035218379508337 128893339785026413784631253)
      ·
        refine ⟨3020937651211556573077295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 128893339785026413784631253 3020937651211556573077295)
        ·
          refine ⟨4531406476817334859615943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020937651211556573077295 4531406476817334859615943)
          ·
            refine ⟨6797109715226002289423915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531406476817334859615943 6797109715226002289423915)
            ·
              refine ⟨10195664572839003434135873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6797109715226002289423915 10195664572839003434135873)
              ·
                refine ⟨7646748429629252575601905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10195664572839003434135873 7646748429629252575601905)
                ·
                  refine ⟨5735061322221939431701429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7646748429629252575601905 5735061322221939431701429)
                  ·
                    refine ⟨537661998958306821722009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5735061322221939431701429 537661998958306821722009)
                    ·
                      rfl

theorem cell23_3141279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_3141279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141279 prefixEnd_3141279 := by exact prefixLift 3141279
  have htrace : WordTrace (prefixWord ++ tailWord_3141279) baseStart_3141279 baseEnd_3141279 := by
    simpa [prefixWord, tailWord_3141279, baseEnd_3141279] using wordTrace_append hprefix tailTrace_3141279
  have hstable : (prefixWord ++ tailWord_3141279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141279).length < 2 ^ (prefixWord ++ tailWord_3141279).sum := by decide
  have hdescent : baseEnd_3141279 < baseStart_3141279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141349 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3141349 : Nat := 118140960795 + 3141349 * 2 ^ 59
def prefixEnd_3141349 : Nat := 4983230072969 + 3 ^ 40 * 3141349 * 2
def baseEnd_3141349 : Nat := 1613021940520735191290705

theorem tailTrace_3141349 : CollatzResearch.WordTrace tailWord_3141349 prefixEnd_3141349 1613021940520735191290705 := by
  unfold tailWord_3141349
  simp only [CollatzResearch.WordTrace]
  refine ⟨114574410696436547541387101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76382940464291031694258067 114574410696436547541387101)
  ·
    refine ⟨42965404011163705328020163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114574410696436547541387101 42965404011163705328020163)
    ·
      refine ⟨64448106016745557992030245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42965404011163705328020163 64448106016745557992030245)
      ·
        refine ⟨12084019878139792123505671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64448106016745557992030245 12084019878139792123505671)
        ·
          refine ⟨18126029817209688185258507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12084019878139792123505671 18126029817209688185258507)
          ·
            refine ⟨27189044725814532277887761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18126029817209688185258507 27189044725814532277887761)
            ·
              refine ⟨20391783544360899208415821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27189044725814532277887761 20391783544360899208415821)
              ·
                refine ⟨7646918829135337203155933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20391783544360899208415821 7646918829135337203155933)
                ·
                  refine ⟨2867594560925751451183475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7646918829135337203155933 2867594560925751451183475)
                  ·
                    refine ⟨4301391841388627176775213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867594560925751451183475 4301391841388627176775213)
                    ·
                      refine ⟨1613021940520735191290705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4301391841388627176775213 1613021940520735191290705)
                      ·
                        rfl

theorem cell23_3141349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3141349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141349 prefixEnd_3141349 := by exact prefixLift 3141349
  have htrace : WordTrace (prefixWord ++ tailWord_3141349) baseStart_3141349 baseEnd_3141349 := by
    simpa [prefixWord, tailWord_3141349, baseEnd_3141349] using wordTrace_append hprefix tailTrace_3141349
  have hstable : (prefixWord ++ tailWord_3141349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141349).length < 2 ^ (prefixWord ++ tailWord_3141349).sum := by decide
  have hdescent : baseEnd_3141349 < baseStart_3141349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141352 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 3, 5]
def baseStart_3141352 : Nat := 118140960795 + 3141352 * 2 ^ 59
def prefixEnd_3141352 : Nat := 4983230072969 + 3 ^ 40 * 3141352 * 2
def baseEnd_3141352 : Nat := 537674493654232893184397

theorem tailTrace_3141352 : CollatzResearch.WordTrace tailWord_3141352 prefixEnd_3141352 537674493654232893184397 := by
  unfold tailWord_3141352
  simp only [CollatzResearch.WordTrace]
  refine ⟨57287260057712839526873155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76383013410283786035830873 57287260057712839526873155)
  ·
    refine ⟨85930890086569259290309733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57287260057712839526873155 85930890086569259290309733)
    ·
      refine ⟨16112041891231736116933075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85930890086569259290309733 16112041891231736116933075)
      ·
        refine ⟨24168062836847604175399613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16112041891231736116933075 24168062836847604175399613)
        ·
          refine ⟨9063023563817851565774855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24168062836847604175399613 9063023563817851565774855)
          ·
            refine ⟨13594535345726777348662283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9063023563817851565774855 13594535345726777348662283)
            ·
              refine ⟨20391803018590166022993425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13594535345726777348662283 20391803018590166022993425)
              ·
                refine ⟨15293852263942624517245069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20391803018590166022993425 15293852263942624517245069)
                ·
                  refine ⟨5735194598978484193966901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15293852263942624517245069 5735194598978484193966901)
                  ·
                    refine ⟨537674493654232893184397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5735194598978484193966901 537674493654232893184397)
                    ·
                      rfl

theorem cell23_3141352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_3141352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141352 prefixEnd_3141352 := by exact prefixLift 3141352
  have htrace : WordTrace (prefixWord ++ tailWord_3141352) baseStart_3141352 baseEnd_3141352 := by
    simpa [prefixWord, tailWord_3141352, baseEnd_3141352] using wordTrace_append hprefix tailTrace_3141352
  have hstable : (prefixWord ++ tailWord_3141352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141352).length < 2 ^ (prefixWord ++ tailWord_3141352).sum := by decide
  have hdescent : baseEnd_3141352 < baseStart_3141352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141366 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3141366 : Nat := 118140960795 + 3141366 * 2 ^ 59
def prefixEnd_3141366 : Nat := 4983230072969 + 3 ^ 40 * 3141366 * 2
def baseEnd_3141366 : Nat := 1613030669691861624778127

theorem tailTrace_3141366 : CollatzResearch.WordTrace tailWord_3141366 prefixEnd_3141366 1613030669691861624778127 := by
  unfold tailWord_3141366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160939421085934965297247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76383353824916639629837301 7160939421085934965297247)
  ·
    refine ⟨10741409131628902447945871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7160939421085934965297247 10741409131628902447945871)
    ·
      refine ⟨16112113697443353671918807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10741409131628902447945871 16112113697443353671918807)
      ·
        refine ⟨24168170546165030507878211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16112113697443353671918807 24168170546165030507878211)
        ·
          refine ⟨36252255819247545761817317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24168170546165030507878211 36252255819247545761817317)
          ·
            refine ⟨6797297966108914830340747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36252255819247545761817317 6797297966108914830340747)
            ·
              refine ⟨10195946949163372245511121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6797297966108914830340747 10195946949163372245511121)
              ·
                refine ⟨7646960211872529184133341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10195946949163372245511121 7646960211872529184133341)
                ·
                  refine ⟨2867610079452198444050003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7646960211872529184133341 2867610079452198444050003)
                  ·
                    refine ⟨4301415119178297666075005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867610079452198444050003 4301415119178297666075005)
                    ·
                      refine ⟨1613030669691861624778127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4301415119178297666075005 1613030669691861624778127)
                      ·
                        rfl

theorem cell23_3141366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3141366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141366 prefixEnd_3141366 := by exact prefixLift 3141366
  have htrace : WordTrace (prefixWord ++ tailWord_3141366) baseStart_3141366 baseEnd_3141366 := by
    simpa [prefixWord, tailWord_3141366, baseEnd_3141366] using wordTrace_append hprefix tailTrace_3141366
  have hstable : (prefixWord ++ tailWord_3141366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141366).length < 2 ^ (prefixWord ++ tailWord_3141366).sum := by decide
  have hdescent : baseEnd_3141366 < baseStart_3141366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141372 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_3141372 : Nat := 118140960795 + 3141372 * 2 ^ 59
def prefixEnd_3141372 : Nat := 4983230072969 + 3 ^ 40 * 3141372 * 2
def baseEnd_3141372 : Nat := 1613033750575788601303099

theorem tailTrace_3141372 : CollatzResearch.WordTrace tailWord_3141372 prefixEnd_3141372 1613033750575788601303099 := by
  unfold tailWord_3141372
  simp only [CollatzResearch.WordTrace]
  refine ⟨57287624787676611234737185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76383499716902148312982913 57287624787676611234737185)
  ·
    refine ⟨42965718590757458426052889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57287624787676611234737185 42965718590757458426052889)
    ·
      refine ⟨32224288943068093819539667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42965718590757458426052889 32224288943068093819539667)
      ·
        refine ⟨48336433414602140729309501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32224288943068093819539667 48336433414602140729309501)
        ·
          refine ⟨18126162530475802773491063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48336433414602140729309501 18126162530475802773491063)
          ·
            refine ⟨27189243795713704160236595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18126162530475802773491063 27189243795713704160236595)
            ·
              refine ⟨40783865693570556240354893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27189243795713704160236595 40783865693570556240354893)
              ·
                refine ⟨15293949635088958590133085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40783865693570556240354893 15293949635088958590133085)
                ·
                  refine ⟨5735231113158359471299907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15293949635088958590133085 5735231113158359471299907)
                  ·
                    refine ⟨8602846669737539206949861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5735231113158359471299907 8602846669737539206949861)
                    ·
                      refine ⟨1613033750575788601303099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8602846669737539206949861 1613033750575788601303099)
                      ·
                        rfl

theorem cell23_3141372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_3141372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141372 prefixEnd_3141372 := by exact prefixLift 3141372
  have htrace : WordTrace (prefixWord ++ tailWord_3141372) baseStart_3141372 baseEnd_3141372 := by
    simpa [prefixWord, tailWord_3141372, baseEnd_3141372] using wordTrace_append hprefix tailTrace_3141372
  have hstable : (prefixWord ++ tailWord_3141372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141372).length < 2 ^ (prefixWord ++ tailWord_3141372).sum := by decide
  have hdescent : baseEnd_3141372 < baseStart_3141372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141385 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_3141385 : Nat := 118140960795 + 3141385 * 2 ^ 59
def prefixEnd_3141385 : Nat := 4983230072969 + 3 ^ 40 * 3141385 * 2
def baseEnd_3141385 : Nat := 1613040425824297050440539

theorem tailTrace_3141385 : CollatzResearch.WordTrace tailWord_3141385 prefixEnd_3141385 1613040425824297050440539 := by
  unfold tailWord_3141385
  simp only [CollatzResearch.WordTrace]
  refine ⟨114575723724306125689697609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76383815816204083793131739 114575723724306125689697609)
  ·
    refine ⟨85931792793229594267273207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114575723724306125689697609 85931792793229594267273207)
    ·
      refine ⟨128897689189844391400909811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85931792793229594267273207 128897689189844391400909811)
      ·
        refine ⟨193346533784766587101364717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128897689189844391400909811 193346533784766587101364717)
        ·
          refine ⟨72504950169287470163011769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193346533784766587101364717 72504950169287470163011769)
          ·
            refine ⟨54378712626965602622258827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72504950169287470163011769 54378712626965602622258827)
            ·
              refine ⟨81568068940448403933388241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54378712626965602622258827 81568068940448403933388241)
              ·
                refine ⟨61176051705336302950041181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81568068940448403933388241 61176051705336302950041181)
                ·
                  refine ⟨22941019389501113606265443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61176051705336302950041181 22941019389501113606265443)
                  ·
                    refine ⟨34411529084251670409398165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22941019389501113606265443 34411529084251670409398165)
                    ·
                      refine ⟨1613040425824297050440539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34411529084251670409398165 1613040425824297050440539)
                      ·
                        rfl

theorem cell23_3141385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_3141385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141385 prefixEnd_3141385 := by exact prefixLift 3141385
  have htrace : WordTrace (prefixWord ++ tailWord_3141385) baseStart_3141385 baseEnd_3141385 := by
    simpa [prefixWord, tailWord_3141385, baseEnd_3141385] using wordTrace_append hprefix tailTrace_3141385
  have hstable : (prefixWord ++ tailWord_3141385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141385).length < 2 ^ (prefixWord ++ tailWord_3141385).sum := by decide
  have hdescent : baseEnd_3141385 < baseStart_3141385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141386 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_3141386 : Nat := 118140960795 + 3141386 * 2 ^ 59
def prefixEnd_3141386 : Nat := 4983230072969 + 3 ^ 40 * 3141386 * 2
def baseEnd_3141386 : Nat := 537680313101650515509345

theorem tailTrace_3141386 : CollatzResearch.WordTrace tailWord_3141386 prefixEnd_3141386 537680313101650515509345 := by
  unfold tailWord_3141386
  simp only [CollatzResearch.WordTrace]
  refine ⟨28643940049325625715121003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76383840131535001906989341 28643940049325625715121003)
  ·
    refine ⟨42965910073988438572681505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28643940049325625715121003 42965910073988438572681505)
    ·
      refine ⟨32224432555491328929511129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42965910073988438572681505 32224432555491328929511129)
      ·
        refine ⟨24168324416618496697133347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32224432555491328929511129 24168324416618496697133347)
        ·
          refine ⟨36252486624927745045700021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24168324416618496697133347 36252486624927745045700021)
          ·
            refine ⟨3398670621086976098034377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36252486624927745045700021 3398670621086976098034377)
            ·
              refine ⟨2549002965815232073525783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398670621086976098034377 2549002965815232073525783)
              ·
                refine ⟨3823504448722848110288675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549002965815232073525783 3823504448722848110288675)
                ·
                  refine ⟨5735256673084272165433013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823504448722848110288675 5735256673084272165433013)
                  ·
                    refine ⟨537680313101650515509345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5735256673084272165433013 537680313101650515509345)
                    ·
                      rfl

theorem cell23_3141386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_3141386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141386 prefixEnd_3141386 := by exact prefixLift 3141386
  have htrace : WordTrace (prefixWord ++ tailWord_3141386) baseStart_3141386 baseEnd_3141386 := by
    simpa [prefixWord, tailWord_3141386, baseEnd_3141386] using wordTrace_append hprefix tailTrace_3141386
  have hstable : (prefixWord ++ tailWord_3141386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141386).length < 2 ^ (prefixWord ++ tailWord_3141386).sum := by decide
  have hdescent : baseEnd_3141386 < baseStart_3141386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141399 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 4, 4]
def baseStart_3141399 : Nat := 118140960795 + 3141399 * 2 ^ 59
def prefixEnd_3141399 : Nat := 4983230072969 + 3 ^ 40 * 3141399 * 2
def baseEnd_3141399 : Nat := 537682538184486665221825

theorem tailTrace_3141399 : CollatzResearch.WordTrace tailWord_3141399 prefixEnd_3141399 537682538184486665221825 := by
  unfold tailWord_3141399
  simp only [CollatzResearch.WordTrace]
  refine ⟨114576234346255406080707251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76384156230836937387138167 114576234346255406080707251)
  ·
    refine ⟨171864351519383109121060877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114576234346255406080707251 171864351519383109121060877)
    ·
      refine ⟨64449131819768665920397829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171864351519383109121060877 64449131819768665920397829)
      ·
        refine ⟨12084212216206624860074593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64449131819768665920397829 12084212216206624860074593)
        ·
          refine ⟨9063159162154968645055945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12084212216206624860074593 9063159162154968645055945)
          ·
            refine ⟨6797369371616226483791959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9063159162154968645055945 6797369371616226483791959)
            ·
              refine ⟨10196054057424339725687939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6797369371616226483791959 10196054057424339725687939)
              ·
                refine ⟨15294081086136509588531909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10196054057424339725687939 15294081086136509588531909)
                ·
                  refine ⟨2867640203650595547849733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15294081086136509588531909 2867640203650595547849733)
                  ·
                    refine ⟨537682538184486665221825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2867640203650595547849733 537682538184486665221825)
                    ·
                      rfl

theorem cell23_3141399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_3141399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141399 prefixEnd_3141399 := by exact prefixLift 3141399
  have htrace : WordTrace (prefixWord ++ tailWord_3141399) baseStart_3141399 baseEnd_3141399 := by
    simpa [prefixWord, tailWord_3141399, baseEnd_3141399] using wordTrace_append hprefix tailTrace_3141399
  have hstable : (prefixWord ++ tailWord_3141399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141399).length < 2 ^ (prefixWord ++ tailWord_3141399).sum := by decide
  have hdescent : baseEnd_3141399 < baseStart_3141399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141426 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_3141426 : Nat := 118140960795 + 3141426 * 2 ^ 59
def prefixEnd_3141426 : Nat := 4983230072969 + 3 ^ 40 * 3141426 * 2
def baseEnd_3141426 : Nat := 1613061478531131390027851

theorem tailTrace_3141426 : CollatzResearch.WordTrace tailWord_3141426 prefixEnd_3141426 1613061478531131390027851 := by
  unfold tailWord_3141426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28644304779289397422985033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76384812744771726461293421 28644304779289397422985033)
  ·
    refine ⟨21483228584467048067238775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28644304779289397422985033 21483228584467048067238775)
    ·
      refine ⟨32224842876700572100858163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21483228584467048067238775 32224842876700572100858163)
      ·
        refine ⟨48337264315050858151287245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32224842876700572100858163 48337264315050858151287245)
        ·
          refine ⟨18126474118144071806732717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48337264315050858151287245 18126474118144071806732717)
          ·
            refine ⟨6797427794304026927524769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18126474118144071806732717 6797427794304026927524769)
            ·
              refine ⟨5098070845728020195643577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6797427794304026927524769 5098070845728020195643577)
              ·
                refine ⟨3823553134296015146732683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098070845728020195643577 3823553134296015146732683)
                ·
                  refine ⟨5735329701444022720099025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823553134296015146732683 5735329701444022720099025)
                  ·
                    refine ⟨4301497276083017040074269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5735329701444022720099025 4301497276083017040074269)
                    ·
                      refine ⟨1613061478531131390027851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4301497276083017040074269 1613061478531131390027851)
                      ·
                        rfl

theorem cell23_3141426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_3141426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141426 prefixEnd_3141426 := by exact prefixLift 3141426
  have htrace : WordTrace (prefixWord ++ tailWord_3141426) baseStart_3141426 baseEnd_3141426 := by
    simpa [prefixWord, tailWord_3141426, baseEnd_3141426] using wordTrace_append hprefix tailTrace_3141426
  have hstable : (prefixWord ++ tailWord_3141426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141426).length < 2 ^ (prefixWord ++ tailWord_3141426).sum := by decide
  have hdescent : baseEnd_3141426 < baseStart_3141426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141446 : List Nat := [6, 1, 1, 2, 1, 3, 9]
def baseStart_3141446 : Nat := 118140960795 + 3141446 * 2 ^ 59
def prefixEnd_3141446 : Nat := 4983230072969 + 3 ^ 40 * 3141446 * 2
def baseEnd_3141446 : Nat := 19914466026471868046639

theorem tailTrace_3141446 : CollatzResearch.WordTrace tailWord_3141446 prefixEnd_3141446 19914466026471868046639 := by
  unfold tailWord_3141446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3580560893033910409614631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76385299051390088738445461 3580560893033910409614631)
  ·
    refine ⟨5370841339550865614421947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3580560893033910409614631 5370841339550865614421947)
    ·
      refine ⟨8056262009326298421632921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5370841339550865614421947 8056262009326298421632921)
      ·
        refine ⟨6042196506994723816224691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8056262009326298421632921 6042196506994723816224691)
        ·
          refine ⟨9063294760492085724337037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042196506994723816224691 9063294760492085724337037)
          ·
            refine ⟨3398735535184532146626389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9063294760492085724337037 3398735535184532146626389)
            ·
              refine ⟨19914466026471868046639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3398735535184532146626389 19914466026471868046639)
              ·
                rfl

theorem cell23_3141446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 9].length) (baseStart_3141446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141446 prefixEnd_3141446 := by exact prefixLift 3141446
  have htrace : WordTrace (prefixWord ++ tailWord_3141446) baseStart_3141446 baseEnd_3141446 := by
    simpa [prefixWord, tailWord_3141446, baseEnd_3141446] using wordTrace_append hprefix tailTrace_3141446
  have hstable : (prefixWord ++ tailWord_3141446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141446).length < 2 ^ (prefixWord ++ tailWord_3141446).sum := by decide
  have hdescent : baseEnd_3141446 < baseStart_3141446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141513 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 2, 2, 2]
def baseStart_3141513 : Nat := 118140960795 + 3141513 * 2 ^ 59
def prefixEnd_3141513 : Nat := 4983230072969 + 3 ^ 40 * 3141513 * 2
def baseEnd_3141513 : Nat := 1613106151348072549639951

theorem tailTrace_3141513 : CollatzResearch.WordTrace tailWord_3141513 prefixEnd_3141513 1613106151348072549639951 := by
  unfold tailWord_3141513
  simp only [CollatzResearch.WordTrace]
  refine ⟨114580392267842403550357193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76386928178561602366904795 114580392267842403550357193)
  ·
    refine ⟨85935294200881802662767895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114580392267842403550357193 85935294200881802662767895)
    ·
      refine ⟨128902941301322703994151843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85935294200881802662767895 128902941301322703994151843)
      ·
        refine ⟨193354411951984055991227765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128902941301322703994151843 193354411951984055991227765)
        ·
          refine ⟨18126976120498505249177603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193354411951984055991227765 18126976120498505249177603)
          ·
            refine ⟨27190464180747757873766405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18126976120498505249177603 27190464180747757873766405)
            ·
              refine ⟨5098212033890204601331201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27190464180747757873766405 5098212033890204601331201)
              ·
                refine ⟨3823659025417653450998401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098212033890204601331201 3823659025417653450998401)
                ·
                  refine ⟨2867744269063240088248801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823659025417653450998401 2867744269063240088248801)
                  ·
                    refine ⟨2150808201797430066186601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867744269063240088248801 2150808201797430066186601)
                    ·
                      refine ⟨1613106151348072549639951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150808201797430066186601 1613106151348072549639951)
                      ·
                        rfl

theorem cell23_3141513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 2, 2].length) (baseStart_3141513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141513 prefixEnd_3141513 := by exact prefixLift 3141513
  have htrace : WordTrace (prefixWord ++ tailWord_3141513) baseStart_3141513 baseEnd_3141513 := by
    simpa [prefixWord, tailWord_3141513, baseEnd_3141513] using wordTrace_append hprefix tailTrace_3141513
  have hstable : (prefixWord ++ tailWord_3141513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141513).length < 2 ^ (prefixWord ++ tailWord_3141513).sum := by decide
  have hdescent : baseEnd_3141513 < baseStart_3141513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141539 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 4, 5, 2]
def baseStart_3141539 : Nat := 118140960795 + 3141539 * 2 ^ 59
def prefixEnd_3141539 : Nat := 4983230072969 + 3 ^ 40 * 3141539 * 2
def baseEnd_3141539 : Nat := 1613119501845089447914831

theorem tailTrace_3141539 : CollatzResearch.WordTrace tailWord_3141539 prefixEnd_3141539 1613119501845089447914831 := by
  unfold tailWord_3141539
  simp only [CollatzResearch.WordTrace]
  refine ⟨114581340565748209990803671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76387560377165473327202447 114581340565748209990803671)
  ·
    refine ⟨171872010848622314986205507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114581340565748209990803671 171872010848622314986205507)
    ·
      refine ⟨257808016272933472479308261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171872010848622314986205507 257808016272933472479308261)
      ·
        refine ⟨48339003051175026089870299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257808016272933472479308261 48339003051175026089870299)
        ·
          refine ⟨72508504576762539134805449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48339003051175026089870299 72508504576762539134805449)
          ·
            refine ⟨54381378432571904351104087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72508504576762539134805449 54381378432571904351104087)
            ·
              refine ⟨81572067648857856526656131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54381378432571904351104087 81572067648857856526656131)
              ·
                refine ⟨122358101473286784789984197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81572067648857856526656131 122358101473286784789984197)
                ·
                  refine ⟨22942144026241272148122037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122358101473286784789984197 22942144026241272148122037)
                  ·
                    refine ⟨2150826002460119263886441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22942144026241272148122037 2150826002460119263886441)
                    ·
                      refine ⟨1613119501845089447914831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150826002460119263886441 1613119501845089447914831)
                      ·
                        rfl

theorem cell23_3141539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_3141539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141539 prefixEnd_3141539 := by exact prefixLift 3141539
  have htrace : WordTrace (prefixWord ++ tailWord_3141539) baseStart_3141539 baseEnd_3141539 := by
    simpa [prefixWord, tailWord_3141539, baseEnd_3141539] using wordTrace_append hprefix tailTrace_3141539
  have hstable : (prefixWord ++ tailWord_3141539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141539).length < 2 ^ (prefixWord ++ tailWord_3141539).sum := by decide
  have hdescent : baseEnd_3141539 < baseStart_3141539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141564 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3141564 : Nat := 118140960795 + 3141564 * 2 ^ 59
def prefixEnd_3141564 : Nat := 4983230072969 + 3 ^ 40 * 3141564 * 2
def baseEnd_3141564 : Nat := 1613132338861451850102217

theorem tailTrace_3141564 : CollatzResearch.WordTrace tailWord_3141564 prefixEnd_3141564 1613132338861451850102217 := by
  unfold tailWord_3141564
  simp only [CollatzResearch.WordTrace]
  refine ⟨57291126195328819630231873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76388168260438426173642497 57291126195328819630231873)
  ·
    refine ⟨42968344646496614722673905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57291126195328819630231873 42968344646496614722673905)
    ·
      refine ⟨32226258484872461042005429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42968344646496614722673905 32226258484872461042005429)
      ·
        refine ⟨3021211732956793222688009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32226258484872461042005429 3021211732956793222688009)
        ·
          refine ⟨2265908799717594917016007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3021211732956793222688009 2265908799717594917016007)
          ·
            refine ⟨3398863199576392375524011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265908799717594917016007 3398863199576392375524011)
            ·
              refine ⟨5098294799364588563286017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398863199576392375524011 5098294799364588563286017)
              ·
                refine ⟨3823721099523441422464513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098294799364588563286017 3823721099523441422464513)
                ·
                  refine ⟨2867790824642581066848385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823721099523441422464513 2867790824642581066848385)
                  ·
                    refine ⟨2150843118481935800136289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867790824642581066848385 2150843118481935800136289)
                    ·
                      refine ⟨1613132338861451850102217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150843118481935800136289 1613132338861451850102217)
                      ·
                        rfl

theorem cell23_3141564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3141564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141564 prefixEnd_3141564 := by exact prefixLift 3141564
  have htrace : WordTrace (prefixWord ++ tailWord_3141564) baseStart_3141564 baseEnd_3141564 := by
    simpa [prefixWord, tailWord_3141564, baseEnd_3141564] using wordTrace_append hprefix tailTrace_3141564
  have hstable : (prefixWord ++ tailWord_3141564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141564).length < 2 ^ (prefixWord ++ tailWord_3141564).sum := by decide
  have hdescent : baseEnd_3141564 < baseStart_3141564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141630 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_3141630 : Nat := 118140960795 + 3141630 * 2 ^ 59
def prefixEnd_3141630 : Nat := 4983230072969 + 3 ^ 40 * 3141630 * 2
def baseEnd_3141630 : Nat := 537722076194882863958971

theorem tailTrace_3141630 : CollatzResearch.WordTrace tailWord_3141630 prefixEnd_3141630 537722076194882863958971 := by
  unfold tailWord_3141630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14323082451052316566545793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76389773072279021688244229 14323082451052316566545793)
  ·
    refine ⟨10742311838289237424909345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14323082451052316566545793 10742311838289237424909345)
    ·
      refine ⟨8056733878716928068682009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10742311838289237424909345 8056733878716928068682009)
      ·
        refine ⟨6042550409037696051511507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8056733878716928068682009 6042550409037696051511507)
        ·
          refine ⟨9063825613556544077267261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042550409037696051511507 9063825613556544077267261)
          ·
            refine ⟨3398934605083704028975223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9063825613556544077267261 3398934605083704028975223)
            ·
              refine ⟨5098401907625556043462835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398934605083704028975223 5098401907625556043462835)
              ·
                refine ⟨7647602861438334065194253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098401907625556043462835 7647602861438334065194253)
                ·
                  refine ⟨2867851073039375274447845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7647602861438334065194253 2867851073039375274447845)
                  ·
                    refine ⟨537722076194882863958971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2867851073039375274447845 537722076194882863958971)
                    ·
                      rfl

theorem cell23_3141630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_3141630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141630 prefixEnd_3141630 := by exact prefixLift 3141630
  have htrace : WordTrace (prefixWord ++ tailWord_3141630) baseStart_3141630 baseEnd_3141630 := by
    simpa [prefixWord, tailWord_3141630, baseEnd_3141630] using wordTrace_append hprefix tailTrace_3141630
  have hstable : (prefixWord ++ tailWord_3141630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141630).length < 2 ^ (prefixWord ++ tailWord_3141630).sum := by decide
  have hdescent : baseEnd_3141630 < baseStart_3141630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141663 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 2, 3, 2]
def baseStart_3141663 : Nat := 118140960795 + 3141663 * 2 ^ 59
def prefixEnd_3141663 : Nat := 4983230072969 + 3 ^ 40 * 3141663 * 2
def baseEnd_3141663 : Nat := 1613183173446246962764261

theorem tailTrace_3141663 : CollatzResearch.WordTrace tailWord_3141663 prefixEnd_3141663 1613183173446246962764261 := by
  unfold tailWord_3141663
  simp only [CollatzResearch.WordTrace]
  refine ⟨114585863217298979168317643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76390575478199319445545095 114585863217298979168317643)
  ·
    refine ⟨171878794825948468752476465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114585863217298979168317643 171878794825948468752476465)
    ·
      refine ⟨128909096119461351564357349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171878794825948468752476465 128909096119461351564357349)
      ·
        refine ⟨24170455522399003418317003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128909096119461351564357349 24170455522399003418317003)
        ·
          refine ⟨36255683283598505127475505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24170455522399003418317003 36255683283598505127475505)
          ·
            refine ⟨27191762462698878845606629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36255683283598505127475505 27191762462698878845606629)
            ·
              refine ⟨5098455461756039783551243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27191762462698878845606629 5098455461756039783551243)
              ·
                refine ⟨7647683192634059675326865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098455461756039783551243 7647683192634059675326865)
                ·
                  refine ⟨5735762394475544756495149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7647683192634059675326865 5735762394475544756495149)
                  ·
                    refine ⟨2150910897928329283685681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5735762394475544756495149 2150910897928329283685681)
                    ·
                      refine ⟨1613183173446246962764261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150910897928329283685681 1613183173446246962764261)
                      ·
                        rfl

theorem cell23_3141663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_3141663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141663 prefixEnd_3141663 := by exact prefixLift 3141663
  have htrace : WordTrace (prefixWord ++ tailWord_3141663) baseStart_3141663 baseEnd_3141663 := by
    simpa [prefixWord, tailWord_3141663, baseEnd_3141663] using wordTrace_append hprefix tailTrace_3141663
  have hstable : (prefixWord ++ tailWord_3141663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141663).length < 2 ^ (prefixWord ++ tailWord_3141663).sum := by decide
  have hdescent : baseEnd_3141663 < baseStart_3141663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141669 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_3141669 : Nat := 118140960795 + 3141669 * 2 ^ 59
def prefixEnd_3141669 : Nat := 4983230072969 + 3 ^ 40 * 3141669 * 2
def baseEnd_3141669 : Nat := 537728751443391313096411

theorem tailTrace_3141669 : CollatzResearch.WordTrace tailWord_3141669 prefixEnd_3141669 537728751443391313096411 := by
  unfold tailWord_3141669
  simp only [CollatzResearch.WordTrace]
  refine ⟨114586082055277242193036061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76390721370184828128690707 114586082055277242193036061)
  ·
    refine ⟨42969780770728965822388523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114586082055277242193036061 42969780770728965822388523)
    ·
      refine ⟨64454671156093448733582785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42969780770728965822388523 64454671156093448733582785)
      ·
        refine ⟨48341003367070086550187089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64454671156093448733582785 48341003367070086550187089)
        ·
          refine ⟨36255752525302564912640317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48341003367070086550187089 36255752525302564912640317)
          ·
            refine ⟨13595907196988461842240119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36255752525302564912640317 13595907196988461842240119)
            ·
              refine ⟨20393860795482692763360179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13595907196988461842240119 20393860795482692763360179)
              ·
                refine ⟨30590791193224039145040269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20393860795482692763360179 30590791193224039145040269)
                ·
                  refine ⟨11471546697459014679390101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30590791193224039145040269 11471546697459014679390101)
                  ·
                    refine ⟨537728751443391313096411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11471546697459014679390101 537728751443391313096411)
                    ·
                      rfl

theorem cell23_3141669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_3141669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141669 prefixEnd_3141669 := by exact prefixLift 3141669
  have htrace : WordTrace (prefixWord ++ tailWord_3141669) baseStart_3141669 baseEnd_3141669 := by
    simpa [prefixWord, tailWord_3141669, baseEnd_3141669] using wordTrace_append hprefix tailTrace_3141669
  have hstable : (prefixWord ++ tailWord_3141669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141669).length < 2 ^ (prefixWord ++ tailWord_3141669).sum := by decide
  have hdescent : baseEnd_3141669 < baseStart_3141669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141679 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_3141679 : Nat := 118140960795 + 3141679 * 2 ^ 59
def prefixEnd_3141679 : Nat := 4983230072969 + 3 ^ 40 * 3141679 * 2
def baseEnd_3141679 : Nat := 1613191389136718900164187

theorem tailTrace_3141679 : CollatzResearch.WordTrace tailWord_3141679 prefixEnd_3141679 1613191389136718900164187 := by
  unfold tailWord_3141679
  simp only [CollatzResearch.WordTrace]
  refine ⟨114586446785241013900900091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76390964523494009267266727 114586446785241013900900091)
  ·
    refine ⟨171879670177861520851350137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114586446785241013900900091 171879670177861520851350137)
    ·
      refine ⟨128909752633396140638512603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171879670177861520851350137 128909752633396140638512603)
      ·
        refine ⟨193364628950094210957768905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128909752633396140638512603 193364628950094210957768905)
        ·
          refine ⟨145023471712570658218326679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193364628950094210957768905 145023471712570658218326679)
          ·
            refine ⟨217535207568855987327490019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145023471712570658218326679 217535207568855987327490019)
            ·
              refine ⟨326302811353283980991235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217535207568855987327490019 326302811353283980991235029)
              ·
                refine ⟨7647722141092593304482071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 326302811353283980991235029 7647722141092593304482071)
                ·
                  refine ⟨11471583211638889956723107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7647722141092593304482071 11471583211638889956723107)
                  ·
                    refine ⟨17207374817458334935084661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11471583211638889956723107 17207374817458334935084661)
                    ·
                      refine ⟨1613191389136718900164187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17207374817458334935084661 1613191389136718900164187)
                      ·
                        rfl

theorem cell23_3141679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_3141679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141679 prefixEnd_3141679 := by exact prefixLift 3141679
  have htrace : WordTrace (prefixWord ++ tailWord_3141679) baseStart_3141679 baseEnd_3141679 := by
    simpa [prefixWord, tailWord_3141679, baseEnd_3141679] using wordTrace_append hprefix tailTrace_3141679
  have hstable : (prefixWord ++ tailWord_3141679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141679).length < 2 ^ (prefixWord ++ tailWord_3141679).sum := by decide
  have hdescent : baseEnd_3141679 < baseStart_3141679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141686 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3141686 : Nat := 118140960795 + 3141686 * 2 ^ 59
def prefixEnd_3141686 : Nat := 4983230072969 + 3 ^ 40 * 3141686 * 2
def baseEnd_3141686 : Nat := 537731661167100124258885

theorem tailTrace_3141686 : CollatzResearch.WordTrace tailWord_3141686 prefixEnd_3141686 537731661167100124258885 := by
  unfold tailWord_3141686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161668881013478381025307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76391134730810436064269941 7161668881013478381025307)
  ·
    refine ⟨10742503321520217571537961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7161668881013478381025307 10742503321520217571537961)
    ·
      refine ⟨8056877491140163178653471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10742503321520217571537961 8056877491140163178653471)
      ·
        refine ⟨12085316236710244767980207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8056877491140163178653471 12085316236710244767980207)
        ·
          refine ⟨18127974355065367151970311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12085316236710244767980207 18127974355065367151970311)
          ·
            refine ⟨27191961532598050727955467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18127974355065367151970311 27191961532598050727955467)
            ·
              refine ⟨40787942298897076091933201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27191961532598050727955467 40787942298897076091933201)
              ·
                refine ⟨30590956724172807068949901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40787942298897076091933201 30590956724172807068949901)
                ·
                  refine ⟨11471608771564802650856213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30590956724172807068949901 11471608771564802650856213)
                  ·
                    refine ⟨537731661167100124258885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11471608771564802650856213 537731661167100124258885)
                    ·
                      rfl

theorem cell23_3141686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3141686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141686 prefixEnd_3141686 := by exact prefixLift 3141686
  have htrace : WordTrace (prefixWord ++ tailWord_3141686) baseStart_3141686 baseEnd_3141686 := by
    simpa [prefixWord, tailWord_3141686, baseEnd_3141686] using wordTrace_append hprefix tailTrace_3141686
  have hstable : (prefixWord ++ tailWord_3141686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141686).length < 2 ^ (prefixWord ++ tailWord_3141686).sum := by decide
  have hdescent : baseEnd_3141686 < baseStart_3141686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141696 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3]
def baseStart_3141696 : Nat := 118140960795 + 3141696 * 2 ^ 59
def prefixEnd_3141696 : Nat := 4983230072969 + 3 ^ 40 * 3141696 * 2
def baseEnd_3141696 : Nat := 1613200118307845333651609

theorem tailTrace_3141696 : CollatzResearch.WordTrace tailWord_3141696 prefixEnd_3141696 1613200118307845333651609 := by
  unfold tailWord_3141696
  simp only [CollatzResearch.WordTrace]
  refine ⟨57293533413089712902134471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76391377884119617202845961 57293533413089712902134471)
  ·
    refine ⟨85940300119634569353201707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57293533413089712902134471 85940300119634569353201707)
    ·
      refine ⟨128910450179451854029802561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85940300119634569353201707 128910450179451854029802561)
      ·
        refine ⟨96682837634588890522351921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128910450179451854029802561 96682837634588890522351921)
        ·
          refine ⟨72512128225941667891763941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96682837634588890522351921 72512128225941667891763941)
          ·
            refine ⟨13596024042364062729705739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72512128225941667891763941 13596024042364062729705739)
            ·
              refine ⟨20394036063546094094558609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13596024042364062729705739 20394036063546094094558609)
              ·
                refine ⟨15295527047659570570918957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20394036063546094094558609 15295527047659570570918957)
                ·
                  refine ⟨5735822642872338964094609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15295527047659570570918957 5735822642872338964094609)
                  ·
                    refine ⟨4301866982154254223070957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5735822642872338964094609 4301866982154254223070957)
                    ·
                      refine ⟨1613200118307845333651609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4301866982154254223070957 1613200118307845333651609)
                      ·
                        rfl

theorem cell23_3141696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_3141696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141696 prefixEnd_3141696 := by exact prefixLift 3141696
  have htrace : WordTrace (prefixWord ++ tailWord_3141696) baseStart_3141696 baseEnd_3141696 := by
    simpa [prefixWord, tailWord_3141696, baseEnd_3141696] using wordTrace_append hprefix tailTrace_3141696
  have hstable : (prefixWord ++ tailWord_3141696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141696).length < 2 ^ (prefixWord ++ tailWord_3141696).sum := by decide
  have hdescent : baseEnd_3141696 < baseStart_3141696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141710 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_3141710 : Nat := 118140960795 + 3141710 * 2 ^ 59
def prefixEnd_3141710 : Nat := 4983230072969 + 3 ^ 40 * 3141710 * 2
def baseEnd_3141710 : Nat := 1613207307037008278876545

theorem tailTrace_3141710 : CollatzResearch.WordTrace tailWord_3141710 prefixEnd_3141710 1613207307037008278876545 := by
  unfold tailWord_3141710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14323447181016088274409823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76391718298752470796852389 14323447181016088274409823)
  ·
    refine ⟨21485170771524132411614735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14323447181016088274409823 21485170771524132411614735)
    ·
      refine ⟨32227756157286198617422103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21485170771524132411614735 32227756157286198617422103)
      ·
        refine ⟨48341634235929297926133155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32227756157286198617422103 48341634235929297926133155)
        ·
          refine ⟨72512451353893946889199733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48341634235929297926133155 72512451353893946889199733)
          ·
            refine ⟨6798042314427557520862475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72512451353893946889199733 6798042314427557520862475)
            ·
              refine ⟨10197063471641336281293713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798042314427557520862475 10197063471641336281293713)
              ·
                refine ⟨7647797603731002210970285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10197063471641336281293713 7647797603731002210970285)
                ·
                  refine ⟨2867924101399125829113857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7647797603731002210970285 2867924101399125829113857)
                  ·
                    refine ⟨2150943076049344371835393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867924101399125829113857 2150943076049344371835393)
                    ·
                      refine ⟨1613207307037008278876545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150943076049344371835393 1613207307037008278876545)
                      ·
                        rfl

theorem cell23_3141710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_3141710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141710 prefixEnd_3141710 := by exact prefixLift 3141710
  have htrace : WordTrace (prefixWord ++ tailWord_3141710) baseStart_3141710 baseEnd_3141710 := by
    simpa [prefixWord, tailWord_3141710, baseEnd_3141710] using wordTrace_append hprefix tailTrace_3141710
  have hstable : (prefixWord ++ tailWord_3141710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141710).length < 2 ^ (prefixWord ++ tailWord_3141710).sum := by decide
  have hdescent : baseEnd_3141710 < baseStart_3141710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141743 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 3]
def baseStart_3141743 : Nat := 118140960795 + 3141743 * 2 ^ 59
def prefixEnd_3141743 : Nat := 4983230072969 + 3 ^ 40 * 3141743 * 2
def baseEnd_3141743 : Nat := 1613224251898606649763893

theorem tailTrace_3141743 : CollatzResearch.WordTrace tailWord_3141743 prefixEnd_3141743 1613224251898606649763893 := by
  unfold tailWord_3141743
  simp only [CollatzResearch.WordTrace]
  refine ⟨114588781057009152831229883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76392520704672768554153255 114588781057009152831229883)
  ·
    refine ⟨171883171585513729246844825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114588781057009152831229883 171883171585513729246844825)
    ·
      refine ⟨128912378689135296935133619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171883171585513729246844825 128912378689135296935133619)
      ·
        refine ⟨193368568033702945402700429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128912378689135296935133619 193368568033702945402700429)
        ·
          refine ⟨72513213012638604526012661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193368568033702945402700429 72513213012638604526012661)
          ·
            refine ⟨6798113719934869174313687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72513213012638604526012661 6798113719934869174313687)
            ·
              refine ⟨10197170579902303761470531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798113719934869174313687 10197170579902303761470531)
              ·
                refine ⟨15295755869853455642205797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10197170579902303761470531 15295755869853455642205797)
                ·
                  refine ⟨2867954225597522932913587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15295755869853455642205797 2867954225597522932913587)
                  ·
                    refine ⟨4301931338396284399370381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867954225597522932913587 4301931338396284399370381)
                    ·
                      refine ⟨1613224251898606649763893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4301931338396284399370381 1613224251898606649763893)
                      ·
                        rfl

theorem cell23_3141743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 3].length) (baseStart_3141743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141743 prefixEnd_3141743 := by exact prefixLift 3141743
  have htrace : WordTrace (prefixWord ++ tailWord_3141743) baseStart_3141743 baseEnd_3141743 := by
    simpa [prefixWord, tailWord_3141743, baseEnd_3141743] using wordTrace_append hprefix tailTrace_3141743
  have hstable : (prefixWord ++ tailWord_3141743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141743).length < 2 ^ (prefixWord ++ tailWord_3141743).sum := by decide
  have hdescent : baseEnd_3141743 < baseStart_3141743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141770 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_3141770 : Nat := 118140960795 + 3141770 * 2 ^ 59
def prefixEnd_3141770 : Nat := 4983230072969 + 3 ^ 40 * 3141770 * 2
def baseEnd_3141770 : Nat := 1613238115876278044126269

theorem tailTrace_3141770 : CollatzResearch.WordTrace tailWord_3141770 prefixEnd_3141770 1613238115876278044126269 := by
  unfold tailWord_3141770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28647441456977834110615691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76393177218607557628308509 28647441456977834110615691)
  ·
    refine ⟨42971162185466751165923537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28647441456977834110615691 42971162185466751165923537)
    ·
      refine ⟨32228371639100063374442653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42971162185466751165923537 32228371639100063374442653)
      ·
        refine ⟨12085639364662523765415995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32228371639100063374442653 12085639364662523765415995)
        ·
          refine ⟨18128459046993785648123993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12085639364662523765415995 18128459046993785648123993)
          ·
            refine ⟨13596344285245339236092995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18128459046993785648123993 13596344285245339236092995)
            ·
              refine ⟨20394516427868008854139493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13596344285245339236092995 20394516427868008854139493)
              ·
                refine ⟨3823971830225251660151155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20394516427868008854139493 3823971830225251660151155)
                ·
                  refine ⟨5735957745337877490226733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823971830225251660151155 5735957745337877490226733)
                  ·
                    refine ⟨2150984154501704058835025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5735957745337877490226733 2150984154501704058835025)
                    ·
                      refine ⟨1613238115876278044126269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2150984154501704058835025 1613238115876278044126269)
                      ·
                        rfl

theorem cell23_3141770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_3141770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141770 prefixEnd_3141770 := by exact prefixLift 3141770
  have htrace : WordTrace (prefixWord ++ tailWord_3141770) baseStart_3141770 baseEnd_3141770 := by
    simpa [prefixWord, tailWord_3141770, baseEnd_3141770] using wordTrace_append hprefix tailTrace_3141770
  have hstable : (prefixWord ++ tailWord_3141770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141770).length < 2 ^ (prefixWord ++ tailWord_3141770).sum := by decide
  have hdescent : baseEnd_3141770 < baseStart_3141770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141816 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_3141816 : Nat := 118140960795 + 3141816 * 2 ^ 59
def prefixEnd_3141816 : Nat := 4983230072969 + 3 ^ 40 * 3141816 * 2
def baseEnd_3141816 : Nat := 1613261735986384864151057

theorem tailTrace_3141816 : CollatzResearch.WordTrace tailWord_3141816 prefixEnd_3141816 1613261735986384864151057 := by
  unfold tailWord_3141816
  simp only [CollatzResearch.WordTrace]
  refine ⟨57295721792872343149318651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76394295723829790865758201 57295721792872343149318651)
  ·
    refine ⟨85943582689308514723977977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57295721792872343149318651 85943582689308514723977977)
    ·
      refine ⟨64457687016981386042983483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85943582689308514723977977 64457687016981386042983483)
      ·
        refine ⟨96686530525472079064475225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64457687016981386042983483 96686530525472079064475225)
        ·
          refine ⟨72514897894104059298356419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96686530525472079064475225 72514897894104059298356419)
          ·
            refine ⟨108772346841156088947534629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72514897894104059298356419 108772346841156088947534629)
            ·
              refine ⟨20394815032716766677662743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108772346841156088947534629 20394815032716766677662743)
              ·
                refine ⟨30592222549075150016494115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20394815032716766677662743 30592222549075150016494115)
                ·
                  refine ⟨45888333823612725024741173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30592222549075150016494115 45888333823612725024741173)
                  ·
                    refine ⟨4302031295963692971069485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45888333823612725024741173 4302031295963692971069485)
                    ·
                      refine ⟨1613261735986384864151057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302031295963692971069485 1613261735986384864151057)
                      ·
                        rfl

theorem cell23_3141816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_3141816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141816 prefixEnd_3141816 := by exact prefixLift 3141816
  have htrace : WordTrace (prefixWord ++ tailWord_3141816) baseStart_3141816 baseEnd_3141816 := by
    simpa [prefixWord, tailWord_3141816, baseEnd_3141816] using wordTrace_append hprefix tailTrace_3141816
  have hstable : (prefixWord ++ tailWord_3141816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141816).length < 2 ^ (prefixWord ++ tailWord_3141816).sum := by decide
  have hdescent : baseEnd_3141816 < baseStart_3141816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141863 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3141863 : Nat := 118140960795 + 3141863 * 2 ^ 59
def prefixEnd_3141863 : Nat := 4983230072969 + 3 ^ 40 * 3141863 * 2
def baseEnd_3141863 : Nat := 1613285869577146180263341

theorem tailTrace_3141863 : CollatzResearch.WordTrace tailWord_3141863 prefixEnd_3141863 1613285869577146180263341 := by
  unfold tailWord_3141863
  simp only [CollatzResearch.WordTrace]
  refine ⟨114593157816574413325598243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76395438544382942217065495 114593157816574413325598243)
  ·
    refine ⟨171889736724861619988397365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114593157816574413325598243 171889736724861619988397365)
    ·
      refine ⟨16114662817955776873912253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171889736724861619988397365 16114662817955776873912253)
      ·
        refine ⟨6042998556733416327717095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16114662817955776873912253 6042998556733416327717095)
        ·
          refine ⟨9064497835100124491575643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042998556733416327717095 9064497835100124491575643)
          ·
            refine ⟨13596746752650186737363465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9064497835100124491575643 13596746752650186737363465)
            ·
              refine ⟨10197560064487640053022599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13596746752650186737363465 10197560064487640053022599)
              ·
                refine ⟨15296340096731460079533899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10197560064487640053022599 15296340096731460079533899)
                ·
                  refine ⟨22944510145097190119300849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15296340096731460079533899 22944510145097190119300849)
                  ·
                    refine ⟨17208382608822892589475637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22944510145097190119300849 17208382608822892589475637)
                    ·
                      refine ⟨1613285869577146180263341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17208382608822892589475637 1613285869577146180263341)
                      ·
                        rfl

theorem cell23_3141863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3141863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141863 prefixEnd_3141863 := by exact prefixLift 3141863
  have htrace : WordTrace (prefixWord ++ tailWord_3141863) baseStart_3141863 baseEnd_3141863 := by
    simpa [prefixWord, tailWord_3141863, baseEnd_3141863] using wordTrace_append hprefix tailTrace_3141863
  have hstable : (prefixWord ++ tailWord_3141863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141863).length < 2 ^ (prefixWord ++ tailWord_3141863).sum := by decide
  have hdescent : baseEnd_3141863 < baseStart_3141863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141873 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 1, 6, 2]
def baseStart_3141873 : Nat := 118140960795 + 3141873 * 2 ^ 59
def prefixEnd_3141873 : Nat := 4983230072969 + 3 ^ 40 * 3141873 * 2
def baseEnd_3141873 : Nat := 1613291004383691141138295

theorem tailTrace_3141873 : CollatzResearch.WordTrace tailWord_3141873 prefixEnd_3141873 1613291004383691141138295 := by
  unfold tailWord_3141873
  simp only [CollatzResearch.WordTrace]
  refine ⟨114593522546538185033462273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76395681697692123355641515 114593522546538185033462273)
  ·
    refine ⟨85945141909903638775096705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114593522546538185033462273 85945141909903638775096705)
    ·
      refine ⟨64458856432427729081322529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85945141909903638775096705 64458856432427729081322529)
      ·
        refine ⟨48344142324320796810991897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64458856432427729081322529 48344142324320796810991897)
        ·
          refine ⟨36258106743240597608243923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48344142324320796810991897 36258106743240597608243923)
          ·
            refine ⟨54387160114860896412365885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36258106743240597608243923 54387160114860896412365885)
            ·
              refine ⟨20395185043072836154637207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54387160114860896412365885 20395185043072836154637207)
              ·
                refine ⟨30592777564609254231955811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20395185043072836154637207 30592777564609254231955811)
                ·
                  refine ⟨45889166346913881347933717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30592777564609254231955811 45889166346913881347933717)
                  ·
                    refine ⟨2151054672511588188184393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45889166346913881347933717 2151054672511588188184393)
                    ·
                      refine ⟨1613291004383691141138295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151054672511588188184393 1613291004383691141138295)
                      ·
                        rfl

theorem cell23_3141873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_3141873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141873 prefixEnd_3141873 := by exact prefixLift 3141873
  have htrace : WordTrace (prefixWord ++ tailWord_3141873) baseStart_3141873 baseEnd_3141873 := by
    simpa [prefixWord, tailWord_3141873, baseEnd_3141873] using wordTrace_append hprefix tailTrace_3141873
  have hstable : (prefixWord ++ tailWord_3141873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141873).length < 2 ^ (prefixWord ++ tailWord_3141873).sum := by decide
  have hdescent : baseEnd_3141873 < baseStart_3141873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141890 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3141890 : Nat := 118140960795 + 3141890 * 2 ^ 59
def prefixEnd_3141890 : Nat := 4983230072969 + 3 ^ 40 * 3141890 * 2
def baseEnd_3141890 : Nat := 1613299733554817574625717

theorem tailTrace_3141890 : CollatzResearch.WordTrace tailWord_3141890 prefixEnd_3141890 1613299733554817574625717 := by
  unfold tailWord_3141890
  simp only [CollatzResearch.WordTrace]
  refine ⟨28648535646869149234207781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76396095058317731291220749 28648535646869149234207781)
  ·
    refine ⟨5371600433787965481413959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28648535646869149234207781 5371600433787965481413959)
    ·
      refine ⟨8057400650681948222120939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5371600433787965481413959 8057400650681948222120939)
      ·
        refine ⟨12086100976022922333181409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8057400650681948222120939 12086100976022922333181409)
        ·
          refine ⟨9064575732017191749886057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12086100976022922333181409 9064575732017191749886057)
          ·
            refine ⟨6798431799012893812414543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9064575732017191749886057 6798431799012893812414543)
            ·
              refine ⟨10197647698519340718621815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798431799012893812414543 10197647698519340718621815)
              ·
                refine ⟨15296471547779011077932723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10197647698519340718621815 15296471547779011077932723)
                ·
                  refine ⟨22944707321668516616899085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15296471547779011077932723 22944707321668516616899085)
                  ·
                    refine ⟨8604265245625693731337157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22944707321668516616899085 8604265245625693731337157)
                    ·
                      refine ⟨1613299733554817574625717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8604265245625693731337157 1613299733554817574625717)
                      ·
                        rfl

theorem cell23_3141890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3141890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141890 prefixEnd_3141890 := by exact prefixLift 3141890
  have htrace : WordTrace (prefixWord ++ tailWord_3141890) baseStart_3141890 baseEnd_3141890 := by
    simpa [prefixWord, tailWord_3141890, baseEnd_3141890] using wordTrace_append hprefix tailTrace_3141890
  have hstable : (prefixWord ++ tailWord_3141890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141890).length < 2 ^ (prefixWord ++ tailWord_3141890).sum := by decide
  have hdescent : baseEnd_3141890 < baseStart_3141890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141893 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_3141893 : Nat := 118140960795 + 3141893 * 2 ^ 59
def prefixEnd_3141893 : Nat := 4983230072969 + 3 ^ 40 * 3141893 * 2
def baseEnd_3141893 : Nat := 1613301273996781062888203

theorem tailTrace_3141893 : CollatzResearch.WordTrace tailWord_3141893 prefixEnd_3141893 1613301273996781062888203 := by
  unfold tailWord_3141893
  simp only [CollatzResearch.WordTrace]
  refine ⟨114594252006465728449190333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76396168004310485632793555 114594252006465728449190333)
  ·
    refine ⟨42972844502424648168446375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114594252006465728449190333 42972844502424648168446375)
    ·
      refine ⟨64459266753636972252669563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42972844502424648168446375 64459266753636972252669563)
      ·
        refine ⟨96688900130455458379004345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64459266753636972252669563 96688900130455458379004345)
        ·
          refine ⟨72516675097841593784253259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96688900130455458379004345 72516675097841593784253259)
          ·
            refine ⟨108775012646762390676379889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72516675097841593784253259 108775012646762390676379889)
            ·
              refine ⟨81581259485071793007284917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108775012646762390676379889 81581259485071793007284917)
              ·
                refine ⟨7648243076725480594432961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81581259485071793007284917 7648243076725480594432961)
                ·
                  refine ⟨5736182307544110445824721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7648243076725480594432961 5736182307544110445824721)
                  ·
                    refine ⟨4302136730658082834368541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5736182307544110445824721 4302136730658082834368541)
                    ·
                      refine ⟨1613301273996781062888203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302136730658082834368541 1613301273996781062888203)
                      ·
                        rfl

theorem cell23_3141893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_3141893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141893 prefixEnd_3141893 := by exact prefixLift 3141893
  have htrace : WordTrace (prefixWord ++ tailWord_3141893) baseStart_3141893 baseEnd_3141893 := by
    simpa [prefixWord, tailWord_3141893, baseEnd_3141893] using wordTrace_append hprefix tailTrace_3141893
  have hstable : (prefixWord ++ tailWord_3141893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141893).length < 2 ^ (prefixWord ++ tailWord_3141893).sum := by decide
  have hdescent : baseEnd_3141893 < baseStart_3141893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141917 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_3141917 : Nat := 118140960795 + 3141917 * 2 ^ 59
def prefixEnd_3141917 : Nat := 4983230072969 + 3 ^ 40 * 3141917 * 2
def baseEnd_3141917 : Nat := 537771199177496322996031

theorem tailTrace_3141917 : CollatzResearch.WordTrace tailWord_3141917 prefixEnd_3141917 537771199177496322996031 := by
  unfold tailWord_3141917
  simp only [CollatzResearch.WordTrace]
  refine ⟨114595127358378780548064005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76396751572252520365376003 114595127358378780548064005)
  ·
    refine ⟨21486586379696021352762001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114595127358378780548064005 21486586379696021352762001)
    ·
      refine ⟨16114939784772016014571501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21486586379696021352762001 16114939784772016014571501)
      ·
        refine ⟨6043102419289506005464313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16114939784772016014571501 6043102419289506005464313)
        ·
          refine ⟨4532326814467129504098235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6043102419289506005464313 4532326814467129504098235)
          ·
            refine ⟨6798490221700694256147353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532326814467129504098235 6798490221700694256147353)
            ·
              refine ⟨5098867666275520692110515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6798490221700694256147353 5098867666275520692110515)
              ·
                refine ⟨7648301499413281038165773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098867666275520692110515 7648301499413281038165773)
                ·
                  refine ⟨2868113062279980389312165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7648301499413281038165773 2868113062279980389312165)
                  ·
                    refine ⟨537771199177496322996031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868113062279980389312165 537771199177496322996031)
                    ·
                      rfl

theorem cell23_3141917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_3141917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141917 prefixEnd_3141917 := by exact prefixLift 3141917
  have htrace : WordTrace (prefixWord ++ tailWord_3141917) baseStart_3141917 baseEnd_3141917 := by
    simpa [prefixWord, tailWord_3141917, baseEnd_3141917] using wordTrace_append hprefix tailTrace_3141917
  have hstable : (prefixWord ++ tailWord_3141917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141917).length < 2 ^ (prefixWord ++ tailWord_3141917).sum := by decide
  have hdescent : baseEnd_3141917 < baseStart_3141917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141983 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_3141983 : Nat := 118140960795 + 3141983 * 2 ^ 59
def prefixEnd_3141983 : Nat := 4983230072969 + 3 ^ 40 * 3141983 * 2
def baseEnd_3141983 : Nat := 1613347487255685710762789

theorem tailTrace_3141983 : CollatzResearch.WordTrace tailWord_3141983 prefixEnd_3141983 1613347487255685710762789 := by
  unfold tailWord_3141983
  simp only [CollatzResearch.WordTrace]
  refine ⟨114597534576139673819966603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76398356384093115879977735 114597534576139673819966603)
  ·
    refine ⟨171896301864209510729949905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114597534576139673819966603 171896301864209510729949905)
    ·
      refine ⟨128922226398157133047462429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171896301864209510729949905 128922226398157133047462429)
      ·
        refine ⟨48345834899308924892798411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128922226398157133047462429 48345834899308924892798411)
        ·
          refine ⟨72518752348963387339197617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48345834899308924892798411 72518752348963387339197617)
          ·
            refine ⟨54389064261722540504398213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72518752348963387339197617 54389064261722540504398213)
            ·
              refine ⟨10197949549072976344574665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54389064261722540504398213 10197949549072976344574665)
              ·
                refine ⟨7648462161804732258430999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10197949549072976344574665 7648462161804732258430999)
                ·
                  refine ⟨11472693242707098387646499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648462161804732258430999 11472693242707098387646499)
                  ·
                    refine ⟨17209039864060647581469749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11472693242707098387646499 17209039864060647581469749)
                    ·
                      refine ⟨1613347487255685710762789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17209039864060647581469749 1613347487255685710762789)
                      ·
                        rfl

theorem cell23_3141983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_3141983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141983 prefixEnd_3141983 := by exact prefixLift 3141983
  have htrace : WordTrace (prefixWord ++ tailWord_3141983) baseStart_3141983 baseEnd_3141983 := by
    simpa [prefixWord, tailWord_3141983, baseEnd_3141983] using wordTrace_append hprefix tailTrace_3141983
  have hstable : (prefixWord ++ tailWord_3141983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141983).length < 2 ^ (prefixWord ++ tailWord_3141983).sum := by decide
  have hdescent : baseEnd_3141983 < baseStart_3141983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141993 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_3141993 : Nat := 118140960795 + 3141993 * 2 ^ 59
def prefixEnd_3141993 : Nat := 4983230072969 + 3 ^ 40 * 3141993 * 2
def baseEnd_3141993 : Nat := 1613352622062230671637743

theorem tailTrace_3141993 : CollatzResearch.WordTrace tailWord_3141993 prefixEnd_3141993 1613352622062230671637743 := by
  unfold tailWord_3141993
  simp only [CollatzResearch.WordTrace]
  refine ⟨114597899306103445527830633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76398599537402297018553755 114597899306103445527830633)
  ·
    refine ⟨85948424479577584145872975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114597899306103445527830633 85948424479577584145872975)
    ·
      refine ⟨128922636719366376218809463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85948424479577584145872975 128922636719366376218809463)
      ·
        refine ⟨193383955079049564328214195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128922636719366376218809463 193383955079049564328214195)
        ·
          refine ⟨290075932618574346492321293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193383955079049564328214195 290075932618574346492321293)
          ·
            refine ⟨108778474731965379934620485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290075932618574346492321293 108778474731965379934620485)
            ·
              refine ⟨20395964012243508737741341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108778474731965379934620485 20395964012243508737741341)
              ·
                refine ⟨7648486504591315776653003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20395964012243508737741341 7648486504591315776653003)
                ·
                  refine ⟨11472729756886973664979505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648486504591315776653003 11472729756886973664979505)
                  ·
                    refine ⟨8604547317665230248734629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11472729756886973664979505 8604547317665230248734629)
                    ·
                      refine ⟨1613352622062230671637743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8604547317665230248734629 1613352622062230671637743)
                      ·
                        rfl

theorem cell23_3141993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_3141993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141993 prefixEnd_3141993 := by exact prefixLift 3141993
  have htrace : WordTrace (prefixWord ++ tailWord_3141993) baseStart_3141993 baseEnd_3141993 := by
    simpa [prefixWord, tailWord_3141993, baseEnd_3141993] using wordTrace_append hprefix tailTrace_3141993
  have hstable : (prefixWord ++ tailWord_3141993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141993).length < 2 ^ (prefixWord ++ tailWord_3141993).sum := by decide
  have hdescent : baseEnd_3141993 < baseStart_3141993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141997 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_3141997 : Nat := 118140960795 + 3141997 * 2 ^ 59
def prefixEnd_3141997 : Nat := 4983230072969 + 3 ^ 40 * 3141997 * 2
def baseEnd_3141997 : Nat := 1613354675984848655987725

theorem tailTrace_3141997 : CollatzResearch.WordTrace tailWord_3141997 prefixEnd_3141997 1613354675984848655987725 := by
  unfold tailWord_3141997
  simp only [CollatzResearch.WordTrace]
  refine ⟨114598045198088954210976245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76398696798725969473984163 114598045198088954210976245)
  ·
    refine ⟨10743566737320839457279023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114598045198088954210976245 10743566737320839457279023)
    ·
      refine ⟨16115350105981259185918535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743566737320839457279023 16115350105981259185918535)
      ·
        refine ⟨24173025158971888778877803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16115350105981259185918535 24173025158971888778877803)
        ·
          refine ⟨36259537738457833168316705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24173025158971888778877803 36259537738457833168316705)
          ·
            refine ⟨27194653303843374876237529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36259537738457833168316705 27194653303843374876237529)
            ·
              refine ⟨20395989977882531157178147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27194653303843374876237529 20395989977882531157178147)
              ·
                refine ⟨30593984966823796735767221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20395989977882531157178147 30593984966823796735767221)
                ·
                  refine ⟨2868186090639730943978177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30593984966823796735767221 2868186090639730943978177)
                  ·
                    refine ⟨2151139567979798207983633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2868186090639730943978177 2151139567979798207983633)
                    ·
                      refine ⟨1613354675984848655987725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151139567979798207983633 1613354675984848655987725)
                      ·
                        rfl

theorem cell23_3141997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_3141997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3141997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3141997 prefixEnd_3141997 := by exact prefixLift 3141997
  have htrace : WordTrace (prefixWord ++ tailWord_3141997) baseStart_3141997 baseEnd_3141997 := by
    simpa [prefixWord, tailWord_3141997, baseEnd_3141997] using wordTrace_append hprefix tailTrace_3141997
  have hstable : (prefixWord ++ tailWord_3141997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141997).length < 2 ^ (prefixWord ++ tailWord_3141997).sum := by decide
  have hdescent : baseEnd_3141997 < baseStart_3141997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142000 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3]
def baseStart_3142000 : Nat := 118140960795 + 3142000 * 2 ^ 59
def prefixEnd_3142000 : Nat := 4983230072969 + 3 ^ 40 * 3142000 * 2
def baseEnd_3142000 : Nat := 1613356216426812144250211

theorem tailTrace_3142000 : CollatzResearch.WordTrace tailWord_3142000 prefixEnd_3142000 1613356216426812144250211 := by
  unfold tailWord_3142000
  simp only [CollatzResearch.WordTrace]
  refine ⟨57299077308539042861667727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76398769744718723815556969 57299077308539042861667727)
  ·
    refine ⟨85948615962808564292501591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57299077308539042861667727 85948615962808564292501591)
    ·
      refine ⟨128922923944212846438752387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85948615962808564292501591 128922923944212846438752387)
      ·
        refine ⟨193384385916319269658128581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128922923944212846438752387 193384385916319269658128581)
        ·
          refine ⟨36259572359309863060899109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193384385916319269658128581 36259572359309863060899109)
          ·
            refine ⟨6798669817370599323918583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36259572359309863060899109 6798669817370599323918583)
            ·
              refine ⟨10198004726055898985877875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798669817370599323918583 10198004726055898985877875)
              ·
                refine ⟨15297007089083848478816813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10198004726055898985877875 15297007089083848478816813)
                ·
                  refine ⟨5736377658406443179556305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15297007089083848478816813 5736377658406443179556305)
                  ·
                    refine ⟨4302283243804832384667229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5736377658406443179556305 4302283243804832384667229)
                    ·
                      refine ⟨1613356216426812144250211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302283243804832384667229 1613356216426812144250211)
                      ·
                        rfl

theorem cell23_3142000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_3142000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142000 prefixEnd_3142000 := by exact prefixLift 3142000
  have htrace : WordTrace (prefixWord ++ tailWord_3142000) baseStart_3142000 baseEnd_3142000 := by
    simpa [prefixWord, tailWord_3142000, baseEnd_3142000] using wordTrace_append hprefix tailTrace_3142000
  have hstable : (prefixWord ++ tailWord_3142000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142000).length < 2 ^ (prefixWord ++ tailWord_3142000).sum := by decide
  have hdescent : baseEnd_3142000 < baseStart_3142000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142017 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3142017 : Nat := 118140960795 + 3142017 * 2 ^ 59
def prefixEnd_3142017 : Nat := 4983230072969 + 3 ^ 40 * 3142017 * 2
def baseEnd_3142017 : Nat := 1613364945597938577737633

theorem tailTrace_3142017 : CollatzResearch.WordTrace tailWord_3142017 prefixEnd_3142017 1613364945597938577737633 := by
  unfold tailWord_3142017
  simp only [CollatzResearch.WordTrace]
  refine ⟨114598774658016497626704305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76399183105344331751136203 114598774658016497626704305)
  ·
    refine ⟨85949080993512373220028229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114598774658016497626704305 85949080993512373220028229)
    ·
      refine ⟨16115452686283569978755293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85949080993512373220028229 16115452686283569978755293)
      ·
        refine ⟨6043294757356338742033235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16115452686283569978755293 6043294757356338742033235)
        ·
          refine ⟨9064942136034508113049853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6043294757356338742033235 9064942136034508113049853)
          ·
            refine ⟨3399353301012940542393695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9064942136034508113049853 3399353301012940542393695)
            ·
              refine ⟨5099029951519410813590543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399353301012940542393695 5099029951519410813590543)
              ·
                refine ⟨7648544927279116220385815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099029951519410813590543 7648544927279116220385815)
                ·
                  refine ⟨11472817390918674330578723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648544927279116220385815 11472817390918674330578723)
                  ·
                    refine ⟨17209226086378011495868085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11472817390918674330578723 17209226086378011495868085)
                    ·
                      refine ⟨1613364945597938577737633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17209226086378011495868085 1613364945597938577737633)
                      ·
                        rfl

theorem cell23_3142017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3142017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142017 prefixEnd_3142017 := by exact prefixLift 3142017
  have htrace : WordTrace (prefixWord ++ tailWord_3142017) baseStart_3142017 baseEnd_3142017 := by
    simpa [prefixWord, tailWord_3142017, baseEnd_3142017] using wordTrace_append hprefix tailTrace_3142017
  have hstable : (prefixWord ++ tailWord_3142017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142017).length < 2 ^ (prefixWord ++ tailWord_3142017).sum := by decide
  have hdescent : baseEnd_3142017 < baseStart_3142017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142047 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3142047 : Nat := 118140960795 + 3142047 * 2 ^ 59
def prefixEnd_3142047 : Nat := 4983230072969 + 3 ^ 40 * 3142047 * 2
def baseEnd_3142047 : Nat := 1613380350017573460362495

theorem tailTrace_3142047 : CollatzResearch.WordTrace tailWord_3142047 prefixEnd_3142047 1613380350017573460362495 := by
  unfold tailWord_3142047
  simp only [CollatzResearch.WordTrace]
  refine ⟨114599868847907812750296395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76399912565271875166864263 114599868847907812750296395)
  ·
    refine ⟨171899803271861719125444593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114599868847907812750296395 171899803271861719125444593)
    ·
      refine ⟨128924852453896289344083445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171899803271861719125444593 128924852453896289344083445)
      ·
        refine ⟨12086704917552777126007823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128924852453896289344083445 12086704917552777126007823)
        ·
          refine ⟨18130057376329165689011735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12086704917552777126007823 18130057376329165689011735)
          ·
            refine ⟨27195086064493748533517603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18130057376329165689011735 27195086064493748533517603)
            ·
              refine ⟨40792629096740622800276405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27195086064493748533517603 40792629096740622800276405)
              ·
                refine ⟨3824308977819433387525913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40792629096740622800276405 3824308977819433387525913)
                ·
                  refine ⟨2868231733364575040644435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3824308977819433387525913 2868231733364575040644435)
                  ·
                    refine ⟨4302347600046862560966653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2868231733364575040644435 4302347600046862560966653)
                    ·
                      refine ⟨1613380350017573460362495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302347600046862560966653 1613380350017573460362495)
                      ·
                        rfl

theorem cell23_3142047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3142047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142047 prefixEnd_3142047 := by exact prefixLift 3142047
  have htrace : WordTrace (prefixWord ++ tailWord_3142047) baseStart_3142047 baseEnd_3142047 := by
    simpa [prefixWord, tailWord_3142047, baseEnd_3142047] using wordTrace_append hprefix tailTrace_3142047
  have hstable : (prefixWord ++ tailWord_3142047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142047).length < 2 ^ (prefixWord ++ tailWord_3142047).sum := by decide
  have hdescent : baseEnd_3142047 < baseStart_3142047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142053 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_3142053 : Nat := 118140960795 + 3142053 * 2 ^ 59
def prefixEnd_3142053 : Nat := 4983230072969 + 3 ^ 40 * 3142053 * 2
def baseEnd_3142053 : Nat := 1613383430901500436887467

theorem tailTrace_3142053 : CollatzResearch.WordTrace tailWord_3142053 prefixEnd_3142053 1613383430901500436887467 := by
  unfold tailWord_3142053
  simp only [CollatzResearch.WordTrace]
  refine ⟨114600087685886075775014813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76400058457257383850009875 114600087685886075775014813)
  ·
    refine ⟨42975032882207278415630555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114600087685886075775014813 42975032882207278415630555)
    ·
      refine ⟨64462549323310917623445833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42975032882207278415630555 64462549323310917623445833)
      ·
        refine ⟨48346911992483188217584375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64462549323310917623445833 48346911992483188217584375)
        ·
          refine ⟨72520367988724782326376563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48346911992483188217584375 72520367988724782326376563)
          ·
            refine ⟨108780551983087173489564845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72520367988724782326376563 108780551983087173489564845)
            ·
              refine ⟨40792706993657690058586817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108780551983087173489564845 40792706993657690058586817)
              ·
                refine ⟨30594530245243267543940113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40792706993657690058586817 30594530245243267543940113)
                ·
                  refine ⟨22945897683932450657955085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30594530245243267543940113 22945897683932450657955085)
                  ·
                    refine ⟨8604711631474668996733157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22945897683932450657955085 8604711631474668996733157)
                    ·
                      refine ⟨1613383430901500436887467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8604711631474668996733157 1613383430901500436887467)
                      ·
                        rfl

theorem cell23_3142053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_3142053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142053 prefixEnd_3142053 := by exact prefixLift 3142053
  have htrace : WordTrace (prefixWord ++ tailWord_3142053) baseStart_3142053 baseEnd_3142053 := by
    simpa [prefixWord, tailWord_3142053, baseEnd_3142053] using wordTrace_append hprefix tailTrace_3142053
  have hstable : (prefixWord ++ tailWord_3142053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142053).length < 2 ^ (prefixWord ++ tailWord_3142053).sum := by decide
  have hdescent : baseEnd_3142053 < baseStart_3142053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142098 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3142098 : Nat := 118140960795 + 3142098 * 2 ^ 59
def prefixEnd_3142098 : Nat := 4983230072969 + 3 ^ 40 * 3142098 * 2
def baseEnd_3142098 : Nat := 1613406537530952760824761

theorem tailTrace_3142098 : CollatzResearch.WordTrace tailWord_3142098 prefixEnd_3142098 1613406537530952760824761 := by
  unfold tailWord_3142098
  simp only [CollatzResearch.WordTrace]
  refine ⟨28650432242680762115100737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76401152647148698973601965 28650432242680762115100737)
  ·
    refine ⟨21487824182010571586325553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28650432242680762115100737 21487824182010571586325553)
    ·
      refine ⟨16115868136507928689744165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21487824182010571586325553 16115868136507928689744165)
      ·
        refine ⟨3021725275595236629327031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16115868136507928689744165 3021725275595236629327031)
        ·
          refine ⟨4532587913392854943990547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021725275595236629327031 4532587913392854943990547)
          ·
            refine ⟨6798881870089282415985821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532587913392854943990547 6798881870089282415985821)
            ·
              refine ⟨2549580701283480905994683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6798881870089282415985821 2549580701283480905994683)
              ·
                refine ⟨3824371051925221358992025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549580701283480905994683 3824371051925221358992025)
                ·
                  refine ⟨2868278288943916019244019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3824371051925221358992025 2868278288943916019244019)
                  ·
                    refine ⟨4302417433415874028866029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2868278288943916019244019 4302417433415874028866029)
                    ·
                      refine ⟨1613406537530952760824761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302417433415874028866029 1613406537530952760824761)
                      ·
                        rfl

theorem cell23_3142098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3142098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142098 prefixEnd_3142098 := by exact prefixLift 3142098
  have htrace : WordTrace (prefixWord ++ tailWord_3142098) baseStart_3142098 baseEnd_3142098 := by
    simpa [prefixWord, tailWord_3142098, baseEnd_3142098] using wordTrace_append hprefix tailTrace_3142098
  have hstable : (prefixWord ++ tailWord_3142098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142098).length < 2 ^ (prefixWord ++ tailWord_3142098).sum := by decide
  have hdescent : baseEnd_3142098 < baseStart_3142098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142123 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 1, 7]
def baseStart_3142123 : Nat := 118140960795 + 3142123 * 2 ^ 59
def prefixEnd_3142123 : Nat := 4983230072969 + 3 ^ 40 * 3142123 * 2
def baseEnd_3142123 : Nat := 537806458182438387670715

theorem tailTrace_3142123 : CollatzResearch.WordTrace tailWord_3142123 prefixEnd_3142123 537806458182438387670715 := by
  unfold tailWord_3142123
  simp only [CollatzResearch.WordTrace]
  refine ⟨114602640795632477730063023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76401760530421651820042015 114602640795632477730063023)
  ·
    refine ⟨171903961193448716595094535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114602640795632477730063023 171903961193448716595094535)
    ·
      refine ⟨257855941790173074892641803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171903961193448716595094535 257855941790173074892641803)
      ·
        refine ⟨386783912685259612338962705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257855941790173074892641803 386783912685259612338962705)
        ·
          refine ⟨290087934513944709254222029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386783912685259612338962705 290087934513944709254222029)
          ·
            refine ⟨108782975442729265970333261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290087934513944709254222029 108782975442729265970333261)
            ·
              refine ⟨40793615791023474738874973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108782975442729265970333261 40793615791023474738874973)
              ·
                refine ⟨15297605921633803027078115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40793615791023474738874973 15297605921633803027078115)
                ·
                  refine ⟨22946408882450704540617173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15297605921633803027078115 22946408882450704540617173)
                  ·
                    refine ⟨537806458182438387670715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22946408882450704540617173 537806458182438387670715)
                    ·
                      rfl

theorem cell23_3142123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 7].length) (baseStart_3142123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142123 prefixEnd_3142123 := by exact prefixLift 3142123
  have htrace : WordTrace (prefixWord ++ tailWord_3142123) baseStart_3142123 baseEnd_3142123 := by
    simpa [prefixWord, tailWord_3142123, baseEnd_3142123] using wordTrace_append hprefix tailTrace_3142123
  have hstable : (prefixWord ++ tailWord_3142123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142123).length < 2 ^ (prefixWord ++ tailWord_3142123).sum := by decide
  have hdescent : baseEnd_3142123 < baseStart_3142123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142153 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 2, 8]
def baseStart_3142153 : Nat := 118140960795 + 3142153 * 2 ^ 59
def prefixEnd_3142153 : Nat := 4983230072969 + 3 ^ 40 * 3142153 * 2
def baseEnd_3142153 : Nat := 537811592988983348545669

theorem tailTrace_3142153 : CollatzResearch.WordTrace tailWord_3142153 prefixEnd_3142153 537811592988983348545669 := by
  unfold tailWord_3142153
  simp only [CollatzResearch.WordTrace]
  refine ⟨114603734985523792853655113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76402489990349195235770075 114603734985523792853655113)
  ·
    refine ⟨85952801239142844640241335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114603734985523792853655113 85952801239142844640241335)
    ·
      refine ⟨128929201858714266960362003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85952801239142844640241335 128929201858714266960362003)
      ·
        refine ⟨193393802788071400440543005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128929201858714266960362003 193393802788071400440543005)
        ·
          refine ⟨72522676045526775165203627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193393802788071400440543005 72522676045526775165203627)
          ·
            refine ⟨108784014068290162747805441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72522676045526775165203627 108784014068290162747805441)
            ·
              refine ⟨81588010551217622060854081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108784014068290162747805441 81588010551217622060854081)
              ·
                refine ⟨61191007913413216545640561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81588010551217622060854081 61191007913413216545640561)
                ·
                  refine ⟨45893255935059912409230421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61191007913413216545640561 45893255935059912409230421)
                  ·
                    refine ⟨537811592988983348545669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45893255935059912409230421 537811592988983348545669)
                    ·
                      rfl

theorem cell23_3142153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_3142153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142153 prefixEnd_3142153 := by exact prefixLift 3142153
  have htrace : WordTrace (prefixWord ++ tailWord_3142153) baseStart_3142153 baseEnd_3142153 := by
    simpa [prefixWord, tailWord_3142153, baseEnd_3142153] using wordTrace_append hprefix tailTrace_3142153
  have hstable : (prefixWord ++ tailWord_3142153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142153).length < 2 ^ (prefixWord ++ tailWord_3142153).sum := by decide
  have hdescent : baseEnd_3142153 < baseStart_3142153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142177 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3142177 : Nat := 118140960795 + 3142177 * 2 ^ 59
def prefixEnd_3142177 : Nat := 4983230072969 + 3 ^ 40 * 3142177 * 2
def baseEnd_3142177 : Nat := 1613447102502657951736897

theorem tailTrace_3142177 : CollatzResearch.WordTrace tailWord_3142177 prefixEnd_3142177 1613447102502657951736897 := by
  unfold tailWord_3142177
  simp only [CollatzResearch.WordTrace]
  refine ⟨114604610337436844952528785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76403073558291229968352523 114604610337436844952528785)
  ·
    refine ⟨85953457753077633714396589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114604610337436844952528785 85953457753077633714396589)
    ·
      refine ⟨32232546657404112642898721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85953457753077633714396589 32232546657404112642898721)
      ·
        refine ⟨24174409993053084482174041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32232546657404112642898721 24174409993053084482174041)
        ·
          refine ⟨18130807494789813361630531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24174409993053084482174041 18130807494789813361630531)
          ·
            refine ⟨27196211242184720042445797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18130807494789813361630531 27196211242184720042445797)
            ·
              refine ⟨5099289607909635007958587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27196211242184720042445797 5099289607909635007958587)
              ·
                refine ⟨7648934411864452511937881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099289607909635007958587 7648934411864452511937881)
                ·
                  refine ⟨5736700808898339383953411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7648934411864452511937881 5736700808898339383953411)
                  ·
                    refine ⟨8605051213347509075930117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736700808898339383953411 8605051213347509075930117)
                    ·
                      refine ⟨1613447102502657951736897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8605051213347509075930117 1613447102502657951736897)
                      ·
                        rfl

theorem cell23_3142177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3142177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142177 prefixEnd_3142177 := by exact prefixLift 3142177
  have htrace : WordTrace (prefixWord ++ tailWord_3142177) baseStart_3142177 baseEnd_3142177 := by
    simpa [prefixWord, tailWord_3142177, baseEnd_3142177] using wordTrace_append hprefix tailTrace_3142177
  have hstable : (prefixWord ++ tailWord_3142177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142177).length < 2 ^ (prefixWord ++ tailWord_3142177).sum := by decide
  have hdescent : baseEnd_3142177 < baseStart_3142177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142197 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_3142197 : Nat := 118140960795 + 3142197 * 2 ^ 59
def prefixEnd_3142197 : Nat := 4983230072969 + 3 ^ 40 * 3142197 * 2
def baseEnd_3142197 : Nat := 1613457372115747873486805

theorem tailTrace_3142197 : CollatzResearch.WordTrace tailWord_3142197 prefixEnd_3142197 1613457372115747873486805 := by
  unfold tailWord_3142197
  simp only [CollatzResearch.WordTrace]
  refine ⟨114605339797364388368256845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76403559864909592245504563 114605339797364388368256845)
  ·
    refine ⟨42977002424011645638096317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114605339797364388368256845 42977002424011645638096317)
    ·
      refine ⟨16116375909004367114286119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42977002424011645638096317 16116375909004367114286119)
      ·
        refine ⟨24174563863506550671429179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16116375909004367114286119 24174563863506550671429179)
        ·
          refine ⟨36261845795259826007143769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24174563863506550671429179 36261845795259826007143769)
          ·
            refine ⟨27196384346444869505357827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36261845795259826007143769 27196384346444869505357827)
            ·
              refine ⟨40794576519667304258036741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27196384346444869505357827 40794576519667304258036741)
              ·
                refine ⟨7648983097437619548381889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40794576519667304258036741 7648983097437619548381889)
                ·
                  refine ⟨5736737323078214661286417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7648983097437619548381889 5736737323078214661286417)
                  ·
                    refine ⟨4302552992308660995964813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5736737323078214661286417 4302552992308660995964813)
                    ·
                      refine ⟨1613457372115747873486805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302552992308660995964813 1613457372115747873486805)
                      ·
                        rfl

theorem cell23_3142197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_3142197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142197 prefixEnd_3142197 := by exact prefixLift 3142197
  have htrace : WordTrace (prefixWord ++ tailWord_3142197) baseStart_3142197 baseEnd_3142197 := by
    simpa [prefixWord, tailWord_3142197, baseEnd_3142197] using wordTrace_append hprefix tailTrace_3142197
  have hstable : (prefixWord ++ tailWord_3142197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142197).length < 2 ^ (prefixWord ++ tailWord_3142197).sum := by decide
  have hdescent : baseEnd_3142197 < baseStart_3142197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142277 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_3142277 : Nat := 118140960795 + 3142277 * 2 ^ 59
def prefixEnd_3142277 : Nat := 4983230072969 + 3 ^ 40 * 3142277 * 2
def baseEnd_3142277 : Nat := 537832816856035853495479

theorem tailTrace_3142277 : CollatzResearch.WordTrace tailWord_3142277 prefixEnd_3142277 537832816856035853495479 := by
  unfold tailWord_3142277
  simp only [CollatzResearch.WordTrace]
  refine ⟨114608257637074562031169085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76405505091383041354112723 114608257637074562031169085)
  ·
    refine ⟨42978096613902960761688407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114608257637074562031169085 42978096613902960761688407)
    ·
      refine ⟨64467144920854441142532611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42978096613902960761688407 64467144920854441142532611)
      ·
        refine ⟨96700717381281661713798917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64467144920854441142532611 96700717381281661713798917)
        ·
          refine ⟨18131384508990311571337297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96700717381281661713798917 18131384508990311571337297)
          ·
            refine ⟨13598538381742733678502973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18131384508990311571337297 13598538381742733678502973)
            ·
              refine ⟨5099451893153525129438615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13598538381742733678502973 5099451893153525129438615)
              ·
                refine ⟨7649177839730287694157923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099451893153525129438615 7649177839730287694157923)
                ·
                  refine ⟨11473766759595431541236885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7649177839730287694157923 11473766759595431541236885)
                  ·
                    refine ⟨537832816856035853495479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11473766759595431541236885 537832816856035853495479)
                    ·
                      rfl

theorem cell23_3142277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_3142277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142277 prefixEnd_3142277 := by exact prefixLift 3142277
  have htrace : WordTrace (prefixWord ++ tailWord_3142277) baseStart_3142277 baseEnd_3142277 := by
    simpa [prefixWord, tailWord_3142277, baseEnd_3142277] using wordTrace_append hprefix tailTrace_3142277
  have hstable : (prefixWord ++ tailWord_3142277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142277).length < 2 ^ (prefixWord ++ tailWord_3142277).sum := by decide
  have hdescent : baseEnd_3142277 < baseStart_3142277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142284 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 5, 2, 2]
def baseStart_3142284 : Nat := 118140960795 + 3142284 * 2 ^ 59
def prefixEnd_3142284 : Nat := 4983230072969 + 3 ^ 40 * 3142284 * 2
def baseEnd_3142284 : Nat := 1613502044932689033098905

theorem tailTrace_3142284 : CollatzResearch.WordTrace tailWord_3142284 prefixEnd_3142284 1613502044932689033098905 := by
  unfold tailWord_3142284
  simp only [CollatzResearch.WordTrace]
  refine ⟨57304256474024601113336953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76405675298699468151115937 57304256474024601113336953)
  ·
    refine ⟨42978192355518450835002715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57304256474024601113336953 42978192355518450835002715)
    ·
      refine ⟨64467288533277676252504073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42978192355518450835002715 64467288533277676252504073)
      ·
        refine ⟨48350466399958257189378055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64467288533277676252504073 48350466399958257189378055)
        ·
          refine ⟨72525699599937385784067083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48350466399958257189378055 72525699599937385784067083)
          ·
            refine ⟨108788549399906078676100625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72525699599937385784067083 108788549399906078676100625)
            ·
              refine ⟨81591412049929559007075469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108788549399906078676100625 81591412049929559007075469)
              ·
                refine ⟨30596779518723584627653301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81591412049929559007075469 30596779518723584627653301)
                ·
                  refine ⟨2868448079880336058842497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30596779518723584627653301 2868448079880336058842497)
                  ·
                    refine ⟨2151336059910252044131873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2868448079880336058842497 2151336059910252044131873)
                    ·
                      refine ⟨1613502044932689033098905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151336059910252044131873 1613502044932689033098905)
                      ·
                        rfl

theorem cell23_3142284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_3142284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142284 prefixEnd_3142284 := by exact prefixLift 3142284
  have htrace : WordTrace (prefixWord ++ tailWord_3142284) baseStart_3142284 baseEnd_3142284 := by
    simpa [prefixWord, tailWord_3142284, baseEnd_3142284] using wordTrace_append hprefix tailTrace_3142284
  have hstable : (prefixWord ++ tailWord_3142284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142284).length < 2 ^ (prefixWord ++ tailWord_3142284).sum := by decide
  have hdescent : baseEnd_3142284 < baseStart_3142284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142304 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3142304 : Nat := 118140960795 + 3142304 * 2 ^ 59
def prefixEnd_3142304 : Nat := 4983230072969 + 3 ^ 40 * 3142304 * 2
def baseEnd_3142304 : Nat := 1613512314545778954848813

theorem tailTrace_3142304 : CollatzResearch.WordTrace tailWord_3142304 prefixEnd_3142304 1613512314545778954848813 := by
  unfold tailWord_3142304
  simp only [CollatzResearch.WordTrace]
  refine ⟨57304621203988372821200983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76406161605317830428267977 57304621203988372821200983)
  ·
    refine ⟨85956931805982559231801475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57304621203988372821200983 85956931805982559231801475)
    ·
      refine ⟨128935397708973838847702213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85956931805982559231801475 128935397708973838847702213)
      ·
        refine ⟨24175387070432594783944165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128935397708973838847702213 24175387070432594783944165)
        ·
          refine ⟨4532885075706111521989531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24175387070432594783944165 4532885075706111521989531)
          ·
            refine ⟨6799327613559167282984297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532885075706111521989531 6799327613559167282984297)
            ·
              refine ⟨5099495710169375462238223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799327613559167282984297 5099495710169375462238223)
              ·
                refine ⟨7649243565254063193357335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099495710169375462238223 7649243565254063193357335)
                ·
                  refine ⟨11473865347881094790036003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7649243565254063193357335 11473865347881094790036003)
                  ·
                    refine ⟨17210798021821642185054005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11473865347881094790036003 17210798021821642185054005)
                    ·
                      refine ⟨1613512314545778954848813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17210798021821642185054005 1613512314545778954848813)
                      ·
                        rfl

theorem cell23_3142304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3142304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142304 prefixEnd_3142304 := by exact prefixLift 3142304
  have htrace : WordTrace (prefixWord ++ tailWord_3142304) baseStart_3142304 baseEnd_3142304 := by
    simpa [prefixWord, tailWord_3142304, baseEnd_3142304] using wordTrace_append hprefix tailTrace_3142304
  have hstable : (prefixWord ++ tailWord_3142304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142304).length < 2 ^ (prefixWord ++ tailWord_3142304).sum := by decide
  have hdescent : baseEnd_3142304 < baseStart_3142304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142320 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 2, 7]
def baseStart_3142320 : Nat := 118140960795 + 3142320 * 2 ^ 59
def prefixEnd_3142320 : Nat := 4983230072969 + 3 ^ 40 * 3142320 * 2
def baseEnd_3142320 : Nat := 537840176745416964082913

theorem tailTrace_3142320 : CollatzResearch.WordTrace tailWord_3142320 prefixEnd_3142320 537840176745416964082913 := by
  unfold tailWord_3142320
  simp only [CollatzResearch.WordTrace]
  refine ⟨57304912987959390187492207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76406550650612520249989609 57304912987959390187492207)
  ·
    refine ⟨85957369481939085281238311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57304912987959390187492207 85957369481939085281238311)
    ·
      refine ⟨128936054222908627921857467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85957369481939085281238311 128936054222908627921857467)
      ·
        refine ⟨193404081334362941882786201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128936054222908627921857467 193404081334362941882786201)
        ·
          refine ⟨145053061000772206412089651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193404081334362941882786201 145053061000772206412089651)
          ·
            refine ⟨217579591501158309618134477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145053061000772206412089651 217579591501158309618134477)
            ·
              refine ⟨81592346812934366106800429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217579591501158309618134477 81592346812934366106800429)
              ·
                refine ⟨30597130054850387290050161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81592346812934366106800429 30597130054850387290050161)
                ·
                  refine ⟨22947847541137790467537621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30597130054850387290050161 22947847541137790467537621)
                  ·
                    refine ⟨537840176745416964082913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22947847541137790467537621 537840176745416964082913)
                    ·
                      rfl

theorem cell23_3142320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_3142320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142320 prefixEnd_3142320 := by exact prefixLift 3142320
  have htrace : WordTrace (prefixWord ++ tailWord_3142320) baseStart_3142320 baseEnd_3142320 := by
    simpa [prefixWord, tailWord_3142320, baseEnd_3142320] using wordTrace_append hprefix tailTrace_3142320
  have hstable : (prefixWord ++ tailWord_3142320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142320).length < 2 ^ (prefixWord ++ tailWord_3142320).sum := by decide
  have hdescent : baseEnd_3142320 < baseStart_3142320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142334 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3142334 : Nat := 118140960795 + 3142334 * 2 ^ 59
def prefixEnd_3142334 : Nat := 4983230072969 + 3 ^ 40 * 3142334 * 2
def baseEnd_3142334 : Nat := 1613527718965413837473675

theorem tailTrace_3142334 : CollatzResearch.WordTrace tailWord_3142334 prefixEnd_3142334 1613527718965413837473675 := by
  unfold tailWord_3142334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14326292074733507595749257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76406891065245373843996037 14326292074733507595749257)
  ·
    refine ⟨10744719056050130696811943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14326292074733507595749257 10744719056050130696811943)
    ·
      refine ⟨16117078584075196045217915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10744719056050130696811943 16117078584075196045217915)
      ·
        refine ⟨24175617876112794067826873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16117078584075196045217915 24175617876112794067826873)
        ·
          refine ⟨18131713407084595550870155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24175617876112794067826873 18131713407084595550870155)
          ·
            refine ⟨27197570110626893326305233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18131713407084595550870155 27197570110626893326305233)
            ·
              refine ⟨20398177582970169994728925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27197570110626893326305233 20398177582970169994728925)
              ·
                refine ⟨7649316593613813748023347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20398177582970169994728925 7649316593613813748023347)
                ·
                  refine ⟨11473974890420720622035021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7649316593613813748023347 11473974890420720622035021)
                  ·
                    refine ⟨4302740583907770233263133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11473974890420720622035021 4302740583907770233263133)
                    ·
                      refine ⟨1613527718965413837473675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302740583907770233263133 1613527718965413837473675)
                      ·
                        rfl

theorem cell23_3142334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3142334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142334 prefixEnd_3142334 := by exact prefixLift 3142334
  have htrace : WordTrace (prefixWord ++ tailWord_3142334) baseStart_3142334 baseEnd_3142334 := by
    simpa [prefixWord, tailWord_3142334, baseEnd_3142334] using wordTrace_append hprefix tailTrace_3142334
  have hstable : (prefixWord ++ tailWord_3142334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142334).length < 2 ^ (prefixWord ++ tailWord_3142334).sum := by decide
  have hdescent : baseEnd_3142334 < baseStart_3142334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142377 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 3]
def baseStart_3142377 : Nat := 118140960795 + 3142377 * 2 ^ 59
def prefixEnd_3142377 : Nat := 4983230072969 + 3 ^ 40 * 3142377 * 2
def baseEnd_3142377 : Nat := 1613549798633557169235977

theorem tailTrace_3142377 : CollatzResearch.WordTrace tailWord_3142377 prefixEnd_3142377 1613549798633557169235977 := by
  unfold tailWord_3142377
  simp only [CollatzResearch.WordTrace]
  refine ⟨114611904936712279109809385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76407936624474852739872923 114611904936712279109809385)
  ·
    refine ⟨85958928702534209332357039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114611904936712279109809385 85958928702534209332357039)
    ·
      refine ⟨128938393053801313998535559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85958928702534209332357039 128938393053801313998535559)
      ·
        refine ⟨193407589580701970997803339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128938393053801313998535559 193407589580701970997803339)
        ·
          refine ⟨290111384371052956496705009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193407589580701970997803339 290111384371052956496705009)
          ·
            refine ⟨217583538278289717372528757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290111384371052956496705009 217583538278289717372528757)
            ·
              refine ⟨20398456713589661003674571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217583538278289717372528757 20398456713589661003674571)
              ·
                refine ⟨30597685070384491505511857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20398456713589661003674571 30597685070384491505511857)
                ·
                  refine ⟨22948263802788368629133893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30597685070384491505511857 22948263802788368629133893)
                  ·
                    refine ⟨4302799463022819117962605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22948263802788368629133893 4302799463022819117962605)
                    ·
                      refine ⟨1613549798633557169235977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302799463022819117962605 1613549798633557169235977)
                      ·
                        rfl

theorem cell23_3142377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_3142377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142377 prefixEnd_3142377 := by exact prefixLift 3142377
  have htrace : WordTrace (prefixWord ++ tailWord_3142377) baseStart_3142377 baseEnd_3142377 := by
    simpa [prefixWord, tailWord_3142377, baseEnd_3142377] using wordTrace_append hprefix tailTrace_3142377
  have hstable : (prefixWord ++ tailWord_3142377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142377).length < 2 ^ (prefixWord ++ tailWord_3142377).sum := by decide
  have hdescent : baseEnd_3142377 < baseStart_3142377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142397 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 7]
def baseStart_3142397 : Nat := 118140960795 + 3142397 * 2 ^ 59
def prefixEnd_3142397 : Nat := 4983230072969 + 3 ^ 40 * 3142397 * 2
def baseEnd_3142397 : Nat := 179284452027405232331765

theorem tailTrace_3142397 : CollatzResearch.WordTrace tailWord_3142397 prefixEnd_3142397 179284452027405232331765 := by
  unfold tailWord_3142397
  simp only [CollatzResearch.WordTrace]
  refine ⟨114612634396639822525537445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76408422931093215017024963 114612634396639822525537445)
  ·
    refine ⟨21489868949369966723538271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114612634396639822525537445 21489868949369966723538271)
    ·
      refine ⟨32234803424054950085307407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21489868949369966723538271 32234803424054950085307407)
      ·
        refine ⟨48352205136082425127961111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32234803424054950085307407 48352205136082425127961111)
        ·
          refine ⟨72528307704123637691941667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48352205136082425127961111 72528307704123637691941667)
          ·
            refine ⟨108792461556185456537912501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72528307704123637691941667 108792461556185456537912501)
            ·
              refine ⟨10199293270892386550429297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108792461556185456537912501 10199293270892386550429297)
              ·
                refine ⟨7649469953169289912821973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10199293270892386550429297 7649469953169289912821973)
                ·
                  refine ⟨179284452027405232331765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7649469953169289912821973 179284452027405232331765)
                  ·
                    rfl

theorem cell23_3142397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_3142397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142397 prefixEnd_3142397 := by exact prefixLift 3142397
  have htrace : WordTrace (prefixWord ++ tailWord_3142397) baseStart_3142397 baseEnd_3142397 := by
    simpa [prefixWord, tailWord_3142397, baseEnd_3142397] using wordTrace_append hprefix tailTrace_3142397
  have hstable : (prefixWord ++ tailWord_3142397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142397).length < 2 ^ (prefixWord ++ tailWord_3142397).sum := by decide
  have hdescent : baseEnd_3142397 < baseStart_3142397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142437 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_3142437 : Nat := 118140960795 + 3142437 * 2 ^ 59
def prefixEnd_3142437 : Nat := 4983230072969 + 3 ^ 40 * 3142437 * 2
def baseEnd_3142437 : Nat := 1613580607472826934485701

theorem tailTrace_3142437 : CollatzResearch.WordTrace tailWord_3142437 prefixEnd_3142437 1613580607472826934485701 := by
  unfold tailWord_3142437
  simp only [CollatzResearch.WordTrace]
  refine ⟨114614093316494909356993565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76409395544329939571329043 114614093316494909356993565)
  ·
    refine ⟨42980284993685591008872587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114614093316494909356993565 42980284993685591008872587)
    ·
      refine ⟨64470427490528386513308881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42980284993685591008872587 64470427490528386513308881)
      ·
        refine ⟨48352820617896289884981661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64470427490528386513308881 48352820617896289884981661)
        ·
          refine ⟨18132307731711108706868123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48352820617896289884981661 18132307731711108706868123)
          ·
            refine ⟨27198461597566663060302185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18132307731711108706868123 27198461597566663060302185)
            ·
              refine ⟨20398846198174997295226639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27198461597566663060302185 20398846198174997295226639)
              ·
                refine ⟨30598269297262495942839959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20398846198174997295226639 30598269297262495942839959)
                ·
                  refine ⟨45897403945893743914259939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30598269297262495942839959 45897403945893743914259939)
                  ·
                    refine ⟨68846105918840615871389909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45897403945893743914259939 68846105918840615871389909)
                    ·
                      refine ⟨1613580607472826934485701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68846105918840615871389909 1613580607472826934485701)
                      ·
                        rfl

theorem cell23_3142437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_3142437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142437 prefixEnd_3142437 := by exact prefixLift 3142437
  have htrace : WordTrace (prefixWord ++ tailWord_3142437) baseStart_3142437 baseEnd_3142437 := by
    simpa [prefixWord, tailWord_3142437, baseEnd_3142437] using wordTrace_append hprefix tailTrace_3142437
  have hstable : (prefixWord ++ tailWord_3142437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142437).length < 2 ^ (prefixWord ++ tailWord_3142437).sum := by decide
  have hdescent : baseEnd_3142437 < baseStart_3142437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142442 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3142442 : Nat := 118140960795 + 3142442 * 2 ^ 59
def prefixEnd_3142442 : Nat := 4983230072969 + 3 ^ 40 * 3142442 * 2
def baseEnd_3142442 : Nat := 1613583174876099414923179

theorem tailTrace_3142442 : CollatzResearch.WordTrace tailWord_3142442 prefixEnd_3142442 1613583174876099414923179 := by
  unfold tailWord_3142442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28653568920369198802731395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76409517120984530140617053 28653568920369198802731395)
  ·
    refine ⟨42980353380553798204097093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28653568920369198802731395 42980353380553798204097093)
    ·
      refine ⟨8058816258853837163268205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42980353380553798204097093 8058816258853837163268205)
      ·
        refine ⟨3022056097070188936225577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8058816258853837163268205 3022056097070188936225577)
        ·
          refine ⟨2266542072802641702169183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3022056097070188936225577 2266542072802641702169183)
          ·
            refine ⟨3399813109203962553253775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266542072802641702169183 3399813109203962553253775)
            ·
              refine ⟨5099719663805943829880663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399813109203962553253775 5099719663805943829880663)
              ·
                refine ⟨7649579495708915744820995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099719663805943829880663 7649579495708915744820995)
                ·
                  refine ⟨11474369243563373617231493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7649579495708915744820995 11474369243563373617231493)
                  ·
                    refine ⟨2151444233168132553230905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11474369243563373617231493 2151444233168132553230905)
                    ·
                      refine ⟨1613583174876099414923179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151444233168132553230905 1613583174876099414923179)
                      ·
                        rfl

theorem cell23_3142442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3142442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142442 prefixEnd_3142442 := by exact prefixLift 3142442
  have htrace : WordTrace (prefixWord ++ tailWord_3142442) baseStart_3142442 baseEnd_3142442 := by
    simpa [prefixWord, tailWord_3142442, baseEnd_3142442] using wordTrace_append hprefix tailTrace_3142442
  have hstable : (prefixWord ++ tailWord_3142442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142442).length < 2 ^ (prefixWord ++ tailWord_3142442).sum := by decide
  have hdescent : baseEnd_3142442 < baseStart_3142442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142464 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 1, 6, 2]
def baseStart_3142464 : Nat := 118140960795 + 3142464 * 2 ^ 59
def prefixEnd_3142464 : Nat := 4983230072969 + 3 ^ 40 * 3142464 * 2
def baseEnd_3142464 : Nat := 1613594471450498328848077

theorem tailTrace_3142464 : CollatzResearch.WordTrace tailWord_3142464 prefixEnd_3142464 1613594471450498328848077 := by
  unfold tailWord_3142464
  simp only [CollatzResearch.WordTrace]
  refine ⟨57307539043698546484113223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76410052058264728645484297 57307539043698546484113223)
  ·
    refine ⟨85961308565547819726169835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57307539043698546484113223 85961308565547819726169835)
    ·
      refine ⟨128941962848321729589254753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85961308565547819726169835 128941962848321729589254753)
      ·
        refine ⟨96706472136241297191941065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128941962848321729589254753 96706472136241297191941065)
        ·
          refine ⟨72529854102180972893955799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96706472136241297191941065 72529854102180972893955799)
          ·
            refine ⟨108794781153271459340933699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72529854102180972893955799 108794781153271459340933699)
            ·
              refine ⟨163192171729907189011400549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108794781153271459340933699 163192171729907189011400549)
              ·
                refine ⟨30598532199357597939637603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163192171729907189011400549 30598532199357597939637603)
                ·
                  refine ⟨45897798299036396909456405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30598532199357597939637603 45897798299036396909456405)
                  ·
                    refine ⟨2151459295267331105130769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45897798299036396909456405 2151459295267331105130769)
                    ·
                      refine ⟨1613594471450498328848077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151459295267331105130769 1613594471450498328848077)
                      ·
                        rfl

theorem cell23_3142464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_3142464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142464 prefixEnd_3142464 := by exact prefixLift 3142464
  have htrace : WordTrace (prefixWord ++ tailWord_3142464) baseStart_3142464 baseEnd_3142464 := by
    simpa [prefixWord, tailWord_3142464, baseEnd_3142464] using wordTrace_append hprefix tailTrace_3142464
  have hstable : (prefixWord ++ tailWord_3142464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142464).length < 2 ^ (prefixWord ++ tailWord_3142464).sum := by decide
  have hdescent : baseEnd_3142464 < baseStart_3142464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142465 : List Nat := [1, 2, 5, 3, 1, 2, 1, 3, 5]
def baseStart_3142465 : Nat := 118140960795 + 3142465 * 2 ^ 59
def prefixEnd_3142465 : Nat := 4983230072969 + 3 ^ 40 * 3142465 * 2
def baseEnd_3142465 : Nat := 179288331659016980548397

theorem tailTrace_3142465 : CollatzResearch.WordTrace tailWord_3142465 prefixEnd_3142465 179288331659016980548397 := by
  unfold tailWord_3142465
  simp only [CollatzResearch.WordTrace]
  refine ⟨114615114560393470139012849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76410076373595646759341899 114615114560393470139012849)
  ·
    refine ⟨85961335920295102604259637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114615114560393470139012849 85961335920295102604259637)
    ·
      refine ⟨8058875242527665869149341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85961335920295102604259637 8058875242527665869149341)
      ·
        refine ⟨3022078215947874700931003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8058875242527665869149341 3022078215947874700931003)
        ·
          refine ⟨4533117323921812051396505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022078215947874700931003 4533117323921812051396505)
          ·
            refine ⟨3399837992941359038547379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4533117323921812051396505 3399837992941359038547379)
            ·
              refine ⟨5099756989412038557821069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399837992941359038547379 5099756989412038557821069)
              ·
                refine ⟨1912408871029514459182901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5099756989412038557821069 1912408871029514459182901)
                ·
                  refine ⟨179288331659016980548397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1912408871029514459182901 179288331659016980548397)
                  ·
                    rfl

theorem cell23_3142465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 5].length) (baseStart_3142465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142465 prefixEnd_3142465 := by exact prefixLift 3142465
  have htrace : WordTrace (prefixWord ++ tailWord_3142465) baseStart_3142465 baseEnd_3142465 := by
    simpa [prefixWord, tailWord_3142465, baseEnd_3142465] using wordTrace_append hprefix tailTrace_3142465
  have hstable : (prefixWord ++ tailWord_3142465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142465).length < 2 ^ (prefixWord ++ tailWord_3142465).sum := by decide
  have hdescent : baseEnd_3142465 < baseStart_3142465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142481 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_3142481 : Nat := 118140960795 + 3142481 * 2 ^ 59
def prefixEnd_3142481 : Nat := 4983230072969 + 3 ^ 40 * 3142481 * 2
def baseEnd_3142481 : Nat := 1613603200621624762335499

theorem tailTrace_3142481 : CollatzResearch.WordTrace tailWord_3142481 prefixEnd_3142481 1613603200621624762335499 := by
  unfold tailWord_3142481
  simp only [CollatzResearch.WordTrace]
  refine ⟨114615698128335504871595297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76410465418890336581063531 114615698128335504871595297)
  ·
    refine ⟨85961773596251628653696473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114615698128335504871595297 85961773596251628653696473)
    ·
      refine ⟨64471330197188721490272355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85961773596251628653696473 64471330197188721490272355)
      ·
        refine ⟨96706995295783082235408533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64471330197188721490272355 96706995295783082235408533)
        ·
          refine ⟨4533140404489831979784775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96706995295783082235408533 4533140404489831979784775)
          ·
            refine ⟨6799710606734747969677163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533140404489831979784775 6799710606734747969677163)
            ·
              refine ⟨10199565910102121954515745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799710606734747969677163 10199565910102121954515745)
              ·
                refine ⟨7649674432576591465886809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10199565910102121954515745 7649674432576591465886809)
                ·
                  refine ⟨5737255824432443599415107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7649674432576591465886809 5737255824432443599415107)
                  ·
                    refine ⟨8605883736648665399122661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5737255824432443599415107 8605883736648665399122661)
                    ·
                      refine ⟨1613603200621624762335499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8605883736648665399122661 1613603200621624762335499)
                      ·
                        rfl

theorem cell23_3142481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_3142481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142481 prefixEnd_3142481 := by exact prefixLift 3142481
  have htrace : WordTrace (prefixWord ++ tailWord_3142481) baseStart_3142481 baseEnd_3142481 := by
    simpa [prefixWord, tailWord_3142481, baseEnd_3142481] using wordTrace_append hprefix tailTrace_3142481
  have hstable : (prefixWord ++ tailWord_3142481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142481).length < 2 ^ (prefixWord ++ tailWord_3142481).sum := by decide
  have hdescent : baseEnd_3142481 < baseStart_3142481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142507 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6]
def baseStart_3142507 : Nat := 118140960795 + 3142507 * 2 ^ 59
def prefixEnd_3142507 : Nat := 4983230072969 + 3 ^ 40 * 3142507 * 2
def baseEnd_3142507 : Nat := 1613616551118641660610379

theorem tailTrace_3142507 : CollatzResearch.WordTrace tailWord_3142507 prefixEnd_3142507 1613616551118641660610379 := by
  unfold tailWord_3142507
  simp only [CollatzResearch.WordTrace]
  refine ⟨114616646426241311312041775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76411097617494207541361183 114616646426241311312041775)
  ·
    refine ⟨171924969639361966968062663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114616646426241311312041775 171924969639361966968062663)
    ·
      refine ⟨257887454459042950452093995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171924969639361966968062663 257887454459042950452093995)
      ·
        refine ⟨386831181688564425678140993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257887454459042950452093995 386831181688564425678140993)
        ·
          refine ⟨290123386266423319258605745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386831181688564425678140993 290123386266423319258605745)
          ·
            refine ⟨217592539699817489443954309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290123386266423319258605745 217592539699817489443954309)
            ·
              refine ⟨40798601193715779270741433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217592539699817489443954309 40798601193715779270741433)
              ·
                refine ⟨30598950895286834453056075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40798601193715779270741433 30598950895286834453056075)
                ·
                  refine ⟨45898426342930251679584113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30598950895286834453056075 45898426342930251679584113)
                  ·
                    refine ⟨34423819757197688759688085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45898426342930251679584113 34423819757197688759688085)
                    ·
                      refine ⟨1613616551118641660610379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34423819757197688759688085 1613616551118641660610379)
                      ·
                        rfl

theorem cell23_3142507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_3142507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142507 prefixEnd_3142507 := by exact prefixLift 3142507
  have htrace : WordTrace (prefixWord ++ tailWord_3142507) baseStart_3142507 baseEnd_3142507 := by
    simpa [prefixWord, tailWord_3142507, baseEnd_3142507] using wordTrace_append hprefix tailTrace_3142507
  have hstable : (prefixWord ++ tailWord_3142507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142507).length < 2 ^ (prefixWord ++ tailWord_3142507).sum := by decide
  have hdescent : baseEnd_3142507 < baseStart_3142507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142514 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3142514 : Nat := 118140960795 + 3142514 * 2 ^ 59
def prefixEnd_3142514 : Nat := 4983230072969 + 3 ^ 40 * 3142514 * 2
def baseEnd_3142514 : Nat := 1613620145483223133222847

theorem tailTrace_3142514 : CollatzResearch.WordTrace tailWord_3142514 prefixEnd_3142514 1613620145483223133222847 := by
  unfold tailWord_3142514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28654225434303987876886649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76411267824810634338364397 28654225434303987876886649)
  ·
    refine ⟨21490669075727990907664987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28654225434303987876886649 21490669075727990907664987)
    ·
      refine ⟨32236003613591986361497481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21490669075727990907664987 32236003613591986361497481)
      ·
        refine ⟨24177002710193989771123111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32236003613591986361497481 24177002710193989771123111)
        ·
          refine ⟨36265504065290984656684667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24177002710193989771123111 36265504065290984656684667)
          ·
            refine ⟨54398256097936476985027001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36265504065290984656684667 54398256097936476985027001)
            ·
              refine ⟨40798692073452357738770251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54398256097936476985027001 40798692073452357738770251)
              ·
                refine ⟨61198038110178536608155377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40798692073452357738770251 61198038110178536608155377)
                ·
                  refine ⟨45898528582633902456116533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61198038110178536608155377 45898528582633902456116533)
                  ·
                    refine ⟨4302987054621928355260925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45898528582633902456116533 4302987054621928355260925)
                    ·
                      refine ⟨1613620145483223133222847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302987054621928355260925 1613620145483223133222847)
                      ·
                        rfl

theorem cell23_3142514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3142514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142514 prefixEnd_3142514 := by exact prefixLift 3142514
  have htrace : WordTrace (prefixWord ++ tailWord_3142514) baseStart_3142514 baseEnd_3142514 := by
    simpa [prefixWord, tailWord_3142514, baseEnd_3142514] using wordTrace_append hprefix tailTrace_3142514
  have hstable : (prefixWord ++ tailWord_3142514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142514).length < 2 ^ (prefixWord ++ tailWord_3142514).sum := by decide
  have hdescent : baseEnd_3142514 < baseStart_3142514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142518 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3142518 : Nat := 118140960795 + 3142518 * 2 ^ 59
def prefixEnd_3142518 : Nat := 4983230072969 + 3 ^ 40 * 3142518 * 2
def baseEnd_3142518 : Nat := 1613622199405841117572829

theorem tailTrace_3142518 : CollatzResearch.WordTrace tailWord_3142518 prefixEnd_3142518 1613622199405841117572829 := by
  unfold tailWord_3142518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7163565476825091261918263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76411365086134306793794805 7163565476825091261918263)
  ·
    refine ⟨10745348215237636892877395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7163565476825091261918263 10745348215237636892877395)
    ·
      refine ⟨16118022322856455339316093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10745348215237636892877395 16118022322856455339316093)
      ·
        refine ⟨6044258371071170752243535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16118022322856455339316093 6044258371071170752243535)
        ·
          refine ⟨9066387556606756128365303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044258371071170752243535 9066387556606756128365303)
          ·
            refine ⟨13599581334910134192547955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066387556606756128365303 13599581334910134192547955)
            ·
              refine ⟨20399372002365201288821933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13599581334910134192547955 20399372002365201288821933)
              ·
                refine ⟨7649764500886950483308225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20399372002365201288821933 7649764500886950483308225)
                ·
                  refine ⟨5737323375665212862481169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7649764500886950483308225 5737323375665212862481169)
                  ·
                    refine ⟨4302992531748909646860877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5737323375665212862481169 4302992531748909646860877)
                    ·
                      refine ⟨1613622199405841117572829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4302992531748909646860877 1613622199405841117572829)
                      ·
                        rfl

theorem cell23_3142518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3142518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142518 prefixEnd_3142518 := by exact prefixLift 3142518
  have htrace : WordTrace (prefixWord ++ tailWord_3142518) baseStart_3142518 baseEnd_3142518 := by
    simpa [prefixWord, tailWord_3142518, baseEnd_3142518] using wordTrace_append hprefix tailTrace_3142518
  have hstable : (prefixWord ++ tailWord_3142518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142518).length < 2 ^ (prefixWord ++ tailWord_3142518).sum := by decide
  have hdescent : baseEnd_3142518 < baseStart_3142518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142548 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3142548 : Nat := 118140960795 + 3142548 * 2 ^ 59
def prefixEnd_3142548 : Nat := 4983230072969 + 3 ^ 40 * 3142548 * 2
def baseEnd_3142548 : Nat := 1613637603825476000197691

theorem tailTrace_3142548 : CollatzResearch.WordTrace tailWord_3142548 prefixEnd_3142548 1613637603825476000197691 := by
  unfold tailWord_3142548
  simp only [CollatzResearch.WordTrace]
  refine ⟨57309070909546387657142149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76412094546061850209522865 57309070909546387657142149)
  ·
    refine ⟨10745450795539947685714153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57309070909546387657142149 10745450795539947685714153)
    ·
      refine ⟨8059088096654960764285615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10745450795539947685714153 8059088096654960764285615)
      ·
        refine ⟨12088632144982441146428423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8059088096654960764285615 12088632144982441146428423)
        ·
          refine ⟨18132948217473661719642635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088632144982441146428423 18132948217473661719642635)
          ·
            refine ⟨27199422326210492579463953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18132948217473661719642635 27199422326210492579463953)
            ·
              refine ⟨20399566744657869434597965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27199422326210492579463953 20399566744657869434597965)
              ·
                refine ⟨7649837529246701037974237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20399566744657869434597965 7649837529246701037974237)
                ·
                  refine ⟨2868689073467512889240339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7649837529246701037974237 2868689073467512889240339)
                  ·
                    refine ⟨4303033610201269333860509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2868689073467512889240339 4303033610201269333860509)
                    ·
                      refine ⟨1613637603825476000197691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4303033610201269333860509 1613637603825476000197691)
                      ·
                        rfl

theorem cell23_3142548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3142548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142548 prefixEnd_3142548 := by exact prefixLift 3142548
  have htrace : WordTrace (prefixWord ++ tailWord_3142548) baseStart_3142548 baseEnd_3142548 := by
    simpa [prefixWord, tailWord_3142548, baseEnd_3142548] using wordTrace_append hprefix tailTrace_3142548
  have hstable : (prefixWord ++ tailWord_3142548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142548).length < 2 ^ (prefixWord ++ tailWord_3142548).sum := by decide
  have hdescent : baseEnd_3142548 < baseStart_3142548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142581 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3142581 : Nat := 118140960795 + 3142581 * 2 ^ 59
def prefixEnd_3142581 : Nat := 4983230072969 + 3 ^ 40 * 3142581 * 2
def baseEnd_3142581 : Nat := 537884849562358123695013

theorem tailTrace_3142581 : CollatzResearch.WordTrace tailWord_3142581 prefixEnd_3142581 537884849562358123695013 := by
  unfold tailWord_3142581
  simp only [CollatzResearch.WordTrace]
  refine ⟨114619345427973221950235597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76412896951982147966823731 114619345427973221950235597)
  ·
    refine ⟨42982254535489958231338349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114619345427973221950235597 42982254535489958231338349)
    ·
      refine ⟨16118345450808734336751881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42982254535489958231338349 16118345450808734336751881)
      ·
        refine ⟨12088759088106550752563911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16118345450808734336751881 12088759088106550752563911)
        ·
          refine ⟨18133138632159826128845867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088759088106550752563911 18133138632159826128845867)
          ·
            refine ⟨27199707948239739193268801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18133138632159826128845867 27199707948239739193268801)
            ·
              refine ⟨20399780961179804394951601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27199707948239739193268801 20399780961179804394951601)
              ·
                refine ⟨15299835720884853296213701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20399780961179804394951601 15299835720884853296213701)
                ·
                  refine ⟨2868719197665909993040069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15299835720884853296213701 2868719197665909993040069)
                  ·
                    refine ⟨537884849562358123695013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868719197665909993040069 537884849562358123695013)
                    ·
                      rfl

theorem cell23_3142581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3142581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142581 prefixEnd_3142581 := by exact prefixLift 3142581
  have htrace : WordTrace (prefixWord ++ tailWord_3142581) baseStart_3142581 baseEnd_3142581 := by
    simpa [prefixWord, tailWord_3142581, baseEnd_3142581] using wordTrace_append hprefix tailTrace_3142581
  have hstable : (prefixWord ++ tailWord_3142581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142581).length < 2 ^ (prefixWord ++ tailWord_3142581).sum := by decide
  have hdescent : baseEnd_3142581 < baseStart_3142581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142618 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_3142618 : Nat := 118140960795 + 3142618 * 2 ^ 59
def prefixEnd_3142618 : Nat := 4983230072969 + 3 ^ 40 * 3142618 * 2
def baseEnd_3142618 : Nat := 1613673547471290726322369

theorem tailTrace_3142618 : CollatzResearch.WordTrace tailWord_3142618 prefixEnd_3142618 1613673547471290726322369 := by
  unfold tailWord_3142618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28655173732209794317333127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76413796619226118179555005 28655173732209794317333127)
  ·
    refine ⟨42982760598314691475999691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28655173732209794317333127 42982760598314691475999691)
    ·
      refine ⟨64474140897472037213999537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42982760598314691475999691 64474140897472037213999537)
      ·
        refine ⟨48355605673104027910499653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64474140897472037213999537 48355605673104027910499653)
        ·
          refine ⟨9066676063707005233218685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48355605673104027910499653 9066676063707005233218685)
          ·
            refine ⟨3400003523890126962457007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9066676063707005233218685 3400003523890126962457007)
            ·
              refine ⟨5100005285835190443685511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400003523890126962457007 5100005285835190443685511)
              ·
                refine ⟨7650007928752785665528267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100005285835190443685511 7650007928752785665528267)
                ·
                  refine ⟨11475011893129178498292401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7650007928752785665528267 11475011893129178498292401)
                  ·
                    refine ⟨8606258919846883873719301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11475011893129178498292401 8606258919846883873719301)
                    ·
                      refine ⟨1613673547471290726322369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8606258919846883873719301 1613673547471290726322369)
                      ·
                        rfl

theorem cell23_3142618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_3142618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142618 prefixEnd_3142618 := by exact prefixLift 3142618
  have htrace : WordTrace (prefixWord ++ tailWord_3142618) baseStart_3142618 baseEnd_3142618 := by
    simpa [prefixWord, tailWord_3142618, baseEnd_3142618] using wordTrace_append hprefix tailTrace_3142618
  have hstable : (prefixWord ++ tailWord_3142618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142618).length < 2 ^ (prefixWord ++ tailWord_3142618).sum := by decide
  have hdescent : baseEnd_3142618 < baseStart_3142618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142645 : List Nat := [1, 3, 5, 2, 2, 1, 9]
def baseStart_3142645 : Nat := 118140960795 + 3142645 * 2 ^ 59
def prefixEnd_3142645 : Nat := 4983230072969 + 3 ^ 40 * 3142645 * 2
def baseEnd_3142645 : Nat := 19922066808011878033145

theorem tailTrace_3142645 : CollatzResearch.WordTrace tailWord_3142645 prefixEnd_3142645 19922066808011878033145 := by
  unfold tailWord_3142645
  simp only [CollatzResearch.WordTrace]
  refine ⟨114621679699741360880565389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76414453133160907253710259 114621679699741360880565389)
  ·
    refine ⟨42983129887403010330212021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114621679699741360880565389 42983129887403010330212021)
    ·
      refine ⟨4029668426944032218457377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42983129887403010330212021 4029668426944032218457377)
      ·
        refine ⟨3022251320208024163843033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4029668426944032218457377 3022251320208024163843033)
        ·
          refine ⟨2266688490156018122882275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3022251320208024163843033 2266688490156018122882275)
          ·
            refine ⟨3400032735234027184323413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266688490156018122882275 3400032735234027184323413)
            ·
              refine ⟨19922066808011878033145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3400032735234027184323413 19922066808011878033145)
              ·
                rfl

theorem cell23_3142645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 9].length) (baseStart_3142645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142645 prefixEnd_3142645 := by exact prefixLift 3142645
  have htrace : WordTrace (prefixWord ++ tailWord_3142645) baseStart_3142645 baseEnd_3142645 := by
    simpa [prefixWord, tailWord_3142645, baseEnd_3142645] using wordTrace_append hprefix tailTrace_3142645
  have hstable : (prefixWord ++ tailWord_3142645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142645).length < 2 ^ (prefixWord ++ tailWord_3142645).sum := by decide
  have hdescent : baseEnd_3142645 < baseStart_3142645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142695 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3142695 : Nat := 118140960795 + 3142695 * 2 ^ 59
def prefixEnd_3142695 : Nat := 4983230072969 + 3 ^ 40 * 3142695 * 2
def baseEnd_3142695 : Nat := 1613713085481686925059515

theorem tailTrace_3142695 : CollatzResearch.WordTrace tailWord_3142695 prefixEnd_3142695 1613713085481686925059515 := by
  unfold tailWord_3142695
  simp only [CollatzResearch.WordTrace]
  refine ⟨114623503349560219419885539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76415668899706812946590359 114623503349560219419885539)
  ·
    refine ⟨171935255024340329129828309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114623503349560219419885539 171935255024340329129828309)
    ·
      refine ⟨4029732539632976463980351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 171935255024340329129828309 4029732539632976463980351)
      ·
        refine ⟨6044598809449464695970527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029732539632976463980351 6044598809449464695970527)
        ·
          refine ⟨9066898214174197043955791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044598809449464695970527 9066898214174197043955791)
          ·
            refine ⟨13600347321261295565933687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066898214174197043955791 13600347321261295565933687)
            ·
              refine ⟨20400520981891943348900531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13600347321261295565933687 20400520981891943348900531)
              ·
                refine ⟨30600781472837915023350797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20400520981891943348900531 30600781472837915023350797)
                ·
                  refine ⟨11475293052314218133756549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30600781472837915023350797 11475293052314218133756549)
                  ·
                    refine ⟨2151617447308915900079353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11475293052314218133756549 2151617447308915900079353)
                    ·
                      refine ⟨1613713085481686925059515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151617447308915900079353 1613713085481686925059515)
                      ·
                        rfl

theorem cell23_3142695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3142695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142695 prefixEnd_3142695 := by exact prefixLift 3142695
  have htrace : WordTrace (prefixWord ++ tailWord_3142695) baseStart_3142695 baseEnd_3142695 := by
    simpa [prefixWord, tailWord_3142695, baseEnd_3142695] using wordTrace_append hprefix tailTrace_3142695
  have hstable : (prefixWord ++ tailWord_3142695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142695).length < 2 ^ (prefixWord ++ tailWord_3142695).sum := by decide
  have hdescent : baseEnd_3142695 < baseStart_3142695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142711 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_3142711 : Nat := 118140960795 + 3142711 * 2 ^ 59
def prefixEnd_3142711 : Nat := 4983230072969 + 3 ^ 40 * 3142711 * 2
def baseEnd_3142711 : Nat := 1613721301172158862459441

theorem tailTrace_3142711 : CollatzResearch.WordTrace tailWord_3142711 prefixEnd_3142711 1613721301172158862459441 := by
  unfold tailWord_3142711
  simp only [CollatzResearch.WordTrace]
  refine ⟨114624086917502254152467987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76416057945001502768311991 114624086917502254152467987)
  ·
    refine ⟨171936130376253381228701981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114624086917502254152467987 171936130376253381228701981)
    ·
      refine ⟨64476048891095017960763243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171936130376253381228701981 64476048891095017960763243)
      ·
        refine ⟨96714073336642526941144865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64476048891095017960763243 96714073336642526941144865)
        ·
          refine ⟨72535555002481895205858649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96714073336642526941144865 72535555002481895205858649)
          ·
            refine ⟨54401666251861421404393987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72535555002481895205858649 54401666251861421404393987)
            ·
              refine ⟨81602499377792132106590981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54401666251861421404393987 81602499377792132106590981)
              ·
                refine ⟨15300468633336024769985809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81602499377792132106590981 15300468633336024769985809)
                ·
                  refine ⟨11475351475002018577489357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15300468633336024769985809 11475351475002018577489357)
                  ·
                    refine ⟨4303256803125756966558509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11475351475002018577489357 4303256803125756966558509)
                    ·
                      refine ⟨1613721301172158862459441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4303256803125756966558509 1613721301172158862459441)
                      ·
                        rfl

theorem cell23_3142711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_3142711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142711 prefixEnd_3142711 := by exact prefixLift 3142711
  have htrace : WordTrace (prefixWord ++ tailWord_3142711) baseStart_3142711 baseEnd_3142711 := by
    simpa [prefixWord, tailWord_3142711, baseEnd_3142711] using wordTrace_append hprefix tailTrace_3142711
  have hstable : (prefixWord ++ tailWord_3142711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142711).length < 2 ^ (prefixWord ++ tailWord_3142711).sum := by decide
  have hdescent : baseEnd_3142711 < baseStart_3142711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142712 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 2, 2, 2]
def baseStart_3142712 : Nat := 118140960795 + 3142712 * 2 ^ 59
def prefixEnd_3142712 : Nat := 4983230072969 + 3 ^ 40 * 3142712 * 2
def baseEnd_3142712 : Nat := 1613721814652813358546937

theorem tailTrace_3142712 : CollatzResearch.WordTrace tailWord_3142712 prefixEnd_3142712 1613721814652813358546937 := by
  unfold tailWord_3142712
  simp only [CollatzResearch.WordTrace]
  refine ⟨57312061695249315661627195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76416082260332420882169593 57312061695249315661627195)
  ·
    refine ⟨85968092542873973492440793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57312061695249315661627195 85968092542873973492440793)
    ·
      refine ⟨64476069407155480119330595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85968092542873973492440793 64476069407155480119330595)
      ·
        refine ⟨96714104110733220178995893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64476069407155480119330595 96714104110733220178995893)
        ·
          refine ⟨9066947260381239391780865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96714104110733220178995893 9066947260381239391780865)
          ·
            refine ⟨6800210445285929543835649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9066947260381239391780865 6800210445285929543835649)
            ·
              refine ⟨5100157833964447157876737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6800210445285929543835649 5100157833964447157876737)
              ·
                refine ⟨3825118375473335368407553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100157833964447157876737 3825118375473335368407553)
                ·
                  refine ⟨2868838781605001526305665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825118375473335368407553 2868838781605001526305665)
                  ·
                    refine ⟨2151629086203751144729249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2868838781605001526305665 2151629086203751144729249)
                    ·
                      refine ⟨1613721814652813358546937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151629086203751144729249 1613721814652813358546937)
                      ·
                        rfl

theorem cell23_3142712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_3142712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142712 prefixEnd_3142712 := by exact prefixLift 3142712
  have htrace : WordTrace (prefixWord ++ tailWord_3142712) baseStart_3142712 baseEnd_3142712 := by
    simpa [prefixWord, tailWord_3142712, baseEnd_3142712] using wordTrace_append hprefix tailTrace_3142712
  have hstable : (prefixWord ++ tailWord_3142712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142712).length < 2 ^ (prefixWord ++ tailWord_3142712).sum := by decide
  have hdescent : baseEnd_3142712 < baseStart_3142712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142751 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3142751 : Nat := 118140960795 + 3142751 * 2 ^ 59
def prefixEnd_3142751 : Nat := 4983230072969 + 3 ^ 40 * 3142751 * 2
def baseEnd_3142751 : Nat := 1613741840398338705959257

theorem tailTrace_3142751 : CollatzResearch.WordTrace tailWord_3142751 prefixEnd_3142751 1613741840398338705959257 := by
  unfold tailWord_3142751
  simp only [CollatzResearch.WordTrace]
  refine ⟨114625545837357340983924107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76417030558238227322616071 114625545837357340983924107)
  ·
    refine ⟨171938318756036011475886161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114625545837357340983924107 171938318756036011475886161)
    ·
      refine ⟨128953739067027008606914621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171938318756036011475886161 128953739067027008606914621)
      ·
        refine ⟨48357652150135128227592983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128953739067027008606914621 48357652150135128227592983)
        ·
          refine ⟨72536478225202692341389475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48357652150135128227592983 72536478225202692341389475)
          ·
            refine ⟨108804717337804038512084213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72536478225202692341389475 108804717337804038512084213)
            ·
              refine ⟨10200442250419128610507895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108804717337804038512084213 10200442250419128610507895)
              ·
                refine ⟨15300663375628692915761843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200442250419128610507895 15300663375628692915761843)
                ·
                  refine ⟨22950995063443039373642765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15300663375628692915761843 22950995063443039373642765)
                  ·
                    refine ⟨8606623148791139765116037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22950995063443039373642765 8606623148791139765116037)
                    ·
                      refine ⟨1613741840398338705959257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8606623148791139765116037 1613741840398338705959257)
                      ·
                        rfl

theorem cell23_3142751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3142751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142751 prefixEnd_3142751 := by exact prefixLift 3142751
  have htrace : WordTrace (prefixWord ++ tailWord_3142751) baseStart_3142751 baseEnd_3142751 := by
    simpa [prefixWord, tailWord_3142751, baseEnd_3142751] using wordTrace_append hprefix tailTrace_3142751
  have hstable : (prefixWord ++ tailWord_3142751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142751).length < 2 ^ (prefixWord ++ tailWord_3142751).sum := by decide
  have hdescent : baseEnd_3142751 < baseStart_3142751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142768 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 4, 4, 2]
def baseStart_3142768 : Nat := 118140960795 + 3142768 * 2 ^ 59
def prefixEnd_3142768 : Nat := 4983230072969 + 3 ^ 40 * 3142768 * 2
def baseEnd_3142768 : Nat := 1613750569569465139446679

theorem tailTrace_3142768 : CollatzResearch.WordTrace tailWord_3142768 prefixEnd_3142768 1613750569569465139446679 := by
  unfold tailWord_3142768
  simp only [CollatzResearch.WordTrace]
  refine ⟨57313082939147876443646479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76417443918863835258195305 57313082939147876443646479)
  ·
    refine ⟨85969624408721814665469719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57313082939147876443646479 85969624408721814665469719)
    ·
      refine ⟨128954436613082721998204579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85969624408721814665469719 128954436613082721998204579)
      ·
        refine ⟨193431654919624082997306869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128954436613082721998204579 193431654919624082997306869)
        ·
          refine ⟨18134217648714757780997519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193431654919624082997306869 18134217648714757780997519)
          ·
            refine ⟨27201326473072136671496279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18134217648714757780997519 27201326473072136671496279)
            ·
              refine ⟨40801989709608205007244419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27201326473072136671496279 40801989709608205007244419)
              ·
                refine ⟨61202984564412307510866629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40801989709608205007244419 61202984564412307510866629)
                ·
                  refine ⟨11475559605827307658287493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61202984564412307510866629 11475559605827307658287493)
                  ·
                    refine ⟨2151667426092620185928905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11475559605827307658287493 2151667426092620185928905)
                    ·
                      refine ⟨1613750569569465139446679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151667426092620185928905 1613750569569465139446679)
                      ·
                        rfl

theorem cell23_3142768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 4, 2].length) (baseStart_3142768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142768 prefixEnd_3142768 := by exact prefixLift 3142768
  have htrace : WordTrace (prefixWord ++ tailWord_3142768) baseStart_3142768 baseEnd_3142768 := by
    simpa [prefixWord, tailWord_3142768, baseEnd_3142768] using wordTrace_append hprefix tailTrace_3142768
  have hstable : (prefixWord ++ tailWord_3142768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142768).length < 2 ^ (prefixWord ++ tailWord_3142768).sum := by decide
  have hdescent : baseEnd_3142768 < baseStart_3142768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142781 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_3142781 : Nat := 118140960795 + 3142781 * 2 ^ 59
def prefixEnd_3142781 : Nat := 4983230072969 + 3 ^ 40 * 3142781 * 2
def baseEnd_3142781 : Nat := 1613757244817973588584119

theorem tailTrace_3142781 : CollatzResearch.WordTrace tailWord_3142781 prefixEnd_3142781 1613757244817973588584119 := by
  unfold tailWord_3142781
  simp only [CollatzResearch.WordTrace]
  refine ⟨114626640027248656107516197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76417760018165770738344131 114626640027248656107516197)
  ·
    refine ⟨21492495005109123020159287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114626640027248656107516197 21492495005109123020159287)
    ·
      refine ⟨32238742507663684530238931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21492495005109123020159287 32238742507663684530238931)
      ·
        refine ⟨48358113761495526795358397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32238742507663684530238931 48358113761495526795358397)
        ·
          refine ⟨18134292660560822548259399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48358113761495526795358397 18134292660560822548259399)
          ·
            refine ⟨27201438990841233822389099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18134292660560822548259399 27201438990841233822389099)
            ·
              refine ⟨40802158486261850733583649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27201438990841233822389099 40802158486261850733583649)
              ·
                refine ⟨30601618864696388050187737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40802158486261850733583649 30601618864696388050187737)
                ·
                  refine ⟨22951214148522291037640803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30601618864696388050187737 22951214148522291037640803)
                  ·
                    refine ⟨34426821222783436556461205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22951214148522291037640803 34426821222783436556461205)
                    ·
                      refine ⟨1613757244817973588584119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34426821222783436556461205 1613757244817973588584119)
                      ·
                        rfl

theorem cell23_3142781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_3142781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142781 prefixEnd_3142781 := by exact prefixLift 3142781
  have htrace : WordTrace (prefixWord ++ tailWord_3142781) baseStart_3142781 baseEnd_3142781 := by
    simpa [prefixWord, tailWord_3142781, baseEnd_3142781] using wordTrace_append hprefix tailTrace_3142781
  have hstable : (prefixWord ++ tailWord_3142781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142781).length < 2 ^ (prefixWord ++ tailWord_3142781).sum := by decide
  have hdescent : baseEnd_3142781 < baseStart_3142781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142785 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_3142785 : Nat := 118140960795 + 3142785 * 2 ^ 59
def prefixEnd_3142785 : Nat := 4983230072969 + 3 ^ 40 * 3142785 * 2
def baseEnd_3142785 : Nat := 1613759298740591572934101

theorem tailTrace_3142785 : CollatzResearch.WordTrace tailWord_3142785 prefixEnd_3142785 1613759298740591572934101 := by
  unfold tailWord_3142785
  simp only [CollatzResearch.WordTrace]
  refine ⟨114626785919234164790661809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76417857279489443193774539 114626785919234164790661809)
  ·
    refine ⟨85970089439425623592996357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114626785919234164790661809 85970089439425623592996357)
    ·
      refine ⟨16119391769892304423686817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85970089439425623592996357 16119391769892304423686817)
      ·
        refine ⟨12089543827419228317765113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16119391769892304423686817 12089543827419228317765113)
        ·
          refine ⟨9067157870564421238323835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12089543827419228317765113 9067157870564421238323835)
          ·
            refine ⟨13600736805846631857485753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067157870564421238323835 13600736805846631857485753)
            ·
              refine ⟨10200552604384973893114315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13600736805846631857485753 10200552604384973893114315)
              ·
                refine ⟨15300828906577460839671473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200552604384973893114315 15300828906577460839671473)
                ·
                  refine ⟨11475621679933095629753605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15300828906577460839671473 11475621679933095629753605)
                  ·
                    refine ⟨2151679064987455430578801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11475621679933095629753605 2151679064987455430578801)
                    ·
                      refine ⟨1613759298740591572934101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151679064987455430578801 1613759298740591572934101)
                      ·
                        rfl

theorem cell23_3142785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_3142785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142785 prefixEnd_3142785 := by exact prefixLift 3142785
  have htrace : WordTrace (prefixWord ++ tailWord_3142785) baseStart_3142785 baseEnd_3142785 := by
    simpa [prefixWord, tailWord_3142785, baseEnd_3142785] using wordTrace_append hprefix tailTrace_3142785
  have hstable : (prefixWord ++ tailWord_3142785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142785).length < 2 ^ (prefixWord ++ tailWord_3142785).sum := by decide
  have hdescent : baseEnd_3142785 < baseStart_3142785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142788 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_3142788 : Nat := 118140960795 + 3142788 * 2 ^ 59
def prefixEnd_3142788 : Nat := 4983230072969 + 3 ^ 40 * 3142788 * 2
def baseEnd_3142788 : Nat := 1613760839182555061196587

theorem tailTrace_3142788 : CollatzResearch.WordTrace tailWord_3142788 prefixEnd_3142788 1613760839182555061196587 := by
  unfold tailWord_3142788
  simp only [CollatzResearch.WordTrace]
  refine ⟨57313447669111648151510509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76417930225482197535347345 57313447669111648151510509)
  ·
    refine ⟨21492542875916868056816441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57313447669111648151510509 21492542875916868056816441)
    ·
      refine ⟨16119407156937651042612331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21492542875916868056816441 16119407156937651042612331)
      ·
        refine ⟨24179110735406476563918497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16119407156937651042612331 24179110735406476563918497)
        ·
          refine ⟨18134333051554857422938873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24179110735406476563918497 18134333051554857422938873)
          ·
            refine ⟨13600749788666143067204155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18134333051554857422938873 13600749788666143067204155)
            ·
              refine ⟨20401124682999214600806233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13600749788666143067204155 20401124682999214600806233)
              ·
                refine ⟨15300843512249410950604675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20401124682999214600806233 15300843512249410950604675)
                ·
                  refine ⟨22951265268374116425907013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15300843512249410950604675 22951265268374116425907013)
                  ·
                    refine ⟨4303362237820146829857565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22951265268374116425907013 4303362237820146829857565)
                    ·
                      refine ⟨1613760839182555061196587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4303362237820146829857565 1613760839182555061196587)
                      ·
                        rfl

theorem cell23_3142788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_3142788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142788 prefixEnd_3142788 := by exact prefixLift 3142788
  have htrace : WordTrace (prefixWord ++ tailWord_3142788) baseStart_3142788 baseEnd_3142788 := by
    simpa [prefixWord, tailWord_3142788, baseEnd_3142788] using wordTrace_append hprefix tailTrace_3142788
  have hstable : (prefixWord ++ tailWord_3142788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142788).length < 2 ^ (prefixWord ++ tailWord_3142788).sum := by decide
  have hdescent : baseEnd_3142788 < baseStart_3142788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142812 : List Nat := [2, 2, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_3142812 : Nat := 118140960795 + 3142812 * 2 ^ 59
def prefixEnd_3142812 : Nat := 4983230072969 + 3 ^ 40 * 3142812 * 2
def baseEnd_3142812 : Nat := 537924387572754322432159

theorem tailTrace_3142812 : CollatzResearch.WordTrace tailWord_3142812 prefixEnd_3142812 537924387572754322432159 := by
  unfold tailWord_3142812
  simp only [CollatzResearch.WordTrace]
  refine ⟨57313885345068174200947345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76418513793424232267929793 57313885345068174200947345)
  ·
    refine ⟨42985414008801130650710509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57313885345068174200947345 42985414008801130650710509)
    ·
      refine ⟨16119530253300423994016441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42985414008801130650710509 16119530253300423994016441)
      ·
        refine ⟨12089647689975317995512331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16119530253300423994016441 12089647689975317995512331)
        ·
          refine ⟨18134471534962976993268497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12089647689975317995512331 18134471534962976993268497)
          ·
            refine ⟨13600853651222232744951373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18134471534962976993268497 13600853651222232744951373)
            ·
              refine ⟨5100320119208337279356765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13600853651222232744951373 5100320119208337279356765)
              ·
                refine ⟨1912620044703126479758787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5100320119208337279356765 1912620044703126479758787)
                ·
                  refine ⟨2868930067054689719638181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912620044703126479758787 2868930067054689719638181)
                  ·
                    refine ⟨537924387572754322432159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868930067054689719638181 537924387572754322432159)
                    ·
                      rfl

theorem cell23_3142812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_3142812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142812 prefixEnd_3142812 := by exact prefixLift 3142812
  have htrace : WordTrace (prefixWord ++ tailWord_3142812) baseStart_3142812 baseEnd_3142812 := by
    simpa [prefixWord, tailWord_3142812, baseEnd_3142812] using wordTrace_append hprefix tailTrace_3142812
  have hstable : (prefixWord ++ tailWord_3142812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142812).length < 2 ^ (prefixWord ++ tailWord_3142812).sum := by decide
  have hdescent : baseEnd_3142812 < baseStart_3142812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142828 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 3, 5, 2]
def baseStart_3142828 : Nat := 118140960795 + 3142828 * 2 ^ 59
def prefixEnd_3142828 : Nat := 4983230072969 + 3 ^ 40 * 3142828 * 2
def baseEnd_3142828 : Nat := 1613781378408734904696403

theorem tailTrace_3142828 : CollatzResearch.WordTrace tailWord_3142828 prefixEnd_3142828 1613781378408734904696403 := by
  unfold tailWord_3142828
  simp only [CollatzResearch.WordTrace]
  refine ⟨57314177129039191567238569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76418902838718922089651425 57314177129039191567238569)
  ·
    refine ⟨42985632846779393675428927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57314177129039191567238569 42985632846779393675428927)
    ·
      refine ⟨64478449270169090513143391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42985632846779393675428927 64478449270169090513143391)
      ·
        refine ⟨96717673905253635769715087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64478449270169090513143391 96717673905253635769715087)
        ·
          refine ⟨145076510857880453654572631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96717673905253635769715087 145076510857880453654572631)
          ·
            refine ⟨217614766286820680481858947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145076510857880453654572631 217614766286820680481858947)
            ·
              refine ⟨326422149430231020722788421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217614766286820680481858947 326422149430231020722788421)
              ·
                refine ⟨61204153018168316385522829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326422149430231020722788421 61204153018168316385522829)
                ·
                  refine ⟨22951557381813118644571061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61204153018168316385522829 22951557381813118644571061)
                  ·
                    refine ⟨2151708504544979872928537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22951557381813118644571061 2151708504544979872928537)
                    ·
                      refine ⟨1613781378408734904696403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151708504544979872928537 1613781378408734904696403)
                      ·
                        rfl

theorem cell23_3142828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_3142828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142828 prefixEnd_3142828 := by exact prefixLift 3142828
  have htrace : WordTrace (prefixWord ++ tailWord_3142828) baseStart_3142828 baseEnd_3142828 := by
    simpa [prefixWord, tailWord_3142828, baseEnd_3142828] using wordTrace_append hprefix tailTrace_3142828
  have hstable : (prefixWord ++ tailWord_3142828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142828).length < 2 ^ (prefixWord ++ tailWord_3142828).sum := by decide
  have hdescent : baseEnd_3142828 < baseStart_3142828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142829 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_3142829 : Nat := 118140960795 + 3142829 * 2 ^ 59
def prefixEnd_3142829 : Nat := 4983230072969 + 3 ^ 40 * 3142829 * 2
def baseEnd_3142829 : Nat := 537927297296463133594633

theorem tailTrace_3142829 : CollatzResearch.WordTrace tailWord_3142829 prefixEnd_3142829 537927297296463133594633 := by
  unfold tailWord_3142829
  simp only [CollatzResearch.WordTrace]
  refine ⟨114628390731074760305263541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76418927154049840203509027 114628390731074760305263541)
  ·
    refine ⟨10746411631038258778618457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114628390731074760305263541 10746411631038258778618457)
    ·
      refine ⟨8059808723278694083963843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10746411631038258778618457 8059808723278694083963843)
      ·
        refine ⟨12089713084918041125945765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8059808723278694083963843 12089713084918041125945765)
        ·
          refine ⟨2266821203422132711114831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12089713084918041125945765 2266821203422132711114831)
          ·
            refine ⟨3400231805133199066672247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266821203422132711114831 3400231805133199066672247)
            ·
              refine ⟨5100347707699798600008371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400231805133199066672247 5100347707699798600008371)
              ·
                refine ⟨7650521561549697900012557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100347707699798600008371 7650521561549697900012557)
                ·
                  refine ⟨2868945585581136712504709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7650521561549697900012557 2868945585581136712504709)
                  ·
                    refine ⟨537927297296463133594633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868945585581136712504709 537927297296463133594633)
                    ·
                      rfl

theorem cell23_3142829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_3142829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142829 prefixEnd_3142829 := by exact prefixLift 3142829
  have htrace : WordTrace (prefixWord ++ tailWord_3142829) baseStart_3142829 baseEnd_3142829 := by
    simpa [prefixWord, tailWord_3142829, baseEnd_3142829] using wordTrace_append hprefix tailTrace_3142829
  have hstable : (prefixWord ++ tailWord_3142829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142829).length < 2 ^ (prefixWord ++ tailWord_3142829).sum := by decide
  have hdescent : baseEnd_3142829 < baseStart_3142829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142835 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 3]
def baseStart_3142835 : Nat := 118140960795 + 3142835 * 2 ^ 59
def prefixEnd_3142835 : Nat := 4983230072969 + 3 ^ 40 * 3142835 * 2
def baseEnd_3142835 : Nat := 1613784972773316377308871

theorem tailTrace_3142835 : CollatzResearch.WordTrace tailWord_3142835 prefixEnd_3142835 1613784972773316377308871 := by
  unfold tailWord_3142835
  simp only [CollatzResearch.WordTrace]
  refine ⟨114628609569053023329981959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76419073046035348886654639 114628609569053023329981959)
  ·
    refine ⟨171942914353579534994972939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114628609569053023329981959 171942914353579534994972939)
    ·
      refine ⟨257914371530369302492459409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171942914353579534994972939 257914371530369302492459409)
      ·
        refine ⟨193435778647776976869344557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257914371530369302492459409 193435778647776976869344557)
        ·
          refine ⟨72538416992916366326004209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193435778647776976869344557 72538416992916366326004209)
          ·
            refine ⟨54403812744687274744503157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72538416992916366326004209 54403812744687274744503157)
            ·
              refine ⟨5100357444814432007297171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54403812744687274744503157 5100357444814432007297171)
              ·
                refine ⟨7650536167221648010945757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100357444814432007297171 7650536167221648010945757)
                ·
                  refine ⟨2868951062708118004104659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7650536167221648010945757 2868951062708118004104659)
                  ·
                    refine ⟨4303426594062177006156989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2868951062708118004104659 4303426594062177006156989)
                    ·
                      refine ⟨1613784972773316377308871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4303426594062177006156989 1613784972773316377308871)
                      ·
                        rfl

theorem cell23_3142835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 3].length) (baseStart_3142835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142835 prefixEnd_3142835 := by exact prefixLift 3142835
  have htrace : WordTrace (prefixWord ++ tailWord_3142835) baseStart_3142835 baseEnd_3142835 := by
    simpa [prefixWord, tailWord_3142835, baseEnd_3142835] using wordTrace_append hprefix tailTrace_3142835
  have hstable : (prefixWord ++ tailWord_3142835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142835).length < 2 ^ (prefixWord ++ tailWord_3142835).sum := by decide
  have hdescent : baseEnd_3142835 < baseStart_3142835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142872 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 1, 5]
def baseStart_3142872 : Nat := 118140960795 + 3142872 * 2 ^ 59
def prefixEnd_3142872 : Nat := 4983230072969 + 3 ^ 40 * 3142872 * 2
def baseEnd_3142872 : Nat := 537934657185844244182067

theorem tailTrace_3142872 : CollatzResearch.WordTrace tailWord_3142872 prefixEnd_3142872 537934657185844244182067 := by
  unfold tailWord_3142872
  simp only [CollatzResearch.WordTrace]
  refine ⟨57314979534959489324539435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76419972713279319099385913 57314979534959489324539435)
  ·
    refine ⟨85972469302439233986809153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57314979534959489324539435 85972469302439233986809153)
    ·
      refine ⟨64479351976829425490106865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85972469302439233986809153 64479351976829425490106865)
      ·
        refine ⟨48359513982622069117580149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64479351976829425490106865 48359513982622069117580149)
        ·
          refine ⟨4533704435870818979773139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48359513982622069117580149 4533704435870818979773139)
          ·
            refine ⟨6800556653806228469659709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533704435870818979773139 6800556653806228469659709)
            ·
              refine ⟨2550208745177335676122391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6800556653806228469659709 2550208745177335676122391)
              ·
                refine ⟨3825313117766003514183587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550208745177335676122391 3825313117766003514183587)
                ·
                  refine ⟨5737969676649005271275381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825313117766003514183587 5737969676649005271275381)
                  ·
                    refine ⟨537934657185844244182067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5737969676649005271275381 537934657185844244182067)
                    ·
                      rfl

theorem cell23_3142872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_3142872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142872 prefixEnd_3142872 := by exact prefixLift 3142872
  have htrace : WordTrace (prefixWord ++ tailWord_3142872) baseStart_3142872 baseEnd_3142872 := by
    simpa [prefixWord, tailWord_3142872, baseEnd_3142872] using wordTrace_append hprefix tailTrace_3142872
  have hstable : (prefixWord ++ tailWord_3142872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142872).length < 2 ^ (prefixWord ++ tailWord_3142872).sum := by decide
  have hdescent : baseEnd_3142872 < baseStart_3142872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142881 : List Nat := [1, 2, 3, 1, 3, 13]
def baseStart_3142881 : Nat := 118140960795 + 3142881 * 2 ^ 59
def prefixEnd_3142881 : Nat := 4983230072969 + 3 ^ 40 * 3142881 * 2
def baseEnd_3142881 : Nat := 6641187625034663363513

theorem tailTrace_3142881 : CollatzResearch.WordTrace tailWord_3142881 prefixEnd_3142881 6641187625034663363513 := by
  unfold tailWord_3142881
  simp only [CollatzResearch.WordTrace]
  refine ⟨114630287326886373186156497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76420191551257582124104331 114630287326886373186156497)
  ·
    refine ⟨85972715495164779889617373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114630287326886373186156497 85972715495164779889617373)
    ·
      refine ⟨32239768310686792458606515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85972715495164779889617373 32239768310686792458606515)
      ·
        refine ⟨48359652466030188687909773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32239768310686792458606515 48359652466030188687909773)
        ·
          refine ⟨18134869674761320757966165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48359652466030188687909773 18134869674761320757966165)
          ·
            refine ⟨6641187625034663363513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 18134869674761320757966165 6641187625034663363513)
            ·
              rfl

theorem cell23_3142881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 13].length) (baseStart_3142881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142881 prefixEnd_3142881 := by exact prefixLift 3142881
  have htrace : WordTrace (prefixWord ++ tailWord_3142881) baseStart_3142881 baseEnd_3142881 := by
    simpa [prefixWord, tailWord_3142881, baseEnd_3142881] using wordTrace_append hprefix tailTrace_3142881
  have hstable : (prefixWord ++ tailWord_3142881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142881).length < 2 ^ (prefixWord ++ tailWord_3142881).sum := by decide
  have hdescent : baseEnd_3142881 < baseStart_3142881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142888 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3142888 : Nat := 118140960795 + 3142888 * 2 ^ 59
def prefixEnd_3142888 : Nat := 4983230072969 + 3 ^ 40 * 3142888 * 2
def baseEnd_3142888 : Nat := 1613812187248004669946127

theorem tailTrace_3142888 : CollatzResearch.WordTrace tailWord_3142888 prefixEnd_3142888 1613812187248004669946127 := by
  unfold tailWord_3142888
  simp only [CollatzResearch.WordTrace]
  refine ⟨57315271318930506690830659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76420361758574008921107545 57315271318930506690830659)
  ·
    refine ⟨85972906978395760036245989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57315271318930506690830659 85972906978395760036245989)
    ·
      refine ⟨16119920058449205006796123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85972906978395760036245989 16119920058449205006796123)
      ·
        refine ⟨24179880087673807510194185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16119920058449205006796123 24179880087673807510194185)
        ·
          refine ⟨18134910065755355632645639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24179880087673807510194185 18134910065755355632645639)
          ·
            refine ⟨27202365098633033448968459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18134910065755355632645639 27202365098633033448968459)
            ·
              refine ⟨40803547647949550173452689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27202365098633033448968459 40803547647949550173452689)
              ·
                refine ⟨30602660735962162630089517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40803547647949550173452689 30602660735962162630089517)
                ·
                  refine ⟨11475997775985810986283569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30602660735962162630089517 11475997775985810986283569)
                  ·
                    refine ⟨8606998331989358239712677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11475997775985810986283569 8606998331989358239712677)
                    ·
                      refine ⟨1613812187248004669946127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8606998331989358239712677 1613812187248004669946127)
                      ·
                        rfl

theorem cell23_3142888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3142888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142888 prefixEnd_3142888 := by exact prefixLift 3142888
  have htrace : WordTrace (prefixWord ++ tailWord_3142888) baseStart_3142888 baseEnd_3142888 := by
    simpa [prefixWord, tailWord_3142888, baseEnd_3142888] using wordTrace_append hprefix tailTrace_3142888
  have hstable : (prefixWord ++ tailWord_3142888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142888).length < 2 ^ (prefixWord ++ tailWord_3142888).sum := by decide
  have hdescent : baseEnd_3142888 < baseStart_3142888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142926 : List Nat := [4, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_3142926 : Nat := 118140960795 + 3142926 * 2 ^ 59
def prefixEnd_3142926 : Nat := 4983230072969 + 3 ^ 40 * 3142926 * 2
def baseEnd_3142926 : Nat := 1613831699512875521270953

theorem tailTrace_3142926 : CollatzResearch.WordTrace tailWord_3142926 prefixEnd_3142926 1613831699512875521270953 := by
  unfold tailWord_3142926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328991076465418233943079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76421285741148897247696421 14328991076465418233943079)
  ·
    refine ⟨21493486614698127350914619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14328991076465418233943079 21493486614698127350914619)
    ·
      refine ⟨32240229922047191026371929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21493486614698127350914619 32240229922047191026371929)
      ·
        refine ⟨24180172441535393269778947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32240229922047191026371929 24180172441535393269778947)
        ·
          refine ⟨36270258662303089904668421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24180172441535393269778947 36270258662303089904668421)
          ·
            refine ⟨6800673499181829357125329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36270258662303089904668421 6800673499181829357125329)
            ·
              refine ⟨5100505124386372017843997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6800673499181829357125329 5100505124386372017843997)
              ·
                refine ⟨1912689421644889506691499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5100505124386372017843997 1912689421644889506691499)
                ·
                  refine ⟨2869034132467334260037249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912689421644889506691499 2869034132467334260037249)
                  ·
                    refine ⟨2151775599350500695027937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2869034132467334260037249 2151775599350500695027937)
                    ·
                      refine ⟨1613831699512875521270953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151775599350500695027937 1613831699512875521270953)
                      ·
                        rfl

theorem cell23_3142926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_3142926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142926 prefixEnd_3142926 := by exact prefixLift 3142926
  have htrace : WordTrace (prefixWord ++ tailWord_3142926) baseStart_3142926 baseEnd_3142926 := by
    simpa [prefixWord, tailWord_3142926, baseEnd_3142926] using wordTrace_append hprefix tailTrace_3142926
  have hstable : (prefixWord ++ tailWord_3142926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142926).length < 2 ^ (prefixWord ++ tailWord_3142926).sum := by decide
  have hdescent : baseEnd_3142926 < baseStart_3142926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142966 : List Nat := [5, 1, 2, 3, 2, 1, 2, 7]
def baseStart_3142966 : Nat := 118140960795 + 3142966 * 2 ^ 59
def prefixEnd_3142966 : Nat := 4983230072969 + 3 ^ 40 * 3142966 * 2
def baseEnd_3142966 : Nat := 59772305138483532028547

theorem tailTrace_3142966 : CollatzResearch.WordTrace tailWord_3142966 prefixEnd_3142966 59772305138483532028547 := by
  unfold tailWord_3142966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164586720723652043937547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76422258354385621802000501 7164586720723652043937547)
  ·
    refine ⟨10746880081085478065906321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7164586720723652043937547 10746880081085478065906321)
    ·
      refine ⟨8060160060814108549429741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10746880081085478065906321 8060160060814108549429741)
      ·
        refine ⟨3022560022805290706036153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8060160060814108549429741 3022560022805290706036153)
        ·
          refine ⟨2266920017103968029527115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3022560022805290706036153 2266920017103968029527115)
          ·
            refine ⟨3400380025655952044290673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266920017103968029527115 3400380025655952044290673)
            ·
              refine ⟨2550285019241964033218005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3400380025655952044290673 2550285019241964033218005)
              ·
                refine ⟨59772305138483532028547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2550285019241964033218005 59772305138483532028547)
                ·
                  rfl

theorem cell23_3142966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_3142966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142966 prefixEnd_3142966 := by exact prefixLift 3142966
  have htrace : WordTrace (prefixWord ++ tailWord_3142966) baseStart_3142966 baseEnd_3142966 := by
    simpa [prefixWord, tailWord_3142966, baseEnd_3142966] using wordTrace_append hprefix tailTrace_3142966
  have hstable : (prefixWord ++ tailWord_3142966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142966).length < 2 ^ (prefixWord ++ tailWord_3142966).sum := by decide
  have hdescent : baseEnd_3142966 < baseStart_3142966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142968 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3142968 : Nat := 118140960795 + 3142968 * 2 ^ 59
def prefixEnd_3142968 : Nat := 4983230072969 + 3 ^ 40 * 3142968 * 2
def baseEnd_3142968 : Nat := 1613853265700364356945759

theorem tailTrace_3142968 : CollatzResearch.WordTrace tailWord_3142968 prefixEnd_3142968 1613853265700364356945759 := by
  unfold tailWord_3142968
  simp only [CollatzResearch.WordTrace]
  refine ⟨57316730238785593522286779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76422306985047458029715705 57316730238785593522286779)
  ·
    refine ⟨85975095358178390283430169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57316730238785593522286779 85975095358178390283430169)
    ·
      refine ⟨64481321518633792712572627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85975095358178390283430169 64481321518633792712572627)
      ·
        refine ⟨96721982277950689068858941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64481321518633792712572627 96721982277950689068858941)
        ·
          refine ⟨36270743354231508400822103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96721982277950689068858941 36270743354231508400822103)
          ·
            refine ⟨54406115031347262601233155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36270743354231508400822103 54406115031347262601233155)
            ·
              refine ⟨81609172547020893901849733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54406115031347262601233155 81609172547020893901849733)
              ·
                refine ⟨15301719852566417606596825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81609172547020893901849733 15301719852566417606596825)
                ·
                  refine ⟨11476289889424813204947619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15301719852566417606596825 11476289889424813204947619)
                  ·
                    refine ⟨17214434834137219807421429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11476289889424813204947619 17214434834137219807421429)
                    ·
                      refine ⟨1613853265700364356945759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17214434834137219807421429 1613853265700364356945759)
                      ·
                        rfl

theorem cell23_3142968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3142968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3142968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3142968 prefixEnd_3142968 := by exact prefixLift 3142968
  have htrace : WordTrace (prefixWord ++ tailWord_3142968) baseStart_3142968 baseEnd_3142968 := by
    simpa [prefixWord, tailWord_3142968, baseEnd_3142968] using wordTrace_append hprefix tailTrace_3142968
  have hstable : (prefixWord ++ tailWord_3142968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142968).length < 2 ^ (prefixWord ++ tailWord_3142968).sum := by decide
  have hdescent : baseEnd_3142968 < baseStart_3142968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143016 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3143016 : Nat := 118140960795 + 3143016 * 2 ^ 59
def prefixEnd_3143016 : Nat := 4983230072969 + 3 ^ 40 * 3143016 * 2
def baseEnd_3143016 : Nat := 1613877912771780169145539

theorem tailTrace_3143016 : CollatzResearch.WordTrace tailWord_3143016 prefixEnd_3143016 1613877912771780169145539 := by
  unfold tailWord_3143016
  simp only [CollatzResearch.WordTrace]
  refine ⟨57317605590698645621160451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76423474120931527494880601 57317605590698645621160451)
  ·
    refine ⟨85976408386047968431740677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57317605590698645621160451 85976408386047968431740677)
    ·
      refine ⟨16120576572383994080951377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85976408386047968431740677 16120576572383994080951377)
      ·
        refine ⟨12090432429287995560713533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16120576572383994080951377 12090432429287995560713533)
        ·
          refine ⟨4533912160982998335267575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12090432429287995560713533 4533912160982998335267575)
          ·
            refine ⟨6800868241474497502901363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533912160982998335267575 6800868241474497502901363)
            ·
              refine ⟨10201302362211746254352045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6800868241474497502901363 10201302362211746254352045)
              ·
                refine ⟨3825488385829404845382017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10201302362211746254352045 3825488385829404845382017)
                ·
                  refine ⟨2869116289372053634036513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825488385829404845382017 2869116289372053634036513)
                  ·
                    refine ⟨2151837217029040225527385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2869116289372053634036513 2151837217029040225527385)
                    ·
                      refine ⟨1613877912771780169145539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151837217029040225527385 1613877912771780169145539)
                      ·
                        rfl

theorem cell23_3143016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3143016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143016 prefixEnd_3143016 := by exact prefixLift 3143016
  have htrace : WordTrace (prefixWord ++ tailWord_3143016) baseStart_3143016 baseEnd_3143016 := by
    simpa [prefixWord, tailWord_3143016, baseEnd_3143016] using wordTrace_append hprefix tailTrace_3143016
  have hstable : (prefixWord ++ tailWord_3143016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143016).length < 2 ^ (prefixWord ++ tailWord_3143016).sum := by decide
  have hdescent : baseEnd_3143016 < baseStart_3143016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143035 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 2, 5]
def baseStart_3143035 : Nat := 118140960795 + 3143035 * 2 ^ 59
def prefixEnd_3143035 : Nat := 4983230072969 + 3 ^ 40 * 3143035 * 2
def baseEnd_3143035 : Nat := 537962556301405198269317

theorem tailTrace_3143035 : CollatzResearch.WordTrace tailWord_3143035 prefixEnd_3143035 537962556301405198269317 := by
  unfold tailWord_3143035
  simp only [CollatzResearch.WordTrace]
  refine ⟨114635904168328457487262559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76423936112218971658175039 114635904168328457487262559)
  ·
    refine ⟨171953856252492686230893839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114635904168328457487262559 171953856252492686230893839)
    ·
      refine ⟨257930784378739029346340759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171953856252492686230893839 257930784378739029346340759)
      ·
        refine ⟨386896176568108544019511139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257930784378739029346340759 386896176568108544019511139)
        ·
          refine ⟨580344264852162816029266709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386896176568108544019511139 580344264852162816029266709)
          ·
            refine ⟨27203637414945132001371877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 580344264852162816029266709 27203637414945132001371877)
            ·
              refine ⟨5100682015302212250257227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27203637414945132001371877 5100682015302212250257227)
              ·
                refine ⟨7651023022953318375385841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100682015302212250257227 7651023022953318375385841)
                ·
                  refine ⟨5738267267214988781539381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7651023022953318375385841 5738267267214988781539381)
                  ·
                    refine ⟨537962556301405198269317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5738267267214988781539381 537962556301405198269317)
                    ·
                      rfl

theorem cell23_3143035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 5].length) (baseStart_3143035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143035 prefixEnd_3143035 := by exact prefixLift 3143035
  have htrace : WordTrace (prefixWord ++ tailWord_3143035) baseStart_3143035 baseEnd_3143035 := by
    simpa [prefixWord, tailWord_3143035, baseEnd_3143035] using wordTrace_append hprefix tailTrace_3143035
  have hstable : (prefixWord ++ tailWord_3143035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143035).length < 2 ^ (prefixWord ++ tailWord_3143035).sum := by decide
  have hdescent : baseEnd_3143035 < baseStart_3143035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143072 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 2, 4, 2]
def baseStart_3143072 : Nat := 118140960795 + 3143072 * 2 ^ 59
def prefixEnd_3143072 : Nat := 4983230072969 + 3 ^ 40 * 3143072 * 2
def baseEnd_3143072 : Nat := 1613906667688431950045281

theorem tailTrace_3143072 : CollatzResearch.WordTrace tailWord_3143072 prefixEnd_3143072 1613906667688431950045281 := by
  unfold tailWord_3143072
  simp only [CollatzResearch.WordTrace]
  refine ⟨57318626834597206403179735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76424835779462941870906313 57318626834597206403179735)
  ·
    refine ⟨85977940251895809604769603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57318626834597206403179735 85977940251895809604769603)
    ·
      refine ⟨128966910377843714407154405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85977940251895809604769603 128966910377843714407154405)
      ·
        refine ⟨24181295695845696451341451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128966910377843714407154405 24181295695845696451341451)
        ·
          refine ⟨36271943543768544677012177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24181295695845696451341451 36271943543768544677012177)
          ·
            refine ⟨27203957657826408507759133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36271943543768544677012177 27203957657826408507759133)
            ·
              refine ⟨10201484121684903190409675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27203957657826408507759133 10201484121684903190409675)
              ·
                refine ⟨15302226182527354785614513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10201484121684903190409675 15302226182527354785614513)
                ·
                  refine ⟨11476669636895516089210885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15302226182527354785614513 11476669636895516089210885)
                  ·
                    refine ⟨2151875556917909266727041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11476669636895516089210885 2151875556917909266727041)
                    ·
                      refine ⟨1613906667688431950045281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2151875556917909266727041 1613906667688431950045281)
                      ·
                        rfl

theorem cell23_3143072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_3143072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143072 prefixEnd_3143072 := by exact prefixLift 3143072
  have htrace : WordTrace (prefixWord ++ tailWord_3143072) baseStart_3143072 baseEnd_3143072 := by
    simpa [prefixWord, tailWord_3143072, baseEnd_3143072] using wordTrace_append hprefix tailTrace_3143072
  have hstable : (prefixWord ++ tailWord_3143072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143072).length < 2 ^ (prefixWord ++ tailWord_3143072).sum := by decide
  have hdescent : baseEnd_3143072 < baseStart_3143072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143075 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 3]
def baseStart_3143075 : Nat := 118140960795 + 3143075 * 2 ^ 59
def prefixEnd_3143075 : Nat := 4983230072969 + 3 ^ 40 * 3143075 * 2
def baseEnd_3143075 : Nat := 1613908208130395438307767

theorem tailTrace_3143075 : CollatzResearch.WordTrace tailWord_3143075 prefixEnd_3143075 1613908208130395438307767 := by
  unfold tailWord_3143075
  simp only [CollatzResearch.WordTrace]
  refine ⟨114637363088183544318718679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76424908725455696212479119 114637363088183544318718679)
  ·
    refine ⟨171956044632275316478078019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114637363088183544318718679 171956044632275316478078019)
    ·
      refine ⟨257934066948412974717117029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171956044632275316478078019 257934066948412974717117029)
      ·
        refine ⟨48362637552827432759459443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257934066948412974717117029 48362637552827432759459443)
        ·
          refine ⟨72543956329241149139189165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48362637552827432759459443 72543956329241149139189165)
          ·
            refine ⟨27203983623465430927195937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72543956329241149139189165 27203983623465430927195937)
            ·
              refine ⟨20402987717599073195396953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27203983623465430927195937 20402987717599073195396953)
              ·
                refine ⟨15302240788199304896547715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20402987717599073195396953 15302240788199304896547715)
                ·
                  refine ⟨22953361182298957344821573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15302240788199304896547715 22953361182298957344821573)
                  ·
                    refine ⟨4303755221681054502154045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22953361182298957344821573 4303755221681054502154045)
                    ·
                      refine ⟨1613908208130395438307767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4303755221681054502154045 1613908208130395438307767)
                      ·
                        rfl

theorem cell23_3143075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_3143075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143075 prefixEnd_3143075 := by exact prefixLift 3143075
  have htrace : WordTrace (prefixWord ++ tailWord_3143075) baseStart_3143075 baseEnd_3143075 := by
    simpa [prefixWord, tailWord_3143075, baseEnd_3143075] using wordTrace_append hprefix tailTrace_3143075
  have hstable : (prefixWord ++ tailWord_3143075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143075).length < 2 ^ (prefixWord ++ tailWord_3143075).sum := by decide
  have hdescent : baseEnd_3143075 < baseStart_3143075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143139 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3143139 : Nat := 118140960795 + 3143139 * 2 ^ 59
def prefixEnd_3143139 : Nat := 4983230072969 + 3 ^ 40 * 3143139 * 2
def baseEnd_3143139 : Nat := 1613941070892283187907473

theorem tailTrace_3143139 : CollatzResearch.WordTrace tailWord_3143139 prefixEnd_3143139 1613941070892283187907473 := by
  unfold tailWord_3143139
  simp only [CollatzResearch.WordTrace]
  refine ⟨114639697359951683249048471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76426464906634455499365647 114639697359951683249048471)
  ·
    refine ⟨171959546039927524873572707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114639697359951683249048471 171959546039927524873572707)
    ·
      refine ⟨257939319059891287310359061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171959546039927524873572707 257939319059891287310359061)
      ·
        refine ⟨12090905580932404092673081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257939319059891287310359061 12090905580932404092673081)
        ·
          refine ⟨9068179185699303069504811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12090905580932404092673081 9068179185699303069504811)
          ·
            refine ⟨13602268778548954604257217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9068179185699303069504811 13602268778548954604257217)
            ·
              refine ⟨10201701583911715953192913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13602268778548954604257217 10201701583911715953192913)
              ·
                refine ⟨7651276187933786964894685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10201701583911715953192913 7651276187933786964894685)
                ·
                  refine ⟨2869228570475170111835507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7651276187933786964894685 2869228570475170111835507)
                  ·
                    refine ⟨4303842855712755167753261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2869228570475170111835507 4303842855712755167753261)
                    ·
                      refine ⟨1613941070892283187907473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4303842855712755167753261 1613941070892283187907473)
                      ·
                        rfl

theorem cell23_3143139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3143139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143139 prefixEnd_3143139 := by exact prefixLift 3143139
  have htrace : WordTrace (prefixWord ++ tailWord_3143139) baseStart_3143139 baseEnd_3143139 := by
    simpa [prefixWord, tailWord_3143139, baseEnd_3143139] using wordTrace_append hprefix tailTrace_3143139
  have hstable : (prefixWord ++ tailWord_3143139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143139).length < 2 ^ (prefixWord ++ tailWord_3143139).sum := by decide
  have hdescent : baseEnd_3143139 < baseStart_3143139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143145 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_3143145 : Nat := 118140960795 + 3143145 * 2 ^ 59
def prefixEnd_3143145 : Nat := 4983230072969 + 3 ^ 40 * 3143145 * 2
def baseEnd_3143145 : Nat := 1613944151776210164432445

theorem tailTrace_3143145 : CollatzResearch.WordTrace tailWord_3143145 prefixEnd_3143145 1613944151776210164432445 := by
  unfold tailWord_3143145
  simp only [CollatzResearch.WordTrace]
  refine ⟨114639916197929946273766889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76426610798619964182511259 114639916197929946273766889)
  ·
    refine ⟨85979937148447459705325167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114639916197929946273766889 85979937148447459705325167)
    ·
      refine ⟨128969905722671189557987751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85979937148447459705325167 128969905722671189557987751)
      ·
        refine ⟨193454858584006784336981627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128969905722671189557987751 193454858584006784336981627)
        ·
          refine ⟨290182287876010176505472441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193454858584006784336981627 290182287876010176505472441)
          ·
            refine ⟨217636715907007632379104331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290182287876010176505472441 217636715907007632379104331)
            ·
              refine ⟨326455073860511448568656497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217636715907007632379104331 326455073860511448568656497)
              ·
                refine ⟨244841305395383586426492373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326455073860511448568656497 244841305395383586426492373)
                ·
                  refine ⟨5738468095204302806870915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 244841305395383586426492373 5738468095204302806870915)
                  ·
                    refine ⟨8607702142806454210306373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5738468095204302806870915 8607702142806454210306373)
                    ·
                      refine ⟨1613944151776210164432445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8607702142806454210306373 1613944151776210164432445)
                      ·
                        rfl

theorem cell23_3143145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_3143145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143145 prefixEnd_3143145 := by exact prefixLift 3143145
  have htrace : WordTrace (prefixWord ++ tailWord_3143145) baseStart_3143145 baseEnd_3143145 := by
    simpa [prefixWord, tailWord_3143145, baseEnd_3143145] using wordTrace_append hprefix tailTrace_3143145
  have hstable : (prefixWord ++ tailWord_3143145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143145).length < 2 ^ (prefixWord ++ tailWord_3143145).sum := by decide
  have hdescent : baseEnd_3143145 < baseStart_3143145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143162 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_3143162 : Nat := 118140960795 + 3143162 * 2 ^ 59
def prefixEnd_3143162 : Nat := 4983230072969 + 3 ^ 40 * 3143162 * 2
def baseEnd_3143162 : Nat := 1613952880947336597919867

theorem tailTrace_3143162 : CollatzResearch.WordTrace tailWord_3143162 prefixEnd_3143162 1613952880947336597919867 := by
  unfold tailWord_3143162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28660134059717089544283935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76427024159245572118090493 28660134059717089544283935)
  ·
    refine ⟨42990201089575634316425903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28660134059717089544283935 42990201089575634316425903)
    ·
      refine ⟨64485301634363451474638855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42990201089575634316425903 64485301634363451474638855)
      ·
        refine ⟨96727952451545177211958283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64485301634363451474638855 96727952451545177211958283)
        ·
          refine ⟨145091928677317765817937425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96727952451545177211958283 145091928677317765817937425)
          ·
            refine ⟨108818946507988324363453069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145091928677317765817937425 108818946507988324363453069)
            ·
              refine ⟨40807104940495621636294901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108818946507988324363453069 40807104940495621636294901)
              ·
                refine ⟨3825666088171464528402647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40807104940495621636294901 3825666088171464528402647)
                ·
                  refine ⟨5738499132257196792603971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825666088171464528402647 5738499132257196792603971)
                  ·
                    refine ⟨8607748698385795188905957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5738499132257196792603971 8607748698385795188905957)
                    ·
                      refine ⟨1613952880947336597919867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8607748698385795188905957 1613952880947336597919867)
                      ·
                        rfl

theorem cell23_3143162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_3143162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143162 prefixEnd_3143162 := by exact prefixLift 3143162
  have htrace : WordTrace (prefixWord ++ tailWord_3143162) baseStart_3143162 baseEnd_3143162 := by
    simpa [prefixWord, tailWord_3143162, baseEnd_3143162] using wordTrace_append hprefix tailTrace_3143162
  have hstable : (prefixWord ++ tailWord_3143162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143162).length < 2 ^ (prefixWord ++ tailWord_3143162).sum := by decide
  have hdescent : baseEnd_3143162 < baseStart_3143162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143185 : List Nat := [1, 2, 2, 1, 1, 2, 6, 8]
def baseStart_3143185 : Nat := 118140960795 + 3143185 * 2 ^ 59
def prefixEnd_3143185 : Nat := 4983230072969 + 3 ^ 40 * 3143185 * 2
def baseEnd_3143185 : Nat := 59776470037125555849343

theorem tailTrace_3143185 : CollatzResearch.WordTrace tailWord_3143185 prefixEnd_3143185 59776470037125555849343 := by
  unfold tailWord_3143185
  simp only [CollatzResearch.WordTrace]
  refine ⟨114641375117785033105223009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76427583411856688736815339 114641375117785033105223009)
  ·
    refine ⟨85981031338338774828917257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114641375117785033105223009 85981031338338774828917257)
    ·
      refine ⟨64485773503754081121687943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85981031338338774828917257 64485773503754081121687943)
      ·
        refine ⟨96728660255631121682531915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64485773503754081121687943 96728660255631121682531915)
        ·
          refine ⟨145092990383446682523797873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96728660255631121682531915 145092990383446682523797873)
          ·
            refine ⟨108819742787585011892848405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145092990383446682523797873 108819742787585011892848405)
            ·
              refine ⟨5100925443168047432477269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108819742787585011892848405 5100925443168047432477269)
              ·
                refine ⟨59776470037125555849343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5100925443168047432477269 59776470037125555849343)
                ·
                  rfl

theorem cell23_3143185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 8].length) (baseStart_3143185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143185 prefixEnd_3143185 := by exact prefixLift 3143185
  have htrace : WordTrace (prefixWord ++ tailWord_3143185) baseStart_3143185 baseEnd_3143185 := by
    simpa [prefixWord, tailWord_3143185, baseEnd_3143185] using wordTrace_append hprefix tailTrace_3143185
  have hstable : (prefixWord ++ tailWord_3143185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143185).length < 2 ^ (prefixWord ++ tailWord_3143185).sum := by decide
  have hdescent : baseEnd_3143185 < baseStart_3143185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143189 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_3143189 : Nat := 118140960795 + 3143189 * 2 ^ 59
def prefixEnd_3143189 : Nat := 4983230072969 + 3 ^ 40 * 3143189 * 2
def baseEnd_3143189 : Nat := 537988914975002664094081

theorem tailTrace_3143189 : CollatzResearch.WordTrace tailWord_3143189 prefixEnd_3143189 537988914975002664094081 := by
  unfold tailWord_3143189
  simp only [CollatzResearch.WordTrace]
  refine ⟨114641521009770541788368621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76427680673180361192245747 114641521009770541788368621)
  ·
    refine ⟨42990570378663953170638233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114641521009770541788368621 42990570378663953170638233)
    ·
      refine ⟨32242927783997964877978675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42990570378663953170638233 32242927783997964877978675)
      ·
        refine ⟨48364391675996947316968013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32242927783997964877978675 48364391675996947316968013)
        ·
          refine ⟨18136646878498855243863005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48364391675996947316968013 18136646878498855243863005)
          ·
            refine ⟨6801242579437070716448627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18136646878498855243863005 6801242579437070716448627)
            ·
              refine ⟨10201863869155606074672941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6801242579437070716448627 10201863869155606074672941)
              ·
                refine ⟨3825698950933352278002353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10201863869155606074672941 3825698950933352278002353)
                ·
                  refine ⟨2869274213200014208501765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825698950933352278002353 2869274213200014208501765)
                  ·
                    refine ⟨537988914975002664094081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2869274213200014208501765 537988914975002664094081)
                    ·
                      rfl

theorem cell23_3143189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_3143189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143189 prefixEnd_3143189 := by exact prefixLift 3143189
  have htrace : WordTrace (prefixWord ++ tailWord_3143189) baseStart_3143189 baseEnd_3143189 := by
    simpa [prefixWord, tailWord_3143189, baseEnd_3143189] using wordTrace_append hprefix tailTrace_3143189
  have hstable : (prefixWord ++ tailWord_3143189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143189).length < 2 ^ (prefixWord ++ tailWord_3143189).sum := by decide
  have hdescent : baseEnd_3143189 < baseStart_3143189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143199 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 3]
def baseStart_3143199 : Nat := 118140960795 + 3143199 * 2 ^ 59
def prefixEnd_3143199 : Nat := 4983230072969 + 3 ^ 40 * 3143199 * 2
def baseEnd_3143199 : Nat := 1613971879731552953157197

theorem tailTrace_3143199 : CollatzResearch.WordTrace tailWord_3143199 prefixEnd_3143199 1613971879731552953157197 := by
  unfold tailWord_3143199
  simp only [CollatzResearch.WordTrace]
  refine ⟨114641885739734313496232651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76427923826489542330821767 114641885739734313496232651)
  ·
    refine ⟨171962828609601470244348977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114641885739734313496232651 171962828609601470244348977)
    ·
      refine ⟨128972121457201102683261733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171962828609601470244348977 128972121457201102683261733)
      ·
        refine ⟨24182272773225206753111575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128972121457201102683261733 24182272773225206753111575)
        ·
          refine ⟨36273409159837810129667363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24182272773225206753111575 36273409159837810129667363)
          ·
            refine ⟨54410113739756715194501045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36273409159837810129667363 54410113739756715194501045)
            ·
              refine ⟨5100948163102192049484473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54410113739756715194501045 5100948163102192049484473)
              ·
                refine ⟨3825711122326644037113355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100948163102192049484473 3825711122326644037113355)
                ·
                  refine ⟨5738566683489966055670033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825711122326644037113355 5738566683489966055670033)
                  ·
                    refine ⟨4303925012617474541752525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5738566683489966055670033 4303925012617474541752525)
                    ·
                      refine ⟨1613971879731552953157197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4303925012617474541752525 1613971879731552953157197)
                      ·
                        rfl

theorem cell23_3143199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_3143199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143199 prefixEnd_3143199 := by exact prefixLift 3143199
  have htrace : WordTrace (prefixWord ++ tailWord_3143199) baseStart_3143199 baseEnd_3143199 := by
    simpa [prefixWord, tailWord_3143199, baseEnd_3143199] using wordTrace_append hprefix tailTrace_3143199
  have hstable : (prefixWord ++ tailWord_3143199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143199).length < 2 ^ (prefixWord ++ tailWord_3143199).sum := by decide
  have hdescent : baseEnd_3143199 < baseStart_3143199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143252 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3143252 : Nat := 118140960795 + 3143252 * 2 ^ 59
def prefixEnd_3143252 : Nat := 4983230072969 + 3 ^ 40 * 3143252 * 2
def baseEnd_3143252 : Nat := 1613999094206241245794453

theorem tailTrace_3143252 : CollatzResearch.WordTrace tailWord_3143252 prefixEnd_3143252 1613999094206241245794453 := by
  unfold tailWord_3143252
  simp only [CollatzResearch.WordTrace]
  refine ⟨57321909404271151773956005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76429212539028202365274673 57321909404271151773956005)
  ·
    refine ⟨10747858013300840957616751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57321909404271151773956005 10747858013300840957616751)
    ·
      refine ⟨16121787019951261436425127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10747858013300840957616751 16121787019951261436425127)
      ·
        refine ⟨24182680529926892154637691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16121787019951261436425127 24182680529926892154637691)
        ·
          refine ⟨36274020794890338231956537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24182680529926892154637691 36274020794890338231956537)
          ·
            refine ⟨27205515596167753673967403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36274020794890338231956537 27205515596167753673967403)
            ·
              refine ⟨40808273394251630510951105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27205515596167753673967403 40808273394251630510951105)
              ·
                refine ⟨30606205045688722883213329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40808273394251630510951105 30606205045688722883213329)
                ·
                  refine ⟨22954653784266542162409997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30606205045688722883213329 22954653784266542162409997)
                  ·
                    refine ⟨8607995169099953310903749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22954653784266542162409997 8607995169099953310903749)
                    ·
                      refine ⟨1613999094206241245794453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8607995169099953310903749 1613999094206241245794453)
                      ·
                        rfl

theorem cell23_3143252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3143252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143252 prefixEnd_3143252 := by exact prefixLift 3143252
  have htrace : WordTrace (prefixWord ++ tailWord_3143252) baseStart_3143252 baseEnd_3143252 := by
    simpa [prefixWord, tailWord_3143252, baseEnd_3143252] using wordTrace_append hprefix tailTrace_3143252
  have hstable : (prefixWord ++ tailWord_3143252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143252).length < 2 ^ (prefixWord ++ tailWord_3143252).sum := by decide
  have hdescent : baseEnd_3143252 < baseStart_3143252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143359 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 1, 6, 2]
def baseStart_3143359 : Nat := 118140960795 + 3143359 * 2 ^ 59
def prefixEnd_3143359 : Nat := 4983230072969 + 3 ^ 40 * 3143359 * 2
def baseEnd_3143359 : Nat := 1614054036636272327156461

theorem tailTrace_3143359 : CollatzResearch.WordTrace tailWord_3143359 prefixEnd_3143359 1614054036636272327156461 := by
  unfold tailWord_3143359
  simp only [CollatzResearch.WordTrace]
  refine ⟨114647721419154660822057131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76431814279436440548038087 114647721419154660822057131)
  ·
    refine ⟨171971582128731991233085697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114647721419154660822057131 171971582128731991233085697)
    ·
      refine ⟨128978686596548993424814273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171971582128731991233085697 128978686596548993424814273)
      ·
        refine ⟨96734014947411745068610705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128978686596548993424814273 96734014947411745068610705)
        ·
          refine ⟨72550511210558808801458029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96734014947411745068610705 72550511210558808801458029)
          ·
            refine ⟨27206441703959553300546761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72550511210558808801458029 27206441703959553300546761)
            ·
              refine ⟨20404831277969664975410071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27206441703959553300546761 20404831277969664975410071)
              ·
                refine ⟨30607246916954497463115107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20404831277969664975410071 30607246916954497463115107)
                ·
                  refine ⟨45910870375431746194672661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30607246916954497463115107 45910870375431746194672661)
                  ·
                    refine ⟨2152072048848363102875281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45910870375431746194672661 2152072048848363102875281)
                    ·
                      refine ⟨1614054036636272327156461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152072048848363102875281 1614054036636272327156461)
                      ·
                        rfl

theorem cell23_3143359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_3143359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143359 prefixEnd_3143359 := by exact prefixLift 3143359
  have htrace : WordTrace (prefixWord ++ tailWord_3143359) baseStart_3143359 baseEnd_3143359 := by
    simpa [prefixWord, tailWord_3143359, baseEnd_3143359] using wordTrace_append hprefix tailTrace_3143359
  have hstable : (prefixWord ++ tailWord_3143359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143359).length < 2 ^ (prefixWord ++ tailWord_3143359).sum := by decide
  have hdescent : baseEnd_3143359 < baseStart_3143359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143373 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3143373 : Nat := 118140960795 + 3143373 * 2 ^ 59
def prefixEnd_3143373 : Nat := 4983230072969 + 3 ^ 40 * 3143373 * 2
def baseEnd_3143373 : Nat := 538020408455145090793799

theorem tailTrace_3143373 : CollatzResearch.WordTrace tailWord_3143373 prefixEnd_3143373 538020408455145090793799 := by
  unfold tailWord_3143373
  simp only [CollatzResearch.WordTrace]
  refine ⟨114648232041103941213066773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76432154694069294142044515 114648232041103941213066773)
  ·
    refine ⟨5374135876926747244362505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114648232041103941213066773 5374135876926747244362505)
    ·
      refine ⟨4030601907695060433271879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5374135876926747244362505 4030601907695060433271879)
      ·
        refine ⟨6045902861542590649907819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030601907695060433271879 6045902861542590649907819)
        ·
          refine ⟨9068854292313885974861729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045902861542590649907819 9068854292313885974861729)
          ·
            refine ⟨6801640719235414481146297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9068854292313885974861729 6801640719235414481146297)
            ·
              refine ⟨5101230539426560860859723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6801640719235414481146297 5101230539426560860859723)
              ·
                refine ⟨7651845809139841291289585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5101230539426560860859723 7651845809139841291289585)
                ·
                  refine ⟨5738884356854880968467189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7651845809139841291289585 5738884356854880968467189)
                  ·
                    refine ⟨538020408455145090793799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5738884356854880968467189 538020408455145090793799)
                    ·
                      rfl

theorem cell23_3143373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3143373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143373 prefixEnd_3143373 := by exact prefixLift 3143373
  have htrace : WordTrace (prefixWord ++ tailWord_3143373) baseStart_3143373 baseEnd_3143373 := by
    simpa [prefixWord, tailWord_3143373, baseEnd_3143373] using wordTrace_append hprefix tailTrace_3143373
  have hstable : (prefixWord ++ tailWord_3143373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143373).length < 2 ^ (prefixWord ++ tailWord_3143373).sum := by decide
  have hdescent : baseEnd_3143373 < baseStart_3143373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143403 : List Nat := [1, 1, 1, 1, 2, 4, 6, 2, 1, 4]
def baseStart_3143403 : Nat := 118140960795 + 3143403 * 2 ^ 59
def prefixEnd_3143403 : Nat := 4983230072969 + 3 ^ 40 * 3143403 * 2
def baseEnd_3143403 : Nat := 538025543261690051668753

theorem tailTrace_3143403 : CollatzResearch.WordTrace tailWord_3143403 prefixEnd_3143403 538025543261690051668753 := by
  unfold tailWord_3143403
  simp only [CollatzResearch.WordTrace]
  refine ⟨114649326230995256336658863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76432884153996837557772575 114649326230995256336658863)
  ·
    refine ⟨171973989346492884504988295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114649326230995256336658863 171973989346492884504988295)
    ·
      refine ⟨257960984019739326757482443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171973989346492884504988295 257960984019739326757482443)
      ·
        refine ⟨386941476029608990136223665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257960984019739326757482443 386941476029608990136223665)
        ·
          refine ⟨290206107022206742602167749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386941476029608990136223665 290206107022206742602167749)
          ·
            refine ⟨54413645066663764237906453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290206107022206742602167749 54413645066663764237906453)
            ·
              refine ⟨2550639612499863948651865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54413645066663764237906453 2550639612499863948651865)
              ·
                refine ⟨1912979709374897961488899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550639612499863948651865 1912979709374897961488899)
                ·
                  refine ⟨2869469564062346942233349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912979709374897961488899 2869469564062346942233349)
                  ·
                    refine ⟨538025543261690051668753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2869469564062346942233349 538025543261690051668753)
                    ·
                      rfl

theorem cell23_3143403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 4].length) (baseStart_3143403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143403 prefixEnd_3143403 := by exact prefixLift 3143403
  have htrace : WordTrace (prefixWord ++ tailWord_3143403) baseStart_3143403 baseEnd_3143403 := by
    simpa [prefixWord, tailWord_3143403, baseEnd_3143403] using wordTrace_append hprefix tailTrace_3143403
  have hstable : (prefixWord ++ tailWord_3143403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143403).length < 2 ^ (prefixWord ++ tailWord_3143403).sum := by decide
  have hdescent : baseEnd_3143403 < baseStart_3143403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143460 : List Nat := [2, 3, 1, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_3143460 : Nat := 118140960795 + 3143460 * 2 ^ 59
def prefixEnd_3143460 : Nat := 4983230072969 + 3 ^ 40 * 3143460 * 2
def baseEnd_3143460 : Nat := 1614105898182376431993497

theorem tailTrace_3143460 : CollatzResearch.WordTrace tailWord_3143460 prefixEnd_3143460 1614105898182376431993497 := by
  unfold tailWord_3143460
  simp only [CollatzResearch.WordTrace]
  refine ⟨57325702595894377535741917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76434270127859170047655889 57325702595894377535741917)
  ·
    refine ⟨21497138473460391575903219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57325702595894377535741917 21497138473460391575903219)
    ·
      refine ⟨32245707710190587363854829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21497138473460391575903219 32245707710190587363854829)
      ·
        refine ⟨12092140391321470261445561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32245707710190587363854829 12092140391321470261445561)
        ·
          refine ⟨9069105293491102696084171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12092140391321470261445561 9069105293491102696084171)
          ·
            refine ⟨13603657940236654044126257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069105293491102696084171 13603657940236654044126257)
            ·
              refine ⟨10202743455177490533094693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13603657940236654044126257 10202743455177490533094693)
              ·
                refine ⟨1913014397845779474955255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10202743455177490533094693 1913014397845779474955255)
                ·
                  refine ⟨2869521596768669212432883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913014397845779474955255 2869521596768669212432883)
                  ·
                    refine ⟨4304282395153003818649325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2869521596768669212432883 4304282395153003818649325)
                    ·
                      refine ⟨1614105898182376431993497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4304282395153003818649325 1614105898182376431993497)
                      ·
                        rfl

theorem cell23_3143460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_3143460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143460 prefixEnd_3143460 := by exact prefixLift 3143460
  have htrace : WordTrace (prefixWord ++ tailWord_3143460) baseStart_3143460 baseEnd_3143460 := by
    simpa [prefixWord, tailWord_3143460, baseEnd_3143460] using wordTrace_append hprefix tailTrace_3143460
  have hstable : (prefixWord ++ tailWord_3143460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143460).length < 2 ^ (prefixWord ++ tailWord_3143460).sum := by decide
  have hdescent : baseEnd_3143460 < baseStart_3143460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143479 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_3143479 : Nat := 118140960795 + 3143479 * 2 ^ 59
def prefixEnd_3143479 : Nat := 4983230072969 + 3 ^ 40 * 3143479 * 2
def baseEnd_3143479 : Nat := 1614115654314811857655909

theorem tailTrace_3143479 : CollatzResearch.WordTrace tailWord_3143479 prefixEnd_3143479 1614115654314811857655909 := by
  unfold tailWord_3143479
  simp only [CollatzResearch.WordTrace]
  refine ⟨114652098178719921316425491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76434732119146614210950327 114652098178719921316425491)
  ·
    refine ⟨171978147268079881974638237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114652098178719921316425491 171978147268079881974638237)
    ·
      refine ⟨64491805225529955740489339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171978147268079881974638237 64491805225529955740489339)
      ·
        refine ⟨96737707838294933610734009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64491805225529955740489339 96737707838294933610734009)
        ·
          refine ⟨72553280878721200208050507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96737707838294933610734009 72553280878721200208050507)
          ·
            refine ⟨108829921318081800312075761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72553280878721200208050507 108829921318081800312075761)
            ·
              refine ⟨81622440988561350234056821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108829921318081800312075761 81622440988561350234056821)
              ·
                refine ⟨7652103842677626584442827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81622440988561350234056821 7652103842677626584442827)
                ·
                  refine ⟨11478155764016439876664241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7652103842677626584442827 11478155764016439876664241)
                  ·
                    refine ⟨8608616823012329907498181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11478155764016439876664241 8608616823012329907498181)
                    ·
                      refine ⟨1614115654314811857655909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8608616823012329907498181 1614115654314811857655909)
                      ·
                        rfl

theorem cell23_3143479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_3143479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143479 prefixEnd_3143479 := by exact prefixLift 3143479
  have htrace : WordTrace (prefixWord ++ tailWord_3143479) baseStart_3143479 baseEnd_3143479 := by
    simpa [prefixWord, tailWord_3143479, baseEnd_3143479] using wordTrace_append hprefix tailTrace_3143479
  have hstable : (prefixWord ++ tailWord_3143479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143479).length < 2 ^ (prefixWord ++ tailWord_3143479).sum := by decide
  have hdescent : baseEnd_3143479 < baseStart_3143479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143494 : List Nat := [6, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3143494 : Nat := 118140960795 + 3143494 * 2 ^ 59
def prefixEnd_3143494 : Nat := 4983230072969 + 3 ^ 40 * 3143494 * 2
def baseEnd_3143494 : Nat := 1614123356524629298968341

theorem tailTrace_3143494 : CollatzResearch.WordTrace tailWord_3143494 prefixEnd_3143494 1614123356524629298968341 := by
  unfold tailWord_3143494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582895164802049339944423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76435096849110385918814357 3582895164802049339944423)
  ·
    refine ⟨5374342747203074009916635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3582895164802049339944423 5374342747203074009916635)
    ·
      refine ⟨8061514120804611014874953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374342747203074009916635 8061514120804611014874953)
      ·
        refine ⟨6046135590603458261156215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8061514120804611014874953 6046135590603458261156215)
        ·
          refine ⟨9069203385905187391734323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046135590603458261156215 9069203385905187391734323)
          ·
            refine ⟨13603805078857781087601485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069203385905187391734323 13603805078857781087601485)
            ·
              refine ⟨5101426904571667907850557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13603805078857781087601485 5101426904571667907850557)
              ·
                refine ⟨1913035089214375465443959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5101426904571667907850557 1913035089214375465443959)
                ·
                  refine ⟨2869552633821563198165939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913035089214375465443959 2869552633821563198165939)
                  ·
                    refine ⟨4304328950732344797248909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2869552633821563198165939 4304328950732344797248909)
                    ·
                      refine ⟨1614123356524629298968341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4304328950732344797248909 1614123356524629298968341)
                      ·
                        rfl

theorem cell23_3143494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3143494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143494 prefixEnd_3143494 := by exact prefixLift 3143494
  have htrace : WordTrace (prefixWord ++ tailWord_3143494) baseStart_3143494 baseEnd_3143494 := by
    simpa [prefixWord, tailWord_3143494, baseEnd_3143494] using wordTrace_append hprefix tailTrace_3143494
  have hstable : (prefixWord ++ tailWord_3143494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143494).length < 2 ^ (prefixWord ++ tailWord_3143494).sum := by decide
  have hdescent : baseEnd_3143494 < baseStart_3143494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143549 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_3143549 : Nat := 118140960795 + 3143549 * 2 ^ 59
def prefixEnd_3143549 : Nat := 4983230072969 + 3 ^ 40 * 3143549 * 2
def baseEnd_3143549 : Nat := 538050532653542194593529

theorem tailTrace_3143549 : CollatzResearch.WordTrace tailWord_3143549 prefixEnd_3143549 538050532653542194593529 := by
  unfold tailWord_3143549
  simp only [CollatzResearch.WordTrace]
  refine ⟨114654651288466323271473701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76436434192310882180982467 114654651288466323271473701)
  ·
    refine ⟨21497747116587435613401319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114654651288466323271473701 21497747116587435613401319)
    ·
      refine ⟨32246620674881153420101979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21497747116587435613401319 32246620674881153420101979)
      ·
        refine ⟨48369931012321730130152969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32246620674881153420101979 48369931012321730130152969)
        ·
          refine ⟨36277448259241297597614727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48369931012321730130152969 36277448259241297597614727)
          ·
            refine ⟨54416172388861946396422091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36277448259241297597614727 54416172388861946396422091)
            ·
              refine ⟨81624258583292919594633137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54416172388861946396422091 81624258583292919594633137)
              ·
                refine ⟨61218193937469689695974853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81624258583292919594633137 61218193937469689695974853)
                ·
                  refine ⟨11478411363275566817995285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61218193937469689695974853 11478411363275566817995285)
                  ·
                    refine ⟨538050532653542194593529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11478411363275566817995285 538050532653542194593529)
                    ·
                      rfl

theorem cell23_3143549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_3143549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143549 prefixEnd_3143549 := by exact prefixLift 3143549
  have htrace : WordTrace (prefixWord ++ tailWord_3143549) baseStart_3143549 baseEnd_3143549 := by
    simpa [prefixWord, tailWord_3143549, baseEnd_3143549] using wordTrace_append hprefix tailTrace_3143549
  have hstable : (prefixWord ++ tailWord_3143549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143549).length < 2 ^ (prefixWord ++ tailWord_3143549).sum := by decide
  have hdescent : baseEnd_3143549 < baseStart_3143549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143550 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3143550 : Nat := 118140960795 + 3143550 * 2 ^ 59
def prefixEnd_3143550 : Nat := 4983230072969 + 3 ^ 40 * 3143550 * 2
def baseEnd_3143550 : Nat := 1614152111441281079868083

theorem tailTrace_3143550 : CollatzResearch.WordTrace tailWord_3143550 prefixEnd_3143550 1614152111441281079868083 := by
  unfold tailWord_3143550
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331835970182837555282513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76436458507641800294840069 14331835970182837555282513)
  ·
    refine ⟨10748876977637128166461885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14331835970182837555282513 10748876977637128166461885)
    ·
      refine ⟨4030828866613923062423207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10748876977637128166461885 4030828866613923062423207)
      ·
        refine ⟨6046243299920884593634811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030828866613923062423207 6046243299920884593634811)
        ·
          refine ⟨9069364949881326890452217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046243299920884593634811 9069364949881326890452217)
          ·
            refine ⟨6802023712410995167839163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9069364949881326890452217 6802023712410995167839163)
            ·
              refine ⟨10203035568616492751758745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6802023712410995167839163 10203035568616492751758745)
              ·
                refine ⟨7652276676462369563819059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10203035568616492751758745 7652276676462369563819059)
                ·
                  refine ⟨11478415014693554345728589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7652276676462369563819059 11478415014693554345728589)
                  ·
                    refine ⟨4304405630510082879648221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11478415014693554345728589 4304405630510082879648221)
                    ·
                      refine ⟨1614152111441281079868083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4304405630510082879648221 1614152111441281079868083)
                      ·
                        rfl

theorem cell23_3143550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3143550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143550 prefixEnd_3143550 := by exact prefixLift 3143550
  have htrace : WordTrace (prefixWord ++ tailWord_3143550) baseStart_3143550 baseEnd_3143550 := by
    simpa [prefixWord, tailWord_3143550, baseEnd_3143550] using wordTrace_append hprefix tailTrace_3143550
  have hstable : (prefixWord ++ tailWord_3143550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143550).length < 2 ^ (prefixWord ++ tailWord_3143550).sum := by decide
  have hdescent : baseEnd_3143550 < baseStart_3143550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143613 : List Nat := [1, 4, 1, 2, 3, 1, 1, 5, 5]
def baseStart_3143613 : Nat := 118140960795 + 3143613 * 2 ^ 59
def prefixEnd_3143613 : Nat := 4983230072969 + 3 ^ 40 * 3143613 * 2
def baseEnd_3143613 : Nat := 179353828969168259264477

theorem tailTrace_3143613 : CollatzResearch.WordTrace tailWord_3143613 prefixEnd_3143613 179353828969168259264477 := by
  unfold tailWord_3143613
  simp only [CollatzResearch.WordTrace]
  refine ⟨114656985560234462201803493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76437990373489641467868995 114656985560234462201803493)
  ·
    refine ⟨21498184792543961662838155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114656985560234462201803493 21498184792543961662838155)
    ·
      refine ⟨32247277188815942494257233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21498184792543961662838155 32247277188815942494257233)
      ·
        refine ⟨24185457891611956870692925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32247277188815942494257233 24185457891611956870692925)
        ·
          refine ⟨9069546709354483826509847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24185457891611956870692925 9069546709354483826509847)
          ·
            refine ⟨13604320064031725739764771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069546709354483826509847 13604320064031725739764771)
            ·
              refine ⟨20406480096047588609647157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13604320064031725739764771 20406480096047588609647157)
              ·
                refine ⟨1913107509004461432154421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20406480096047588609647157 1913107509004461432154421)
                ·
                  refine ⟨179353828969168259264477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1913107509004461432154421 179353828969168259264477)
                  ·
                    rfl

theorem cell23_3143613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_3143613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143613 prefixEnd_3143613 := by exact prefixLift 3143613
  have htrace : WordTrace (prefixWord ++ tailWord_3143613) baseStart_3143613 baseEnd_3143613 := by
    simpa [prefixWord, tailWord_3143613, baseEnd_3143613] using wordTrace_append hprefix tailTrace_3143613
  have hstable : (prefixWord ++ tailWord_3143613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143613).length < 2 ^ (prefixWord ++ tailWord_3143613).sum := by decide
  have hdescent : baseEnd_3143613 < baseStart_3143613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143626 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3143626 : Nat := 118140960795 + 3143626 * 2 ^ 59
def prefixEnd_3143626 : Nat := 4983230072969 + 3 ^ 40 * 3143626 * 2
def baseEnd_3143626 : Nat := 538063711990340927505911

theorem tailTrace_3143626 : CollatzResearch.WordTrace tailWord_3143626 prefixEnd_3143626 538063711990340927505911 := by
  unfold tailWord_3143626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28664364927296841355506683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76438306472791576948017821 28664364927296841355506683)
  ·
    refine ⟨42996547390945262033260025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28664364927296841355506683 42996547390945262033260025)
    ·
      refine ⟨32247410543208946524945019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42996547390945262033260025 32247410543208946524945019)
      ·
        refine ⟨48371115814813419787417529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32247410543208946524945019 48371115814813419787417529)
        ·
          refine ⟨36278336861110064840563147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48371115814813419787417529 36278336861110064840563147)
          ·
            refine ⟨54417505291665097260844721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36278336861110064840563147 54417505291665097260844721)
            ·
              refine ⟨40813128968748822945633541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54417505291665097260844721 40813128968748822945633541)
              ·
                refine ⟨7652461681640404302306289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40813128968748822945633541 7652461681640404302306289)
                ·
                  refine ⟨5739346261230303226729717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7652461681640404302306289 5739346261230303226729717)
                  ·
                    refine ⟨538063711990340927505911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5739346261230303226729717 538063711990340927505911)
                    ·
                      rfl

theorem cell23_3143626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3143626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143626 prefixEnd_3143626 := by exact prefixLift 3143626
  have htrace : WordTrace (prefixWord ++ tailWord_3143626) baseStart_3143626 baseEnd_3143626 := by
    simpa [prefixWord, tailWord_3143626, baseEnd_3143626] using wordTrace_append hprefix tailTrace_3143626
  have hstable : (prefixWord ++ tailWord_3143626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143626).length < 2 ^ (prefixWord ++ tailWord_3143626).sum := by decide
  have hdescent : baseEnd_3143626 < baseStart_3143626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143636 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3143636 : Nat := 118140960795 + 3143636 * 2 ^ 59
def prefixEnd_3143636 : Nat := 4983230072969 + 3 ^ 40 * 3143636 * 2
def baseEnd_3143636 : Nat := 1614196270777567743392687

theorem tailTrace_3143636 : CollatzResearch.WordTrace tailWord_3143636 prefixEnd_3143636 1614196270777567743392687 := by
  unfold tailWord_3143636
  simp only [CollatzResearch.WordTrace]
  refine ⟨57328912219575568564945381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76438549626100758086593841 57328912219575568564945381)
  ·
    refine ⟨10749171041170419105927259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57328912219575568564945381 10749171041170419105927259)
    ·
      refine ⟨16123756561755628658890889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10749171041170419105927259 16123756561755628658890889)
      ·
        refine ⟨12092817421316721494168167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16123756561755628658890889 12092817421316721494168167)
        ·
          refine ⟨18139226131975082241252251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12092817421316721494168167 18139226131975082241252251)
          ·
            refine ⟨27208839197962623361878377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18139226131975082241252251 27208839197962623361878377)
            ·
              refine ⟨20406629398471967521408783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27208839197962623361878377 20406629398471967521408783)
              ·
                refine ⟨30609944097707951282113175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20406629398471967521408783 30609944097707951282113175)
                ·
                  refine ⟨45914916146561926923169763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30609944097707951282113175 45914916146561926923169763)
                  ·
                    refine ⟨68872374219842890384754645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45914916146561926923169763 68872374219842890384754645)
                    ·
                      refine ⟨1614196270777567743392687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68872374219842890384754645 1614196270777567743392687)
                      ·
                        rfl

theorem cell23_3143636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3143636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143636 prefixEnd_3143636 := by exact prefixLift 3143636
  have htrace : WordTrace (prefixWord ++ tailWord_3143636) baseStart_3143636 baseEnd_3143636 := by
    simpa [prefixWord, tailWord_3143636, baseEnd_3143636] using wordTrace_append hprefix tailTrace_3143636
  have hstable : (prefixWord ++ tailWord_3143636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143636).length < 2 ^ (prefixWord ++ tailWord_3143636).sum := by decide
  have hdescent : baseEnd_3143636 < baseStart_3143636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143733 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3143733 : Nat := 118140960795 + 3143733 * 2 ^ 59
def prefixEnd_3143733 : Nat := 4983230072969 + 3 ^ 40 * 3143733 * 2
def baseEnd_3143733 : Nat := 538082026133684621293247

theorem tailTrace_3143733 : CollatzResearch.WordTrace tailWord_3143733 prefixEnd_3143733 538082026133684621293247 := by
  unfold tailWord_3143733
  simp only [CollatzResearch.WordTrace]
  refine ⟨114661362319799722696171853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76440908213199815130781235 114661362319799722696171853)
  ·
    refine ⟨42998010869924896011064445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114661362319799722696171853 42998010869924896011064445)
    ·
      refine ⟨16124254076221836004149167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42998010869924896011064445 16124254076221836004149167)
      ·
        refine ⟨24186381114332754006223751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16124254076221836004149167 24186381114332754006223751)
        ·
          refine ⟨36279571671499131009335627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24186381114332754006223751 36279571671499131009335627)
          ·
            refine ⟨54419357507248696514003441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36279571671499131009335627 54419357507248696514003441)
            ·
              refine ⟨40814518130436522385502581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54419357507248696514003441 40814518130436522385502581)
              ·
                refine ⟨3826361074728423973640867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40814518130436522385502581 3826361074728423973640867)
                ·
                  refine ⟨5739541612092635960461301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826361074728423973640867 5739541612092635960461301)
                  ·
                    refine ⟨538082026133684621293247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5739541612092635960461301 538082026133684621293247)
                    ·
                      rfl

theorem cell23_3143733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3143733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143733 prefixEnd_3143733 := by exact prefixLift 3143733
  have htrace : WordTrace (prefixWord ++ tailWord_3143733) baseStart_3143733 baseEnd_3143733 := by
    simpa [prefixWord, tailWord_3143733, baseEnd_3143733] using wordTrace_append hprefix tailTrace_3143733
  have hstable : (prefixWord ++ tailWord_3143733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143733).length < 2 ^ (prefixWord ++ tailWord_3143733).sum := by decide
  have hdescent : baseEnd_3143733 < baseStart_3143733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143740 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_3143740 : Nat := 118140960795 + 3143740 * 2 ^ 59
def prefixEnd_3143740 : Nat := 4983230072969 + 3 ^ 40 * 3143740 * 2
def baseEnd_3143740 : Nat := 1614249672765635336492209

theorem tailTrace_3143740 : CollatzResearch.WordTrace tailWord_3143740 prefixEnd_3143740 1614249672765635336492209 := by
  unfold tailWord_3143740
  simp only [CollatzResearch.WordTrace]
  refine ⟨57330808815387181445838337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76441078420516241927784449 57330808815387181445838337)
  ·
    refine ⟨42998106611540386084378753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57330808815387181445838337 42998106611540386084378753)
    ·
      refine ⟨32248579958655289563284065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42998106611540386084378753 32248579958655289563284065)
      ·
        refine ⟨24186434968991467172463049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32248579958655289563284065 24186434968991467172463049)
        ·
          refine ⟨18139826226743600379347287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24186434968991467172463049 18139826226743600379347287)
          ·
            refine ⟨27209739340115400569020931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18139826226743600379347287 27209739340115400569020931)
            ·
              refine ⟨40814609010173100853531397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27209739340115400569020931 40814609010173100853531397)
              ·
                refine ⟨7652739189407456410037137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40814609010173100853531397 7652739189407456410037137)
                ·
                  refine ⟨5739554392055592307527853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7652739189407456410037137 5739554392055592307527853)
                  ·
                    refine ⟨2152332897020847115322945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5739554392055592307527853 2152332897020847115322945)
                    ·
                      refine ⟨1614249672765635336492209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152332897020847115322945 1614249672765635336492209)
                      ·
                        rfl

theorem cell23_3143740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_3143740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143740 prefixEnd_3143740 := by exact prefixLift 3143740
  have htrace : WordTrace (prefixWord ++ tailWord_3143740) baseStart_3143740 baseEnd_3143740 := by
    simpa [prefixWord, tailWord_3143740, baseEnd_3143740] using wordTrace_append hprefix tailTrace_3143740
  have hstable : (prefixWord ++ tailWord_3143740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143740).length < 2 ^ (prefixWord ++ tailWord_3143740).sum := by decide
  have hdescent : baseEnd_3143740 < baseStart_3143740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143750 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3143750 : Nat := 118140960795 + 3143750 * 2 ^ 59
def prefixEnd_3143750 : Nat := 4983230072969 + 3 ^ 40 * 3143750 * 2
def baseEnd_3143750 : Nat := 538084935857393432455721

theorem tailTrace_3143750 : CollatzResearch.WordTrace tailWord_3143750 prefixEnd_3143750 538084935857393432455721 := by
  unfold tailWord_3143750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583186948773066706235647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76441321573825423066360469 3583186948773066706235647)
  ·
    refine ⟨5374780423159600059353471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583186948773066706235647 5374780423159600059353471)
    ·
      refine ⟨8062170634739400089030207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374780423159600059353471 8062170634739400089030207)
      ·
        refine ⟨12093255952109100133545311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8062170634739400089030207 12093255952109100133545311)
        ·
          refine ⟨18139883928163650200317967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12093255952109100133545311 18139883928163650200317967)
          ·
            refine ⟨27209825892245475300476951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18139883928163650200317967 27209825892245475300476951)
            ·
              refine ⟨40814738838368212950715427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27209825892245475300476951 40814738838368212950715427)
              ·
                refine ⟨61222108257552319426073141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40814738838368212950715427 61222108257552319426073141)
                ·
                  refine ⟨5739572649145529946194357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61222108257552319426073141 5739572649145529946194357)
                  ·
                    refine ⟨538084935857393432455721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5739572649145529946194357 538084935857393432455721)
                    ·
                      rfl

theorem cell23_3143750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3143750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143750 prefixEnd_3143750 := by exact prefixLift 3143750
  have htrace : WordTrace (prefixWord ++ tailWord_3143750) baseStart_3143750 baseEnd_3143750 := by
    simpa [prefixWord, tailWord_3143750, baseEnd_3143750] using wordTrace_append hprefix tailTrace_3143750
  have hstable : (prefixWord ++ tailWord_3143750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143750).length < 2 ^ (prefixWord ++ tailWord_3143750).sum := by decide
  have hdescent : baseEnd_3143750 < baseStart_3143750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143783 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3143783 : Nat := 118140960795 + 3143783 * 2 ^ 59
def prefixEnd_3143783 : Nat := 4983230072969 + 3 ^ 40 * 3143783 * 2
def baseEnd_3143783 : Nat := 1614271752433778668254511

theorem tailTrace_3143783 : CollatzResearch.WordTrace tailWord_3143783 prefixEnd_3143783 1614271752433778668254511 := by
  unfold tailWord_3143783
  simp only [CollatzResearch.WordTrace]
  refine ⟨114663185969618581235492003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76442123979745720823661335 114663185969618581235492003)
  ·
    refine ⟨171994778954427871853238005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114663185969618581235492003 171994778954427871853238005)
    ·
      refine ⟨16124510526977612986241063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171994778954427871853238005 16124510526977612986241063)
      ·
        refine ⟨24186765790466419479361595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16124510526977612986241063 24186765790466419479361595)
        ·
          refine ⟨36280148685699629219042393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24186765790466419479361595 36280148685699629219042393)
          ·
            refine ⟨27210111514274721914281795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36280148685699629219042393 27210111514274721914281795)
            ·
              refine ⟨40815167271412082871422693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27210111514274721914281795 40815167271412082871422693)
              ·
                refine ⟨7652843863389765538391755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40815167271412082871422693 7652843863389765538391755)
                ·
                  refine ⟨11479265795084648307587633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7652843863389765538391755 11479265795084648307587633)
                  ·
                    refine ⟨8609449346313486230690725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11479265795084648307587633 8609449346313486230690725)
                    ·
                      refine ⟨1614271752433778668254511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8609449346313486230690725 1614271752433778668254511)
                      ·
                        rfl

theorem cell23_3143783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3143783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143783 prefixEnd_3143783 := by exact prefixLift 3143783
  have htrace : WordTrace (prefixWord ++ tailWord_3143783) baseStart_3143783 baseEnd_3143783 := by
    simpa [prefixWord, tailWord_3143783, baseEnd_3143783] using wordTrace_append hprefix tailTrace_3143783
  have hstable : (prefixWord ++ tailWord_3143783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143783).length < 2 ^ (prefixWord ++ tailWord_3143783).sum := by decide
  have hdescent : baseEnd_3143783 < baseStart_3143783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143804 : List Nat := [2, 2, 2, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_3143804 : Nat := 118140960795 + 3143804 * 2 ^ 59
def prefixEnd_3143804 : Nat := 4983230072969 + 3 ^ 40 * 3143804 * 2
def baseEnd_3143804 : Nat := 1614282535527523086091915

theorem tailTrace_3143804 : CollatzResearch.WordTrace tailWord_3143804 prefixEnd_3143804 1614282535527523086091915 := by
  unfold tailWord_3143804
  simp only [CollatzResearch.WordTrace]
  refine ⟨57331975951271250911003233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76442634601695001214670977 57331975951271250911003233)
  ·
    refine ⟨42998981963453438183252425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57331975951271250911003233 42998981963453438183252425)
    ·
      refine ⟨32249236472590078637439319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42998981963453438183252425 32249236472590078637439319)
      ·
        refine ⟨48373854708885117956158979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32249236472590078637439319 48373854708885117956158979)
        ·
          refine ⟨72560782063327676934238469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48373854708885117956158979 72560782063327676934238469)
          ·
            refine ⟨13605146636873939425169713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72560782063327676934238469 13605146636873939425169713)
            ·
              refine ⟨10203859977655454568877285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13605146636873939425169713 10203859977655454568877285)
              ·
                refine ⟨1913223745810397731664491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10203859977655454568877285 1913223745810397731664491)
                ·
                  refine ⟨2869835618715596597496737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913223745810397731664491 2869835618715596597496737)
                  ·
                    refine ⟨2152376714036697448122553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2869835618715596597496737 2152376714036697448122553)
                    ·
                      refine ⟨1614282535527523086091915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152376714036697448122553 1614282535527523086091915)
                      ·
                        rfl

theorem cell23_3143804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_3143804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143804 prefixEnd_3143804 := by exact prefixLift 3143804
  have htrace : WordTrace (prefixWord ++ tailWord_3143804) baseStart_3143804 baseEnd_3143804 := by
    simpa [prefixWord, tailWord_3143804, baseEnd_3143804] using wordTrace_append hprefix tailTrace_3143804
  have hstable : (prefixWord ++ tailWord_3143804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143804).length < 2 ^ (prefixWord ++ tailWord_3143804).sum := by decide
  have hdescent : baseEnd_3143804 < baseStart_3143804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143894 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3143894 : Nat := 118140960795 + 3143894 * 2 ^ 59
def prefixEnd_3143894 : Nat := 4983230072969 + 3 ^ 40 * 3143894 * 2
def baseEnd_3143894 : Nat := 1614328748786427733966501

theorem tailTrace_3143894 : CollatzResearch.WordTrace tailWord_3143894 prefixEnd_3143894 1614328748786427733966501 := by
  unfold tailWord_3143894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7166702154513527949548921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76444822981477631461855157 7166702154513527949548921)
  ·
    refine ⟨5375026615885145962161691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7166702154513527949548921 5375026615885145962161691)
    ·
      refine ⟨8062539923827718943242537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375026615885145962161691 8062539923827718943242537)
      ·
        refine ⟨6046904942870789207431903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8062539923827718943242537 6046904942870789207431903)
        ·
          refine ⟨9070357414306183811147855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046904942870789207431903 9070357414306183811147855)
          ·
            refine ⟨13605536121459275716721783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070357414306183811147855 13605536121459275716721783)
            ·
              refine ⟨20408304182188913575082675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13605536121459275716721783 20408304182188913575082675)
              ·
                refine ⟨30612456273283370362624013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20408304182188913575082675 30612456273283370362624013)
                ·
                  refine ⟨11479671102481263885984005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30612456273283370362624013 11479671102481263885984005)
                  ·
                    refine ⟨2152438331715236978622001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11479671102481263885984005 2152438331715236978622001)
                    ·
                      refine ⟨1614328748786427733966501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152438331715236978622001 1614328748786427733966501)
                      ·
                        rfl

theorem cell23_3143894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3143894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143894 prefixEnd_3143894 := by exact prefixLift 3143894
  have htrace : WordTrace (prefixWord ++ tailWord_3143894) baseStart_3143894 baseEnd_3143894 := by
    simpa [prefixWord, tailWord_3143894, baseEnd_3143894] using wordTrace_append hprefix tailTrace_3143894
  have hstable : (prefixWord ++ tailWord_3143894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143894).length < 2 ^ (prefixWord ++ tailWord_3143894).sum := by decide
  have hdescent : baseEnd_3143894 < baseStart_3143894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143911 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3143911 : Nat := 118140960795 + 3143911 * 2 ^ 59
def prefixEnd_3143911 : Nat := 4983230072969 + 3 ^ 40 * 3143911 * 2
def baseEnd_3143911 : Nat := 1614337477957554167453923

theorem tailTrace_3143911 : CollatzResearch.WordTrace tailWord_3143911 prefixEnd_3143911 1614337477957554167453923 := by
  unfold tailWord_3143911
  simp only [CollatzResearch.WordTrace]
  refine ⟨114667854513154859096151587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76445236342103239397434391 114667854513154859096151587)
  ·
    refine ⟨172001781769732288644227381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114667854513154859096151587 172001781769732288644227381)
    ·
      refine ⟨16125167040912402060396317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172001781769732288644227381 16125167040912402060396317)
      ·
        refine ⟨6046937640342150772648619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16125167040912402060396317 6046937640342150772648619)
        ·
          refine ⟨9070406460513226158972929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046937640342150772648619 9070406460513226158972929)
          ·
            refine ⟨6802804845384919619229697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9070406460513226158972929 6802804845384919619229697)
            ·
              refine ⟨5102103634038689714422273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6802804845384919619229697 5102103634038689714422273)
              ·
                refine ⟨3826577725529017285816705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5102103634038689714422273 3826577725529017285816705)
                ·
                  refine ⟨2869933294146762964362529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826577725529017285816705 2869933294146762964362529)
                  ·
                    refine ⟨2152449970610072223271897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2869933294146762964362529 2152449970610072223271897)
                    ·
                      refine ⟨1614337477957554167453923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152449970610072223271897 1614337477957554167453923)
                      ·
                        rfl

theorem cell23_3143911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3143911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143911 prefixEnd_3143911 := by exact prefixLift 3143911
  have htrace : WordTrace (prefixWord ++ tailWord_3143911) baseStart_3143911 baseEnd_3143911 := by
    simpa [prefixWord, tailWord_3143911, baseEnd_3143911] using wordTrace_append hprefix tailTrace_3143911
  have hstable : (prefixWord ++ tailWord_3143911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143911).length < 2 ^ (prefixWord ++ tailWord_3143911).sum := by decide
  have hdescent : baseEnd_3143911 < baseStart_3143911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143923 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5]
def baseStart_3143923 : Nat := 118140960795 + 3143923 * 2 ^ 59
def prefixEnd_3143923 : Nat := 4983230072969 + 3 ^ 40 * 3143923 * 2
def baseEnd_3143923 : Nat := 1614343639725408120503867

theorem tailTrace_3143923 : CollatzResearch.WordTrace tailWord_3143923 prefixEnd_3143923 1614343639725408120503867 := by
  unfold tailWord_3143923
  simp only [CollatzResearch.WordTrace]
  refine ⟨114668292189111385145588423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76445528126074256763725615 114668292189111385145588423)
  ·
    refine ⟨172002438283667077718382635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114668292189111385145588423 172002438283667077718382635)
    ·
      refine ⟨258003657425500616577573953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172002438283667077718382635 258003657425500616577573953)
      ·
        refine ⟨193502743069125462433180465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258003657425500616577573953 193502743069125462433180465)
        ·
          refine ⟨145127057301844096824885349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193502743069125462433180465 145127057301844096824885349)
          ·
            refine ⟨27211323244095768154666003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145127057301844096824885349 27211323244095768154666003)
            ·
              refine ⟨40816984866143652231999005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27211323244095768154666003 40816984866143652231999005)
              ·
                refine ⟨15306369324803869586999627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40816984866143652231999005 15306369324803869586999627)
                ·
                  refine ⟨22959553987205804380499441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15306369324803869586999627 22959553987205804380499441)
                  ·
                    refine ⟨17219665490404353285374581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22959553987205804380499441 17219665490404353285374581)
                    ·
                      refine ⟨1614343639725408120503867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17219665490404353285374581 1614343639725408120503867)
                      ·
                        rfl

theorem cell23_3143923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_3143923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143923 prefixEnd_3143923 := by exact prefixLift 3143923
  have htrace : WordTrace (prefixWord ++ tailWord_3143923) baseStart_3143923 baseEnd_3143923 := by
    simpa [prefixWord, tailWord_3143923, baseEnd_3143923] using wordTrace_append hprefix tailTrace_3143923
  have hstable : (prefixWord ++ tailWord_3143923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143923).length < 2 ^ (prefixWord ++ tailWord_3143923).sum := by decide
  have hdescent : baseEnd_3143923 < baseStart_3143923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143950 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3143950 : Nat := 118140960795 + 3143950 * 2 ^ 59
def prefixEnd_3143950 : Nat := 4983230072969 + 3 ^ 40 * 3143950 * 2
def baseEnd_3143950 : Nat := 1614357503703079514866243

theorem tailTrace_3143950 : CollatzResearch.WordTrace tailWord_3143950 prefixEnd_3143950 1614357503703079514866243 := by
  unfold tailWord_3143950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14333659620001696094602663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76446184640009045837880869 14333659620001696094602663)
  ·
    refine ⟨21500489430002544141903995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14333659620001696094602663 21500489430002544141903995)
    ·
      refine ⟨32250734145003816212855993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21500489430002544141903995 32250734145003816212855993)
      ·
        refine ⟨24188050608752862159641995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32250734145003816212855993 24188050608752862159641995)
        ·
          refine ⟨36282075913129293239462993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24188050608752862159641995 36282075913129293239462993)
          ·
            refine ⟨27211556934846969929597245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36282075913129293239462993 27211556934846969929597245)
            ·
              refine ⟨10204333850567613723598967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27211556934846969929597245 10204333850567613723598967)
              ·
                refine ⟨15306500775851420585398451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10204333850567613723598967 15306500775851420585398451)
                ·
                  refine ⟨22959751163777130878097677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15306500775851420585398451 22959751163777130878097677)
                  ·
                    refine ⟨8609906686416424079286629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22959751163777130878097677 8609906686416424079286629)
                    ·
                      refine ⟨1614357503703079514866243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8609906686416424079286629 1614357503703079514866243)
                      ·
                        rfl

theorem cell23_3143950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3143950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143950 prefixEnd_3143950 := by exact prefixLift 3143950
  have htrace : WordTrace (prefixWord ++ tailWord_3143950) baseStart_3143950 baseEnd_3143950 := by
    simpa [prefixWord, tailWord_3143950, baseEnd_3143950] using wordTrace_append hprefix tailTrace_3143950
  have hstable : (prefixWord ++ tailWord_3143950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143950).length < 2 ^ (prefixWord ++ tailWord_3143950).sum := by decide
  have hdescent : baseEnd_3143950 < baseStart_3143950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143960 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 5, 4]
def baseStart_3143960 : Nat := 118140960795 + 3143960 * 2 ^ 59
def prefixEnd_3143960 : Nat := 4983230072969 + 3 ^ 40 * 3143960 * 2
def baseEnd_3143960 : Nat := 538120879503208158580399

theorem tailTrace_3143960 : CollatzResearch.WordTrace tailWord_3143960 prefixEnd_3143960 538120879503208158580399 := by
  unfold tailWord_3143960
  simp only [CollatzResearch.WordTrace]
  refine ⟨57334820844988670232342667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76446427793318226976456889 57334820844988670232342667)
  ·
    refine ⟨86002231267483005348514001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57334820844988670232342667 86002231267483005348514001)
    ·
      refine ⟨64501673450612254011385501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86002231267483005348514001 64501673450612254011385501)
      ·
        refine ⟨24188127543979595254269563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64501673450612254011385501 24188127543979595254269563)
        ·
          refine ⟨36282191315969392881404345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24188127543979595254269563 36282191315969392881404345)
          ·
            refine ⟨27211643486977044661053259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36282191315969392881404345 27211643486977044661053259)
            ·
              refine ⟨40817465230465566991579889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27211643486977044661053259 40817465230465566991579889)
              ·
                refine ⟨30613098922849175243684917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40817465230465566991579889 30613098922849175243684917)
                ·
                  refine ⟨2869978024017110179095461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30613098922849175243684917 2869978024017110179095461)
                  ·
                    refine ⟨538120879503208158580399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2869978024017110179095461 538120879503208158580399)
                    ·
                      rfl

theorem cell23_3143960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_3143960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143960 prefixEnd_3143960 := by exact prefixLift 3143960
  have htrace : WordTrace (prefixWord ++ tailWord_3143960) baseStart_3143960 baseEnd_3143960 := by
    simpa [prefixWord, tailWord_3143960, baseEnd_3143960] using wordTrace_append hprefix tailTrace_3143960
  have hstable : (prefixWord ++ tailWord_3143960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143960).length < 2 ^ (prefixWord ++ tailWord_3143960).sum := by decide
  have hdescent : baseEnd_3143960 < baseStart_3143960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143963 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6]
def baseStart_3143963 : Nat := 118140960795 + 3143963 * 2 ^ 59
def prefixEnd_3143963 : Nat := 4983230072969 + 3 ^ 40 * 3143963 * 2
def baseEnd_3143963 : Nat := 1614364178951587964003683

theorem tailTrace_3143963 : CollatzResearch.WordTrace tailWord_3143963 prefixEnd_3143963 1614364178951587964003683 := by
  unfold tailWord_3143963
  simp only [CollatzResearch.WordTrace]
  refine ⟨114669751108966471977044543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76446500739310981318029695 114669751108966471977044543)
  ·
    refine ⟨172004626663449707965566815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114669751108966471977044543 172004626663449707965566815)
    ·
      refine ⟨258006939995174561948350223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172004626663449707965566815 258006939995174561948350223)
      ·
        refine ⟨387010409992761842922525335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258006939995174561948350223 387010409992761842922525335)
        ·
          refine ⟨580515614989142764383788003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387010409992761842922525335 580515614989142764383788003)
          ·
            refine ⟨870773422483714146575682005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580515614989142764383788003 870773422483714146575682005)
            ·
              refine ⟨20408752089462050310367547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 870773422483714146575682005 20408752089462050310367547)
              ·
                refine ⟨30613128134193075465551321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20408752089462050310367547 30613128134193075465551321)
                ·
                  refine ⟨22959846100644806599163491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30613128134193075465551321 22959846100644806599163491)
                  ·
                    refine ⟨34439769150967209898745237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22959846100644806599163491 34439769150967209898745237)
                    ·
                      refine ⟨1614364178951587964003683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34439769150967209898745237 1614364178951587964003683)
                      ·
                        rfl

theorem cell23_3143963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_3143963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143963 prefixEnd_3143963 := by exact prefixLift 3143963
  have htrace : WordTrace (prefixWord ++ tailWord_3143963) baseStart_3143963 baseEnd_3143963 := by
    simpa [prefixWord, tailWord_3143963, baseEnd_3143963] using wordTrace_append hprefix tailTrace_3143963
  have hstable : (prefixWord ++ tailWord_3143963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143963).length < 2 ^ (prefixWord ++ tailWord_3143963).sum := by decide
  have hdescent : baseEnd_3143963 < baseStart_3143963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143967 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 2, 4, 2]
def baseStart_3143967 : Nat := 118140960795 + 3143967 * 2 ^ 59
def prefixEnd_3143967 : Nat := 4983230072969 + 3 ^ 40 * 3143967 * 2
def baseEnd_3143967 : Nat := 1614366232874205948353665

theorem tailTrace_3143967 : CollatzResearch.WordTrace tailWord_3143967 prefixEnd_3143967 1614366232874205948353665 := by
  unfold tailWord_3143967
  simp only [CollatzResearch.WordTrace]
  refine ⟨114669897000951980660190155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76446598000634653773460103 114669897000951980660190155)
  ·
    refine ⟨172004845501427970990285233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114669897000951980660190155 172004845501427970990285233)
    ·
      refine ⟨129003634126070978242713925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172004845501427970990285233 129003634126070978242713925)
      ·
        refine ⟨24188181398638308420508861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129003634126070978242713925 24188181398638308420508861)
        ·
          refine ⟨9070568024489365657690823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24188181398638308420508861 9070568024489365657690823)
          ·
            refine ⟨13605852036734048486536235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070568024489365657690823 13605852036734048486536235)
            ·
              refine ⟨20408778055101072729804353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13605852036734048486536235 20408778055101072729804353)
              ·
                refine ⟨15306583541325804547353265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20408778055101072729804353 15306583541325804547353265)
                ·
                  refine ⟨11479937655994353410514949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15306583541325804547353265 11479937655994353410514949)
                  ·
                    refine ⟨2152488310498941264471553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11479937655994353410514949 2152488310498941264471553)
                    ·
                      refine ⟨1614366232874205948353665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152488310498941264471553 1614366232874205948353665)
                      ·
                        rfl

theorem cell23_3143967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_3143967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3143967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3143967 prefixEnd_3143967 := by exact prefixLift 3143967
  have htrace : WordTrace (prefixWord ++ tailWord_3143967) baseStart_3143967 baseEnd_3143967 := by
    simpa [prefixWord, tailWord_3143967, baseEnd_3143967] using wordTrace_append hprefix tailTrace_3143967
  have hstable : (prefixWord ++ tailWord_3143967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143967).length < 2 ^ (prefixWord ++ tailWord_3143967).sum := by decide
  have hdescent : baseEnd_3143967 < baseStart_3143967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144028 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_3144028 : Nat := 118140960795 + 3144028 * 2 ^ 59
def prefixEnd_3144028 : Nat := 4983230072969 + 3 ^ 40 * 3144028 * 2
def baseEnd_3144028 : Nat := 538132518398043403230295

theorem tailTrace_3144028 : CollatzResearch.WordTrace tailWord_3144028 prefixEnd_3144028 538132518398043403230295 := by
  unfold tailWord_3144028
  simp only [CollatzResearch.WordTrace]
  refine ⟨57336060926865494039080369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76448081235820658718773825 57336060926865494039080369)
  ·
    refine ⟨43002045695149120529310277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57336060926865494039080369 43002045695149120529310277)
    ·
      refine ⟨8062883567840460099245677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43002045695149120529310277 8062883567840460099245677)
      ·
        refine ⟨3023581337940172537217129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8062883567840460099245677 3023581337940172537217129)
        ·
          refine ⟨2267686003455129402912847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3023581337940172537217129 2267686003455129402912847)
          ·
            refine ⟨3401529005182694104369271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267686003455129402912847 3401529005182694104369271)
            ·
              refine ⟨5102293507774041156553907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401529005182694104369271 5102293507774041156553907)
              ·
                refine ⟨7653440261661061734830861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102293507774041156553907 7653440261661061734830861)
                ·
                  refine ⟨2870040098122898150561573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7653440261661061734830861 2870040098122898150561573)
                  ·
                    refine ⟨538132518398043403230295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2870040098122898150561573 538132518398043403230295)
                    ·
                      rfl

theorem cell23_3144028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_3144028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144028 prefixEnd_3144028 := by exact prefixLift 3144028
  have htrace : WordTrace (prefixWord ++ tailWord_3144028) baseStart_3144028 baseEnd_3144028 := by
    simpa [prefixWord, tailWord_3144028, baseEnd_3144028] using wordTrace_append hprefix tailTrace_3144028
  have hstable : (prefixWord ++ tailWord_3144028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144028).length < 2 ^ (prefixWord ++ tailWord_3144028).sum := by decide
  have hdescent : baseEnd_3144028 < baseStart_3144028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144067 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 1, 6]
def baseStart_3144067 : Nat := 118140960795 + 3144067 * 2 ^ 59
def prefixEnd_3144067 : Nat := 4983230072969 + 3 ^ 40 * 3144067 * 2
def baseEnd_3144067 : Nat := 538139193646551852367735

theorem tailTrace_3144067 : CollatzResearch.WordTrace tailWord_3144067 prefixEnd_3144067 538139193646551852367735 := by
  unfold tailWord_3144067
  simp only [CollatzResearch.WordTrace]
  refine ⟨114673544300589697738830455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76449029533726465159220303 114673544300589697738830455)
  ·
    refine ⟨172010316450884546608245683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114673544300589697738830455 172010316450884546608245683)
    ·
      refine ⟨258015474676326819912368525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172010316450884546608245683 258015474676326819912368525)
      ·
        refine ⟨96755803003622557467138197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258015474676326819912368525 96755803003622557467138197)
        ·
          refine ⟨4535428265794807381272103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96755803003622557467138197 4535428265794807381272103)
          ·
            refine ⟨6803142398692211071908155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535428265794807381272103 6803142398692211071908155)
            ·
              refine ⟨10204713598038316607862233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803142398692211071908155 10204713598038316607862233)
              ·
                refine ⟨7653535198528737455896675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10204713598038316607862233 7653535198528737455896675)
                ·
                  refine ⟨11480302797793106183845013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7653535198528737455896675 11480302797793106183845013)
                  ·
                    refine ⟨538139193646551852367735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11480302797793106183845013 538139193646551852367735)
                    ·
                      rfl

theorem cell23_3144067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 6].length) (baseStart_3144067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144067 prefixEnd_3144067 := by exact prefixLift 3144067
  have htrace : WordTrace (prefixWord ++ tailWord_3144067) baseStart_3144067 baseEnd_3144067 := by
    simpa [prefixWord, tailWord_3144067, baseEnd_3144067] using wordTrace_append hprefix tailTrace_3144067
  have hstable : (prefixWord ++ tailWord_3144067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144067).length < 2 ^ (prefixWord ++ tailWord_3144067).sum := by decide
  have hdescent : baseEnd_3144067 < baseStart_3144067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144100 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3144100 : Nat := 118140960795 + 3144100 * 2 ^ 59
def prefixEnd_3144100 : Nat := 4983230072969 + 3 ^ 40 * 3144100 * 2
def baseEnd_3144100 : Nat := 1614434525801253927990553

theorem tailTrace_3144100 : CollatzResearch.WordTrace tailWord_3144100 prefixEnd_3144100 1614434525801253927990553 := by
  unfold tailWord_3144100
  simp only [CollatzResearch.WordTrace]
  refine ⟨57337373954735072187390877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76449831939646762916521169 57337373954735072187390877)
  ·
    refine ⟨21501515233025652070271579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57337373954735072187390877 21501515233025652070271579)
    ·
      refine ⟨32252272849538478105407369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21501515233025652070271579 32252272849538478105407369)
      ·
        refine ⟨24189204637153858579055527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32252272849538478105407369 24189204637153858579055527)
        ·
          refine ⟨36283806955730787868583291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24189204637153858579055527 36283806955730787868583291)
          ·
            refine ⟨54425710433596181802874937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36283806955730787868583291 54425710433596181802874937)
            ·
              refine ⟨40819282825197136352156203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54425710433596181802874937 40819282825197136352156203)
              ·
                refine ⟨61228924237795704528234305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40819282825197136352156203 61228924237795704528234305)
                ·
                  refine ⟨45921693178346778396175729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61228924237795704528234305 45921693178346778396175729)
                  ·
                    refine ⟨34441269883760083797131797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45921693178346778396175729 34441269883760083797131797)
                    ·
                      refine ⟨1614434525801253927990553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34441269883760083797131797 1614434525801253927990553)
                      ·
                        rfl

theorem cell23_3144100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3144100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144100 prefixEnd_3144100 := by exact prefixLift 3144100
  have htrace : WordTrace (prefixWord ++ tailWord_3144100) baseStart_3144100 baseEnd_3144100 := by
    simpa [prefixWord, tailWord_3144100, baseEnd_3144100] using wordTrace_append hprefix tailTrace_3144100
  have hstable : (prefixWord ++ tailWord_3144100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144100).length < 2 ^ (prefixWord ++ tailWord_3144100).sum := by decide
  have hdescent : baseEnd_3144100 < baseStart_3144100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144104 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3144104 : Nat := 118140960795 + 3144104 * 2 ^ 59
def prefixEnd_3144104 : Nat := 4983230072969 + 3 ^ 40 * 3144104 * 2
def baseEnd_3144104 : Nat := 1614436579723871912340535

theorem tailTrace_3144104 : CollatzResearch.WordTrace tailWord_3144104 prefixEnd_3144104 1614436579723871912340535 := by
  unfold tailWord_3144104
  simp only [CollatzResearch.WordTrace]
  refine ⟨57337446900727826528963683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76449929200970435371951577 57337446900727826528963683)
  ·
    refine ⟨86006170351091739793445525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57337446900727826528963683 86006170351091739793445525)
    ·
      refine ⟨4031539235207425302817759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86006170351091739793445525 4031539235207425302817759)
      ·
        refine ⟨6047308852811137954226639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4031539235207425302817759 6047308852811137954226639)
        ·
          refine ⟨9070963279216706931339959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047308852811137954226639 9070963279216706931339959)
          ·
            refine ⟨13606444918825060397009939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070963279216706931339959 13606444918825060397009939)
            ·
              refine ⟨20409667378237590595514909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13606444918825060397009939 20409667378237590595514909)
              ·
                refine ⟨7653625266839096473318091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20409667378237590595514909 7653625266839096473318091)
                ·
                  refine ⟨11480437900258644709977137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7653625266839096473318091 11480437900258644709977137)
                  ·
                    refine ⟨8610328425193983532482853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11480437900258644709977137 8610328425193983532482853)
                    ·
                      refine ⟨1614436579723871912340535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8610328425193983532482853 1614436579723871912340535)
                      ·
                        rfl

theorem cell23_3144104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3144104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144104 prefixEnd_3144104 := by exact prefixLift 3144104
  have htrace : WordTrace (prefixWord ++ tailWord_3144104) baseStart_3144104 baseEnd_3144104 := by
    simpa [prefixWord, tailWord_3144104, baseEnd_3144104] using wordTrace_append hprefix tailTrace_3144104
  have hstable : (prefixWord ++ tailWord_3144104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144104).length < 2 ^ (prefixWord ++ tailWord_3144104).sum := by decide
  have hdescent : baseEnd_3144104 < baseStart_3144104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144120 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3144120 : Nat := 118140960795 + 3144120 * 2 ^ 59
def prefixEnd_3144120 : Nat := 4983230072969 + 3 ^ 40 * 3144120 * 2
def baseEnd_3144120 : Nat := 1614444795414343849740461

theorem tailTrace_3144120 : CollatzResearch.WordTrace tailWord_3144120 prefixEnd_3144120 1614444795414343849740461 := by
  unfold tailWord_3144120
  simp only [CollatzResearch.WordTrace]
  refine ⟨57337738684698843895254907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76450318246265125193673209 57337738684698843895254907)
  ·
    refine ⟨86006608027048265842882361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57337738684698843895254907 86006608027048265842882361)
    ·
      refine ⟨64504956020286199382161771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86006608027048265842882361 64504956020286199382161771)
      ·
        refine ⟨96757434030429299073242657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64504956020286199382161771 96757434030429299073242657)
        ·
          refine ⟨72568075522821974304931993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96757434030429299073242657 72568075522821974304931993)
          ·
            refine ⟨54426056642116480728698995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72568075522821974304931993 54426056642116480728698995)
            ·
              refine ⟨81639084963174721093048493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54426056642116480728698995 81639084963174721093048493)
              ·
                refine ⟨30614656861190520409893185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81639084963174721093048493 30614656861190520409893185)
                ·
                  refine ⟨22960992645892890307419889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30614656861190520409893185 22960992645892890307419889)
                  ·
                    refine ⟨17220744484419667730564917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22960992645892890307419889 17220744484419667730564917)
                    ·
                      refine ⟨1614444795414343849740461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17220744484419667730564917 1614444795414343849740461)
                      ·
                        rfl

theorem cell23_3144120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3144120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144120 prefixEnd_3144120 := by exact prefixLift 3144120
  have htrace : WordTrace (prefixWord ++ tailWord_3144120) baseStart_3144120 baseEnd_3144120 := by
    simpa [prefixWord, tailWord_3144120, baseEnd_3144120] using wordTrace_append hprefix tailTrace_3144120
  have hstable : (prefixWord ++ tailWord_3144120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144120).length < 2 ^ (prefixWord ++ tailWord_3144120).sum := by decide
  have hdescent : baseEnd_3144120 < baseStart_3144120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144124 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3144124 : Nat := 118140960795 + 3144124 * 2 ^ 59
def prefixEnd_3144124 : Nat := 4983230072969 + 3 ^ 40 * 3144124 * 2
def baseEnd_3144124 : Nat := 1614446849336961834090443

theorem tailTrace_3144124 : CollatzResearch.WordTrace tailWord_3144124 prefixEnd_3144124 1614446849336961834090443 := by
  unfold tailWord_3144124
  simp only [CollatzResearch.WordTrace]
  refine ⟨57337811630691598236827713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76450415507588797649103617 57337811630691598236827713)
  ·
    refine ⟨43003358723018698677620785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57337811630691598236827713 43003358723018698677620785)
    ·
      refine ⟨32252519042264024008215589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43003358723018698677620785 32252519042264024008215589)
      ·
        refine ⟨6047347320424504501540423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32252519042264024008215589 6047347320424504501540423)
        ·
          refine ⟨9071020980636756752310635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047347320424504501540423 9071020980636756752310635)
          ·
            refine ⟨13606531470955135128465953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9071020980636756752310635 13606531470955135128465953)
            ·
              refine ⟨10204898603216351346349465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13606531470955135128465953 10204898603216351346349465)
              ·
                refine ⟨7653673952412263509762099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10204898603216351346349465 7653673952412263509762099)
                ·
                  refine ⟨11480510928618395264643149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7653673952412263509762099 11480510928618395264643149)
                  ·
                    refine ⟨4305191598231898224241181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11480510928618395264643149 4305191598231898224241181)
                    ·
                      refine ⟨1614446849336961834090443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4305191598231898224241181 1614446849336961834090443)
                      ·
                        rfl

theorem cell23_3144124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3144124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144124 prefixEnd_3144124 := by exact prefixLift 3144124
  have htrace : WordTrace (prefixWord ++ tailWord_3144124) baseStart_3144124 baseEnd_3144124 := by
    simpa [prefixWord, tailWord_3144124, baseEnd_3144124] using wordTrace_append hprefix tailTrace_3144124
  have hstable : (prefixWord ++ tailWord_3144124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144124).length < 2 ^ (prefixWord ++ tailWord_3144124).sum := by decide
  have hdescent : baseEnd_3144124 < baseStart_3144124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144157 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_3144157 : Nat := 118140960795 + 3144157 * 2 ^ 59
def prefixEnd_3144157 : Nat := 4983230072969 + 3 ^ 40 * 3144157 * 2
def baseEnd_3144157 : Nat := 538154598066186734992597

theorem tailTrace_3144157 : CollatzResearch.WordTrace tailWord_3144157 prefixEnd_3144157 538154598066186734992597 := by
  unfold tailWord_3144157
  simp only [CollatzResearch.WordTrace]
  refine ⟨114676826870263643109606725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76451217913509095406404483 114676826870263643109606725)
  ·
    refine ⟨21501905038174433083051261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114676826870263643109606725 21501905038174433083051261)
    ·
      refine ⟨8063214389315412406144223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21501905038174433083051261 8063214389315412406144223)
      ·
        refine ⟨12094821583973118609216335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063214389315412406144223 12094821583973118609216335)
        ·
          refine ⟨18142232375959677913824503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12094821583973118609216335 18142232375959677913824503)
          ·
            refine ⟨27213348563939516870736755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18142232375959677913824503 27213348563939516870736755)
            ·
              refine ⟨40820022845909275306105133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27213348563939516870736755 40820022845909275306105133)
              ·
                refine ⟨15307508567215978239789425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40820022845909275306105133 15307508567215978239789425)
                ·
                  refine ⟨11480631425411983679842069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15307508567215978239789425 11480631425411983679842069)
                  ·
                    refine ⟨538154598066186734992597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11480631425411983679842069 538154598066186734992597)
                    ·
                      rfl

theorem cell23_3144157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_3144157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144157 prefixEnd_3144157 := by exact prefixLift 3144157
  have htrace : WordTrace (prefixWord ++ tailWord_3144157) baseStart_3144157 baseEnd_3144157 := by
    simpa [prefixWord, tailWord_3144157, baseEnd_3144157] using wordTrace_append hprefix tailTrace_3144157
  have hstable : (prefixWord ++ tailWord_3144157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144157).length < 2 ^ (prefixWord ++ tailWord_3144157).sum := by decide
  have hdescent : baseEnd_3144157 < baseStart_3144157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144167 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3144167 : Nat := 118140960795 + 3144167 * 2 ^ 59
def prefixEnd_3144167 : Nat := 4983230072969 + 3 ^ 40 * 3144167 * 2
def baseEnd_3144167 : Nat := 1614468929005105165852745

theorem tailTrace_3144167 : CollatzResearch.WordTrace tailWord_3144167 prefixEnd_3144167 1614468929005105165852745 := by
  unfold tailWord_3144167
  simp only [CollatzResearch.WordTrace]
  refine ⟨114677191600227414817470755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76451461066818276544980503 114677191600227414817470755)
  ·
    refine ⟨172015787400341122226206133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114677191600227414817470755 172015787400341122226206133)
    ·
      refine ⟨16126480068781980208706825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172015787400341122226206133 16126480068781980208706825)
      ·
        refine ⟨12094860051586485156530119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16126480068781980208706825 12094860051586485156530119)
        ·
          refine ⟨18142290077379727734795179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12094860051586485156530119 18142290077379727734795179)
          ·
            refine ⟨27213435116069591602192769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18142290077379727734795179 27213435116069591602192769)
            ·
              refine ⟨20410076337052193701644577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27213435116069591602192769 20410076337052193701644577)
              ·
                refine ⟨15307557252789145276233433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20410076337052193701644577 15307557252789145276233433)
                ·
                  refine ⟨11480667939591858957175075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15307557252789145276233433 11480667939591858957175075)
                  ·
                    refine ⟨17221001909387788435762613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11480667939591858957175075 17221001909387788435762613)
                    ·
                      refine ⟨1614468929005105165852745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17221001909387788435762613 1614468929005105165852745)
                      ·
                        rfl

theorem cell23_3144167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3144167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144167 prefixEnd_3144167 := by exact prefixLift 3144167
  have htrace : WordTrace (prefixWord ++ tailWord_3144167) baseStart_3144167 baseEnd_3144167 := by
    simpa [prefixWord, tailWord_3144167, baseEnd_3144167] using wordTrace_append hprefix tailTrace_3144167
  have hstable : (prefixWord ++ tailWord_3144167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144167).length < 2 ^ (prefixWord ++ tailWord_3144167).sum := by decide
  have hdescent : baseEnd_3144167 < baseStart_3144167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144197 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_3144197 : Nat := 118140960795 + 3144197 * 2 ^ 59
def prefixEnd_3144197 : Nat := 4983230072969 + 3 ^ 40 * 3144197 * 2
def baseEnd_3144197 : Nat := 1614484333424740048477607

theorem tailTrace_3144197 : CollatzResearch.WordTrace tailWord_3144197 prefixEnd_3144197 1614484333424740048477607 := by
  unfold tailWord_3144197
  simp only [CollatzResearch.WordTrace]
  refine ⟨114678285790118729941062845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76452190526745819960708563 114678285790118729941062845)
  ·
    refine ⟨43004357171294523727898567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114678285790118729941062845 43004357171294523727898567)
    ·
      refine ⟨64506535756941785591847851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43004357171294523727898567 64506535756941785591847851)
      ·
        refine ⟨96759803635412678387771777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64506535756941785591847851 96759803635412678387771777)
        ·
          refine ⟨72569852726559508790828833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96759803635412678387771777 72569852726559508790828833)
          ·
            refine ⟨54427389544919631593121625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72569852726559508790828833 54427389544919631593121625)
            ·
              refine ⟨40820542158689723694841219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54427389544919631593121625 40820542158689723694841219)
              ·
                refine ⟨61230813238034585542261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40820542158689723694841219 61230813238034585542261829)
                ·
                  refine ⟨11480777482131484789174093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61230813238034585542261829 11480777482131484789174093)
                  ·
                    refine ⟨4305291555799306795940285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11480777482131484789174093 4305291555799306795940285)
                    ·
                      refine ⟨1614484333424740048477607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4305291555799306795940285 1614484333424740048477607)
                      ·
                        rfl

theorem cell23_3144197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_3144197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144197 prefixEnd_3144197 := by exact prefixLift 3144197
  have htrace : WordTrace (prefixWord ++ tailWord_3144197) baseStart_3144197 baseEnd_3144197 := by
    simpa [prefixWord, tailWord_3144197, baseEnd_3144197] using wordTrace_append hprefix tailTrace_3144197
  have hstable : (prefixWord ++ tailWord_3144197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144197).length < 2 ^ (prefixWord ++ tailWord_3144197).sum := by decide
  have hdescent : baseEnd_3144197 < baseStart_3144197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144204 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 7]
def baseStart_3144204 : Nat := 118140960795 + 3144204 * 2 ^ 59
def prefixEnd_3144204 : Nat := 4983230072969 + 3 ^ 40 * 3144204 * 2
def baseEnd_3144204 : Nat := 179387547532146835676675

theorem tailTrace_3144204 : CollatzResearch.WordTrace tailWord_3144204 prefixEnd_3144204 179387547532146835676675 := by
  unfold tailWord_3144204
  simp only [CollatzResearch.WordTrace]
  refine ⟨57339270550546685068283833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76452360734062246757711777 57339270550546685068283833)
  ·
    refine ⟨43004452912910013801212875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57339270550546685068283833 43004452912910013801212875)
    ·
      refine ⟨64506679369365020701819313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43004452912910013801212875 64506679369365020701819313)
      ·
        refine ⟨48380009527023765526364485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64506679369365020701819313 48380009527023765526364485)
        ·
          refine ⟨9071251786316956036193341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48380009527023765526364485 9071251786316956036193341)
          ·
            refine ⟨3401719419868858513572503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9071251786316956036193341 3401719419868858513572503)
            ·
              refine ⟨5102579129803287770358755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401719419868858513572503 5102579129803287770358755)
              ·
                refine ⟨7653868694704931655538133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102579129803287770358755 7653868694704931655538133)
                ·
                  refine ⟨179387547532146835676675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7653868694704931655538133 179387547532146835676675)
                  ·
                    rfl

theorem cell23_3144204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_3144204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144204 prefixEnd_3144204 := by exact prefixLift 3144204
  have htrace : WordTrace (prefixWord ++ tailWord_3144204) baseStart_3144204 baseEnd_3144204 := by
    simpa [prefixWord, tailWord_3144204, baseEnd_3144204] using wordTrace_append hprefix tailTrace_3144204
  have hstable : (prefixWord ++ tailWord_3144204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144204).length < 2 ^ (prefixWord ++ tailWord_3144204).sum := by decide
  have hdescent : baseEnd_3144204 < baseStart_3144204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144215 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3144215 : Nat := 118140960795 + 3144215 * 2 ^ 59
def prefixEnd_3144215 : Nat := 4983230072969 + 3 ^ 40 * 3144215 * 2
def baseEnd_3144215 : Nat := 1614493576076520978052525

theorem tailTrace_3144215 : CollatzResearch.WordTrace tailWord_3144215 prefixEnd_3144215 1614493576076520978052525 := by
  unfold tailWord_3144215
  simp only [CollatzResearch.WordTrace]
  refine ⟨114678942304053519015218099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76452628202702346010145399 114678942304053519015218099)
  ·
    refine ⟨172018413456080278522827149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114678942304053519015218099 172018413456080278522827149)
    ·
      refine ⟨64506905046030104446060181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172018413456080278522827149 64506905046030104446060181)
      ·
        refine ⟨3023761174032661145909071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64506905046030104446060181 3023761174032661145909071)
        ·
          refine ⟨4535641761048991718863607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023761174032661145909071 4535641761048991718863607)
          ·
            refine ⟨6803462641573487578295411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535641761048991718863607 6803462641573487578295411)
            ·
              refine ⟨10205193962360231367443117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803462641573487578295411 10205193962360231367443117)
              ·
                refine ⟨3826947735885086762791169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10205193962360231367443117 3826947735885086762791169)
                ·
                  refine ⟨2870210801913815072093377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826947735885086762791169 2870210801913815072093377)
                  ·
                    refine ⟨2152658101435361304070033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2870210801913815072093377 2152658101435361304070033)
                    ·
                      refine ⟨1614493576076520978052525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152658101435361304070033 1614493576076520978052525)
                      ·
                        rfl

theorem cell23_3144215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3144215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144215 prefixEnd_3144215 := by exact prefixLift 3144215
  have htrace : WordTrace (prefixWord ++ tailWord_3144215) baseStart_3144215 baseEnd_3144215 := by
    simpa [prefixWord, tailWord_3144215, baseEnd_3144215] using wordTrace_append hprefix tailTrace_3144215
  have hstable : (prefixWord ++ tailWord_3144215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144215).length < 2 ^ (prefixWord ++ tailWord_3144215).sum := by decide
  have hdescent : baseEnd_3144215 < baseStart_3144215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144234 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3144234 : Nat := 118140960795 + 3144234 * 2 ^ 59
def prefixEnd_3144234 : Nat := 4983230072969 + 3 ^ 40 * 3144234 * 2
def baseEnd_3144234 : Nat := 538167777402985467904979

theorem tailTrace_3144234 : CollatzResearch.WordTrace tailWord_3144234 prefixEnd_3144234 538167777402985467904979 := by
  unfold tailWord_3144234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28669908822746171315039939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76453090193989790173439837 28669908822746171315039939)
  ·
    refine ⟨43004863234119256972559909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28669908822746171315039939 43004863234119256972559909)
    ·
      refine ⟨8063411856397360682354983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43004863234119256972559909 8063411856397360682354983)
      ·
        refine ⟨12095117784596041023532475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063411856397360682354983 12095117784596041023532475)
        ·
          refine ⟨18142676676894061535298713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12095117784596041023532475 18142676676894061535298713)
          ·
            refine ⟨13607007507670546151474035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18142676676894061535298713 13607007507670546151474035)
            ·
              refine ⟨20410511261505819227211053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13607007507670546151474035 20410511261505819227211053)
              ·
                refine ⟨7653941723064682210204145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20410511261505819227211053 7653941723064682210204145)
                ·
                  refine ⟨5740456292298511657653109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7653941723064682210204145 5740456292298511657653109)
                  ·
                    refine ⟨538167777402985467904979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5740456292298511657653109 538167777402985467904979)
                    ·
                      rfl

theorem cell23_3144234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3144234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144234 prefixEnd_3144234 := by exact prefixLift 3144234
  have htrace : WordTrace (prefixWord ++ tailWord_3144234) baseStart_3144234 baseEnd_3144234 := by
    simpa [prefixWord, tailWord_3144234, baseEnd_3144234] using wordTrace_append hprefix tailTrace_3144234
  have hstable : (prefixWord ++ tailWord_3144234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144234).length < 2 ^ (prefixWord ++ tailWord_3144234).sum := by decide
  have hdescent : baseEnd_3144234 < baseStart_3144234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144274 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_3144274 : Nat := 118140960795 + 3144274 * 2 ^ 59
def prefixEnd_3144274 : Nat := 4983230072969 + 3 ^ 40 * 3144274 * 2
def baseEnd_3144274 : Nat := 1614523871435136247214753

theorem tailTrace_3144274 : CollatzResearch.WordTrace tailWord_3144274 prefixEnd_3144274 1614523871435136247214753 := by
  unfold tailWord_3144274
  simp only [CollatzResearch.WordTrace]
  refine ⟨28670273552709943022903969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76454062807226514727743917 28670273552709943022903969)
  ·
    refine ⟨21502705164532457267177977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28670273552709943022903969 21502705164532457267177977)
    ·
      refine ⟨16127028873399342950383483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21502705164532457267177977 16127028873399342950383483)
      ·
        refine ⟨24190543310099014425575225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16127028873399342950383483 24190543310099014425575225)
        ·
          refine ⟨18142907482574260819181419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24190543310099014425575225 18142907482574260819181419)
          ·
            refine ⟨27214361223861391228772129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18142907482574260819181419 27214361223861391228772129)
            ·
              refine ⟨20410770917896043421579097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27214361223861391228772129 20410770917896043421579097)
              ·
                refine ⟨15308078188422032566184323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20410770917896043421579097 15308078188422032566184323)
                ·
                  refine ⟨22962117282633048849276485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15308078188422032566184323 22962117282633048849276485)
                  ·
                    refine ⟨4305396990493696659239341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22962117282633048849276485 4305396990493696659239341)
                    ·
                      refine ⟨1614523871435136247214753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4305396990493696659239341 1614523871435136247214753)
                      ·
                        rfl

theorem cell23_3144274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_3144274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144274 prefixEnd_3144274 := by exact prefixLift 3144274
  have htrace : WordTrace (prefixWord ++ tailWord_3144274) baseStart_3144274 baseEnd_3144274 := by
    simpa [prefixWord, tailWord_3144274, baseEnd_3144274] using wordTrace_append hprefix tailTrace_3144274
  have hstable : (prefixWord ++ tailWord_3144274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144274).length < 2 ^ (prefixWord ++ tailWord_3144274).sum := by decide
  have hdescent : baseEnd_3144274 < baseStart_3144274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144298 : List Nat := [3, 1, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3144298 : Nat := 118140960795 + 3144298 * 2 ^ 59
def prefixEnd_3144298 : Nat := 4983230072969 + 3 ^ 40 * 3144298 * 2
def baseEnd_3144298 : Nat := 538178731656948051104881

theorem tailTrace_3144298 : CollatzResearch.WordTrace tailWord_3144298 prefixEnd_3144298 538178731656948051104881 := by
  unfold tailWord_3144298
  simp only [CollatzResearch.WordTrace]
  refine ⟨28670492390688206047622387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76454646375168549460326365 28670492390688206047622387)
  ·
    refine ⟨43005738586032309071433581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28670492390688206047622387 43005738586032309071433581)
    ·
      refine ⟨16127151969762115901787593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43005738586032309071433581 16127151969762115901787593)
      ·
        refine ⟨12095363977321586926340695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16127151969762115901787593 12095363977321586926340695)
        ·
          refine ⟨18143045965982380389511043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12095363977321586926340695 18143045965982380389511043)
          ·
            refine ⟨27214568948973570584266565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18143045965982380389511043 27214568948973570584266565)
            ·
              refine ⟨5102731677932544484549981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27214568948973570584266565 5102731677932544484549981)
              ·
                refine ⟨1913524379224704181706243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5102731677932544484549981 1913524379224704181706243)
                ·
                  refine ⟨2870286568837056272559365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913524379224704181706243 2870286568837056272559365)
                  ·
                    refine ⟨538178731656948051104881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2870286568837056272559365 538178731656948051104881)
                    ·
                      rfl

theorem cell23_3144298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3144298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144298 prefixEnd_3144298 := by exact prefixLift 3144298
  have htrace : WordTrace (prefixWord ++ tailWord_3144298) baseStart_3144298 baseEnd_3144298 := by
    simpa [prefixWord, tailWord_3144298, baseEnd_3144298] using wordTrace_append hprefix tailTrace_3144298
  have hstable : (prefixWord ++ tailWord_3144298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144298).length < 2 ^ (prefixWord ++ tailWord_3144298).sum := by decide
  have hdescent : baseEnd_3144298 < baseStart_3144298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144307 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 5, 5]
def baseStart_3144307 : Nat := 118140960795 + 3144307 * 2 ^ 59
def prefixEnd_3144307 : Nat := 4983230072969 + 3 ^ 40 * 3144307 * 2
def baseEnd_3144307 : Nat := 538180272098911539367367

theorem tailTrace_3144307 : CollatzResearch.WordTrace tailWord_3144307 prefixEnd_3144307 538180272098911539367367 := by
  unfold tailWord_3144307
  simp only [CollatzResearch.WordTrace]
  refine ⟨114682297819720218727567175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76454865213146812485044783 114682297819720218727567175)
  ·
    refine ⟨172023446729580328091350763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114682297819720218727567175 172023446729580328091350763)
    ·
      refine ⟨258035170094370492137026145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172023446729580328091350763 258035170094370492137026145)
      ·
        refine ⟨193526377570777869102769609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258035170094370492137026145 193526377570777869102769609)
        ·
          refine ⟨145144783178083401827077207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193526377570777869102769609 145144783178083401827077207)
          ·
            refine ⟨217717174767125102740615811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145144783178083401827077207 217717174767125102740615811)
            ·
              refine ⟨326575762150687654110923717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217717174767125102740615811 326575762150687654110923717)
              ·
                refine ⟨61232955403253935145798197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326575762150687654110923717 61232955403253935145798197)
                ·
                  refine ⟨5740589569055056419918581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61232955403253935145798197 5740589569055056419918581)
                  ·
                    refine ⟨538180272098911539367367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5740589569055056419918581 538180272098911539367367)
                    ·
                      rfl

theorem cell23_3144307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 5].length) (baseStart_3144307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144307 prefixEnd_3144307 := by exact prefixLift 3144307
  have htrace : WordTrace (prefixWord ++ tailWord_3144307) baseStart_3144307 baseEnd_3144307 := by
    simpa [prefixWord, tailWord_3144307, baseEnd_3144307] using wordTrace_append hprefix tailTrace_3144307
  have hstable : (prefixWord ++ tailWord_3144307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144307).length < 2 ^ (prefixWord ++ tailWord_3144307).sum := by decide
  have hdescent : baseEnd_3144307 < baseStart_3144307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144338 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3144338 : Nat := 118140960795 + 3144338 * 2 ^ 59
def prefixEnd_3144338 : Nat := 4983230072969 + 3 ^ 40 * 3144338 * 2
def baseEnd_3144338 : Nat := 1614556734197023996814459

theorem tailTrace_3144338 : CollatzResearch.WordTrace tailWord_3144338 prefixEnd_3144338 1614556734197023996814459 := by
  unfold tailWord_3144338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28670857120651977755486417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76455618988405274014630445 28670857120651977755486417)
  ·
    refine ⟨21503142840488983316614813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28670857120651977755486417 21503142840488983316614813)
    ·
      refine ⟨8063678565183368743730555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21503142840488983316614813 8063678565183368743730555)
      ·
        refine ⟨12095517847775053115595833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063678565183368743730555 12095517847775053115595833)
        ·
          refine ⟨9071638385831289836696875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12095517847775053115595833 9071638385831289836696875)
          ·
            refine ⟨13607457578746934755045313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9071638385831289836696875 13607457578746934755045313)
            ·
              refine ⟨10205593184060201066283985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13607457578746934755045313 10205593184060201066283985)
              ·
                refine ⟨7654194888045150799712989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10205593184060201066283985 7654194888045150799712989)
                ·
                  refine ⟨2870323083016931549892371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7654194888045150799712989 2870323083016931549892371)
                  ·
                    refine ⟨4305484624525397324838557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2870323083016931549892371 4305484624525397324838557)
                    ·
                      refine ⟨1614556734197023996814459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4305484624525397324838557 1614556734197023996814459)
                      ·
                        rfl

theorem cell23_3144338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3144338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144338 prefixEnd_3144338 := by exact prefixLift 3144338
  have htrace : WordTrace (prefixWord ++ tailWord_3144338) baseStart_3144338 baseEnd_3144338 := by
    simpa [prefixWord, tailWord_3144338, baseEnd_3144338] using wordTrace_append hprefix tailTrace_3144338
  have hstable : (prefixWord ++ tailWord_3144338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144338).length < 2 ^ (prefixWord ++ tailWord_3144338).sum := by decide
  have hdescent : baseEnd_3144338 < baseStart_3144338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144361 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 7, 2, 2]
def baseStart_3144361 : Nat := 118140960795 + 3144361 * 2 ^ 59
def prefixEnd_3144361 : Nat := 4983230072969 + 3 ^ 40 * 3144361 * 2
def baseEnd_3144361 : Nat := 1614568544252077406826853

theorem tailTrace_3144361 : CollatzResearch.WordTrace tailWord_3144361 prefixEnd_3144361 1614568544252077406826853 := by
  unfold tailWord_3144361
  simp only [CollatzResearch.WordTrace]
  refine ⟨114684267361524585950032937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76456178241016390633355291 114684267361524585950032937)
  ·
    refine ⟨86013200521143439462524703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114684267361524585950032937 86013200521143439462524703)
    ·
      refine ⟨129019800781715159193787055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86013200521143439462524703 129019800781715159193787055)
      ·
        refine ⟨193529701172572738790680583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129019800781715159193787055 193529701172572738790680583)
        ·
          refine ⟨290294551758859108186020875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193529701172572738790680583 290294551758859108186020875)
          ·
            refine ⟨435441827638288662279031313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290294551758859108186020875 435441827638288662279031313)
            ·
              refine ⟨326581370728716496709273485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435441827638288662279031313 326581370728716496709273485)
              ·
                refine ⟨122468014023268686265977557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326581370728716496709273485 122468014023268686265977557)
                ·
                  refine ⟨2870344078670359834358849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 122468014023268686265977557 2870344078670359834358849)
                  ·
                    refine ⟨2152758059002769875769137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2870344078670359834358849 2152758059002769875769137)
                    ·
                      refine ⟨1614568544252077406826853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152758059002769875769137 1614568544252077406826853)
                      ·
                        rfl

theorem cell23_3144361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 2, 2].length) (baseStart_3144361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144361 prefixEnd_3144361 := by exact prefixLift 3144361
  have htrace : WordTrace (prefixWord ++ tailWord_3144361) baseStart_3144361 baseEnd_3144361 := by
    simpa [prefixWord, tailWord_3144361, baseEnd_3144361] using wordTrace_append hprefix tailTrace_3144361
  have hstable : (prefixWord ++ tailWord_3144361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144361).length < 2 ^ (prefixWord ++ tailWord_3144361).sum := by decide
  have hdescent : baseEnd_3144361 < baseStart_3144361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144367 : List Nat := [1, 1, 2, 1, 2, 5, 11]
def baseStart_3144367 : Nat := 118140960795 + 3144367 * 2 ^ 59
def prefixEnd_3144367 : Nat := 4983230072969 + 3 ^ 40 * 3144367 * 2
def baseEnd_3144367 : Nat := 19932983026370424485825

theorem tailTrace_3144367 : CollatzResearch.WordTrace tailWord_3144367 prefixEnd_3144367 19932983026370424485825 := by
  unfold tailWord_3144367
  simp only [CollatzResearch.WordTrace]
  refine ⟨114684486199502848974751355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76456324133001899316500903 114684486199502848974751355)
  ·
    refine ⟨172026729299254273462127033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114684486199502848974751355 172026729299254273462127033)
    ·
      refine ⟨129020046974440705096595275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172026729299254273462127033 129020046974440705096595275)
      ·
        refine ⟨193530070461661057644892913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129020046974440705096595275 193530070461661057644892913)
        ·
          refine ⟨145147552846245793233669685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193530070461661057644892913 145147552846245793233669685)
          ·
            refine ⟨13607583079335543115656533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145147552846245793233669685 13607583079335543115656533)
            ·
              refine ⟨19932983026370424485825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13607583079335543115656533 19932983026370424485825)
              ·
                rfl

theorem cell23_3144367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 11].length) (baseStart_3144367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144367 prefixEnd_3144367 := by exact prefixLift 3144367
  have htrace : WordTrace (prefixWord ++ tailWord_3144367) baseStart_3144367 baseEnd_3144367 := by
    simpa [prefixWord, tailWord_3144367, baseEnd_3144367] using wordTrace_append hprefix tailTrace_3144367
  have hstable : (prefixWord ++ tailWord_3144367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144367).length < 2 ^ (prefixWord ++ tailWord_3144367).sum := by decide
  have hdescent : baseEnd_3144367 < baseStart_3144367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144384 : List Nat := [2, 1, 1, 2, 4, 3, 2, 8]
def baseStart_3144384 : Nat := 118140960795 + 3144384 * 2 ^ 59
def prefixEnd_3144384 : Nat := 4983230072969 + 3 ^ 40 * 3144384 * 2
def baseEnd_3144384 : Nat := 59799272381745585808861

theorem tailTrace_3144384 : CollatzResearch.WordTrace tailWord_3144384 prefixEnd_3144384 59799272381745585808861 := by
  unfold tailWord_3144384
  simp only [CollatzResearch.WordTrace]
  refine ⟨57342553120220630439060103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76456737493627507252080137 57342553120220630439060103)
  ·
    refine ⟨86013829680330945658590155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57342553120220630439060103 86013829680330945658590155)
    ·
      refine ⟨129020744520496418487885233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86013829680330945658590155 129020744520496418487885233)
      ·
        refine ⟨96765558390372313865913925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129020744520496418487885233 96765558390372313865913925)
        ·
          refine ⟨18143542198194808849858861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96765558390372313865913925 18143542198194808849858861)
          ·
            refine ⟨6803828324323053318697073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18143542198194808849858861 6803828324323053318697073)
            ·
              refine ⟨5102871243242289989022805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6803828324323053318697073 5102871243242289989022805)
              ·
                refine ⟨59799272381745585808861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5102871243242289989022805 59799272381745585808861)
                ·
                  rfl

theorem cell23_3144384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 8].length) (baseStart_3144384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144384 prefixEnd_3144384 := by exact prefixLift 3144384
  have htrace : WordTrace (prefixWord ++ tailWord_3144384) baseStart_3144384 baseEnd_3144384 := by
    simpa [prefixWord, tailWord_3144384, baseEnd_3144384] using wordTrace_append hprefix tailTrace_3144384
  have hstable : (prefixWord ++ tailWord_3144384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144384).length < 2 ^ (prefixWord ++ tailWord_3144384).sum := by decide
  have hdescent : baseEnd_3144384 < baseStart_3144384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144388 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3144388 : Nat := 118140960795 + 3144388 * 2 ^ 59
def prefixEnd_3144388 : Nat := 4983230072969 + 3 ^ 40 * 3144388 * 2
def baseEnd_3144388 : Nat := 538194136076582933729743

theorem tailTrace_3144388 : CollatzResearch.WordTrace tailWord_3144388 prefixEnd_3144388 538194136076582933729743 := by
  unfold tailWord_3144388
  simp only [CollatzResearch.WordTrace]
  refine ⟨57342626066213384780632909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76456834754951179707510545 57342626066213384780632909)
  ·
    refine ⟨21503484774830019292737341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57342626066213384780632909 21503484774830019292737341)
    ·
      refine ⟨8063806790561257234776503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21503484774830019292737341 8063806790561257234776503)
      ·
        refine ⟨12095710185841885852164755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063806790561257234776503 12095710185841885852164755)
        ·
          refine ⟨18143565278762828778247133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12095710185841885852164755 18143565278762828778247133)
          ·
            refine ⟨6803836979536060791842675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18143565278762828778247133 6803836979536060791842675)
            ·
              refine ⟨10205755469304091187764013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803836979536060791842675 10205755469304091187764013)
              ·
                refine ⟨3827158300989034195411505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10205755469304091187764013 3827158300989034195411505)
                ·
                  refine ⟨2870368725741775646558629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3827158300989034195411505 2870368725741775646558629)
                  ·
                    refine ⟨538194136076582933729743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2870368725741775646558629 538194136076582933729743)
                    ·
                      rfl

theorem cell23_3144388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3144388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144388 prefixEnd_3144388 := by exact prefixLift 3144388
  have htrace : WordTrace (prefixWord ++ tailWord_3144388) baseStart_3144388 baseEnd_3144388 := by
    simpa [prefixWord, tailWord_3144388, baseEnd_3144388] using wordTrace_append hprefix tailTrace_3144388
  have hstable : (prefixWord ++ tailWord_3144388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144388).length < 2 ^ (prefixWord ++ tailWord_3144388).sum := by decide
  have hdescent : baseEnd_3144388 < baseStart_3144388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144398 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_3144398 : Nat := 118140960795 + 3144398 * 2 ^ 59
def prefixEnd_3144398 : Nat := 4983230072969 + 3 ^ 40 * 3144398 * 2
def baseEnd_3144398 : Nat := 1614587543036293762064183

theorem tailTrace_3144398 : CollatzResearch.WordTrace tailWord_3144398 prefixEnd_3144398 1614587543036293762064183 := by
  unfold tailWord_3144398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14335702107798817658641231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76457077908260360846086565 14335702107798817658641231)
  ·
    refine ⟨21503553161698226487961847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14335702107798817658641231 21503553161698226487961847)
    ·
      refine ⟨32255329742547339731942771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21503553161698226487961847 32255329742547339731942771)
      ·
        refine ⟨48382994613821009597914157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32255329742547339731942771 48382994613821009597914157)
        ·
          refine ⟨18143622980182878599217809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48382994613821009597914157 18143622980182878599217809)
          ·
            refine ⟨13607717235137158949413357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18143622980182878599217809 13607717235137158949413357)
            ·
              refine ⟨5102893963176434606030009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13607717235137158949413357 5102893963176434606030009)
              ·
                refine ⟨3827170472382325954522507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5102893963176434606030009 3827170472382325954522507)
                ·
                  refine ⟨5740755708573488931783761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827170472382325954522507 5740755708573488931783761)
                  ·
                    refine ⟨4305566781430116698837821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5740755708573488931783761 4305566781430116698837821)
                    ·
                      refine ⟨1614587543036293762064183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4305566781430116698837821 1614587543036293762064183)
                      ·
                        rfl

theorem cell23_3144398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_3144398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144398 prefixEnd_3144398 := by exact prefixLift 3144398
  have htrace : WordTrace (prefixWord ++ tailWord_3144398) baseStart_3144398 baseEnd_3144398 := by
    simpa [prefixWord, tailWord_3144398, baseEnd_3144398] using wordTrace_append hprefix tailTrace_3144398
  have hstable : (prefixWord ++ tailWord_3144398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144398).length < 2 ^ (prefixWord ++ tailWord_3144398).sum := by decide
  have hdescent : baseEnd_3144398 < baseStart_3144398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144438 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_3144438 : Nat := 118140960795 + 3144438 * 2 ^ 59
def prefixEnd_3144438 : Nat := 4983230072969 + 3 ^ 40 * 3144438 * 2
def baseEnd_3144438 : Nat := 1614608082262473605563999

theorem tailTrace_3144438 : CollatzResearch.WordTrace tailWord_3144438 prefixEnd_3144438 1614608082262473605563999 := by
  unfold tailWord_3144438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167942236390351756286623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76458050521497085400390645 7167942236390351756286623)
  ·
    refine ⟨10751913354585527634429935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7167942236390351756286623 10751913354585527634429935)
    ·
      refine ⟨16127870031878291451644903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10751913354585527634429935 16127870031878291451644903)
      ·
        refine ⟨24191805047817437177467355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16127870031878291451644903 24191805047817437177467355)
        ·
          refine ⟨36287707571726155766201033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24191805047817437177467355 36287707571726155766201033)
          ·
            refine ⟨27215780678794616824650775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36287707571726155766201033 27215780678794616824650775)
            ·
              refine ⟨40823671018191925236976163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27215780678794616824650775 40823671018191925236976163)
              ·
                refine ⟨61235506527287887855464245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40823671018191925236976163 61235506527287887855464245)
                ·
                  refine ⟨5740828736933239486449773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61235506527287887855464245 5740828736933239486449773)
                  ·
                    refine ⟨2152810776349964807418665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5740828736933239486449773 2152810776349964807418665)
                    ·
                      refine ⟨1614608082262473605563999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152810776349964807418665 1614608082262473605563999)
                      ·
                        rfl

theorem cell23_3144438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_3144438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144438 prefixEnd_3144438 := by exact prefixLift 3144438
  have htrace : WordTrace (prefixWord ++ tailWord_3144438) baseStart_3144438 baseEnd_3144438 := by
    simpa [prefixWord, tailWord_3144438, baseEnd_3144438] using wordTrace_append hprefix tailTrace_3144438
  have hstable : (prefixWord ++ tailWord_3144438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144438).length < 2 ^ (prefixWord ++ tailWord_3144438).sum := by decide
  have hdescent : baseEnd_3144438 < baseStart_3144438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144444 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_3144444 : Nat := 118140960795 + 3144444 * 2 ^ 59
def prefixEnd_3144444 : Nat := 4983230072969 + 3 ^ 40 * 3144444 * 2
def baseEnd_3144444 : Nat := 538203721048800194029657

theorem tailTrace_3144444 : CollatzResearch.WordTrace tailWord_3144444 prefixEnd_3144444 538203721048800194029657 := by
  unfold tailWord_3144444
  simp only [CollatzResearch.WordTrace]
  refine ⟨57343647310111945562652193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76458196413482594083536257 57343647310111945562652193)
  ·
    refine ⟨43007735482583959171989145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57343647310111945562652193 43007735482583959171989145)
    ·
      refine ⟨32255801611937969378991859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43007735482583959171989145 32255801611937969378991859)
      ·
        refine ⟨48383702417906954068487789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32255801611937969378991859 48383702417906954068487789)
        ·
          refine ⟨18143888406715107775682921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48383702417906954068487789 18143888406715107775682921)
          ·
            refine ⟨13607916305036330831762191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18143888406715107775682921 13607916305036330831762191)
            ·
              refine ⟨20411874457554496247643287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13607916305036330831762191 20411874457554496247643287)
              ·
                refine ⟨30617811686331744371464931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20411874457554496247643287 30617811686331744371464931)
                ·
                  refine ⟨45926717529497616557197397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30617811686331744371464931 45926717529497616557197397)
                  ·
                    refine ⟨538203721048800194029657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45926717529497616557197397 538203721048800194029657)
                    ·
                      rfl

theorem cell23_3144444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_3144444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144444 prefixEnd_3144444 := by exact prefixLift 3144444
  have htrace : WordTrace (prefixWord ++ tailWord_3144444) baseStart_3144444 baseEnd_3144444 := by
    simpa [prefixWord, tailWord_3144444, baseEnd_3144444] using wordTrace_append hprefix tailTrace_3144444
  have hstable : (prefixWord ++ tailWord_3144444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144444).length < 2 ^ (prefixWord ++ tailWord_3144444).sum := by decide
  have hdescent : baseEnd_3144444 < baseStart_3144444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144474 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 9]
def baseStart_3144474 : Nat := 118140960795 + 3144474 * 2 ^ 59
def prefixEnd_3144474 : Nat := 4983230072969 + 3 ^ 40 * 3144474 * 2
def baseEnd_3144474 : Nat := 179402951951781718301537

theorem tailTrace_3144474 : CollatzResearch.WordTrace tailWord_3144474 prefixEnd_3144474 179402951951781718301537 := by
  unfold tailWord_3144474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28672097202528801562224119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76458925873410137499264317 28672097202528801562224119)
  ·
    refine ⟨43008145803793202343336179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28672097202528801562224119 43008145803793202343336179)
    ·
      refine ⟨64512218705689803515004269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43008145803793202343336179 64512218705689803515004269)
      ·
        refine ⟨24192082014633676318126601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64512218705689803515004269 24192082014633676318126601)
        ·
          refine ⟨18144061510975257238594951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24192082014633676318126601 18144061510975257238594951)
          ·
            refine ⟨27216092266462885857892427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18144061510975257238594951 27216092266462885857892427)
            ·
              refine ⟨40824138399694328786838641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27216092266462885857892427 40824138399694328786838641)
              ·
                refine ⟨30618103799770746590128981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40824138399694328786838641 30618103799770746590128981)
                ·
                  refine ⟨179402951951781718301537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30618103799770746590128981 179402951951781718301537)
                  ·
                    rfl

theorem cell23_3144474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_3144474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144474 prefixEnd_3144474 := by exact prefixLift 3144474
  have htrace : WordTrace (prefixWord ++ tailWord_3144474) baseStart_3144474 baseEnd_3144474 := by
    simpa [prefixWord, tailWord_3144474, baseEnd_3144474] using wordTrace_append hprefix tailTrace_3144474
  have hstable : (prefixWord ++ tailWord_3144474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144474).length < 2 ^ (prefixWord ++ tailWord_3144474).sum := by decide
  have hdescent : baseEnd_3144474 < baseStart_3144474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144504 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 3, 7]
def baseStart_3144504 : Nat := 118140960795 + 3144504 * 2 ^ 59
def prefixEnd_3144504 : Nat := 4983230072969 + 3 ^ 40 * 3144504 * 2
def baseEnd_3144504 : Nat := 538213990661890115779565

theorem tailTrace_3144504 : CollatzResearch.WordTrace tailWord_3144504 prefixEnd_3144504 538213990661890115779565 := by
  unfold tailWord_3144504
  simp only [CollatzResearch.WordTrace]
  refine ⟨57344741500003260686244283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76459655333337680914992377 57344741500003260686244283)
  ·
    refine ⟨86017112250004891029366425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57344741500003260686244283 86017112250004891029366425)
    ·
      refine ⟨64512834187503668272024819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86017112250004891029366425 64512834187503668272024819)
      ·
        refine ⟨96769251281255502408037229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64512834187503668272024819 96769251281255502408037229)
        ·
          refine ⟨36288469230470813403013961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96769251281255502408037229 36288469230470813403013961)
          ·
            refine ⟨27216351922853110052260471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36288469230470813403013961 27216351922853110052260471)
            ·
              refine ⟨40824527884279665078390707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27216351922853110052260471 40824527884279665078390707)
              ·
                refine ⟨61236791826419497617586061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40824527884279665078390707 61236791826419497617586061)
                ·
                  refine ⟨22963796934907311606594773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61236791826419497617586061 22963796934907311606594773)
                  ·
                    refine ⟨538213990661890115779565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22963796934907311606594773 538213990661890115779565)
                    ·
                      rfl

theorem cell23_3144504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_3144504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144504 prefixEnd_3144504 := by exact prefixLift 3144504
  have htrace : WordTrace (prefixWord ++ tailWord_3144504) baseStart_3144504 baseEnd_3144504 := by
    simpa [prefixWord, tailWord_3144504, baseEnd_3144504] using wordTrace_append hprefix tailTrace_3144504
  have hstable : (prefixWord ++ tailWord_3144504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144504).length < 2 ^ (prefixWord ++ tailWord_3144504).sum := by decide
  have hdescent : baseEnd_3144504 < baseStart_3144504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144602 : List Nat := [3, 1, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_3144602 : Nat := 118140960795 + 3144602 * 2 ^ 59
def prefixEnd_3144602 : Nat := 4983230072969 + 3 ^ 40 * 3144602 * 2
def baseEnd_3144602 : Nat := 538230764363270321304415

theorem tailTrace_3144602 : CollatzResearch.WordTrace tailWord_3144602 prefixEnd_3144602 538230764363270321304415 := by
  unfold tailWord_3144602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28673264338412871027389015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76462038235767656073037373 28673264338412871027389015)
  ·
    refine ⟨43009896507619306541083523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28673264338412871027389015 43009896507619306541083523)
    ·
      refine ⟨64514844761428959811625285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43009896507619306541083523 64514844761428959811625285)
      ·
        refine ⟨12096533392767929964679741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64514844761428959811625285 12096533392767929964679741)
        ·
          refine ⟨4536200022287973736754903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12096533392767929964679741 4536200022287973736754903)
          ·
            refine ⟨6804300033431960605132355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536200022287973736754903 6804300033431960605132355)
            ·
              refine ⟨10206450050147940907698533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6804300033431960605132355 10206450050147940907698533)
              ·
                refine ⟨1913709384402738920193475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10206450050147940907698533 1913709384402738920193475)
                ·
                  refine ⟨2870564076604108380290213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913709384402738920193475 2870564076604108380290213)
                  ·
                    refine ⟨538230764363270321304415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2870564076604108380290213 538230764363270321304415)
                    ·
                      rfl

theorem cell23_3144602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_3144602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144602 prefixEnd_3144602 := by exact prefixLift 3144602
  have htrace : WordTrace (prefixWord ++ tailWord_3144602) baseStart_3144602 baseEnd_3144602 := by
    simpa [prefixWord, tailWord_3144602, baseEnd_3144602] using wordTrace_append hprefix tailTrace_3144602
  have hstable : (prefixWord ++ tailWord_3144602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144602).length < 2 ^ (prefixWord ++ tailWord_3144602).sum := by decide
  have hdescent : baseEnd_3144602 < baseStart_3144602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144611 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 3, 5]
def baseStart_3144611 : Nat := 118140960795 + 3144611 * 2 ^ 59
def prefixEnd_3144611 : Nat := 4983230072969 + 3 ^ 40 * 3144611 * 2
def baseEnd_3144611 : Nat := 538232304805233809566901

theorem tailTrace_3144611 : CollatzResearch.WordTrace tailWord_3144611 prefixEnd_3144611 538232304805233809566901 := by
  unfold tailWord_3144611
  simp only [CollatzResearch.WordTrace]
  refine ⟨114693385610618878646633687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76462257073745919097755791 114693385610618878646633687)
  ·
    refine ⟨172040078415928317969950531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114693385610618878646633687 172040078415928317969950531)
    ·
      refine ⟨258060117623892476954925797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172040078415928317969950531 258060117623892476954925797)
      ·
        refine ⟨48386272054479839429048587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258060117623892476954925797 48386272054479839429048587)
        ·
          refine ⟨72579408081719759143572881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48386272054479839429048587 72579408081719759143572881)
          ·
            refine ⟨54434556061289819357679661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72579408081719759143572881 54434556061289819357679661)
            ·
              refine ⟨20412958522983682259129873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54434556061289819357679661 20412958522983682259129873)
              ·
                refine ⟨15309718892237761694347405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20412958522983682259129873 15309718892237761694347405)
                ·
                  refine ⟨5741144584589160635380277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15309718892237761694347405 5741144584589160635380277)
                  ·
                    refine ⟨538232304805233809566901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5741144584589160635380277 538232304805233809566901)
                    ·
                      rfl

theorem cell23_3144611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 5].length) (baseStart_3144611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144611 prefixEnd_3144611 := by exact prefixLift 3144611
  have htrace : WordTrace (prefixWord ++ tailWord_3144611) baseStart_3144611 baseEnd_3144611 := by
    simpa [prefixWord, tailWord_3144611, baseEnd_3144611] using wordTrace_append hprefix tailTrace_3144611
  have hstable : (prefixWord ++ tailWord_3144611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144611).length < 2 ^ (prefixWord ++ tailWord_3144611).sum := by decide
  have hdescent : baseEnd_3144611 < baseStart_3144611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144682 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_3144682 : Nat := 118140960795 + 3144682 * 2 ^ 59
def prefixEnd_3144682 : Nat := 4983230072969 + 3 ^ 40 * 3144682 * 2
def baseEnd_3144682 : Nat := 1614733371542170650912877

theorem tailTrace_3144682 : CollatzResearch.WordTrace tailWord_3144682 prefixEnd_3144682 1614733371542170650912877 := by
  unfold tailWord_3144682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28673993798340414443117075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76463983462241105181645533 28673993798340414443117075)
  ·
    refine ⟨43010990697510621664675613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28673993798340414443117075 43010990697510621664675613)
    ·
      refine ⟨16129121511566483124253355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43010990697510621664675613 16129121511566483124253355)
      ·
        refine ⟨24193682267349724686380033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16129121511566483124253355 24193682267349724686380033)
        ·
          refine ⟨18145261700512293514785025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24193682267349724686380033 18145261700512293514785025)
          ·
            refine ⟨13608946275384220136088769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18145261700512293514785025 13608946275384220136088769)
            ·
              refine ⟨10206709706538165102066577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13608946275384220136088769 10206709706538165102066577)
              ·
                refine ⟨7655032279903623826549933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10206709706538165102066577 7655032279903623826549933)
                ·
                  refine ⟨2870637104963858934956225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7655032279903623826549933 2870637104963858934956225)
                  ·
                    refine ⟨2152977828722894201217169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2870637104963858934956225 2152977828722894201217169)
                    ·
                      refine ⟨1614733371542170650912877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2152977828722894201217169 1614733371542170650912877)
                      ·
                        rfl

theorem cell23_3144682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_3144682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144682 prefixEnd_3144682 := by exact prefixLift 3144682
  have htrace : WordTrace (prefixWord ++ tailWord_3144682) baseStart_3144682 baseEnd_3144682 := by
    simpa [prefixWord, tailWord_3144682, baseEnd_3144682] using wordTrace_append hprefix tailTrace_3144682
  have hstable : (prefixWord ++ tailWord_3144682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144682).length < 2 ^ (prefixWord ++ tailWord_3144682).sum := by decide
  have hdescent : baseEnd_3144682 < baseStart_3144682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144693 : List Nat := [1, 3, 5, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3144693 : Nat := 118140960795 + 3144693 * 2 ^ 59
def prefixEnd_3144693 : Nat := 4983230072969 + 3 ^ 40 * 3144693 * 2
def baseEnd_3144693 : Nat := 1614739019829370107875327

theorem tailTrace_3144693 : CollatzResearch.WordTrace tailWord_3144693 prefixEnd_3144693 1614739019829370107875327 := by
  unfold tailWord_3144693
  simp only [CollatzResearch.WordTrace]
  refine ⟨114696376396321806651118733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76464250930881204434079155 114696376396321806651118733)
  ·
    refine ⟨43011141148620677494169525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114696376396321806651118733 43011141148620677494169525)
    ·
      refine ⟨4032294482683188515078393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43011141148620677494169525 4032294482683188515078393)
      ·
        refine ⟨3024220862012391386308795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4032294482683188515078393 3024220862012391386308795)
        ·
          refine ⟨4536331293018587079463193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024220862012391386308795 4536331293018587079463193)
          ·
            refine ⟨3402248469763940309597395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4536331293018587079463193 3402248469763940309597395)
            ·
              refine ⟨5103372704645910464396093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402248469763940309597395 5103372704645910464396093)
              ·
                refine ⟨1913764764242216424148535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5103372704645910464396093 1913764764242216424148535)
                ·
                  refine ⟨2870647146363324636222803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913764764242216424148535 2870647146363324636222803)
                  ·
                    refine ⟨4305970719544986954334205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2870647146363324636222803 4305970719544986954334205)
                    ·
                      refine ⟨1614739019829370107875327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4305970719544986954334205 1614739019829370107875327)
                      ·
                        rfl

theorem cell23_3144693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3144693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144693 prefixEnd_3144693 := by exact prefixLift 3144693
  have htrace : WordTrace (prefixWord ++ tailWord_3144693) baseStart_3144693 baseEnd_3144693 := by
    simpa [prefixWord, tailWord_3144693, baseEnd_3144693] using wordTrace_append hprefix tailTrace_3144693
  have hstable : (prefixWord ++ tailWord_3144693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144693).length < 2 ^ (prefixWord ++ tailWord_3144693).sum := by decide
  have hdescent : baseEnd_3144693 < baseStart_3144693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144698 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_3144698 : Nat := 118140960795 + 3144698 * 2 ^ 59
def prefixEnd_3144698 : Nat := 4983230072969 + 3 ^ 40 * 3144698 * 2
def baseEnd_3144698 : Nat := 1614741587232642588312803

theorem tailTrace_3144698 : CollatzResearch.WordTrace tailWord_3144698 prefixEnd_3144698 1614741587232642588312803 := by
  unfold tailWord_3144698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28674139690325923126262687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76464372507535795003367165 28674139690325923126262687)
  ·
    refine ⟨43011209535488884689394031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28674139690325923126262687 43011209535488884689394031)
    ·
      refine ⟨64516814303233327034091047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43011209535488884689394031 64516814303233327034091047)
      ·
        refine ⟨96775221454849990551136571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64516814303233327034091047 96775221454849990551136571)
        ·
          refine ⟨145162832182274985826704857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96775221454849990551136571 145162832182274985826704857)
          ·
            refine ⟨108872124136706239370028643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145162832182274985826704857 108872124136706239370028643)
            ·
              refine ⟨163308186205059359055042965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108872124136706239370028643 163308186205059359055042965)
              ·
                refine ⟨7655071228362157455705139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163308186205059359055042965 7655071228362157455705139)
                ·
                  refine ⟨11482606842543236183557709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7655071228362157455705139 11482606842543236183557709)
                  ·
                    refine ⟨4305977565953713568834141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11482606842543236183557709 4305977565953713568834141)
                    ·
                      refine ⟨1614741587232642588312803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4305977565953713568834141 1614741587232642588312803)
                      ·
                        rfl

theorem cell23_3144698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_3144698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144698 prefixEnd_3144698 := by exact prefixLift 3144698
  have htrace : WordTrace (prefixWord ++ tailWord_3144698) baseStart_3144698 baseEnd_3144698 := by
    simpa [prefixWord, tailWord_3144698, baseEnd_3144698] using wordTrace_append hprefix tailTrace_3144698
  have hstable : (prefixWord ++ tailWord_3144698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144698).length < 2 ^ (prefixWord ++ tailWord_3144698).sum := by decide
  have hdescent : baseEnd_3144698 < baseStart_3144698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144701 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_3144701 : Nat := 118140960795 + 3144701 * 2 ^ 59
def prefixEnd_3144701 : Nat := 4983230072969 + 3 ^ 40 * 3144701 * 2
def baseEnd_3144701 : Nat := 538247709224868692191763

theorem tailTrace_3144701 : CollatzResearch.WordTrace tailWord_3144701 prefixEnd_3144701 538247709224868692191763 := by
  unfold tailWord_3144701
  simp only [CollatzResearch.WordTrace]
  refine ⟨114696668180292824017409957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76464445453528549344939971 114696668180292824017409957)
  ·
    refine ⟨21505625283804904503264367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114696668180292824017409957 21505625283804904503264367)
    ·
      refine ⟨32258437925707356754896551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21505625283804904503264367 32258437925707356754896551)
      ·
        refine ⟨48387656888561035132344827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32258437925707356754896551 48387656888561035132344827)
        ·
          refine ⟨72581485332841552698517241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48387656888561035132344827 72581485332841552698517241)
          ·
            refine ⟨54436113999631164523887931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72581485332841552698517241 54436113999631164523887931)
            ·
              refine ⟨81654170999446746785831897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54436113999631164523887931 81654170999446746785831897)
              ·
                refine ⟨61240628249585060089373923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81654170999446746785831897 61240628249585060089373923)
                ·
                  refine ⟨91860942374377590134060885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61240628249585060089373923 91860942374377590134060885)
                  ·
                    refine ⟨538247709224868692191763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 91860942374377590134060885 538247709224868692191763)
                    ·
                      rfl

theorem cell23_3144701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_3144701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144701 prefixEnd_3144701 := by exact prefixLift 3144701
  have htrace : WordTrace (prefixWord ++ tailWord_3144701) baseStart_3144701 baseEnd_3144701 := by
    simpa [prefixWord, tailWord_3144701, baseEnd_3144701] using wordTrace_append hprefix tailTrace_3144701
  have hstable : (prefixWord ++ tailWord_3144701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144701).length < 2 ^ (prefixWord ++ tailWord_3144701).sum := by decide
  have hdescent : baseEnd_3144701 < baseStart_3144701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144702 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3144702 : Nat := 118140960795 + 3144702 * 2 ^ 59
def prefixEnd_3144702 : Nat := 4983230072969 + 3 ^ 40 * 3144702 * 2
def baseEnd_3144702 : Nat := 1614743641155260572662785

theorem tailTrace_3144702 : CollatzResearch.WordTrace tailWord_3144702 prefixEnd_3144702 1614743641155260572662785 := by
  unfold tailWord_3144702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337088081661150148524545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76464469768859467458797573 14337088081661150148524545)
  ·
    refine ⟨10752816061245862611393409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14337088081661150148524545 10752816061245862611393409)
    ·
      refine ⟨8064612045934396958545057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10752816061245862611393409 8064612045934396958545057)
      ·
        refine ⟨6048459034450797718908793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8064612045934396958545057 6048459034450797718908793)
        ·
          refine ⟨4536344275838098289181595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6048459034450797718908793 4536344275838098289181595)
          ·
            refine ⟨6804516413757147433772393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536344275838098289181595 6804516413757147433772393)
            ·
              refine ⟨5103387310317860575329295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6804516413757147433772393 5103387310317860575329295)
              ·
                refine ⟨7655080965476790862993943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103387310317860575329295 7655080965476790862993943)
                ·
                  refine ⟨11482621448215186294490915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7655080965476790862993943 11482621448215186294490915)
                  ·
                    refine ⟨17223932172322779441736373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11482621448215186294490915 17223932172322779441736373)
                    ·
                      refine ⟨1614743641155260572662785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17223932172322779441736373 1614743641155260572662785)
                      ·
                        rfl

theorem cell23_3144702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3144702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144702 prefixEnd_3144702 := by exact prefixLift 3144702
  have htrace : WordTrace (prefixWord ++ tailWord_3144702) baseStart_3144702 baseEnd_3144702 := by
    simpa [prefixWord, tailWord_3144702, baseEnd_3144702] using wordTrace_append hprefix tailTrace_3144702
  have hstable : (prefixWord ++ tailWord_3144702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144702).length < 2 ^ (prefixWord ++ tailWord_3144702).sum := by decide
  have hdescent : baseEnd_3144702 < baseStart_3144702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144715 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 3]
def baseStart_3144715 : Nat := 118140960795 + 3144715 * 2 ^ 59
def prefixEnd_3144715 : Nat := 4983230072969 + 3 ^ 40 * 3144715 * 2
def baseEnd_3144715 : Nat := 1614750316403769021800225

theorem tailTrace_3144715 : CollatzResearch.WordTrace tailWord_3144715 prefixEnd_3144715 1614750316403769021800225 := by
  unfold tailWord_3144715
  simp only [CollatzResearch.WordTrace]
  refine ⟨114697178802242104408419599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76464785868161402938946399 114697178802242104408419599)
  ·
    refine ⟨172045768203363156612629399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114697178802242104408419599 172045768203363156612629399)
    ·
      refine ⟨258068652305044734918944099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172045768203363156612629399 258068652305044734918944099)
      ·
        refine ⟨387102978457567102378416149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258068652305044734918944099 387102978457567102378416149)
        ·
          refine ⟨18145452115198457923988257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 387102978457567102378416149 18145452115198457923988257)
          ·
            refine ⟨13609089086398843442991193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18145452115198457923988257 13609089086398843442991193)
            ·
              refine ⟨10206816814799132582243395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13609089086398843442991193 10206816814799132582243395)
              ·
                refine ⟨15310225222198698873365093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10206816814799132582243395 15310225222198698873365093)
                ·
                  refine ⟨2870667229162256038755955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15310225222198698873365093 2870667229162256038755955)
                  ·
                    refine ⟨4306000843743384058133933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2870667229162256038755955 4306000843743384058133933)
                    ·
                      refine ⟨1614750316403769021800225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4306000843743384058133933 1614750316403769021800225)
                      ·
                        rfl

theorem cell23_3144715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 3].length) (baseStart_3144715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144715 prefixEnd_3144715 := by exact prefixLift 3144715
  have htrace : WordTrace (prefixWord ++ tailWord_3144715) baseStart_3144715 baseEnd_3144715 := by
    simpa [prefixWord, tailWord_3144715, baseEnd_3144715] using wordTrace_append hprefix tailTrace_3144715
  have hstable : (prefixWord ++ tailWord_3144715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144715).length < 2 ^ (prefixWord ++ tailWord_3144715).sum := by decide
  have hdescent : baseEnd_3144715 < baseStart_3144715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144716 : List Nat := [2, 2, 1, 2, 3, 3, 3, 2, 1, 2, 2]
def baseStart_3144716 : Nat := 118140960795 + 3144716 * 2 ^ 59
def prefixEnd_3144716 : Nat := 4983230072969 + 3 ^ 40 * 3144716 * 2
def baseEnd_3144716 : Nat := 1614750829884423517887721

theorem tailTrace_3144716 : CollatzResearch.WordTrace tailWord_3144716 prefixEnd_3144716 1614750829884423517887721 := by
  unfold tailWord_3144716
  simp only [CollatzResearch.WordTrace]
  refine ⟨57348607637619240789603001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76464810183492321052804001 57348607637619240789603001)
  ·
    refine ⟨43011455728214430592202251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57348607637619240789603001 43011455728214430592202251)
    ·
      refine ⟨64517183592321645888303377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43011455728214430592202251 64517183592321645888303377)
      ·
        refine ⟨48387887694241234416227533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64517183592321645888303377 48387887694241234416227533)
        ·
          refine ⟨18145457885340462906085325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48387887694241234416227533 18145457885340462906085325)
          ·
            refine ⟨6804546707002673589781997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18145457885340462906085325 6804546707002673589781997)
            ·
              refine ⟨2551705015126002596168249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6804546707002673589781997 2551705015126002596168249)
              ·
                refine ⟨1913778761344501947126187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2551705015126002596168249 1913778761344501947126187)
                ·
                  refine ⟨2870668142016752920689281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913778761344501947126187 2870668142016752920689281)
                  ·
                    refine ⟨2153001106512564690516961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2870668142016752920689281 2153001106512564690516961)
                    ·
                      refine ⟨1614750829884423517887721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153001106512564690516961 1614750829884423517887721)
                      ·
                        rfl

theorem cell23_3144716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_3144716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144716 prefixEnd_3144716 := by exact prefixLift 3144716
  have htrace : WordTrace (prefixWord ++ tailWord_3144716) baseStart_3144716 baseEnd_3144716 := by
    simpa [prefixWord, tailWord_3144716, baseEnd_3144716] using wordTrace_append hprefix tailTrace_3144716
  have hstable : (prefixWord ++ tailWord_3144716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144716).length < 2 ^ (prefixWord ++ tailWord_3144716).sum := by decide
  have hdescent : baseEnd_3144716 < baseStart_3144716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144731 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 6, 6]
def baseStart_3144731 : Nat := 118140960795 + 3144731 * 2 ^ 59
def prefixEnd_3144731 : Nat := 4983230072969 + 3 ^ 40 * 3144731 * 2
def baseEnd_3144731 : Nat := 538252844031413653066717

theorem tailTrace_3144731 : CollatzResearch.WordTrace tailWord_3144731 prefixEnd_3144731 538252844031413653066717 := by
  unfold tailWord_3144731
  simp only [CollatzResearch.WordTrace]
  refine ⟨114697762370184139141002047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76465174913456092760668031 114697762370184139141002047)
  ·
    refine ⟨172046643555276208711503071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114697762370184139141002047 172046643555276208711503071)
    ·
      refine ⟨258069965332914313067254607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172046643555276208711503071 258069965332914313067254607)
      ·
        refine ⟨387104947999371469600881911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258069965332914313067254607 387104947999371469600881911)
        ·
          refine ⟨580657421999057204401322867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387104947999371469600881911 580657421999057204401322867)
          ·
            refine ⟨870986132998585806601984301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580657421999057204401322867 870986132998585806601984301)
            ·
              refine ⟨326619799874469677475744113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 870986132998585806601984301 326619799874469677475744113)
              ·
                refine ⟨244964849905852258106808085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326619799874469677475744113 244964849905852258106808085)
                ·
                  refine ⟨11482727339336824598756629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 244964849905852258106808085 11482727339336824598756629)
                  ·
                    refine ⟨538252844031413653066717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11482727339336824598756629 538252844031413653066717)
                    ·
                      rfl

theorem cell23_3144731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 6].length) (baseStart_3144731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144731 prefixEnd_3144731 := by exact prefixLift 3144731
  have htrace : WordTrace (prefixWord ++ tailWord_3144731) baseStart_3144731 baseEnd_3144731 := by
    simpa [prefixWord, tailWord_3144731, baseEnd_3144731] using wordTrace_append hprefix tailTrace_3144731
  have hstable : (prefixWord ++ tailWord_3144731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144731).length < 2 ^ (prefixWord ++ tailWord_3144731).sum := by decide
  have hdescent : baseEnd_3144731 < baseStart_3144731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144736 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3144736 : Nat := 118140960795 + 3144736 * 2 ^ 59
def prefixEnd_3144736 : Nat := 4983230072969 + 3 ^ 40 * 3144736 * 2
def baseEnd_3144736 : Nat := 1614761099497513439637629

theorem tailTrace_3144736 : CollatzResearch.WordTrace tailWord_3144736 prefixEnd_3144736 1614761099497513439637629 := by
  unfold tailWord_3144736
  simp only [CollatzResearch.WordTrace]
  refine ⟨57348972367583012497467031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76465296490110683329956041 57348972367583012497467031)
  ·
    refine ⟨86023458551374518746200547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57348972367583012497467031 86023458551374518746200547)
    ·
      refine ⟨129035187827061778119300821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86023458551374518746200547 129035187827061778119300821)
      ·
        refine ⟨3024262214696760424671113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 129035187827061778119300821 3024262214696760424671113)
        ·
          refine ⟨2268196661022570318503335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024262214696760424671113 2268196661022570318503335)
          ·
            refine ⟨3402294991533855477755003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268196661022570318503335 3402294991533855477755003)
            ·
              refine ⟨5103442487300783216632505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402294991533855477755003 5103442487300783216632505)
              ·
                refine ⟨3827581865475587412474379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5103442487300783216632505 3827581865475587412474379)
                ·
                  refine ⟨5741372798213381118711569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827581865475587412474379 5741372798213381118711569)
                  ·
                    refine ⟨4306029598660035839033677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5741372798213381118711569 4306029598660035839033677)
                    ·
                      refine ⟨1614761099497513439637629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4306029598660035839033677 1614761099497513439637629)
                      ·
                        rfl

theorem cell23_3144736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3144736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144736 prefixEnd_3144736 := by exact prefixLift 3144736
  have htrace : WordTrace (prefixWord ++ tailWord_3144736) baseStart_3144736 baseEnd_3144736 := by
    simpa [prefixWord, tailWord_3144736, baseEnd_3144736] using wordTrace_append hprefix tailTrace_3144736
  have hstable : (prefixWord ++ tailWord_3144736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144736).length < 2 ^ (prefixWord ++ tailWord_3144736).sum := by decide
  have hdescent : baseEnd_3144736 < baseStart_3144736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144751 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_3144751 : Nat := 118140960795 + 3144751 * 2 ^ 59
def prefixEnd_3144751 : Nat := 4983230072969 + 3 ^ 40 * 3144751 * 2
def baseEnd_3144751 : Nat := 1614768801707330880950059

theorem tailTrace_3144751 : CollatzResearch.WordTrace tailWord_3144751 prefixEnd_3144751 1614768801707330880950059 := by
  unfold tailWord_3144751
  simp only [CollatzResearch.WordTrace]
  refine ⟨114698491830111682556730107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76465661220074455037820071 114698491830111682556730107)
  ·
    refine ⟨172047737745167523835095161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114698491830111682556730107 172047737745167523835095161)
    ·
      refine ⟨129035803308875642876321371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172047737745167523835095161 129035803308875642876321371)
      ·
        refine ⟨193553704963313464314482057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129035803308875642876321371 193553704963313464314482057)
        ·
          refine ⟨145165278722485098235861543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193553704963313464314482057 145165278722485098235861543)
          ·
            refine ⟨217747918083727647353792315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145165278722485098235861543 217747918083727647353792315)
            ·
              refine ⟨326621877125591471030688473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217747918083727647353792315 326621877125591471030688473)
              ·
                refine ⟨244966407844193603273016355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326621877125591471030688473 244966407844193603273016355)
                ·
                  refine ⟨367449611766290404909524533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244966407844193603273016355 367449611766290404909524533)
                  ·
                    refine ⟨34448401103089725460267925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 367449611766290404909524533 34448401103089725460267925)
                    ·
                      refine ⟨1614768801707330880950059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34448401103089725460267925 1614768801707330880950059)
                      ·
                        rfl

theorem cell23_3144751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_3144751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144751 prefixEnd_3144751 := by exact prefixLift 3144751
  have htrace : WordTrace (prefixWord ++ tailWord_3144751) baseStart_3144751 baseEnd_3144751 := by
    simpa [prefixWord, tailWord_3144751, baseEnd_3144751] using wordTrace_append hprefix tailTrace_3144751
  have hstable : (prefixWord ++ tailWord_3144751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144751).length < 2 ^ (prefixWord ++ tailWord_3144751).sum := by decide
  have hdescent : baseEnd_3144751 < baseStart_3144751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144768 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_3144768 : Nat := 118140960795 + 3144768 * 2 ^ 59
def prefixEnd_3144768 : Nat := 4983230072969 + 3 ^ 40 * 3144768 * 2
def baseEnd_3144768 : Nat := 1614777530878457314437481

theorem tailTrace_3144768 : CollatzResearch.WordTrace tailWord_3144768 prefixEnd_3144768 1614777530878457314437481 := by
  unfold tailWord_3144768
  simp only [CollatzResearch.WordTrace]
  refine ⟨57349555935525047230049479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76466074580700062973399305 57349555935525047230049479)
  ·
    refine ⟨86024333903287570845074219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57349555935525047230049479 86024333903287570845074219)
    ·
      refine ⟨129036500854931356267611329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86024333903287570845074219 129036500854931356267611329)
      ·
        refine ⟨96777375641198517200708497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129036500854931356267611329 96777375641198517200708497)
        ·
          refine ⟨72583031730898887900531373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96777375641198517200708497 72583031730898887900531373)
          ·
            refine ⟨27218636899087082962699265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72583031730898887900531373 27218636899087082962699265)
            ·
              refine ⟨20413977674315312222024449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27218636899087082962699265 20413977674315312222024449)
              ·
                refine ⟨15310483255736484166518337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20413977674315312222024449 15310483255736484166518337)
                ·
                  refine ⟨11482862441802363124888753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15310483255736484166518337 11482862441802363124888753)
                  ·
                    refine ⟨8612146831351772343666565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11482862441802363124888753 8612146831351772343666565)
                    ·
                      refine ⟨1614777530878457314437481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8612146831351772343666565 1614777530878457314437481)
                      ·
                        rfl

theorem cell23_3144768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_3144768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144768 prefixEnd_3144768 := by exact prefixLift 3144768
  have htrace : WordTrace (prefixWord ++ tailWord_3144768) baseStart_3144768 baseEnd_3144768 := by
    simpa [prefixWord, tailWord_3144768, baseEnd_3144768] using wordTrace_append hprefix tailTrace_3144768
  have hstable : (prefixWord ++ tailWord_3144768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144768).length < 2 ^ (prefixWord ++ tailWord_3144768).sum := by decide
  have hdescent : baseEnd_3144768 < baseStart_3144768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144862 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3144862 : Nat := 118140960795 + 3144862 * 2 ^ 59
def prefixEnd_3144862 : Nat := 4983230072969 + 3 ^ 40 * 3144862 * 2
def baseEnd_3144862 : Nat := 1614825798059979946662049

theorem tailTrace_3144862 : CollatzResearch.WordTrace tailWord_3144862 prefixEnd_3144862 1614825798059979946662049 := by
  unfold tailWord_3144862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337817541588693564252605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76468360221806365676013893 14337817541588693564252605)
  ·
    refine ⟨5376681578095760086594727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14337817541588693564252605 5376681578095760086594727)
    ·
      refine ⟨8065022367143640129892091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5376681578095760086594727 8065022367143640129892091)
      ·
        refine ⟨12097533550715460194838137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8065022367143640129892091 12097533550715460194838137)
        ·
          refine ⟨9073150163036595146128603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12097533550715460194838137 9073150163036595146128603)
          ·
            refine ⟨13609725244554892719192905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9073150163036595146128603 13609725244554892719192905)
            ·
              refine ⟨10207293933416169539394679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13609725244554892719192905 10207293933416169539394679)
              ·
                refine ⟨15310940900124254309092019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10207293933416169539394679 15310940900124254309092019)
                ·
                  refine ⟨22966411350186381463638029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15310940900124254309092019 22966411350186381463638029)
                  ·
                    refine ⟨8612404256319893048864261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22966411350186381463638029 8612404256319893048864261)
                    ·
                      refine ⟨1614825798059979946662049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8612404256319893048864261 1614825798059979946662049)
                      ·
                        rfl

theorem cell23_3144862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3144862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144862 prefixEnd_3144862 := by exact prefixLift 3144862
  have htrace : WordTrace (prefixWord ++ tailWord_3144862) baseStart_3144862 baseEnd_3144862 := by
    simpa [prefixWord, tailWord_3144862, baseEnd_3144862] using wordTrace_append hprefix tailTrace_3144862
  have hstable : (prefixWord ++ tailWord_3144862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144862).length < 2 ^ (prefixWord ++ tailWord_3144862).sum := by decide
  have hdescent : baseEnd_3144862 < baseStart_3144862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144865 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3144865 : Nat := 118140960795 + 3144865 * 2 ^ 59
def prefixEnd_3144865 : Nat := 4983230072969 + 3 ^ 40 * 3144865 * 2
def baseEnd_3144865 : Nat := 1614827338501943434924535

theorem tailTrace_3144865 : CollatzResearch.WordTrace tailWord_3144865 prefixEnd_3144865 1614827338501943434924535 := by
  unfold tailWord_3144865
  simp only [CollatzResearch.WordTrace]
  refine ⟨114702649751698680026380049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76468433167799120017586699 114702649751698680026380049)
  ·
    refine ⟨86026987313774010019785037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114702649751698680026380049 86026987313774010019785037)
    ·
      refine ⟨32260120242665253757419389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86026987313774010019785037 32260120242665253757419389)
      ·
        refine ⟨12097545090999470159032271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32260120242665253757419389 12097545090999470159032271)
        ·
          refine ⟨18146317636499205238548407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12097545090999470159032271 18146317636499205238548407)
          ·
            refine ⟨27219476454748807857822611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18146317636499205238548407 27219476454748807857822611)
            ·
              refine ⟨40829214682123211786733917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27219476454748807857822611 40829214682123211786733917)
              ·
                refine ⟨15310955505796204420025219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40829214682123211786733917 15310955505796204420025219)
                ·
                  refine ⟨22966433258694306630037829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15310955505796204420025219 22966433258694306630037829)
                  ·
                    refine ⟨4306206236005182493132093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22966433258694306630037829 4306206236005182493132093)
                    ·
                      refine ⟨1614827338501943434924535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4306206236005182493132093 1614827338501943434924535)
                      ·
                        rfl

theorem cell23_3144865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3144865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144865 prefixEnd_3144865 := by exact prefixLift 3144865
  have htrace : WordTrace (prefixWord ++ tailWord_3144865) baseStart_3144865 baseEnd_3144865 := by
    simpa [prefixWord, tailWord_3144865, baseEnd_3144865] using wordTrace_append hprefix tailTrace_3144865
  have hstable : (prefixWord ++ tailWord_3144865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144865).length < 2 ^ (prefixWord ++ tailWord_3144865).sum := by decide
  have hdescent : baseEnd_3144865 < baseStart_3144865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144882 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_3144882 : Nat := 118140960795 + 3144882 * 2 ^ 59
def prefixEnd_3144882 : Nat := 4983230072969 + 3 ^ 40 * 3144882 * 2
def baseEnd_3144882 : Nat := 1614836067673069868411957

theorem tailTrace_3144882 : CollatzResearch.WordTrace tailWord_3144882 prefixEnd_3144882 1614836067673069868411957 := by
  unfold tailWord_3144882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28675817448159272982437225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76468846528424727953165933 28675817448159272982437225)
  ·
    refine ⟨21506863086119454736827919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28675817448159272982437225 21506863086119454736827919)
    ·
      refine ⟨32260294629179182105241879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21506863086119454736827919 32260294629179182105241879)
      ·
        refine ⟨48390441943768773157862819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32260294629179182105241879 48390441943768773157862819)
        ·
          refine ⟨72585662915653159736794229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48390441943768773157862819 72585662915653159736794229)
          ·
            refine ⟨6804905898342483725324459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72585662915653159736794229 6804905898342483725324459)
            ·
              refine ⟨10207358847513725587986689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6804905898342483725324459 10207358847513725587986689)
              ·
                refine ⟨7655519135635294190990017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10207358847513725587986689 7655519135635294190990017)
                ·
                  refine ⟨5741639351726470643242513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655519135635294190990017 5741639351726470643242513)
                  ·
                    refine ⟨4306229513794852982431885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5741639351726470643242513 4306229513794852982431885)
                    ·
                      refine ⟨1614836067673069868411957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4306229513794852982431885 1614836067673069868411957)
                      ·
                        rfl

theorem cell23_3144882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_3144882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144882 prefixEnd_3144882 := by exact prefixLift 3144882
  have htrace : WordTrace (prefixWord ++ tailWord_3144882) baseStart_3144882 baseEnd_3144882 := by
    simpa [prefixWord, tailWord_3144882, baseEnd_3144882] using wordTrace_append hprefix tailTrace_3144882
  have hstable : (prefixWord ++ tailWord_3144882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144882).length < 2 ^ (prefixWord ++ tailWord_3144882).sum := by decide
  have hdescent : baseEnd_3144882 < baseStart_3144882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144888 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3144888 : Nat := 118140960795 + 3144888 * 2 ^ 59
def prefixEnd_3144888 : Nat := 4983230072969 + 3 ^ 40 * 3144888 * 2
def baseEnd_3144888 : Nat := 1614839148556996844936929

theorem tailTrace_3144888 : CollatzResearch.WordTrace tailWord_3144888 prefixEnd_3144888 1614839148556996844936929 := by
  unfold tailWord_3144888
  simp only [CollatzResearch.WordTrace]
  refine ⟨57351744315307677477233659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76468992420410236636311545 57351744315307677477233659)
  ·
    refine ⟨86027616472961516215850489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57351744315307677477233659 86027616472961516215850489)
    ·
      refine ⟨64520712354721137161887867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86027616472961516215850489 64520712354721137161887867)
      ·
        refine ⟨96781068532081705742831801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64520712354721137161887867 96781068532081705742831801)
        ·
          refine ⟨72585801399061279307123851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96781068532081705742831801 72585801399061279307123851)
          ·
            refine ⟨108878702098591918960685777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72585801399061279307123851 108878702098591918960685777)
            ·
              refine ⟨81659026573943939220514333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108878702098591918960685777 81659026573943939220514333)
              ·
                refine ⟨30622134965228977207692875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81659026573943939220514333 30622134965228977207692875)
                ·
                  refine ⟨45933202447843465811539313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30622134965228977207692875 45933202447843465811539313)
                  ·
                    refine ⟨34449901835882599358654485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45933202447843465811539313 34449901835882599358654485)
                    ·
                      refine ⟨1614839148556996844936929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34449901835882599358654485 1614839148556996844936929)
                      ·
                        rfl

theorem cell23_3144888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3144888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144888 prefixEnd_3144888 := by exact prefixLift 3144888
  have htrace : WordTrace (prefixWord ++ tailWord_3144888) baseStart_3144888 baseEnd_3144888 := by
    simpa [prefixWord, tailWord_3144888, baseEnd_3144888] using wordTrace_append hprefix tailTrace_3144888
  have hstable : (prefixWord ++ tailWord_3144888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144888).length < 2 ^ (prefixWord ++ tailWord_3144888).sum := by decide
  have hdescent : baseEnd_3144888 < baseStart_3144888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144916 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3144916 : Nat := 118140960795 + 3144916 * 2 ^ 59
def prefixEnd_3144916 : Nat := 4983230072969 + 3 ^ 40 * 3144916 * 2
def baseEnd_3144916 : Nat := 1614853526015322735386801

theorem tailTrace_3144916 : CollatzResearch.WordTrace tailWord_3144916 prefixEnd_3144916 1614853526015322735386801 := by
  unfold tailWord_3144916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57352254937256957868243301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76469673249675943824324401 57352254937256957868243301)
  ·
    refine ⟨10753547800735679600295619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57352254937256957868243301 10753547800735679600295619)
    ·
      refine ⟨16130321701103519400443429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10753547800735679600295619 16130321701103519400443429)
      ·
        refine ⟨3024435318956909887583143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16130321701103519400443429 3024435318956909887583143)
        ·
          refine ⟨4536652978435364831374715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024435318956909887583143 4536652978435364831374715)
          ·
            refine ⟨6804979467653047247062073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536652978435364831374715 6804979467653047247062073)
            ·
              refine ⟨5103734600739785435296555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6804979467653047247062073 5103734600739785435296555)
              ·
                refine ⟨7655601901109678152944833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103734600739785435296555 7655601901109678152944833)
                ·
                  refine ⟨5741701425832258614708625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655601901109678152944833 5741701425832258614708625)
                  ·
                    refine ⟨4306276069374193961031469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5741701425832258614708625 4306276069374193961031469)
                    ·
                      refine ⟨1614853526015322735386801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4306276069374193961031469 1614853526015322735386801)
                      ·
                        rfl

theorem cell23_3144916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3144916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144916 prefixEnd_3144916 := by exact prefixLift 3144916
  have htrace : WordTrace (prefixWord ++ tailWord_3144916) baseStart_3144916 baseEnd_3144916 := by
    simpa [prefixWord, tailWord_3144916, baseEnd_3144916] using wordTrace_append hprefix tailTrace_3144916
  have hstable : (prefixWord ++ tailWord_3144916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144916).length < 2 ^ (prefixWord ++ tailWord_3144916).sum := by decide
  have hdescent : baseEnd_3144916 < baseStart_3144916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144969 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 3, 2, 2]
def baseStart_3144969 : Nat := 118140960795 + 3144969 * 2 ^ 59
def prefixEnd_3144969 : Nat := 4983230072969 + 3 ^ 40 * 3144969 * 2
def baseEnd_3144969 : Nat := 1614880740490011028024057

theorem tailTrace_3144969 : CollatzResearch.WordTrace tailWord_3144969 prefixEnd_3144969 1614880740490011028024057 := by
  unfold tailWord_3144969
  simp only [CollatzResearch.WordTrace]
  refine ⟨114706442943321905788165961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76470961962214603858777307 114706442943321905788165961)
  ·
    refine ⟨86029832207491429341124471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114706442943321905788165961 86029832207491429341124471)
    ·
      refine ⟨129044748311237144011686707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86029832207491429341124471 129044748311237144011686707)
      ·
        refine ⟨193567122466855716017530061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129044748311237144011686707 193567122466855716017530061)
        ·
          refine ⟨72587670925070893506573773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193567122466855716017530061 72587670925070893506573773)
          ·
            refine ⟨27220376596901585064965165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72587670925070893506573773 27220376596901585064965165)
            ·
              refine ⟨10207641223838094399361937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27220376596901585064965165 10207641223838094399361937)
              ·
                refine ⟨7655730917878570799521453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10207641223838094399361937 7655730917878570799521453)
                ·
                  refine ⟨2870899094204464049820545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7655730917878570799521453 2870899094204464049820545)
                  ·
                    refine ⟨2153174320653348037365409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2870899094204464049820545 2153174320653348037365409)
                    ·
                      refine ⟨1614880740490011028024057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153174320653348037365409 1614880740490011028024057)
                      ·
                        rfl

theorem cell23_3144969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 2, 2].length) (baseStart_3144969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144969 prefixEnd_3144969 := by exact prefixLift 3144969
  have htrace : WordTrace (prefixWord ++ tailWord_3144969) baseStart_3144969 baseEnd_3144969 := by
    simpa [prefixWord, tailWord_3144969, baseEnd_3144969] using wordTrace_append hprefix tailTrace_3144969
  have hstable : (prefixWord ++ tailWord_3144969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144969).length < 2 ^ (prefixWord ++ tailWord_3144969).sum := by decide
  have hdescent : baseEnd_3144969 < baseStart_3144969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144972 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3144972 : Nat := 118140960795 + 3144972 * 2 ^ 59
def prefixEnd_3144972 : Nat := 4983230072969 + 3 ^ 40 * 3144972 * 2
def baseEnd_3144972 : Nat := 1614882280931974516286543

theorem tailTrace_3144972 : CollatzResearch.WordTrace tailWord_3144972 prefixEnd_3144972 1614882280931974516286543 := by
  unfold tailWord_3144972
  simp only [CollatzResearch.WordTrace]
  refine ⟨57353276181155518650262585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76471034908207358200350113 57353276181155518650262585)
  ·
    refine ⟨43014957135866638987696939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57353276181155518650262585 43014957135866638987696939)
    ·
      refine ⟨64522435703799958481545409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43014957135866638987696939 64522435703799958481545409)
      ·
        refine ⟨48391826777849968861159057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64522435703799958481545409 48391826777849968861159057)
        ·
          refine ⟨36293870083387476645869293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48391826777849968861159057 36293870083387476645869293)
          ·
            refine ⟨13610201281270303742200985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36293870083387476645869293 13610201281270303742200985)
            ·
              refine ⟨10207650960952727806650739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13610201281270303742200985 10207650960952727806650739)
              ·
                refine ⟨15311476441429091709976109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10207650960952727806650739 15311476441429091709976109)
                ·
                  refine ⟨5741803665535909391241041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15311476441429091709976109 5741803665535909391241041)
                  ·
                    refine ⟨4306352749151932043430781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5741803665535909391241041 4306352749151932043430781)
                    ·
                      refine ⟨1614882280931974516286543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4306352749151932043430781 1614882280931974516286543)
                      ·
                        rfl

theorem cell23_3144972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3144972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144972 prefixEnd_3144972 := by exact prefixLift 3144972
  have htrace : WordTrace (prefixWord ++ tailWord_3144972) baseStart_3144972 baseEnd_3144972 := by
    simpa [prefixWord, tailWord_3144972, baseEnd_3144972] using wordTrace_append hprefix tailTrace_3144972
  have hstable : (prefixWord ++ tailWord_3144972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144972).length < 2 ^ (prefixWord ++ tailWord_3144972).sum := by decide
  have hdescent : baseEnd_3144972 < baseStart_3144972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144986 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4]
def baseStart_3144986 : Nat := 118140960795 + 3144986 * 2 ^ 59
def prefixEnd_3144986 : Nat := 4983230072969 + 3 ^ 40 * 3144986 * 2
def baseEnd_3144986 : Nat := 1614889469661137461511479

theorem tailTrace_3144986 : CollatzResearch.WordTrace tailWord_3144986 prefixEnd_3144986 1614889469661137461511479 := by
  unfold tailWord_3144986
  simp only [CollatzResearch.WordTrace]
  refine ⟨28676765746065079422883703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76471375322840211794356541 28676765746065079422883703)
  ·
    refine ⟨43015148619097619134325555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28676765746065079422883703 43015148619097619134325555)
    ·
      refine ⟨64522722928646428701488333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43015148619097619134325555 64522722928646428701488333)
      ·
        refine ⟨24196021098242410763058125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64522722928646428701488333 24196021098242410763058125)
        ·
          refine ⟨9073507911840904036146797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24196021098242410763058125 9073507911840904036146797)
          ·
            refine ⟨3402565466940339013555049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9073507911840904036146797 3402565466940339013555049)
            ·
              refine ⟨2551924100205254260166287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3402565466940339013555049 2551924100205254260166287)
              ·
                refine ⟨3827886150307881390249431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551924100205254260166287 3827886150307881390249431)
                ·
                  refine ⟨5741829225461822085374147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827886150307881390249431 5741829225461822085374147)
                  ·
                    refine ⟨8612743838192733128061221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5741829225461822085374147 8612743838192733128061221)
                    ·
                      refine ⟨1614889469661137461511479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8612743838192733128061221 1614889469661137461511479)
                      ·
                        rfl

theorem cell23_3144986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_3144986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3144986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3144986 prefixEnd_3144986 := by exact prefixLift 3144986
  have htrace : WordTrace (prefixWord ++ tailWord_3144986) baseStart_3144986 baseEnd_3144986 := by
    simpa [prefixWord, tailWord_3144986, baseEnd_3144986] using wordTrace_append hprefix tailTrace_3144986
  have hstable : (prefixWord ++ tailWord_3144986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144986).length < 2 ^ (prefixWord ++ tailWord_3144986).sum := by decide
  have hdescent : baseEnd_3144986 < baseStart_3144986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145065 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 7]
def baseStart_3145065 : Nat := 118140960795 + 3145065 * 2 ^ 59
def prefixEnd_3145065 : Nat := 4983230072969 + 3 ^ 40 * 3145065 * 2
def baseEnd_3145065 : Nat := 179436670514760294713735

theorem tailTrace_3145065 : CollatzResearch.WordTrace tailWord_3145065 prefixEnd_3145065 179436670514760294713735 := by
  unfold tailWord_3145065
  simp only [CollatzResearch.WordTrace]
  refine ⟨114709944350974114183660649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76473296233982742789107099 114709944350974114183660649)
  ·
    refine ⟨86032458263230585637745487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114709944350974114183660649 86032458263230585637745487)
    ·
      refine ⟨129048687394845878456618231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86032458263230585637745487 129048687394845878456618231)
      ·
        refine ⟨193573031092268817684927347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129048687394845878456618231 193573031092268817684927347)
        ·
          refine ⟨290359546638403226527391021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193573031092268817684927347 290359546638403226527391021)
          ·
            refine ⟨108884829989401209947771633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290359546638403226527391021 108884829989401209947771633)
            ·
              refine ⟨81663622492050907460828725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108884829989401209947771633 81663622492050907460828725)
              ·
                refine ⟨7655964608629772574452693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81663622492050907460828725 7655964608629772574452693)
                ·
                  refine ⟨179436670514760294713735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7655964608629772574452693 179436670514760294713735)
                  ·
                    rfl

theorem cell23_3145065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_3145065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145065 prefixEnd_3145065 := by exact prefixLift 3145065
  have htrace : WordTrace (prefixWord ++ tailWord_3145065) baseStart_3145065 baseEnd_3145065 := by
    simpa [prefixWord, tailWord_3145065, baseEnd_3145065] using wordTrace_append hprefix tailTrace_3145065
  have hstable : (prefixWord ++ tailWord_3145065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145065).length < 2 ^ (prefixWord ++ tailWord_3145065).sum := by decide
  have hdescent : baseEnd_3145065 < baseStart_3145065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145105 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_3145105 : Nat := 118140960795 + 3145105 * 2 ^ 59
def prefixEnd_3145105 : Nat := 4983230072969 + 3 ^ 40 * 3145105 * 2
def baseEnd_3145105 : Nat := 1614950573859022495923431

theorem tailTrace_3145105 : CollatzResearch.WordTrace tailWord_3145105 prefixEnd_3145105 1614950573859022495923431 := by
  unfold tailWord_3145105
  simp only [CollatzResearch.WordTrace]
  refine ⟨114711403270829201015116769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76474268847219467343411179 114711403270829201015116769)
  ·
    refine ⟨86033552453121900761337577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114711403270829201015116769 86033552453121900761337577)
    ·
      refine ⟨64525164339841425571003183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86033552453121900761337577 64525164339841425571003183)
      ·
        refine ⟨96787746509762138356504775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64525164339841425571003183 96787746509762138356504775)
        ·
          refine ⟨145181619764643207534757163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96787746509762138356504775 145181619764643207534757163)
          ·
            refine ⟨217772429646964811302135745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145181619764643207534757163 217772429646964811302135745)
            ·
              refine ⟨163329322235223608476601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217772429646964811302135745 163329322235223608476601809)
              ·
                refine ⟨122496991676417706357451357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163329322235223608476601809 122496991676417706357451357)
                ·
                  refine ⟨45936371878656639884044259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122496991676417706357451357 45936371878656639884044259)
                  ·
                    refine ⟨68904557817984959826066389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45936371878656639884044259 68904557817984959826066389)
                    ·
                      refine ⟨1614950573859022495923431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68904557817984959826066389 1614950573859022495923431)
                      ·
                        rfl

theorem cell23_3145105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_3145105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145105 prefixEnd_3145105 := by exact prefixLift 3145105
  have htrace : WordTrace (prefixWord ++ tailWord_3145105) baseStart_3145105 baseEnd_3145105 := by
    simpa [prefixWord, tailWord_3145105, baseEnd_3145105] using wordTrace_append hprefix tailTrace_3145105
  have hstable : (prefixWord ++ tailWord_3145105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145105).length < 2 ^ (prefixWord ++ tailWord_3145105).sum := by decide
  have hdescent : baseEnd_3145105 < baseStart_3145105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145119 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 2, 5, 2]
def baseStart_3145119 : Nat := 118140960795 + 3145119 * 2 ^ 59
def prefixEnd_3145119 : Nat := 4983230072969 + 3 ^ 40 * 3145119 * 2
def baseEnd_3145119 : Nat := 1614957762588185441148367

theorem tailTrace_3145119 : CollatzResearch.WordTrace tailWord_3145119 prefixEnd_3145119 1614957762588185441148367 := by
  unfold tailWord_3145119
  simp only [CollatzResearch.WordTrace]
  refine ⟨114711913892778481406126411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76474609261852320937417607 114711913892778481406126411)
  ·
    refine ⟨172067870839167722109189617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114711913892778481406126411 172067870839167722109189617)
    ·
      refine ⟨129050903129375791581892213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172067870839167722109189617 129050903129375791581892213)
      ·
        refine ⟨12098522168378980460802395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129050903129375791581892213 12098522168378980460802395)
        ·
          refine ⟨18147783252568470691203593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12098522168378980460802395 18147783252568470691203593)
          ·
            refine ⟨13610837439426353018402695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18147783252568470691203593 13610837439426353018402695)
            ·
              refine ⟨20416256159139529527604043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13610837439426353018402695 20416256159139529527604043)
              ·
                refine ⟨30624384238709294291406065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20416256159139529527604043 30624384238709294291406065)
                ·
                  refine ⟨22968288179031970718554549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30624384238709294291406065 22968288179031970718554549)
                  ·
                    refine ⟨2153277016784247254864489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22968288179031970718554549 2153277016784247254864489)
                    ·
                      refine ⟨1614957762588185441148367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153277016784247254864489 1614957762588185441148367)
                      ·
                        rfl

theorem cell23_3145119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_3145119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145119 prefixEnd_3145119 := by exact prefixLift 3145119
  have htrace : WordTrace (prefixWord ++ tailWord_3145119) baseStart_3145119 baseEnd_3145119 := by
    simpa [prefixWord, tailWord_3145119, baseEnd_3145119] using wordTrace_append hprefix tailTrace_3145119
  have hstable : (prefixWord ++ tailWord_3145119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145119).length < 2 ^ (prefixWord ++ tailWord_3145119).sum := by decide
  have hdescent : baseEnd_3145119 < baseStart_3145119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145132 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_3145132 : Nat := 118140960795 + 3145132 * 2 ^ 59
def prefixEnd_3145132 : Nat := 4983230072969 + 3 ^ 40 * 3145132 * 2
def baseEnd_3145132 : Nat := 1614964437836693890285807

theorem tailTrace_3145132 : CollatzResearch.WordTrace tailWord_3145132 prefixEnd_3145132 1614964437836693890285807 := by
  unfold tailWord_3145132
  simp only [CollatzResearch.WordTrace]
  refine ⟨57356194020865692313174825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76474925361154256417566433 57356194020865692313174825)
  ·
    refine ⟨43017145515649269234881119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57356194020865692313174825 43017145515649269234881119)
    ·
      refine ⟨64525718273473903852321679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43017145515649269234881119 64525718273473903852321679)
      ·
        refine ⟨96788577410210855778482519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64525718273473903852321679 96788577410210855778482519)
        ·
          refine ⟨145182866115316283667723779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96788577410210855778482519 145182866115316283667723779)
          ·
            refine ⟨217774299172974425501585669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145182866115316283667723779 217774299172974425501585669)
            ·
              refine ⟨40832681094932704781547313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217774299172974425501585669 40832681094932704781547313)
              ·
                refine ⟨30624510821199528586160485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40832681094932704781547313 30624510821199528586160485)
                ·
                  refine ⟨5742095778974911609905091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30624510821199528586160485 5742095778974911609905091)
                  ·
                    refine ⟨8613143668462367414857637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5742095778974911609905091 8613143668462367414857637)
                    ·
                      refine ⟨1614964437836693890285807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8613143668462367414857637 1614964437836693890285807)
                      ·
                        rfl

theorem cell23_3145132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_3145132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145132 prefixEnd_3145132 := by exact prefixLift 3145132
  have htrace : WordTrace (prefixWord ++ tailWord_3145132) baseStart_3145132 baseEnd_3145132 := by
    simpa [prefixWord, tailWord_3145132, baseEnd_3145132] using wordTrace_append hprefix tailTrace_3145132
  have hstable : (prefixWord ++ tailWord_3145132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145132).length < 2 ^ (prefixWord ++ tailWord_3145132).sum := by decide
  have hdescent : baseEnd_3145132 < baseStart_3145132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145149 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_3145149 : Nat := 118140960795 + 3145149 * 2 ^ 59
def prefixEnd_3145149 : Nat := 4983230072969 + 3 ^ 40 * 3145149 * 2
def baseEnd_3145149 : Nat := 1614973167007820323773229

theorem tailTrace_3145149 : CollatzResearch.WordTrace tailWord_3145149 prefixEnd_3145149 1614973167007820323773229 := by
  unfold tailWord_3145149
  simp only [CollatzResearch.WordTrace]
  refine ⟨114713008082669796529718501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76475338721779864353145667 114713008082669796529718501)
  ·
    refine ⟨21508689015500586849322219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114713008082669796529718501 21508689015500586849322219)
    ·
      refine ⟨32263033523250880273983329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21508689015500586849322219 32263033523250880273983329)
      ·
        refine ⟨24197275142438160205487497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32263033523250880273983329 24197275142438160205487497)
        ·
          refine ⟨18147956356828620154115623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24197275142438160205487497 18147956356828620154115623)
          ·
            refine ⟨27221934535242930231173435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18147956356828620154115623 27221934535242930231173435)
            ·
              refine ⟨40832901802864395346760153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27221934535242930231173435 40832901802864395346760153)
              ·
                refine ⟨30624676352148296510070115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40832901802864395346760153 30624676352148296510070115)
                ·
                  refine ⟨45937014528222444765105173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30624676352148296510070115 45937014528222444765105173)
                  ·
                    refine ⟨2153297556010427098364305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45937014528222444765105173 2153297556010427098364305)
                    ·
                      refine ⟨1614973167007820323773229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153297556010427098364305 1614973167007820323773229)
                      ·
                        rfl

theorem cell23_3145149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_3145149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145149 prefixEnd_3145149 := by exact prefixLift 3145149
  have htrace : WordTrace (prefixWord ++ tailWord_3145149) baseStart_3145149 baseEnd_3145149 := by
    simpa [prefixWord, tailWord_3145149, baseEnd_3145149] using wordTrace_append hprefix tailTrace_3145149
  have hstable : (prefixWord ++ tailWord_3145149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145149).length < 2 ^ (prefixWord ++ tailWord_3145149).sum := by decide
  have hdescent : baseEnd_3145149 < baseStart_3145149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145162 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3145162 : Nat := 118140960795 + 3145162 * 2 ^ 59
def prefixEnd_3145162 : Nat := 4983230072969 + 3 ^ 40 * 3145162 * 2
def baseEnd_3145162 : Nat := 1614979842256328772910669

theorem tailTrace_3145162 : CollatzResearch.WordTrace tailWord_3145162 prefixEnd_3145162 1614979842256328772910669 := by
  unfold tailWord_3145162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28678370557905674937485435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76475654821081799833294493 28678370557905674937485435)
  ·
    refine ⟨43017555836858512406228153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28678370557905674937485435 43017555836858512406228153)
    ·
      refine ⟨32263166877643884304671115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43017555836858512406228153 32263166877643884304671115)
      ·
        refine ⟨48394750316465826457006673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32263166877643884304671115 48394750316465826457006673)
        ·
          refine ⟨36296062737349369842755005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48394750316465826457006673 36296062737349369842755005)
          ·
            refine ⟨13611023526506013691033127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36296062737349369842755005 13611023526506013691033127)
            ·
              refine ⟨20416535289759020536549691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13611023526506013691033127 20416535289759020536549691)
              ·
                refine ⟨30624802934638530804824537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20416535289759020536549691 30624802934638530804824537)
                ·
                  refine ⟨22968602200978898103618403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30624802934638530804824537 22968602200978898103618403)
                  ·
                    refine ⟨34452903301468347155427605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22968602200978898103618403 34452903301468347155427605)
                    ·
                      refine ⟨1614979842256328772910669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34452903301468347155427605 1614979842256328772910669)
                      ·
                        rfl

theorem cell23_3145162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3145162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145162 prefixEnd_3145162 := by exact prefixLift 3145162
  have htrace : WordTrace (prefixWord ++ tailWord_3145162) baseStart_3145162 baseEnd_3145162 := by
    simpa [prefixWord, tailWord_3145162, baseEnd_3145162] using wordTrace_append hprefix tailTrace_3145162
  have hstable : (prefixWord ++ tailWord_3145162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145162).length < 2 ^ (prefixWord ++ tailWord_3145162).sum := by decide
  have hdescent : baseEnd_3145162 < baseStart_3145162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145176 : List Nat := [2, 1, 2, 2, 2, 1, 4, 4, 1, 4]
def baseStart_3145176 : Nat := 118140960795 + 3145176 * 2 ^ 59
def prefixEnd_3145176 : Nat := 4983230072969 + 3 ^ 40 * 3145176 * 2
def baseEnd_3145176 : Nat := 538329010328497239378535

theorem tailTrace_3145176 : CollatzResearch.WordTrace tailWord_3145176 prefixEnd_3145176 538329010328497239378535 := by
  unfold tailWord_3145176
  simp only [CollatzResearch.WordTrace]
  refine ⟨57356996426785990070475691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76475995235714653427300921 57356996426785990070475691)
  ·
    refine ⟨86035494640178985105713537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57356996426785990070475691 86035494640178985105713537)
    ·
      refine ⟨64526620980134238829285153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86035494640178985105713537 64526620980134238829285153)
      ·
        refine ⟨48394965735100679121963865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64526620980134238829285153 48394965735100679121963865)
        ·
          refine ⟨36296224301325509341472899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48394965735100679121963865 36296224301325509341472899)
          ·
            refine ⟨54444336451988264012209349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36296224301325509341472899 54444336451988264012209349)
            ·
              refine ⟨10208313084747799502289253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54444336451988264012209349 10208313084747799502289253)
              ·
                refine ⟨1914058703390212406679235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10208313084747799502289253 1914058703390212406679235)
                ·
                  refine ⟨2871088055085318610018853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914058703390212406679235 2871088055085318610018853)
                  ·
                    refine ⟨538329010328497239378535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2871088055085318610018853 538329010328497239378535)
                    ·
                      rfl

theorem cell23_3145176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_3145176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145176 prefixEnd_3145176 := by exact prefixLift 3145176
  have htrace : WordTrace (prefixWord ++ tailWord_3145176) baseStart_3145176 baseEnd_3145176 := by
    simpa [prefixWord, tailWord_3145176, baseEnd_3145176] using wordTrace_append hprefix tailTrace_3145176
  have hstable : (prefixWord ++ tailWord_3145176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145176).length < 2 ^ (prefixWord ++ tailWord_3145176).sum := by decide
  have hdescent : baseEnd_3145176 < baseStart_3145176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145192 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3145192 : Nat := 118140960795 + 3145192 * 2 ^ 59
def prefixEnd_3145192 : Nat := 4983230072969 + 3 ^ 40 * 3145192 * 2
def baseEnd_3145192 : Nat := 1614995246675963655535531

theorem tailTrace_3145192 : CollatzResearch.WordTrace tailWord_3145192 prefixEnd_3145192 1614995246675963655535531 := by
  unfold tailWord_3145192
  simp only [CollatzResearch.WordTrace]
  refine ⟨57357288210757007436766915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76476384281009343249022553 57357288210757007436766915)
  ·
    refine ⟨86035932316135511155150373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57357288210757007436766915 86035932316135511155150373)
    ·
      refine ⟨16131737309275408341590695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86035932316135511155150373 16131737309275408341590695)
      ·
        refine ⟨24197605963913112512386043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16131737309275408341590695 24197605963913112512386043)
        ·
          refine ⟨36296408945869668768579065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24197605963913112512386043 36296408945869668768579065)
          ·
            refine ⟨27222306709402251576434299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36296408945869668768579065 27222306709402251576434299)
            ·
              refine ⟨40833460064103377364651449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27222306709402251576434299 40833460064103377364651449)
              ·
                refine ⟨30625095048077533023488587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40833460064103377364651449 30625095048077533023488587)
                ·
                  refine ⟨45937642572116299535232881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30625095048077533023488587 45937642572116299535232881)
                  ·
                    refine ⟨34453231929087224651424661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45937642572116299535232881 34453231929087224651424661)
                    ·
                      refine ⟨1614995246675963655535531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34453231929087224651424661 1614995246675963655535531)
                      ·
                        rfl

theorem cell23_3145192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3145192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145192 prefixEnd_3145192 := by exact prefixLift 3145192
  have htrace : WordTrace (prefixWord ++ tailWord_3145192) baseStart_3145192 baseEnd_3145192 := by
    simpa [prefixWord, tailWord_3145192, baseEnd_3145192] using wordTrace_append hprefix tailTrace_3145192
  have hstable : (prefixWord ++ tailWord_3145192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145192).length < 2 ^ (prefixWord ++ tailWord_3145192).sum := by decide
  have hdescent : baseEnd_3145192 < baseStart_3145192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145226 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_3145226 : Nat := 118140960795 + 3145226 * 2 ^ 59
def prefixEnd_3145226 : Nat := 4983230072969 + 3 ^ 40 * 3145226 * 2
def baseEnd_3145226 : Nat := 1615012705018216522510375

theorem tailTrace_3145226 : CollatzResearch.WordTrace tailWord_3145226 prefixEnd_3145226 1615012705018216522510375 := by
  unfold tailWord_3145226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28678954125847709670067883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76477211002260559120181021 28678954125847709670067883)
  ·
    refine ⟨43018431188771564505101825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28678954125847709670067883 43018431188771564505101825)
    ·
      refine ⟨32263823391578673378826369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43018431188771564505101825 32263823391578673378826369)
      ·
        refine ⟨24197867543684005034119777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32263823391578673378826369 24197867543684005034119777)
        ·
          refine ⟨18148400657763003775589833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24197867543684005034119777 18148400657763003775589833)
          ·
            refine ⟨13611300493322252831692375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18148400657763003775589833 13611300493322252831692375)
            ·
              refine ⟨20416950739983379247538563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13611300493322252831692375 20416950739983379247538563)
              ·
                refine ⟨30625426109975068871307845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20416950739983379247538563 30625426109975068871307845)
                ·
                  refine ⟨5742267395620325413370221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30625426109975068871307845 5742267395620325413370221)
                  ·
                    refine ⟨2153350273357622030013833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5742267395620325413370221 2153350273357622030013833)
                    ·
                      refine ⟨1615012705018216522510375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153350273357622030013833 1615012705018216522510375)
                      ·
                        rfl

theorem cell23_3145226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_3145226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145226 prefixEnd_3145226 := by exact prefixLift 3145226
  have htrace : WordTrace (prefixWord ++ tailWord_3145226) baseStart_3145226 baseEnd_3145226 := by
    simpa [prefixWord, tailWord_3145226, baseEnd_3145226] using wordTrace_append hprefix tailTrace_3145226
  have hstable : (prefixWord ++ tailWord_3145226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145226).length < 2 ^ (prefixWord ++ tailWord_3145226).sum := by decide
  have hdescent : baseEnd_3145226 < baseStart_3145226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145269 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3145269 : Nat := 118140960795 + 3145269 * 2 ^ 59
def prefixEnd_3145269 : Nat := 4983230072969 + 3 ^ 40 * 3145269 * 2
def baseEnd_3145269 : Nat := 1615034784686359854272677

theorem tailTrace_3145269 : CollatzResearch.WordTrace tailWord_3145269 prefixEnd_3145269 1615034784686359854272677 := by
  unfold tailWord_3145269
  simp only [CollatzResearch.WordTrace]
  refine ⟨114717384842235057024086861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76478256561490038016057907 114717384842235057024086861)
  ·
    refine ⟨43019019315838146384032573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114717384842235057024086861 43019019315838146384032573)
    ·
      refine ⟨16132132243439304894012215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43019019315838146384032573 16132132243439304894012215)
      ·
        refine ⟨24198198365158957341018323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16132132243439304894012215 24198198365158957341018323)
        ·
          refine ⟨36297297547738436011527485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24198198365158957341018323 36297297547738436011527485)
          ·
            refine ⟨13611486580401913504322807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36297297547738436011527485 13611486580401913504322807)
            ·
              refine ⟨20417229870602870256484211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13611486580401913504322807 20417229870602870256484211)
              ·
                refine ⟨30625844805904305384726317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20417229870602870256484211 30625844805904305384726317)
                ·
                  refine ⟨11484691802214114519272369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30625844805904305384726317 11484691802214114519272369)
                  ·
                    refine ⟨8613518851660585889454277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11484691802214114519272369 8613518851660585889454277)
                    ·
                      refine ⟨1615034784686359854272677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8613518851660585889454277 1615034784686359854272677)
                      ·
                        rfl

theorem cell23_3145269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3145269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145269 prefixEnd_3145269 := by exact prefixLift 3145269
  have htrace : WordTrace (prefixWord ++ tailWord_3145269) baseStart_3145269 baseEnd_3145269 := by
    simpa [prefixWord, tailWord_3145269, baseEnd_3145269] using wordTrace_append hprefix tailTrace_3145269
  have hstable : (prefixWord ++ tailWord_3145269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145269).length < 2 ^ (prefixWord ++ tailWord_3145269).sum := by decide
  have hdescent : baseEnd_3145269 < baseStart_3145269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
