import V185TrunkScan23Chunk0180

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1071834 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1071834 : Nat := 118140960795 + 1071834 * 2 ^ 59
def prefixEnd_1071834 : Nat := 4983230072969 + 3 ^ 40 * 1071834 * 2
def baseEnd_1071834 : Nat := 550366023831264678245731

theorem tailTrace_1071834 : CollatzResearch.WordTrace tailWord_1071834 prefixEnd_1071834 550366023831264678245731 := by
  unfold tailWord_1071834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773249399733986879645639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26061998399290631679055037 9773249399733986879645639)
  ·
    refine ⟨14659874099600980319468459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9773249399733986879645639 14659874099600980319468459)
    ·
      refine ⟨21989811149401470479202689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14659874099600980319468459 21989811149401470479202689)
      ·
        refine ⟨16492358362051102859402017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21989811149401470479202689 16492358362051102859402017)
        ·
          refine ⟨12369268771538327144551513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16492358362051102859402017 12369268771538327144551513)
          ·
            refine ⟨9276951578653745358413635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12369268771538327144551513 9276951578653745358413635)
            ·
              refine ⟨13915427367980618037620453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9276951578653745358413635 13915427367980618037620453)
              ·
                refine ⟨2609142631496365882053835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13915427367980618037620453 2609142631496365882053835)
                ·
                  refine ⟨3913713947244548823080753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609142631496365882053835 3913713947244548823080753)
                  ·
                    refine ⟨2935285460433411617310565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3913713947244548823080753 2935285460433411617310565)
                    ·
                      refine ⟨550366023831264678245731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2935285460433411617310565 550366023831264678245731)
                      ·
                        rfl

theorem cell23_1071834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1071834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071834 prefixEnd_1071834 := by exact prefixLift 1071834
  have htrace : WordTrace (prefixWord ++ tailWord_1071834) baseStart_1071834 baseEnd_1071834 := by
    simpa [prefixWord, tailWord_1071834, baseEnd_1071834] using wordTrace_append hprefix tailTrace_1071834
  have hstable : (prefixWord ++ tailWord_1071834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071834).length < 2 ^ (prefixWord ++ tailWord_1071834).sum := by decide
  have hdescent : baseEnd_1071834 < baseStart_1071834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071855 : List Nat := [1, 1, 2, 1, 5, 2, 2, 4, 1, 2, 2]
def baseStart_1071855 : Nat := 118140960795 + 1071855 * 2 ^ 59
def prefixEnd_1071855 : Nat := 4983230072969 + 3 ^ 40 * 1071855 * 2
def baseEnd_1071855 : Nat := 550376806925009096083135

theorem tailTrace_1071855 : CollatzResearch.WordTrace tailWord_1071855 prefixEnd_1071855 550376806925009096083135 := by
  unfold tailWord_1071855
  simp only [CollatzResearch.WordTrace]
  refine ⟨39093763531859868105097019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26062509021239912070064679 39093763531859868105097019)
  ·
    refine ⟨58640645297789802157645529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39093763531859868105097019 58640645297789802157645529)
    ·
      refine ⟨43980483973342351618234147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58640645297789802157645529 43980483973342351618234147)
      ·
        refine ⟨65970725960013527427351221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43980483973342351618234147 65970725960013527427351221)
        ·
          refine ⟨6184755558751268196314177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65970725960013527427351221 6184755558751268196314177)
          ·
            refine ⟨4638566669063451147235633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6184755558751268196314177 4638566669063451147235633)
            ·
              refine ⟨3478925001797588360426725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638566669063451147235633 3478925001797588360426725)
              ·
                refine ⟨652298437837047817580011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3478925001797588360426725 652298437837047817580011)
                ·
                  refine ⟨978447656755571726370017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652298437837047817580011 978447656755571726370017)
                  ·
                    refine ⟨733835742566678794777513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 978447656755571726370017 733835742566678794777513)
                    ·
                      refine ⟨550376806925009096083135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733835742566678794777513 550376806925009096083135)
                      ·
                        rfl

theorem cell23_1071855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 2, 2].length) (baseStart_1071855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071855 prefixEnd_1071855 := by exact prefixLift 1071855
  have htrace : WordTrace (prefixWord ++ tailWord_1071855) baseStart_1071855 baseEnd_1071855 := by
    simpa [prefixWord, tailWord_1071855, baseEnd_1071855] using wordTrace_append hprefix tailTrace_1071855
  have hstable : (prefixWord ++ tailWord_1071855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071855).length < 2 ^ (prefixWord ++ tailWord_1071855).sum := by decide
  have hdescent : baseEnd_1071855 < baseStart_1071855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071881 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 3, 3, 2]
def baseStart_1071881 : Nat := 118140960795 + 1071881 * 2 ^ 59
def prefixEnd_1071881 : Nat := 4983230072969 + 3 ^ 40 * 1071881 * 2
def baseEnd_1071881 : Nat := 550390157422025994358015

theorem tailTrace_1071881 : CollatzResearch.WordTrace tailWord_1071881 prefixEnd_1071881 550390157422025994358015 := by
  unfold tailWord_1071881
  simp only [CollatzResearch.WordTrace]
  refine ⟨39094711829765674545543497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26063141219843783030362331 39094711829765674545543497)
  ·
    refine ⟨29321033872324255909157623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39094711829765674545543497 29321033872324255909157623)
    ·
      refine ⟨43981550808486383863736435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29321033872324255909157623 43981550808486383863736435)
      ·
        refine ⟨65972326212729575795604653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43981550808486383863736435 65972326212729575795604653)
        ·
          refine ⟨24739622329773590923351745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65972326212729575795604653 24739622329773590923351745)
          ·
            refine ⟨18554716747330193192513809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24739622329773590923351745 18554716747330193192513809)
            ·
              refine ⟨13916037560497644894385357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18554716747330193192513809 13916037560497644894385357)
              ·
                refine ⟨5218514085186616835394509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13916037560497644894385357 5218514085186616835394509)
                ·
                  refine ⟨1956942781944981313272941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5218514085186616835394509 1956942781944981313272941)
                  ·
                    refine ⟨733853543229367992477353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956942781944981313272941 733853543229367992477353)
                    ·
                      refine ⟨550390157422025994358015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733853543229367992477353 550390157422025994358015)
                      ·
                        rfl

theorem cell23_1071881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 3, 2].length) (baseStart_1071881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071881 prefixEnd_1071881 := by exact prefixLift 1071881
  have htrace : WordTrace (prefixWord ++ tailWord_1071881) baseStart_1071881 baseEnd_1071881 := by
    simpa [prefixWord, tailWord_1071881, baseEnd_1071881] using wordTrace_append hprefix tailTrace_1071881
  have hstable : (prefixWord ++ tailWord_1071881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071881).length < 2 ^ (prefixWord ++ tailWord_1071881).sum := by decide
  have hdescent : baseEnd_1071881 < baseStart_1071881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071898 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2]
def baseStart_1071898 : Nat := 118140960795 + 1071898 * 2 ^ 59
def prefixEnd_1071898 : Nat := 4983230072969 + 3 ^ 40 * 1071898 * 2
def baseEnd_1071898 : Nat := 550398886593152427845437

theorem tailTrace_1071898 : CollatzResearch.WordTrace tailWord_1071898 prefixEnd_1071898 550398886593152427845437 := by
  unfold tailWord_1071898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773832967676021612228087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26063554580469390965941565 9773832967676021612228087)
  ·
    refine ⟨14660749451514032418342131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9773832967676021612228087 14660749451514032418342131)
    ·
      refine ⟨21991124177271048627513197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14660749451514032418342131 21991124177271048627513197)
      ·
        refine ⟨8246671566476643235317449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21991124177271048627513197 8246671566476643235317449)
        ·
          refine ⟨6185003674857482426488087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8246671566476643235317449 6185003674857482426488087)
          ·
            refine ⟨9277505512286223639732131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6185003674857482426488087 9277505512286223639732131)
            ·
              refine ⟨13916258268429335459598197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9277505512286223639732131 13916258268429335459598197)
              ·
                refine ⟨1304649212665250199337331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13916258268429335459598197 1304649212665250199337331)
                ·
                  refine ⟨1956973818997875299005997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304649212665250199337331 1956973818997875299005997)
                  ·
                    refine ⟨733865182124203237127249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956973818997875299005997 733865182124203237127249)
                    ·
                      refine ⟨550398886593152427845437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733865182124203237127249 550398886593152427845437)
                      ·
                        rfl

theorem cell23_1071898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_1071898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071898 prefixEnd_1071898 := by exact prefixLift 1071898
  have htrace : WordTrace (prefixWord ++ tailWord_1071898) baseStart_1071898 baseEnd_1071898 := by
    simpa [prefixWord, tailWord_1071898, baseEnd_1071898] using wordTrace_append hprefix tailTrace_1071898
  have hstable : (prefixWord ++ tailWord_1071898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071898).length < 2 ^ (prefixWord ++ tailWord_1071898).sum := by decide
  have hdescent : baseEnd_1071898 < baseStart_1071898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071949 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1071949 : Nat := 118140960795 + 1071949 * 2 ^ 59
def prefixEnd_1071949 : Nat := 4983230072969 + 3 ^ 40 * 1071949 * 2
def baseEnd_1071949 : Nat := 550425074106531728307703

theorem tailTrace_1071949 : CollatzResearch.WordTrace tailWord_1071949 prefixEnd_1071949 550425074106531728307703 := by
  unfold tailWord_1071949
  simp only [CollatzResearch.WordTrace]
  refine ⟨39097191993519322159018901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26064794662346214772679267 39097191993519322159018901)
  ·
    refine ⟨1832680874696218226204011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39097191993519322159018901 1832680874696218226204011)
    ·
      refine ⟨2749021312044327339306017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832680874696218226204011 2749021312044327339306017)
      ·
        refine ⟨2061765984033245504479513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2749021312044327339306017 2061765984033245504479513)
        ·
          refine ⟨1546324488024934128359635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2061765984033245504479513 1546324488024934128359635)
          ·
            refine ⟨2319486732037401192539453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546324488024934128359635 2319486732037401192539453)
            ·
              refine ⟨869807524514025447202295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2319486732037401192539453 869807524514025447202295)
              ·
                refine ⟨1304711286771038170803443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869807524514025447202295 1304711286771038170803443)
                ·
                  refine ⟨1957066930156557256205165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304711286771038170803443 1957066930156557256205165)
                  ·
                    refine ⟨733900098808708971076937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1957066930156557256205165 733900098808708971076937)
                    ·
                      refine ⟨550425074106531728307703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733900098808708971076937 550425074106531728307703)
                      ·
                        rfl

theorem cell23_1071949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1071949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071949 prefixEnd_1071949 := by exact prefixLift 1071949
  have htrace : WordTrace (prefixWord ++ tailWord_1071949) baseStart_1071949 baseEnd_1071949 := by
    simpa [prefixWord, tailWord_1071949, baseEnd_1071949] using wordTrace_append hprefix tailTrace_1071949
  have hstable : (prefixWord ++ tailWord_1071949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071949).length < 2 ^ (prefixWord ++ tailWord_1071949).sum := by decide
  have hdescent : baseEnd_1071949 < baseStart_1071949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072118 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1072118 : Nat := 118140960795 + 1072118 * 2 ^ 59
def prefixEnd_1072118 : Nat := 4983230072969 + 3 ^ 40 * 1072118 * 2
def baseEnd_1072118 : Nat := 183503950779047189031475

theorem tailTrace_1072118 : CollatzResearch.WordTrace tailWord_1072118 prefixEnd_1072118 183503950779047189031475 := by
  unfold tailWord_1072118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443959745619191501370063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26068903953271376014614005 2443959745619191501370063)
  ·
    refine ⟨3665939618428787252055095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2443959745619191501370063 3665939618428787252055095)
    ·
      refine ⟨5498909427643180878082643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665939618428787252055095 5498909427643180878082643)
      ·
        refine ⟨8248364141464771317123965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498909427643180878082643 8248364141464771317123965)
        ·
          refine ⟨3093136553049289243921487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8248364141464771317123965 3093136553049289243921487)
          ·
            refine ⟨4639704829573933865882231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093136553049289243921487 4639704829573933865882231)
            ·
              refine ⟨6959557244360900798823347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639704829573933865882231 6959557244360900798823347)
              ·
                refine ⟨10439335866541351198235021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959557244360900798823347 10439335866541351198235021)
                ·
                  refine ⟨3914750949953006699338133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10439335866541351198235021 3914750949953006699338133)
                  ·
                    refine ⟨183503950779047189031475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3914750949953006699338133 183503950779047189031475)
                    ·
                      rfl

theorem cell23_1072118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1072118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072118 prefixEnd_1072118 := by exact prefixLift 1072118
  have htrace : WordTrace (prefixWord ++ tailWord_1072118) baseStart_1072118 baseEnd_1072118 := by
    simpa [prefixWord, tailWord_1072118, baseEnd_1072118] using wordTrace_append hprefix tailTrace_1072118
  have hstable : (prefixWord ++ tailWord_1072118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072118).length < 2 ^ (prefixWord ++ tailWord_1072118).sum := by decide
  have hdescent : baseEnd_1072118 < baseStart_1072118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072135 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 2, 4]
def baseStart_1072135 : Nat := 118140960795 + 1072135 * 2 ^ 59
def prefixEnd_1072135 : Nat := 4983230072969 + 3 ^ 40 * 1072135 * 2
def baseEnd_1072135 : Nat := 183506860502756000193949

theorem tailTrace_1072135 : CollatzResearch.WordTrace tailWord_1072135 prefixEnd_1072135 183506860502756000193949 := by
  unfold tailWord_1072135
  simp only [CollatzResearch.WordTrace]
  refine ⟨39103975970845475925289859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26069317313896983950193239 39103975970845475925289859)
  ·
    refine ⟨58655963956268213887934789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39103975970845475925289859 58655963956268213887934789)
    ·
      refine ⟨10997993241800290103987773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58655963956268213887934789 10997993241800290103987773)
      ·
        refine ⟨4124247465675108788995415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10997993241800290103987773 4124247465675108788995415)
        ·
          refine ⟨6186371198512663183493123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124247465675108788995415 6186371198512663183493123)
          ·
            refine ⟨9279556797768994775239685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6186371198512663183493123 9279556797768994775239685)
            ·
              refine ⟨1739916899581686520357441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9279556797768994775239685 1739916899581686520357441)
              ·
                refine ⟨1304937674686264890268081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1739916899581686520357441 1304937674686264890268081)
                ·
                  refine ⟨978703256014698667701061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304937674686264890268081 978703256014698667701061)
                  ·
                    refine ⟨183506860502756000193949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 978703256014698667701061 183506860502756000193949)
                    ·
                      rfl

theorem cell23_1072135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_1072135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072135 prefixEnd_1072135 := by exact prefixLift 1072135
  have htrace : WordTrace (prefixWord ++ tailWord_1072135) baseStart_1072135 baseEnd_1072135 := by
    simpa [prefixWord, tailWord_1072135, baseEnd_1072135] using wordTrace_append hprefix tailTrace_1072135
  have hstable : (prefixWord ++ tailWord_1072135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072135).length < 2 ^ (prefixWord ++ tailWord_1072135).sum := by decide
  have hdescent : baseEnd_1072135 < baseStart_1072135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072171 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5]
def baseStart_1072171 : Nat := 118140960795 + 1072171 * 2 ^ 59
def prefixEnd_1072171 : Nat := 4983230072969 + 3 ^ 40 * 1072171 * 2
def baseEnd_1072171 : Nat := 550539066811829859731681

theorem tailTrace_1072171 : CollatzResearch.WordTrace tailWord_1072171 prefixEnd_1072171 550539066811829859731681 := by
  unfold tailWord_1072171
  simp only [CollatzResearch.WordTrace]
  refine ⟨39105288998715054073600367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26070192665810036049066911 39105288998715054073600367)
  ·
    refine ⟨58657933498072581110400551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39105288998715054073600367 58657933498072581110400551)
    ·
      refine ⟨87986900247108871665600827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58657933498072581110400551 87986900247108871665600827)
      ·
        refine ⟨131980350370663307498401241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87986900247108871665600827 131980350370663307498401241)
        ·
          refine ⟨98985262777997480623800931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131980350370663307498401241 98985262777997480623800931)
          ·
            refine ⟨148477894166996220935701397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98985262777997480623800931 148477894166996220935701397)
            ·
              refine ⟨6959901289077947856361003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148477894166996220935701397 6959901289077947856361003)
              ·
                refine ⟨10439851933616921784541505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959901289077947856361003 10439851933616921784541505)
                ·
                  refine ⟨7829888950212691338406129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10439851933616921784541505 7829888950212691338406129)
                  ·
                    refine ⟨5872416712659518503804597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7829888950212691338406129 5872416712659518503804597)
                    ·
                      refine ⟨550539066811829859731681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5872416712659518503804597 550539066811829859731681)
                      ·
                        rfl

theorem cell23_1072171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_1072171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072171 prefixEnd_1072171 := by exact prefixLift 1072171
  have htrace : WordTrace (prefixWord ++ tailWord_1072171) baseStart_1072171 baseEnd_1072171 := by
    simpa [prefixWord, tailWord_1072171, baseEnd_1072171] using wordTrace_append hprefix tailTrace_1072171
  have hstable : (prefixWord ++ tailWord_1072171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072171).length < 2 ^ (prefixWord ++ tailWord_1072171).sum := by decide
  have hdescent : baseEnd_1072171 < baseStart_1072171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072201 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_1072201 : Nat := 118140960795 + 1072201 * 2 ^ 59
def prefixEnd_1072201 : Nat := 4983230072969 + 3 ^ 40 * 1072201 * 2
def baseEnd_1072201 : Nat := 550554471231464742356543

theorem tailTrace_1072201 : CollatzResearch.WordTrace tailWord_1072201 prefixEnd_1072201 550554471231464742356543 := by
  unfold tailWord_1072201
  simp only [CollatzResearch.WordTrace]
  refine ⟨39106383188606369197192457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26070922125737579464794971 39106383188606369197192457)
  ·
    refine ⟨29329787391454776897894343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39106383188606369197192457 29329787391454776897894343)
    ·
      refine ⟨43994681087182165346841515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29329787391454776897894343 43994681087182165346841515)
      ·
        refine ⟨65992021630773248020262273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43994681087182165346841515 65992021630773248020262273)
        ·
          refine ⟨49494016223079936015196705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65992021630773248020262273 49494016223079936015196705)
          ·
            refine ⟨37120512167309952011397529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49494016223079936015196705 37120512167309952011397529)
            ·
              refine ⟨27840384125482464008548147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37120512167309952011397529 27840384125482464008548147)
              ·
                refine ⟨41760576188223696012822221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27840384125482464008548147 41760576188223696012822221)
                ·
                  refine ⟨15660216070583886004808333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41760576188223696012822221 15660216070583886004808333)
                  ·
                    refine ⟨5872581026468957251803125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15660216070583886004808333 5872581026468957251803125)
                    ·
                      refine ⟨550554471231464742356543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5872581026468957251803125 550554471231464742356543)
                      ·
                        rfl

theorem cell23_1072201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_1072201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072201 prefixEnd_1072201 := by exact prefixLift 1072201
  have htrace : WordTrace (prefixWord ++ tailWord_1072201) baseStart_1072201 baseEnd_1072201 := by
    simpa [prefixWord, tailWord_1072201, baseEnd_1072201] using wordTrace_append hprefix tailTrace_1072201
  have hstable : (prefixWord ++ tailWord_1072201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072201).length < 2 ^ (prefixWord ++ tailWord_1072201).sum := by decide
  have hdescent : baseEnd_1072201 < baseStart_1072201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072222 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1072222 : Nat := 118140960795 + 1072222 * 2 ^ 59
def prefixEnd_1072222 : Nat := 4983230072969 + 3 ^ 40 * 1072222 * 2
def baseEnd_1072222 : Nat := 550565254325209160193947

theorem tailTrace_1072222 : CollatzResearch.WordTrace tailWord_1072222 prefixEnd_1072222 550565254325209160193947 := by
  unfold tailWord_1072222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4888393640191286222963365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26071432747686859855804613 4888393640191286222963365)
  ·
    refine ⟨916573807535866166805631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4888393640191286222963365 916573807535866166805631)
    ·
      refine ⟨1374860711303799250208447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916573807535866166805631 1374860711303799250208447)
      ·
        refine ⟨2062291066955698875312671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374860711303799250208447 2062291066955698875312671)
        ·
          refine ⟨3093436600433548312969007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062291066955698875312671 3093436600433548312969007)
          ·
            refine ⟨4640154900650322469453511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093436600433548312969007 4640154900650322469453511)
            ·
              refine ⟨6960232350975483704180267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640154900650322469453511 6960232350975483704180267)
              ·
                refine ⟨10440348526463225556270401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960232350975483704180267 10440348526463225556270401)
                ·
                  refine ⟨7830261394847419167202801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10440348526463225556270401 7830261394847419167202801)
                  ·
                    refine ⟨5872696046135564375402101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7830261394847419167202801 5872696046135564375402101)
                    ·
                      refine ⟨550565254325209160193947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5872696046135564375402101 550565254325209160193947)
                      ·
                        rfl

theorem cell23_1072222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1072222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072222 prefixEnd_1072222 := by exact prefixLift 1072222
  have htrace : WordTrace (prefixWord ++ tailWord_1072222) baseStart_1072222 baseEnd_1072222 := by
    simpa [prefixWord, tailWord_1072222, baseEnd_1072222] using wordTrace_append hprefix tailTrace_1072222
  have hstable : (prefixWord ++ tailWord_1072222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072222).length < 2 ^ (prefixWord ++ tailWord_1072222).sum := by decide
  have hdescent : baseEnd_1072222 < baseStart_1072222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072248 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_1072248 : Nat := 118140960795 + 1072248 * 2 ^ 59
def prefixEnd_1072248 : Nat := 4983230072969 + 3 ^ 40 * 1072248 * 2
def baseEnd_1072248 : Nat := 550578604822226058468827

theorem tailTrace_1072248 : CollatzResearch.WordTrace tailWord_1072248 prefixEnd_1072248 550578604822226058468827 := by
  unfold tailWord_1072248
  simp only [CollatzResearch.WordTrace]
  refine ⟨19554048709718048112076699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26072064946290730816102265 19554048709718048112076699)
  ·
    refine ⟨29331073064577072168115049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19554048709718048112076699 29331073064577072168115049)
    ·
      refine ⟨21998304798432804126086287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29331073064577072168115049 21998304798432804126086287)
      ·
        refine ⟨32997457197649206189129431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21998304798432804126086287 32997457197649206189129431)
        ·
          refine ⟨49496185796473809283694147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32997457197649206189129431 49496185796473809283694147)
          ·
            refine ⟨74244278694710713925541221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49496185796473809283694147 74244278694710713925541221)
            ·
              refine ⟨13920802255258258861038979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74244278694710713925541221 13920802255258258861038979)
              ·
                refine ⟨20881203382887388291558469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13920802255258258861038979 20881203382887388291558469)
                ·
                  refine ⟨3915225634291385304667213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20881203382887388291558469 3915225634291385304667213)
                  ·
                    refine ⟨1468209612859269489250205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3915225634291385304667213 1468209612859269489250205)
                    ·
                      refine ⟨550578604822226058468827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1468209612859269489250205 550578604822226058468827)
                      ·
                        rfl

theorem cell23_1072248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_1072248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072248 prefixEnd_1072248 := by exact prefixLift 1072248
  have htrace : WordTrace (prefixWord ++ tailWord_1072248) baseStart_1072248 baseEnd_1072248 := by
    simpa [prefixWord, tailWord_1072248, baseEnd_1072248] using wordTrace_append hprefix tailTrace_1072248
  have hstable : (prefixWord ++ tailWord_1072248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072248).length < 2 ^ (prefixWord ++ tailWord_1072248).sum := by decide
  have hdescent : baseEnd_1072248 < baseStart_1072248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072285 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1072285 : Nat := 118140960795 + 1072285 * 2 ^ 59
def prefixEnd_1072285 : Nat := 4983230072969 + 3 ^ 40 * 1072285 * 2
def baseEnd_1072285 : Nat := 183532534535480804568719

theorem tailTrace_1072285 : CollatzResearch.WordTrace tailWord_1072285 prefixEnd_1072285 183532534535480804568719 := by
  unfold tailWord_1072285
  simp only [CollatzResearch.WordTrace]
  refine ⟨39109446920302051543250309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26072964613534701028833539 39109446920302051543250309)
  ·
    refine ⟨7333021297556634664359433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39109446920302051543250309 7333021297556634664359433)
    ·
      refine ⟨5499765973167475998269575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7333021297556634664359433 5499765973167475998269575)
      ·
        refine ⟨8249648959751213997404363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5499765973167475998269575 8249648959751213997404363)
        ·
          refine ⟨12374473439626820996106545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8249648959751213997404363 12374473439626820996106545)
          ·
            refine ⟨9280855079720115747079909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12374473439626820996106545 9280855079720115747079909)
            ·
              refine ⟨1740160327447521702577483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9280855079720115747079909 1740160327447521702577483)
              ·
                refine ⟨2610240491171282553866225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740160327447521702577483 2610240491171282553866225)
                ·
                  refine ⟨1957680368378461915399669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2610240491171282553866225 1957680368378461915399669)
                  ·
                    refine ⟨183532534535480804568719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1957680368378461915399669 183532534535480804568719)
                    ·
                      rfl

theorem cell23_1072285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1072285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072285 prefixEnd_1072285 := by exact prefixLift 1072285
  have htrace : WordTrace (prefixWord ++ tailWord_1072285) baseStart_1072285 baseEnd_1072285 := by
    simpa [prefixWord, tailWord_1072285, baseEnd_1072285] using wordTrace_append hprefix tailTrace_1072285
  have hstable : (prefixWord ++ tailWord_1072285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072285).length < 2 ^ (prefixWord ++ tailWord_1072285).sum := by decide
  have hdescent : baseEnd_1072285 < baseStart_1072285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072295 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1072295 : Nat := 118140960795 + 1072295 * 2 ^ 59
def prefixEnd_1072295 : Nat := 4983230072969 + 3 ^ 40 * 1072295 * 2
def baseEnd_1072295 : Nat := 550602738412987374581111

theorem tailTrace_1072295 : CollatzResearch.WordTrace tailWord_1072295 prefixEnd_1072295 550602738412987374581111 := by
  unfold tailWord_1072295
  simp only [CollatzResearch.WordTrace]
  refine ⟨39109811650265823251114339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26073207766843882167409559 39109811650265823251114339)
  ·
    refine ⟨58664717475398734876671509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39109811650265823251114339 58664717475398734876671509)
    ·
      refine ⟨2749908631659315697343977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58664717475398734876671509 2749908631659315697343977)
      ·
        refine ⟨2062431473744486773007983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2749908631659315697343977 2062431473744486773007983)
        ·
          refine ⟨3093647210616730159511975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062431473744486773007983 3093647210616730159511975)
          ·
            refine ⟨4640470815925095239267963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093647210616730159511975 4640470815925095239267963)
            ·
              refine ⟨6960706223887642858901945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640470815925095239267963 6960706223887642858901945)
              ·
                refine ⟨5220529667915732144176459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6960706223887642858901945 5220529667915732144176459)
                ·
                  refine ⟨7830794501873598216264689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220529667915732144176459 7830794501873598216264689)
                  ·
                    refine ⟨5873095876405198662198517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7830794501873598216264689 5873095876405198662198517)
                    ·
                      refine ⟨550602738412987374581111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5873095876405198662198517 550602738412987374581111)
                      ·
                        rfl

theorem cell23_1072295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1072295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072295 prefixEnd_1072295 := by exact prefixLift 1072295
  have htrace : WordTrace (prefixWord ++ tailWord_1072295) baseStart_1072295 baseEnd_1072295 := by
    simpa [prefixWord, tailWord_1072295, baseEnd_1072295] using wordTrace_append hprefix tailTrace_1072295
  have hstable : (prefixWord ++ tailWord_1072295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072295).length < 2 ^ (prefixWord ++ tailWord_1072295).sum := by decide
  have hdescent : baseEnd_1072295 < baseStart_1072295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072362 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 6]
def baseStart_1072362 : Nat := 118140960795 + 1072362 * 2 ^ 59
def prefixEnd_1072362 : Nat := 4983230072969 + 3 ^ 40 * 1072362 * 2
def baseEnd_1072362 : Nat := 61181904624093179160367

theorem tailTrace_1072362 : CollatzResearch.WordTrace tailWord_1072362 prefixEnd_1072362 61181904624093179160367 := by
  unfold tailWord_1072362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9778063835255773423450835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26074836894015395795868893 9778063835255773423450835)
  ·
    refine ⟨14667095752883660135176253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9778063835255773423450835 14667095752883660135176253)
    ·
      refine ⟨5500160907331372550691095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14667095752883660135176253 5500160907331372550691095)
      ·
        refine ⟨8250241360997058826036643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5500160907331372550691095 8250241360997058826036643)
        ·
          refine ⟨12375362041495588239054965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8250241360997058826036643 12375362041495588239054965)
          ·
            refine ⟨1160190191390211397411403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12375362041495588239054965 1160190191390211397411403)
            ·
              refine ⟨1740285287085317096117105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160190191390211397411403 1740285287085317096117105)
              ·
                refine ⟨1305213965313987822087829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740285287085317096117105 1305213965313987822087829)
                ·
                  refine ⟨61181904624093179160367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1305213965313987822087829 61181904624093179160367)
                  ·
                    rfl

theorem cell23_1072362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_1072362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072362 prefixEnd_1072362 := by exact prefixLift 1072362
  have htrace : WordTrace (prefixWord ++ tailWord_1072362) baseStart_1072362 baseEnd_1072362 := by
    simpa [prefixWord, tailWord_1072362, baseEnd_1072362] using wordTrace_append hprefix tailTrace_1072362
  have hstable : (prefixWord ++ tailWord_1072362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072362).length < 2 ^ (prefixWord ++ tailWord_1072362).sum := by decide
  have hdescent : baseEnd_1072362 < baseStart_1072362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072365 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1072365 : Nat := 118140960795 + 1072365 * 2 ^ 59
def prefixEnd_1072365 : Nat := 4983230072969 + 3 ^ 40 * 1072365 * 2
def baseEnd_1072365 : Nat := 550638682058802100705789

theorem tailTrace_1072365 : CollatzResearch.WordTrace tailWord_1072365 prefixEnd_1072365 550638682058802100705789 := by
  unfold tailWord_1072365
  simp only [CollatzResearch.WordTrace]
  refine ⟨39112364760012225206162549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26074909840008150137441699 39112364760012225206162549)
  ·
    refine ⟨3666784196251146113077739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39112364760012225206162549 3666784196251146113077739)
    ·
      refine ⟨5500176294376719169616609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3666784196251146113077739 5500176294376719169616609)
      ·
        refine ⟨4125132220782539377212457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5500176294376719169616609 4125132220782539377212457)
        ·
          refine ⟨3093849165586904532909343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4125132220782539377212457 3093849165586904532909343)
          ·
            refine ⟨4640773748380356799364015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093849165586904532909343 4640773748380356799364015)
            ·
              refine ⟨6961160622570535199046023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640773748380356799364015 6961160622570535199046023)
              ·
                refine ⟨10441740933855802798569035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6961160622570535199046023 10441740933855802798569035)
                ·
                  refine ⟨15662611400783704197853553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10441740933855802798569035 15662611400783704197853553)
                  ·
                    refine ⟨11746958550587778148390165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15662611400783704197853553 11746958550587778148390165)
                    ·
                      refine ⟨550638682058802100705789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11746958550587778148390165 550638682058802100705789)
                      ·
                        rfl

theorem cell23_1072365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1072365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072365 prefixEnd_1072365 := by exact prefixLift 1072365
  have htrace : WordTrace (prefixWord ++ tailWord_1072365) baseStart_1072365 baseEnd_1072365 := by
    simpa [prefixWord, tailWord_1072365, baseEnd_1072365] using wordTrace_append hprefix tailTrace_1072365
  have hstable : (prefixWord ++ tailWord_1072365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072365).length < 2 ^ (prefixWord ++ tailWord_1072365).sum := by decide
  have hdescent : baseEnd_1072365 < baseStart_1072365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072412 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1072412 : Nat := 118140960795 + 1072412 * 2 ^ 59
def prefixEnd_1072412 : Nat := 4983230072969 + 3 ^ 40 * 1072412 * 2
def baseEnd_1072412 : Nat := 550662815649563416818073

theorem tailTrace_1072412 : CollatzResearch.WordTrace tailWord_1072412 prefixEnd_1072412 550662815649563416818073 := by
  unfold tailWord_1072412
  simp only [CollatzResearch.WordTrace]
  refine ⟨19557039495420976116561745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26076052660561301488748993 19557039495420976116561745)
  ·
    refine ⟨14667779621565732087421309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19557039495420976116561745 14667779621565732087421309)
    ·
      refine ⟨5500417358087149532782991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14667779621565732087421309 5500417358087149532782991)
      ·
        refine ⟨8250626037130724299174487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5500417358087149532782991 8250626037130724299174487)
        ·
          refine ⟨12375939055696086448761731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8250626037130724299174487 12375939055696086448761731)
          ·
            refine ⟨18563908583544129673142597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12375939055696086448761731 18563908583544129673142597)
            ·
              refine ⟨3480732859414524313714237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18563908583544129673142597 3480732859414524313714237)
              ·
                refine ⟨1305274822280446617642839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3480732859414524313714237 1305274822280446617642839)
                ·
                  refine ⟨1957912233420669926464259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305274822280446617642839 1957912233420669926464259)
                  ·
                    refine ⟨2936868350131004889696389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1957912233420669926464259 2936868350131004889696389)
                    ·
                      refine ⟨550662815649563416818073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2936868350131004889696389 550662815649563416818073)
                      ·
                        rfl

theorem cell23_1072412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1072412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072412 prefixEnd_1072412 := by exact prefixLift 1072412
  have htrace : WordTrace (prefixWord ++ tailWord_1072412) baseStart_1072412 baseEnd_1072412 := by
    simpa [prefixWord, tailWord_1072412, baseEnd_1072412] using wordTrace_append hprefix tailTrace_1072412
  have hstable : (prefixWord ++ tailWord_1072412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072412).length < 2 ^ (prefixWord ++ tailWord_1072412).sum := by decide
  have hdescent : baseEnd_1072412 < baseStart_1072412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072435 : List Nat := [1, 1, 1, 2, 5, 3, 2, 8]
def baseStart_1072435 : Nat := 118140960795 + 1072435 * 2 ^ 59
def prefixEnd_1072435 : Nat := 4983230072969 + 3 ^ 40 * 1072435 * 2
def baseEnd_1072435 : Nat := 20395356507578400993721

theorem tailTrace_1072435 : CollatzResearch.WordTrace tailWord_1072435 prefixEnd_1072435 20395356507578400993721 := by
  unfold tailWord_1072435
  simp only [CollatzResearch.WordTrace]
  refine ⟨39114917869758627161210759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26076611913172418107473839 39114917869758627161210759)
  ·
    refine ⟨58672376804637940741816139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39114917869758627161210759 58672376804637940741816139)
    ·
      refine ⟨88008565206956911112724209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58672376804637940741816139 88008565206956911112724209)
      ·
        refine ⟨66006423905217683334543157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88008565206956911112724209 66006423905217683334543157)
        ·
          refine ⟨6188102241114157812613421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66006423905217683334543157 6188102241114157812613421)
          ·
            refine ⟨2320538340417809179730033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6188102241114157812613421 2320538340417809179730033)
            ·
              refine ⟨1740403755313356884797525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2320538340417809179730033 1740403755313356884797525)
              ·
                refine ⟨20395356507578400993721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1740403755313356884797525 20395356507578400993721)
                ·
                  rfl

theorem cell23_1072435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 8].length) (baseStart_1072435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072435 prefixEnd_1072435 := by exact prefixLift 1072435
  have htrace : WordTrace (prefixWord ++ tailWord_1072435) baseStart_1072435 baseEnd_1072435 := by
    simpa [prefixWord, tailWord_1072435, baseEnd_1072435] using wordTrace_append hprefix tailTrace_1072435
  have hstable : (prefixWord ++ tailWord_1072435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072435).length < 2 ^ (prefixWord ++ tailWord_1072435).sum := by decide
  have hdescent : baseEnd_1072435 < baseStart_1072435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072449 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1072449 : Nat := 118140960795 + 1072449 * 2 ^ 59
def prefixEnd_1072449 : Nat := 4983230072969 + 3 ^ 40 * 1072449 * 2
def baseEnd_1072449 : Nat := 550681814433779772055403

theorem tailTrace_1072449 : CollatzResearch.WordTrace tailWord_1072449 prefixEnd_1072449 550681814433779772055403 := by
  unfold tailWord_1072449
  simp only [CollatzResearch.WordTrace]
  refine ⟨39115428491707907552220401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26076952327805271701480267 39115428491707907552220401)
  ·
    refine ⟨29336571368780930664165301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39115428491707907552220401 29336571368780930664165301)
    ·
      refine ⟨2750303565823212249765497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29336571368780930664165301 2750303565823212249765497)
      ·
        refine ⟨2062727674367409187324123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2750303565823212249765497 2062727674367409187324123)
        ·
          refine ⟨3094091511551113780986185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062727674367409187324123 3094091511551113780986185)
          ·
            refine ⟨2320568633663335335739639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3094091511551113780986185 2320568633663335335739639)
            ·
              refine ⟨3480852950495003003609459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320568633663335335739639 3480852950495003003609459)
              ·
                refine ⟨5221279425742504505414189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480852950495003003609459 5221279425742504505414189)
                ·
                  refine ⟨1957979784653439189530321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5221279425742504505414189 1957979784653439189530321)
                  ·
                    refine ⟨1468484838490079392147741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1957979784653439189530321 1468484838490079392147741)
                    ·
                      refine ⟨550681814433779772055403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1468484838490079392147741 550681814433779772055403)
                      ·
                        rfl

theorem cell23_1072449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1072449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072449 prefixEnd_1072449 := by exact prefixLift 1072449
  have htrace : WordTrace (prefixWord ++ tailWord_1072449) baseStart_1072449 baseEnd_1072449 := by
    simpa [prefixWord, tailWord_1072449, baseEnd_1072449] using wordTrace_append hprefix tailTrace_1072449
  have hstable : (prefixWord ++ tailWord_1072449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072449).length < 2 ^ (prefixWord ++ tailWord_1072449).sum := by decide
  have hdescent : baseEnd_1072449 < baseStart_1072449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072452 : List Nat := [2, 3, 4, 1, 1, 1, 2, 9]
def baseStart_1072452 : Nat := 118140960795 + 1072452 * 2 ^ 59
def prefixEnd_1072452 : Nat := 4983230072969 + 3 ^ 40 * 1072452 * 2
def baseEnd_1072452 : Nat := 20395679810212713345107

theorem tailTrace_1072452 : CollatzResearch.WordTrace tailWord_1072452 prefixEnd_1072452 20395679810212713345107 := by
  unfold tailWord_1072452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19557768955348519532289805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26077025273798026043053073 19557768955348519532289805)
  ·
    refine ⟨7334163358255694824608677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19557768955348519532289805 7334163358255694824608677)
    ·
      refine ⟨1375155629672942779614127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7334163358255694824608677 1375155629672942779614127)
      ·
        refine ⟨2062733444509414169421191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375155629672942779614127 2062733444509414169421191)
        ·
          refine ⟨3094100166764121254131787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062733444509414169421191 3094100166764121254131787)
          ·
            refine ⟨4641150250146181881197681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094100166764121254131787 4641150250146181881197681)
            ·
              refine ⟨3480862687609636410898261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4641150250146181881197681 3480862687609636410898261)
              ·
                refine ⟨20395679810212713345107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3480862687609636410898261 20395679810212713345107)
                ·
                  rfl

theorem cell23_1072452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 9].length) (baseStart_1072452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072452 prefixEnd_1072452 := by exact prefixLift 1072452
  have htrace : WordTrace (prefixWord ++ tailWord_1072452) baseStart_1072452 baseEnd_1072452 := by
    simpa [prefixWord, tailWord_1072452, baseEnd_1072452] using wordTrace_append hprefix tailTrace_1072452
  have hstable : (prefixWord ++ tailWord_1072452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072452).length < 2 ^ (prefixWord ++ tailWord_1072452).sum := by decide
  have hdescent : baseEnd_1072452 < baseStart_1072452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072462 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_1072462 : Nat := 118140960795 + 1072462 * 2 ^ 59
def prefixEnd_1072462 : Nat := 4983230072969 + 3 ^ 40 * 1072462 * 2
def baseEnd_1072462 : Nat := 550688489682288221192843

theorem tailTrace_1072462 : CollatzResearch.WordTrace tailWord_1072462 prefixEnd_1072462 550688489682288221192843 := by
  unfold tailWord_1072462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889487830082601346555455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26077268427107207181629093 4889487830082601346555455)
  ·
    refine ⟨7334231745123902019833183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4889487830082601346555455 7334231745123902019833183)
    ·
      refine ⟨11001347617685853029749775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7334231745123902019833183 11001347617685853029749775)
      ·
        refine ⟨16502021426528779544624663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11001347617685853029749775 16502021426528779544624663)
        ·
          refine ⟨24753032139793169316936995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16502021426528779544624663 24753032139793169316936995)
          ·
            refine ⟨37129548209689753975405493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24753032139793169316936995 37129548209689753975405493)
            ·
              refine ⟨3480895144658414435194265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37129548209689753975405493 3480895144658414435194265)
              ·
                refine ⟨2610671358493810826395699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3480895144658414435194265 2610671358493810826395699)
                ·
                  refine ⟨3916007037740716239593549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2610671358493810826395699 3916007037740716239593549)
                  ·
                    refine ⟨1468502639152768589847581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3916007037740716239593549 1468502639152768589847581)
                    ·
                      refine ⟨550688489682288221192843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1468502639152768589847581 550688489682288221192843)
                      ·
                        rfl

theorem cell23_1072462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_1072462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072462 prefixEnd_1072462 := by exact prefixLift 1072462
  have htrace : WordTrace (prefixWord ++ tailWord_1072462) baseStart_1072462 baseEnd_1072462 := by
    simpa [prefixWord, tailWord_1072462, baseEnd_1072462] using wordTrace_append hprefix tailTrace_1072462
  have hstable : (prefixWord ++ tailWord_1072462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072462).length < 2 ^ (prefixWord ++ tailWord_1072462).sum := by decide
  have hdescent : baseEnd_1072462 < baseStart_1072462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072480 : List Nat := [2, 1, 1, 3, 4, 3, 2, 2, 1, 2, 2]
def baseStart_1072480 : Nat := 118140960795 + 1072480 * 2 ^ 59
def prefixEnd_1072480 : Nat := 4983230072969 + 3 ^ 40 * 1072480 * 2
def baseEnd_1072480 : Nat := 550697732334069150767761

theorem tailTrace_1072480 : CollatzResearch.WordTrace tailWord_1072480 prefixEnd_1072480 550697732334069150767761 := by
  unfold tailWord_1072480
  simp only [CollatzResearch.WordTrace]
  refine ⟨19558279577297799923299447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26077706103063733231065929 19558279577297799923299447)
  ·
    refine ⟨29337419365946699884949171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19558279577297799923299447 29337419365946699884949171)
    ·
      refine ⟨44006129048920049827423757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29337419365946699884949171 44006129048920049827423757)
      ·
        refine ⟨16502298393345018685283909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44006129048920049827423757 16502298393345018685283909)
        ·
          refine ⟨3094180948752191003490733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16502298393345018685283909 3094180948752191003490733)
          ·
            refine ⟨1160317855782071626309025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3094180948752191003490733 1160317855782071626309025)
            ·
              refine ⟨870238391836553719731769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160317855782071626309025 870238391836553719731769)
              ·
                refine ⟨652678793877415289798827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870238391836553719731769 652678793877415289798827)
                ·
                  refine ⟨979018190816122934698241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652678793877415289798827 979018190816122934698241)
                  ·
                    refine ⟨734263643112092201023681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 979018190816122934698241 734263643112092201023681)
                    ·
                      refine ⟨550697732334069150767761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 734263643112092201023681 550697732334069150767761)
                      ·
                        rfl

theorem cell23_1072480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_1072480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072480 prefixEnd_1072480 := by exact prefixLift 1072480
  have htrace : WordTrace (prefixWord ++ tailWord_1072480) baseStart_1072480 baseEnd_1072480 := by
    simpa [prefixWord, tailWord_1072480, baseEnd_1072480] using wordTrace_append hprefix tailTrace_1072480
  have hstable : (prefixWord ++ tailWord_1072480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072480).length < 2 ^ (prefixWord ++ tailWord_1072480).sum := by decide
  have hdescent : baseEnd_1072480 < baseStart_1072480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072485 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1072485 : Nat := 118140960795 + 1072485 * 2 ^ 59
def prefixEnd_1072485 : Nat := 4983230072969 + 3 ^ 40 * 1072485 * 2
def baseEnd_1072485 : Nat := 550700299737341631205237

theorem tailTrace_1072485 : CollatzResearch.WordTrace tailWord_1072485 prefixEnd_1072485 550700299737341631205237 := by
  unfold tailWord_1072485
  simp only [CollatzResearch.WordTrace]
  refine ⟨39116741519577485700530909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26077827679718323800353939 39116741519577485700530909)
  ·
    refine ⟨14668778069841557137699091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39116741519577485700530909 14668778069841557137699091)
    ·
      refine ⟨22003167104762335706548637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14668778069841557137699091 22003167104762335706548637)
      ·
        refine ⟨8251187664285875889955739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22003167104762335706548637 8251187664285875889955739)
        ·
          refine ⟨12376781496428813834933609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8251187664285875889955739 12376781496428813834933609)
          ·
            refine ⟨9282586122321610376200207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12376781496428813834933609 9282586122321610376200207)
            ·
              refine ⟨13923879183482415564300311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9282586122321610376200207 13923879183482415564300311)
              ·
                refine ⟨20885818775223623346450467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13923879183482415564300311 20885818775223623346450467)
                ·
                  refine ⟨31328728162835435019675701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20885818775223623346450467 31328728162835435019675701)
                  ·
                    refine ⟨2937068265265822033094597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31328728162835435019675701 2937068265265822033094597)
                    ·
                      refine ⟨550700299737341631205237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2937068265265822033094597 550700299737341631205237)
                      ·
                        rfl

theorem cell23_1072485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1072485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072485 prefixEnd_1072485 := by exact prefixLift 1072485
  have htrace : WordTrace (prefixWord ++ tailWord_1072485) baseStart_1072485 baseEnd_1072485 := by
    simpa [prefixWord, tailWord_1072485, baseEnd_1072485] using wordTrace_append hprefix tailTrace_1072485
  have hstable : (prefixWord ++ tailWord_1072485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072485).length < 2 ^ (prefixWord ++ tailWord_1072485).sum := by decide
  have hdescent : baseEnd_1072485 < baseStart_1072485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072495 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 2, 6]
def baseStart_1072495 : Nat := 118140960795 + 1072495 * 2 ^ 59
def prefixEnd_1072495 : Nat := 4983230072969 + 3 ^ 40 * 1072495 * 2
def baseEnd_1072495 : Nat := 183568478181295530693397

theorem tailTrace_1072495 : CollatzResearch.WordTrace tailWord_1072495 prefixEnd_1072495 183568478181295530693397 := by
  unfold tailWord_1072495
  simp only [CollatzResearch.WordTrace]
  refine ⟨39117106249541257408394939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26078070833027504938929959 39117106249541257408394939)
  ·
    refine ⟨58675659374311886112592409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39117106249541257408394939 58675659374311886112592409)
    ·
      refine ⟨44006744530733914584444307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58675659374311886112592409 44006744530733914584444307)
      ·
        refine ⟨66010116796100871876666461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44006744530733914584444307 66010116796100871876666461)
        ·
          refine ⟨24753793798537826953749923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66010116796100871876666461 24753793798537826953749923)
          ·
            refine ⟨37130690697806740430624885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24753793798537826953749923 37130690697806740430624885)
            ·
              refine ⟨3481002252919381915371083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37130690697806740430624885 3481002252919381915371083)
              ·
                refine ⟨5221503379379072873056625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481002252919381915371083 5221503379379072873056625)
                ·
                  refine ⟨3916127534534304654792469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5221503379379072873056625 3916127534534304654792469)
                  ·
                    refine ⟨183568478181295530693397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3916127534534304654792469 183568478181295530693397)
                    ·
                      rfl

theorem cell23_1072495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_1072495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072495 prefixEnd_1072495 := by exact prefixLift 1072495
  have htrace : WordTrace (prefixWord ++ tailWord_1072495) baseStart_1072495 baseEnd_1072495 := by
    simpa [prefixWord, tailWord_1072495, baseEnd_1072495] using wordTrace_append hprefix tailTrace_1072495
  have hstable : (prefixWord ++ tailWord_1072495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072495).length < 2 ^ (prefixWord ++ tailWord_1072495).sum := by decide
  have hdescent : baseEnd_1072495 < baseStart_1072495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072505 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_1072505 : Nat := 118140960795 + 1072505 * 2 ^ 59
def prefixEnd_1072505 : Nat := 4983230072969 + 3 ^ 40 * 1072505 * 2
def baseEnd_1072505 : Nat := 550710569350431552955145

theorem tailTrace_1072505 : CollatzResearch.WordTrace tailWord_1072505 prefixEnd_1072505 550710569350431552955145 := by
  unfold tailWord_1072505
  simp only [CollatzResearch.WordTrace]
  refine ⟨39117470979505029116258969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26078313986336686077505979 39117470979505029116258969)
  ·
    refine ⟨29338103234628771837194227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39117470979505029116258969 29338103234628771837194227)
    ·
      refine ⟨44007154851943157755791341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29338103234628771837194227 44007154851943157755791341)
      ·
        refine ⟨16502683069478684158421753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44007154851943157755791341 16502683069478684158421753)
        ·
          refine ⟨12377012302109013118816315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16502683069478684158421753 12377012302109013118816315)
          ·
            refine ⟨18565518453163519678224473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12377012302109013118816315 18565518453163519678224473)
            ·
              refine ⟨13924138839872639758668355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18565518453163519678224473 13924138839872639758668355)
              ·
                refine ⟨20886208259808959638002533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13924138839872639758668355 20886208259808959638002533)
                ·
                  refine ⟨3916164048714179932125475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20886208259808959638002533 3916164048714179932125475)
                  ·
                    refine ⟨5874246073071269898188213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3916164048714179932125475 5874246073071269898188213)
                    ·
                      refine ⟨550710569350431552955145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5874246073071269898188213 550710569350431552955145)
                      ·
                        rfl

theorem cell23_1072505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_1072505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072505 prefixEnd_1072505 := by exact prefixLift 1072505
  have htrace : WordTrace (prefixWord ++ tailWord_1072505) baseStart_1072505 baseEnd_1072505 := by
    simpa [prefixWord, tailWord_1072505, baseEnd_1072505] using wordTrace_append hprefix tailTrace_1072505
  have hstable : (prefixWord ++ tailWord_1072505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072505).length < 2 ^ (prefixWord ++ tailWord_1072505).sum := by decide
  have hdescent : baseEnd_1072505 < baseStart_1072505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072519 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_1072519 : Nat := 118140960795 + 1072519 * 2 ^ 59
def prefixEnd_1072519 : Nat := 4983230072969 + 3 ^ 40 * 1072519 * 2
def baseEnd_1072519 : Nat := 550717758079594498180081

theorem tailTrace_1072519 : CollatzResearch.WordTrace tailWord_1072519 prefixEnd_1072519 550717758079594498180081 := by
  unfold tailWord_1072519
  simp only [CollatzResearch.WordTrace]
  refine ⟨39117981601454309507268611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26078654400969539671512407 39117981601454309507268611)
  ·
    refine ⟨58676972402181464260902917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39117981601454309507268611 58676972402181464260902917)
    ·
      refine ⟨11001932325409024548919297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58676972402181464260902917 11001932325409024548919297)
      ·
        refine ⟨8251449244056768411689473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11001932325409024548919297 8251449244056768411689473)
        ·
          refine ⟨6188586933042576308767105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8251449244056768411689473 6188586933042576308767105)
          ·
            refine ⟨4641440199781932231575329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6188586933042576308767105 4641440199781932231575329)
            ·
              refine ⟨3481080149836449173681497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4641440199781932231575329 3481080149836449173681497)
              ·
                refine ⟨2610810112377336880261123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481080149836449173681497 2610810112377336880261123)
                ·
                  refine ⟨3916215168566005320391685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2610810112377336880261123 3916215168566005320391685)
                  ·
                    refine ⟨734290344106125997573441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3916215168566005320391685 734290344106125997573441)
                    ·
                      refine ⟨550717758079594498180081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 734290344106125997573441 550717758079594498180081)
                      ·
                        rfl

theorem cell23_1072519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_1072519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072519 prefixEnd_1072519 := by exact prefixLift 1072519
  have htrace : WordTrace (prefixWord ++ tailWord_1072519) baseStart_1072519 baseEnd_1072519 := by
    simpa [prefixWord, tailWord_1072519, baseEnd_1072519] using wordTrace_append hprefix tailTrace_1072519
  have hstable : (prefixWord ++ tailWord_1072519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072519).length < 2 ^ (prefixWord ++ tailWord_1072519).sum := by decide
  have hdescent : baseEnd_1072519 < baseStart_1072519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072530 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1072530 : Nat := 118140960795 + 1072530 * 2 ^ 59
def prefixEnd_1072530 : Nat := 4983230072969 + 3 ^ 40 * 1072530 * 2
def baseEnd_1072530 : Nat := 550723406366793955142531

theorem tailTrace_1072530 : CollatzResearch.WordTrace tailWord_1072530 prefixEnd_1072530 550723406366793955142531 := by
  unfold tailWord_1072530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779595701103614596479761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26078921869609638923946029 9779595701103614596479761)
  ·
    refine ⟨7334696775827710947359821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9779595701103614596479761 7334696775827710947359821)
    ·
      refine ⟨2750511290935391605259933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7334696775827710947359821 2750511290935391605259933)
      ·
        refine ⟨1031441734100771851972475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2750511290935391605259933 1031441734100771851972475)
        ·
          refine ⟨1547162601151157777958713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031441734100771851972475 1547162601151157777958713)
          ·
            refine ⟨1160371950863368333469035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1547162601151157777958713 1160371950863368333469035)
            ·
              refine ⟨1740557926295052500203553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160371950863368333469035 1740557926295052500203553)
              ·
                refine ⟨1305418444721289375152665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740557926295052500203553 1305418444721289375152665)
                ·
                  refine ⟨979063833540967031364499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305418444721289375152665 979063833540967031364499)
                  ·
                    refine ⟨1468595750311450547046749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 979063833540967031364499 1468595750311450547046749)
                    ·
                      refine ⟨550723406366793955142531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1468595750311450547046749 550723406366793955142531)
                      ·
                        rfl

theorem cell23_1072530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1072530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072530 prefixEnd_1072530 := by exact prefixLift 1072530
  have htrace : WordTrace (prefixWord ++ tailWord_1072530) baseStart_1072530 baseEnd_1072530 := by
    simpa [prefixWord, tailWord_1072530, baseEnd_1072530] using wordTrace_append hprefix tailTrace_1072530
  have hstable : (prefixWord ++ tailWord_1072530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072530).length < 2 ^ (prefixWord ++ tailWord_1072530).sum := by decide
  have hdescent : baseEnd_1072530 < baseStart_1072530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072592 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_1072592 : Nat := 118140960795 + 1072592 * 2 ^ 59
def prefixEnd_1072592 : Nat := 4983230072969 + 3 ^ 40 * 1072592 * 2
def baseEnd_1072592 : Nat := 550755242167372712567245

theorem tailTrace_1072592 : CollatzResearch.WordTrace tailWord_1072592 prefixEnd_1072592 550755242167372712567245 := by
  unfold tailWord_1072592
  simp only [CollatzResearch.WordTrace]
  refine ⟨19560322065094921487338015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26080429420126561983117353 19560322065094921487338015)
  ·
    refine ⟨29340483097642382231007023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19560322065094921487338015 29340483097642382231007023)
    ·
      refine ⟨44010724646463573346510535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29340483097642382231007023 44010724646463573346510535)
      ·
        refine ⟨66016086969695360019765803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44010724646463573346510535 66016086969695360019765803)
        ·
          refine ⟨99024130454543040029648705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66016086969695360019765803 99024130454543040029648705)
          ·
            refine ⟨74268097840907280022236529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99024130454543040029648705 74268097840907280022236529)
            ·
              refine ⟨55701073380680460016677397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74268097840907280022236529 55701073380680460016677397)
              ·
                refine ⟨2610987814719396563281753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55701073380680460016677397 2610987814719396563281753)
                ·
                  refine ⟨1958240861039547422461315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2610987814719396563281753 1958240861039547422461315)
                  ·
                    refine ⟨2937361291559321133691973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1958240861039547422461315 2937361291559321133691973)
                    ·
                      refine ⟨550755242167372712567245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2937361291559321133691973 550755242167372712567245)
                      ·
                        rfl

theorem cell23_1072592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_1072592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072592 prefixEnd_1072592 := by exact prefixLift 1072592
  have htrace : WordTrace (prefixWord ++ tailWord_1072592) baseStart_1072592 baseEnd_1072592 := by
    simpa [prefixWord, tailWord_1072592, baseEnd_1072592] using wordTrace_append hprefix tailTrace_1072592
  have hstable : (prefixWord ++ tailWord_1072592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072592).length < 2 ^ (prefixWord ++ tailWord_1072592).sum := by decide
  have hdescent : baseEnd_1072592 < baseStart_1072592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072612 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_1072612 : Nat := 118140960795 + 1072612 * 2 ^ 59
def prefixEnd_1072612 : Nat := 4983230072969 + 3 ^ 40 * 1072612 * 2
def baseEnd_1072612 : Nat := 550765511780462634317153

theorem tailTrace_1072612 : CollatzResearch.WordTrace tailWord_1072612 prefixEnd_1072612 550765511780462634317153 := by
  unfold tailWord_1072612
  simp only [CollatzResearch.WordTrace]
  refine ⟨19560686795058693195202045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26080915726744924260269393 19560686795058693195202045)
  ·
    refine ⟨7335257548147009948200767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19560686795058693195202045 7335257548147009948200767)
    ·
      refine ⟨11002886322220514922301151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7335257548147009948200767 11002886322220514922301151)
      ·
        refine ⟨16504329483330772383451727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11002886322220514922301151 16504329483330772383451727)
        ·
          refine ⟨24756494224996158575177591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16504329483330772383451727 24756494224996158575177591)
          ·
            refine ⟨37134741337494237862766387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24756494224996158575177591 37134741337494237862766387)
            ·
              refine ⟨55702112006241356794149581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37134741337494237862766387 55702112006241356794149581)
              ·
                refine ⟨20888292002340508797806093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55702112006241356794149581 20888292002340508797806093)
                ·
                  refine ⟨7833109500877690799177285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20888292002340508797806093 7833109500877690799177285)
                  ·
                    refine ⟨1468708031414567024845741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7833109500877690799177285 1468708031414567024845741)
                    ·
                      refine ⟨550765511780462634317153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1468708031414567024845741 550765511780462634317153)
                      ·
                        rfl

theorem cell23_1072612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_1072612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072612 prefixEnd_1072612 := by exact prefixLift 1072612
  have htrace : WordTrace (prefixWord ++ tailWord_1072612) baseStart_1072612 baseEnd_1072612 := by
    simpa [prefixWord, tailWord_1072612, baseEnd_1072612] using wordTrace_append hprefix tailTrace_1072612
  have hstable : (prefixWord ++ tailWord_1072612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072612).length < 2 ^ (prefixWord ++ tailWord_1072612).sum := by decide
  have hdescent : baseEnd_1072612 < baseStart_1072612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072626 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1072626 : Nat := 118140960795 + 1072626 * 2 ^ 59
def prefixEnd_1072626 : Nat := 4983230072969 + 3 ^ 40 * 1072626 * 2
def baseEnd_1072626 : Nat := 550772700509625579542089

theorem tailTrace_1072626 : CollatzResearch.WordTrace tailWord_1072626 prefixEnd_1072626 550772700509625579542089 := by
  unfold tailWord_1072626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9780471053016666695353433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26081256141377777854275821 9780471053016666695353433)
  ·
    refine ⟨7335353289762500021515075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9780471053016666695353433 7335353289762500021515075)
    ·
      refine ⟨11003029934643750032272613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7335353289762500021515075 11003029934643750032272613)
      ·
        refine ⟨2063068112745703131051115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11003029934643750032272613 2063068112745703131051115)
        ·
          refine ⟨3094602169118554696576673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063068112745703131051115 3094602169118554696576673)
          ·
            refine ⟨2320951626838916022432505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3094602169118554696576673 2320951626838916022432505)
            ·
              refine ⟨1740713720129187016824379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2320951626838916022432505 1740713720129187016824379)
              ·
                refine ⟨2611070580193780525236569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740713720129187016824379 2611070580193780525236569)
                ·
                  refine ⟨1958302935145335393927427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611070580193780525236569 1958302935145335393927427)
                  ·
                    refine ⟨2937454402718003090891141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1958302935145335393927427 2937454402718003090891141)
                    ·
                      refine ⟨550772700509625579542089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2937454402718003090891141 550772700509625579542089)
                      ·
                        rfl

theorem cell23_1072626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1072626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072626 prefixEnd_1072626 := by exact prefixLift 1072626
  have htrace : WordTrace (prefixWord ++ tailWord_1072626) baseStart_1072626 baseEnd_1072626 := by
    simpa [prefixWord, tailWord_1072626, baseEnd_1072626] using wordTrace_append hprefix tailTrace_1072626
  have hstable : (prefixWord ++ tailWord_1072626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072626).length < 2 ^ (prefixWord ++ tailWord_1072626).sum := by decide
  have hdescent : baseEnd_1072626 < baseStart_1072626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072680 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1072680 : Nat := 118140960795 + 1072680 * 2 ^ 59
def prefixEnd_1072680 : Nat := 4983230072969 + 3 ^ 40 * 1072680 * 2
def baseEnd_1072680 : Nat := 550800428464968368266841

theorem tailTrace_1072680 : CollatzResearch.WordTrace tailWord_1072680 prefixEnd_1072680 550800428464968368266841 := by
  unfold tailWord_1072680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19561926876935517001939747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26082569169247356002586329 19561926876935517001939747)
  ·
    refine ⟨29342890315403275502909621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19561926876935517001939747 29342890315403275502909621)
    ·
      refine ⟨2750895967069057078397777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29342890315403275502909621 2750895967069057078397777)
      ·
        refine ⟨2063171975301792808798333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2750895967069057078397777 2063171975301792808798333)
        ·
          refine ⟨773689490738172303299375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2063171975301792808798333 773689490738172303299375)
          ·
            refine ⟨1160534236107258454949063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773689490738172303299375 1160534236107258454949063)
            ·
              refine ⟨1740801354160887682423595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160534236107258454949063 1740801354160887682423595)
              ·
                refine ⟨2611202031241331523635393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740801354160887682423595 2611202031241331523635393)
                ·
                  refine ⟨1958401523430998642726545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611202031241331523635393 1958401523430998642726545)
                  ·
                    refine ⟨1468801142573248982044909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1958401523430998642726545 1468801142573248982044909)
                    ·
                      refine ⟨550800428464968368266841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1468801142573248982044909 550800428464968368266841)
                      ·
                        rfl

theorem cell23_1072680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1072680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072680 prefixEnd_1072680 := by exact prefixLift 1072680
  have htrace : WordTrace (prefixWord ++ tailWord_1072680) baseStart_1072680 baseEnd_1072680 := by
    simpa [prefixWord, tailWord_1072680, baseEnd_1072680] using wordTrace_append hprefix tailTrace_1072680
  have hstable : (prefixWord ++ tailWord_1072680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072680).length < 2 ^ (prefixWord ++ tailWord_1072680).sum := by decide
  have hdescent : baseEnd_1072680 < baseStart_1072680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072693 : List Nat := [1, 3, 3, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_1072693 : Nat := 118140960795 + 1072693 * 2 ^ 59
def prefixEnd_1072693 : Nat := 4983230072969 + 3 ^ 40 * 1072693 * 2
def baseEnd_1072693 : Nat := 550807103713476817404281

theorem tailTrace_1072693 : CollatzResearch.WordTrace tailWord_1072693 prefixEnd_1072693 550807103713476817404281 := by
  unfold tailWord_1072693
  simp only [CollatzResearch.WordTrace]
  refine ⟨39124327902823937224102733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26082885268549291482735155 39124327902823937224102733)
  ·
    refine ⟨14671622963558976459038525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39124327902823937224102733 14671622963558976459038525)
    ·
      refine ⟨5501858611334616172139447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14671622963558976459038525 5501858611334616172139447)
      ·
        refine ⟨8252787917001924258209171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5501858611334616172139447 8252787917001924258209171)
        ·
          refine ⟨12379181875502886387313757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8252787917001924258209171 12379181875502886387313757)
          ·
            refine ⟨4642193203313582395242659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12379181875502886387313757 4642193203313582395242659)
            ·
              refine ⟨6963289804970373592863989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642193203313582395242659 6963289804970373592863989)
              ·
                refine ⟨652808419215972524330999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6963289804970373592863989 652808419215972524330999)
                ·
                  refine ⟨979212628823958786496499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652808419215972524330999 979212628823958786496499)
                  ·
                    refine ⟨1468818943235938179744749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 979212628823958786496499 1468818943235938179744749)
                    ·
                      refine ⟨550807103713476817404281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1468818943235938179744749 550807103713476817404281)
                      ·
                        rfl

theorem cell23_1072693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_1072693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072693 prefixEnd_1072693 := by exact prefixLift 1072693
  have htrace : WordTrace (prefixWord ++ tailWord_1072693) baseStart_1072693 baseEnd_1072693 := by
    simpa [prefixWord, tailWord_1072693, baseEnd_1072693] using wordTrace_append hprefix tailTrace_1072693
  have hstable : (prefixWord ++ tailWord_1072693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072693).length < 2 ^ (prefixWord ++ tailWord_1072693).sum := by decide
  have hdescent : baseEnd_1072693 < baseStart_1072693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072696 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 1, 5]
def baseStart_1072696 : Nat := 118140960795 + 1072696 * 2 ^ 59
def prefixEnd_1072696 : Nat := 4983230072969 + 3 ^ 40 * 1072696 * 2
def baseEnd_1072696 : Nat := 183602881385146768555589

theorem tailTrace_1072696 : CollatzResearch.WordTrace tailWord_1072696 prefixEnd_1072696 183602881385146768555589 := by
  unfold tailWord_1072696
  simp only [CollatzResearch.WordTrace]
  refine ⟨19562218660906534368230971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26082958214542045824307961 19562218660906534368230971)
  ·
    refine ⟨29343327991359801552346457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19562218660906534368230971 29343327991359801552346457)
    ·
      refine ⟨22007495993519851164259843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29343327991359801552346457 22007495993519851164259843)
      ·
        refine ⟨33011243990279776746389765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22007495993519851164259843 33011243990279776746389765)
        ·
          refine ⟨6189608248177458139948081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33011243990279776746389765 6189608248177458139948081)
          ·
            refine ⟨4642206186133093604961061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6189608248177458139948081 4642206186133093604961061)
            ·
              refine ⟨870413659899955050930199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4642206186133093604961061 870413659899955050930199)
              ·
                refine ⟨1305620489849932576395299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870413659899955050930199 1305620489849932576395299)
                ·
                  refine ⟨1958430734774898864592949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305620489849932576395299 1958430734774898864592949)
                  ·
                    refine ⟨183602881385146768555589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1958430734774898864592949 183602881385146768555589)
                    ·
                      rfl

theorem cell23_1072696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_1072696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072696 prefixEnd_1072696 := by exact prefixLift 1072696
  have htrace : WordTrace (prefixWord ++ tailWord_1072696) baseStart_1072696 baseEnd_1072696 := by
    simpa [prefixWord, tailWord_1072696, baseEnd_1072696] using wordTrace_append hprefix tailTrace_1072696
  have hstable : (prefixWord ++ tailWord_1072696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072696).length < 2 ^ (prefixWord ++ tailWord_1072696).sum := by decide
  have hdescent : baseEnd_1072696 < baseStart_1072696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072709 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_1072709 : Nat := 118140960795 + 1072709 * 2 ^ 59
def prefixEnd_1072709 : Nat := 4983230072969 + 3 ^ 40 * 1072709 * 2
def baseEnd_1072709 : Nat := 183605106467982918268069

theorem tailTrace_1072709 : CollatzResearch.WordTrace tailWord_1072709 prefixEnd_1072709 183605106467982918268069 := by
  unfold tailWord_1072709
  simp only [CollatzResearch.WordTrace]
  refine ⟨39124911470765971956685181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26083274313843981304456787 39124911470765971956685181)
  ·
    refine ⟨14671841801537239483756943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39124911470765971956685181 14671841801537239483756943)
    ·
      refine ⟨22007762702305859225635415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14671841801537239483756943 22007762702305859225635415)
      ·
        refine ⟨33011644053458788838453123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22007762702305859225635415 33011644053458788838453123)
        ·
          refine ⟨49517466080188183257679685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33011644053458788838453123 49517466080188183257679685)
          ·
            refine ⟨9284524890035284360814941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49517466080188183257679685 9284524890035284360814941)
            ·
              refine ⟨3481696833763231635305603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9284524890035284360814941 3481696833763231635305603)
              ·
                refine ⟨5222545250644847452958405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481696833763231635305603 5222545250644847452958405)
                ·
                  refine ⟨979227234495908897429701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5222545250644847452958405 979227234495908897429701)
                  ·
                    refine ⟨183605106467982918268069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 979227234495908897429701 183605106467982918268069)
                    ·
                      rfl

theorem cell23_1072709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_1072709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072709 prefixEnd_1072709 := by exact prefixLift 1072709
  have htrace : WordTrace (prefixWord ++ tailWord_1072709) baseStart_1072709 baseEnd_1072709 := by
    simpa [prefixWord, tailWord_1072709, baseEnd_1072709] using wordTrace_append hprefix tailTrace_1072709
  have hstable : (prefixWord ++ tailWord_1072709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072709).length < 2 ^ (prefixWord ++ tailWord_1072709).sum := by decide
  have hdescent : baseEnd_1072709 < baseStart_1072709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072712 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1072712 : Nat := 118140960795 + 1072712 * 2 ^ 59
def prefixEnd_1072712 : Nat := 4983230072969 + 3 ^ 40 * 1072712 * 2
def baseEnd_1072712 : Nat := 550816859845912243066693

theorem tailTrace_1072712 : CollatzResearch.WordTrace tailWord_1072712 prefixEnd_1072712 550816859845912243066693 := by
  unfold tailWord_1072712
  simp only [CollatzResearch.WordTrace]
  refine ⟨19562510444877551734522195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26083347259836735646029593 19562510444877551734522195)
  ·
    refine ⟨29343765667316327601783293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19562510444877551734522195 29343765667316327601783293)
    ·
      refine ⟨11003912125243622850668735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29343765667316327601783293 11003912125243622850668735)
      ·
        refine ⟨16505868187865434276003103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11003912125243622850668735 16505868187865434276003103)
        ·
          refine ⟨24758802281798151414004655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16505868187865434276003103 24758802281798151414004655)
          ·
            refine ⟨37138203422697227121006983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24758802281798151414004655 37138203422697227121006983)
            ·
              refine ⟨55707305134045840681510475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37138203422697227121006983 55707305134045840681510475)
              ·
                refine ⟨83560957701068761022265713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55707305134045840681510475 83560957701068761022265713)
                ·
                  refine ⟨62670718275801570766699285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83560957701068761022265713 62670718275801570766699285)
                  ·
                    refine ⟨2937689919178198629689029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62670718275801570766699285 2937689919178198629689029)
                    ·
                      refine ⟨550816859845912243066693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2937689919178198629689029 550816859845912243066693)
                      ·
                        rfl

theorem cell23_1072712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1072712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072712 prefixEnd_1072712 := by exact prefixLift 1072712
  have htrace : WordTrace (prefixWord ++ tailWord_1072712) baseStart_1072712 baseEnd_1072712 := by
    simpa [prefixWord, tailWord_1072712, baseEnd_1072712] using wordTrace_append hprefix tailTrace_1072712
  have hstable : (prefixWord ++ tailWord_1072712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072712).length < 2 ^ (prefixWord ++ tailWord_1072712).sum := by decide
  have hdescent : baseEnd_1072712 < baseStart_1072712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072739 : List Nat := [1, 1, 1, 5, 1, 3, 4, 7]
def baseStart_1072739 : Nat := 118140960795 + 1072739 * 2 ^ 59
def prefixEnd_1072739 : Nat := 4983230072969 + 3 ^ 40 * 1072739 * 2
def baseEnd_1072739 : Nat := 20401137919391986571447

theorem tailTrace_1072739 : CollatzResearch.WordTrace tailWord_1072739 prefixEnd_1072739 20401137919391986571447 := by
  unfold tailWord_1072739
  simp only [CollatzResearch.WordTrace]
  refine ⟨39126005660657287080277271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26084003773771524720184847 39126005660657287080277271)
  ·
    refine ⟨58689008490985930620415907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39126005660657287080277271 58689008490985930620415907)
    ·
      refine ⟨88033512736478895930623861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58689008490985930620415907 88033512736478895930623861)
      ·
        refine ⟨8253141819044896493495987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88033512736478895930623861 8253141819044896493495987)
        ·
          refine ⟨12379712728567344740243981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8253141819044896493495987 12379712728567344740243981)
          ·
            refine ⟨4642392273212754277591493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12379712728567344740243981 4642392273212754277591493)
            ·
              refine ⟨870448551227391427048405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4642392273212754277591493 870448551227391427048405)
              ·
                refine ⟨20401137919391986571447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 870448551227391427048405 20401137919391986571447)
                ·
                  rfl

theorem cell23_1072739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 7].length) (baseStart_1072739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072739 prefixEnd_1072739 := by exact prefixLift 1072739
  have htrace : WordTrace (prefixWord ++ tailWord_1072739) baseStart_1072739 baseEnd_1072739 := by
    simpa [prefixWord, tailWord_1072739, baseEnd_1072739] using wordTrace_append hprefix tailTrace_1072739
  have hstable : (prefixWord ++ tailWord_1072739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072739).length < 2 ^ (prefixWord ++ tailWord_1072739).sum := by decide
  have hdescent : baseEnd_1072739 < baseStart_1072739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072819 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4]
def baseStart_1072819 : Nat := 118140960795 + 1072819 * 2 ^ 59
def prefixEnd_1072819 : Nat := 4983230072969 + 3 ^ 40 * 1072819 * 2
def baseEnd_1072819 : Nat := 550871802275943324428701

theorem tailTrace_1072819 : CollatzResearch.WordTrace tailWord_1072819 prefixEnd_1072819 550871802275943324428701 := by
  unfold tailWord_1072819
  simp only [CollatzResearch.WordTrace]
  refine ⟨39128923500367460743189511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26085949000244973828793007 39128923500367460743189511)
  ·
    refine ⟨58693385250551191114784267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39128923500367460743189511 58693385250551191114784267)
    ·
      refine ⟨88040077875826786672176401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58693385250551191114784267 88040077875826786672176401)
      ·
        refine ⟨66030058406870090004132301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88040077875826786672176401 66030058406870090004132301)
        ·
          refine ⟨24761271902576283751549613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66030058406870090004132301 24761271902576283751549613)
          ·
            refine ⟨9285476963466106406831105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24761271902576283751549613 9285476963466106406831105)
            ·
              refine ⟨6964107722599579805123329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9285476963466106406831105 6964107722599579805123329)
              ·
                refine ⟨5223080791949684853842497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6964107722599579805123329 5223080791949684853842497)
                ·
                  refine ⟨3917310593962263640381873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5223080791949684853842497 3917310593962263640381873)
                  ·
                    refine ⟨2937982945471697730286405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917310593962263640381873 2937982945471697730286405)
                    ·
                      refine ⟨550871802275943324428701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2937982945471697730286405 550871802275943324428701)
                      ·
                        rfl

theorem cell23_1072819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_1072819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072819 prefixEnd_1072819 := by exact prefixLift 1072819
  have htrace : WordTrace (prefixWord ++ tailWord_1072819) baseStart_1072819 baseEnd_1072819 := by
    simpa [prefixWord, tailWord_1072819, baseEnd_1072819] using wordTrace_append hprefix tailTrace_1072819
  have hstable : (prefixWord ++ tailWord_1072819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072819).length < 2 ^ (prefixWord ++ tailWord_1072819).sum := by decide
  have hdescent : baseEnd_1072819 < baseStart_1072819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072829 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 7]
def baseStart_1072829 : Nat := 118140960795 + 1072829 * 2 ^ 59
def prefixEnd_1072829 : Nat := 4983230072969 + 3 ^ 40 * 1072829 * 2
def baseEnd_1072829 : Nat := 61208548564720920589295

theorem tailTrace_1072829 : CollatzResearch.WordTrace tailWord_1072829 prefixEnd_1072829 61208548564720920589295 := by
  unfold tailWord_1072829
  simp only [CollatzResearch.WordTrace]
  refine ⟨39129288230331232451053541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26086192153554154967369027 39129288230331232451053541)
  ·
    refine ⟨7336741543187106084572539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39129288230331232451053541 7336741543187106084572539)
    ·
      refine ⟨11005112314780659126858809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7336741543187106084572539 11005112314780659126858809)
      ·
        refine ⟨8253834236085494345144107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11005112314780659126858809 8253834236085494345144107)
        ·
          refine ⟨12380751354128241517716161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8253834236085494345144107 12380751354128241517716161)
          ·
            refine ⟨9285563515596181138287121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12380751354128241517716161 9285563515596181138287121)
            ·
              refine ⟨6964172636697135853715341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9285563515596181138287121 6964172636697135853715341)
              ·
                refine ⟨2611564738761425945143253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6964172636697135853715341 2611564738761425945143253)
                ·
                  refine ⟨61208548564720920589295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2611564738761425945143253 61208548564720920589295)
                  ·
                    rfl

theorem cell23_1072829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_1072829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072829 prefixEnd_1072829 := by exact prefixLift 1072829
  have htrace : WordTrace (prefixWord ++ tailWord_1072829) baseStart_1072829 baseEnd_1072829 := by
    simpa [prefixWord, tailWord_1072829, baseEnd_1072829] using wordTrace_append hprefix tailTrace_1072829
  have hstable : (prefixWord ++ tailWord_1072829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072829).length < 2 ^ (prefixWord ++ tailWord_1072829).sum := by decide
  have hdescent : baseEnd_1072829 < baseStart_1072829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072836 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1072836 : Nat := 118140960795 + 1072836 * 2 ^ 59
def prefixEnd_1072836 : Nat := 4983230072969 + 3 ^ 40 * 1072836 * 2
def baseEnd_1072836 : Nat := 550880531447069757916123

theorem tailTrace_1072836 : CollatzResearch.WordTrace tailWord_1072836 prefixEnd_1072836 550880531447069757916123 := by
  unfold tailWord_1072836
  simp only [CollatzResearch.WordTrace]
  refine ⟨19564771770652936323279181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26086362360870581764372241 19564771770652936323279181)
  ·
    refine ⟨7336789413994851121229693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19564771770652936323279181 7336789413994851121229693)
    ·
      refine ⟨2751296030248069170461135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7336789413994851121229693 2751296030248069170461135)
      ·
        refine ⟨4126944045372103755691703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751296030248069170461135 4126944045372103755691703)
        ·
          refine ⟨6190416068058155633537555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126944045372103755691703 6190416068058155633537555)
          ·
            refine ⟨9285624102087233450306333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6190416068058155633537555 9285624102087233450306333)
            ·
              refine ⟨3482109038282712543864875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9285624102087233450306333 3482109038282712543864875)
              ·
                refine ⟨5223163557424068815797313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482109038282712543864875 5223163557424068815797313)
                ·
                  refine ⟨3917372668068051611847985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5223163557424068815797313 3917372668068051611847985)
                  ·
                    refine ⟨2938029501051038708885989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917372668068051611847985 2938029501051038708885989)
                    ·
                      refine ⟨550880531447069757916123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2938029501051038708885989 550880531447069757916123)
                      ·
                        rfl

theorem cell23_1072836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1072836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072836 prefixEnd_1072836 := by exact prefixLift 1072836
  have htrace : WordTrace (prefixWord ++ tailWord_1072836) baseStart_1072836 baseEnd_1072836 := by
    simpa [prefixWord, tailWord_1072836, baseEnd_1072836] using wordTrace_append hprefix tailTrace_1072836
  have hstable : (prefixWord ++ tailWord_1072836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072836).length < 2 ^ (prefixWord ++ tailWord_1072836).sum := by decide
  have hdescent : baseEnd_1072836 < baseStart_1072836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072861 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1072861 : Nat := 118140960795 + 1072861 * 2 ^ 59
def prefixEnd_1072861 : Nat := 4983230072969 + 3 ^ 40 * 1072861 * 2
def baseEnd_1072861 : Nat := 550893368463432160103509

theorem tailTrace_1072861 : CollatzResearch.WordTrace tailWord_1072861 prefixEnd_1072861 550893368463432160103509 := by
  unfold tailWord_1072861
  simp only [CollatzResearch.WordTrace]
  refine ⟨39130455366215301916218437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26086970244143534610812291 39130455366215301916218437)
  ·
    refine ⟨7336960381165369109290957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39130455366215301916218437 7336960381165369109290957)
    ·
      refine ⟨2751360142937013415984109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7336960381165369109290957 2751360142937013415984109)
      ·
        refine ⟨1031760053601380030994041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2751360142937013415984109 1031760053601380030994041)
        ·
          refine ⟨773820040201035023245531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031760053601380030994041 773820040201035023245531)
          ·
            refine ⟨1160730060301552534868297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773820040201035023245531 1160730060301552534868297)
            ·
              refine ⟨870547545226164401151223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160730060301552534868297 870547545226164401151223)
              ·
                refine ⟨1305821317839246601726835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870547545226164401151223 1305821317839246601726835)
                ·
                  refine ⟨1958731976758869902590253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305821317839246601726835 1958731976758869902590253)
                  ·
                    refine ⟨734524491284576213471345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1958731976758869902590253 734524491284576213471345)
                    ·
                      refine ⟨550893368463432160103509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 734524491284576213471345 550893368463432160103509)
                      ·
                        rfl

theorem cell23_1072861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1072861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072861 prefixEnd_1072861 := by exact prefixLift 1072861
  have htrace : WordTrace (prefixWord ++ tailWord_1072861) baseStart_1072861 baseEnd_1072861 := by
    simpa [prefixWord, tailWord_1072861, baseEnd_1072861] using wordTrace_append hprefix tailTrace_1072861
  have hstable : (prefixWord ++ tailWord_1072861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072861).length < 2 ^ (prefixWord ++ tailWord_1072861).sum := by decide
  have hdescent : baseEnd_1072861 < baseStart_1072861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072933 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_1072933 : Nat := 118140960795 + 1072933 * 2 ^ 59
def prefixEnd_1072933 : Nat := 4983230072969 + 3 ^ 40 * 1072933 * 2
def baseEnd_1072933 : Nat := 550930339070555878403177

theorem tailTrace_1072933 : CollatzResearch.WordTrace tailWord_1072933 prefixEnd_1072933 550930339070555878403177 := by
  unfold tailWord_1072933
  simp only [CollatzResearch.WordTrace]
  refine ⟨39133081421954458212839453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26088720947969638808559635 39133081421954458212839453)
  ·
    refine ⟨14674905533232921829814795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39133081421954458212839453 14674905533232921829814795)
    ·
      refine ⟨22012358299849382744722193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14674905533232921829814795 22012358299849382744722193)
      ·
        refine ⟨16509268724887037058541645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22012358299849382744722193 16509268724887037058541645)
        ·
          refine ⟨6190975771832638896953117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16509268724887037058541645 6190975771832638896953117)
          ·
            refine ⟨2321615914437239586357419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6190975771832638896953117 2321615914437239586357419)
            ·
              refine ⟨3482423871655859379536129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321615914437239586357419 3482423871655859379536129)
              ·
                refine ⟨2611817903741894534652097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3482423871655859379536129 2611817903741894534652097)
                ·
                  refine ⟨1958863427806420900989073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611817903741894534652097 1958863427806420900989073)
                  ·
                    refine ⟨1469147570854815675741805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1958863427806420900989073 1469147570854815675741805)
                    ·
                      refine ⟨550930339070555878403177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1469147570854815675741805 550930339070555878403177)
                      ·
                        rfl

theorem cell23_1072933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_1072933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072933 prefixEnd_1072933 := by exact prefixLift 1072933
  have htrace : WordTrace (prefixWord ++ tailWord_1072933) baseStart_1072933 baseEnd_1072933 := by
    simpa [prefixWord, tailWord_1072933, baseEnd_1072933] using wordTrace_append hprefix tailTrace_1072933
  have hstable : (prefixWord ++ tailWord_1072933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072933).length < 2 ^ (prefixWord ++ tailWord_1072933).sum := by decide
  have hdescent : baseEnd_1072933 < baseStart_1072933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072936 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 8]
def baseStart_1072936 : Nat := 118140960795 + 1072936 * 2 ^ 59
def prefixEnd_1072936 : Nat := 4983230072969 + 3 ^ 40 * 1072936 * 2
def baseEnd_1072936 : Nat := 61214653279168818518407

theorem tailTrace_1072936 : CollatzResearch.WordTrace tailWord_1072936 prefixEnd_1072936 61214653279168818518407 := by
  unfold tailWord_1072936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19566595420471794862599331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26088793893962393150132441 19566595420471794862599331)
  ·
    refine ⟨29349893130707692293898997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19566595420471794862599331 29349893130707692293898997)
    ·
      refine ⟨2751552481003846152553031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29349893130707692293898997 2751552481003846152553031)
      ·
        refine ⟨4127328721505769228829547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751552481003846152553031 4127328721505769228829547)
        ·
          refine ⟨6190993082258653843244321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4127328721505769228829547 6190993082258653843244321)
          ·
            refine ⟨4643244811693990382433241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6190993082258653843244321 4643244811693990382433241)
            ·
              refine ⟨3482433608770492786824931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4643244811693990382433241 3482433608770492786824931)
              ·
                refine ⟨5223650413155739180237397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482433608770492786824931 5223650413155739180237397)
                ·
                  refine ⟨61214653279168818518407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5223650413155739180237397 61214653279168818518407)
                  ·
                    rfl

theorem cell23_1072936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 8].length) (baseStart_1072936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1072936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1072936 prefixEnd_1072936 := by exact prefixLift 1072936
  have htrace : WordTrace (prefixWord ++ tailWord_1072936) baseStart_1072936 baseEnd_1072936 := by
    simpa [prefixWord, tailWord_1072936, baseEnd_1072936] using wordTrace_append hprefix tailTrace_1072936
  have hstable : (prefixWord ++ tailWord_1072936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072936).length < 2 ^ (prefixWord ++ tailWord_1072936).sum := by decide
  have hdescent : baseEnd_1072936 < baseStart_1072936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073013 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1073013 : Nat := 118140960795 + 1073013 * 2 ^ 59
def prefixEnd_1073013 : Nat := 4983230072969 + 3 ^ 40 * 1073013 * 2
def baseEnd_1073013 : Nat := 183657139174305188467603

theorem tailTrace_1073013 : CollatzResearch.WordTrace tailWord_1073013 prefixEnd_1073013 183657139174305188467603 := by
  unfold tailWord_1073013
  simp only [CollatzResearch.WordTrace]
  refine ⟨39135999261664631875751693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26090666174443087917167795 39135999261664631875751693)
  ·
    refine ⟨14675999723124236953406885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39135999261664631875751693 14675999723124236953406885)
    ·
      refine ⟨2751749948085794428763791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14675999723124236953406885 2751749948085794428763791)
      ·
        refine ⟨4127624922128691643145687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751749948085794428763791 4127624922128691643145687)
        ·
          refine ⟨6191437383193037464718531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4127624922128691643145687 6191437383193037464718531)
          ·
            refine ⟨9287156074789556197077797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6191437383193037464718531 9287156074789556197077797)
            ·
              refine ⟨1741341764023041786952087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9287156074789556197077797 1741341764023041786952087)
              ·
                refine ⟨2612012646034562680428131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741341764023041786952087 2612012646034562680428131)
                ·
                  refine ⟨3918018969051844020642197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612012646034562680428131 3918018969051844020642197)
                  ·
                    refine ⟨183657139174305188467603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3918018969051844020642197 183657139174305188467603)
                    ·
                      rfl

theorem cell23_1073013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1073013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073013 prefixEnd_1073013 := by exact prefixLift 1073013
  have htrace : WordTrace (prefixWord ++ tailWord_1073013) baseStart_1073013 baseEnd_1073013 := by
    simpa [prefixWord, tailWord_1073013, baseEnd_1073013] using wordTrace_append hprefix tailTrace_1073013
  have hstable : (prefixWord ++ tailWord_1073013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073013).length < 2 ^ (prefixWord ++ tailWord_1073013).sum := by decide
  have hdescent : baseEnd_1073013 < baseStart_1073013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073023 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 3]
def baseStart_1073023 : Nat := 118140960795 + 1073023 * 2 ^ 59
def prefixEnd_1073023 : Nat := 4983230072969 + 3 ^ 40 * 1073023 * 2
def baseEnd_1073023 : Nat := 550976552329460526277763

theorem tailTrace_1073023 : CollatzResearch.WordTrace tailWord_1073023 prefixEnd_1073023 550976552329460526277763 := by
  unfold tailWord_1073023
  simp only [CollatzResearch.WordTrace]
  refine ⟨39136363991628403583615723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26090909327752269055743815 39136363991628403583615723)
  ·
    refine ⟨58704545987442605375423585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39136363991628403583615723 58704545987442605375423585)
    ·
      refine ⟨44028409490581954031567689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58704545987442605375423585 44028409490581954031567689)
      ·
        refine ⟨33021307117936465523675767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44028409490581954031567689 33021307117936465523675767)
        ·
          refine ⟨49531960676904698285513651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33021307117936465523675767 49531960676904698285513651)
          ·
            refine ⟨74297941015357047428270477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49531960676904698285513651 74297941015357047428270477)
            ·
              refine ⟨27861727880758892785601429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74297941015357047428270477 27861727880758892785601429)
              ·
                refine ⟨1306018494410573099325067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27861727880758892785601429 1306018494410573099325067)
                ·
                  refine ⟨1959027741615859648987601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306018494410573099325067 1959027741615859648987601)
                  ·
                    refine ⟨1469270806211894736740701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1959027741615859648987601 1469270806211894736740701)
                    ·
                      refine ⟨550976552329460526277763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1469270806211894736740701 550976552329460526277763)
                      ·
                        rfl

theorem cell23_1073023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_1073023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073023 prefixEnd_1073023 := by exact prefixLift 1073023
  have htrace : WordTrace (prefixWord ++ tailWord_1073023) baseStart_1073023 baseEnd_1073023 := by
    simpa [prefixWord, tailWord_1073023, baseEnd_1073023] using wordTrace_append hprefix tailTrace_1073023
  have hstable : (prefixWord ++ tailWord_1073023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073023).length < 2 ^ (prefixWord ++ tailWord_1073023).sum := by decide
  have hdescent : baseEnd_1073023 < baseStart_1073023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073034 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_1073034 : Nat := 118140960795 + 1073034 * 2 ^ 59
def prefixEnd_1073034 : Nat := 4983230072969 + 3 ^ 40 * 1073034 * 2
def baseEnd_1073034 : Nat := 183660733538886661080071

theorem tailTrace_1073034 : CollatzResearch.WordTrace tailWord_1073034 prefixEnd_1073034 183660733538886661080071 := by
  unfold tailWord_1073034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9784191298647138115566539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26091176796392368308177437 9784191298647138115566539)
  ·
    refine ⟨14676286947970707173349809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9784191298647138115566539 14676286947970707173349809)
    ·
      refine ⟨11007215210978030380012357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14676286947970707173349809 11007215210978030380012357)
      ·
        refine ⟨2063852852058380696252317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11007215210978030380012357 2063852852058380696252317)
        ·
          refine ⟨773944819521892761094619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2063852852058380696252317 773944819521892761094619)
          ·
            refine ⟨1160917229282839141641929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773944819521892761094619 1160917229282839141641929)
            ·
              refine ⟨870687921962129356231447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160917229282839141641929 870687921962129356231447)
              ·
                refine ⟨1306031882943194034347171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870687921962129356231447 1306031882943194034347171)
                ·
                  refine ⟨1959047824414791051520757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306031882943194034347171 1959047824414791051520757)
                  ·
                    refine ⟨183660733538886661080071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1959047824414791051520757 183660733538886661080071)
                    ·
                      rfl

theorem cell23_1073034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_1073034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073034 prefixEnd_1073034 := by exact prefixLift 1073034
  have htrace : WordTrace (prefixWord ++ tailWord_1073034) baseStart_1073034 baseEnd_1073034 := by
    simpa [prefixWord, tailWord_1073034, baseEnd_1073034] using wordTrace_append hprefix tailTrace_1073034
  have hstable : (prefixWord ++ tailWord_1073034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073034).length < 2 ^ (prefixWord ++ tailWord_1073034).sum := by decide
  have hdescent : baseEnd_1073034 < baseStart_1073034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073064 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1073064 : Nat := 118140960795 + 1073064 * 2 ^ 59
def prefixEnd_1073064 : Nat := 4983230072969 + 3 ^ 40 * 1073064 * 2
def baseEnd_1073064 : Nat := 183665868345431621955025

theorem tailTrace_1073064 : CollatzResearch.WordTrace tailWord_1073064 prefixEnd_1073064 183665868345431621955025 := by
  unfold tailWord_1073064
  simp only [CollatzResearch.WordTrace]
  refine ⟨19568929692239933792929123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26091906256319911723905497 19568929692239933792929123)
  ·
    refine ⟨29353394538359900689393685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19568929692239933792929123 29353394538359900689393685)
    ·
      refine ⟨1375940368985620344815329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29353394538359900689393685 1375940368985620344815329)
      ·
        refine ⟨1031955276739215258611497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1375940368985620344815329 1031955276739215258611497)
        ·
          refine ⟨773966457554411443958623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031955276739215258611497 773966457554411443958623)
          ·
            refine ⟨1160949686331617165937935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773966457554411443958623 1160949686331617165937935)
            ·
              refine ⟨1741424529497425748906903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160949686331617165937935 1741424529497425748906903)
              ·
                refine ⟨2612136794246138623360355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741424529497425748906903 2612136794246138623360355)
                ·
                  refine ⟨3918205191369207935040533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612136794246138623360355 3918205191369207935040533)
                  ·
                    refine ⟨183665868345431621955025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3918205191369207935040533 183665868345431621955025)
                    ·
                      rfl

theorem cell23_1073064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1073064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073064 prefixEnd_1073064 := by exact prefixLift 1073064
  have htrace : WordTrace (prefixWord ++ tailWord_1073064) baseStart_1073064 baseEnd_1073064 := by
    simpa [prefixWord, tailWord_1073064, baseEnd_1073064] using wordTrace_append hprefix tailTrace_1073064
  have hstable : (prefixWord ++ tailWord_1073064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073064).length < 2 ^ (prefixWord ++ tailWord_1073064).sum := by decide
  have hdescent : baseEnd_1073064 < baseStart_1073064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073163 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 2, 5]
def baseStart_1073163 : Nat := 118140960795 + 1073163 * 2 ^ 59
def prefixEnd_1073163 : Nat := 4983230072969 + 3 ^ 40 * 1073163 * 2
def baseEnd_1073163 : Nat := 183682813207029992842373

theorem tailTrace_1073163 : CollatzResearch.WordTrace tailWord_1073163 prefixEnd_1073163 183682813207029992842373 := by
  unfold tailWord_1073163
  simp only [CollatzResearch.WordTrace]
  refine ⟨39141470211121207493712143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26094313474080804995808095 39141470211121207493712143)
  ·
    refine ⟨58712205316681811240568215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39141470211121207493712143 58712205316681811240568215)
    ·
      refine ⟨88068307975022716860852323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58712205316681811240568215 88068307975022716860852323)
      ·
        refine ⟨132102461962534075291278485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88068307975022716860852323 132102461962534075291278485)
        ·
          refine ⟨6192302904493784779278679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132102461962534075291278485 6192302904493784779278679)
          ·
            refine ⟨9288454356740677168918019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6192302904493784779278679 9288454356740677168918019)
            ·
              refine ⟨13932681535111015753377029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9288454356740677168918019 13932681535111015753377029)
              ·
                refine ⟨2612377787833315453758193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13932681535111015753377029 2612377787833315453758193)
                ·
                  refine ⟨1959283340874986590318645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612377787833315453758193 1959283340874986590318645)
                  ·
                    refine ⟨183682813207029992842373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1959283340874986590318645 183682813207029992842373)
                    ·
                      rfl

theorem cell23_1073163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 5].length) (baseStart_1073163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073163 prefixEnd_1073163 := by exact prefixLift 1073163
  have htrace : WordTrace (prefixWord ++ tailWord_1073163) baseStart_1073163 baseEnd_1073163 := by
    simpa [prefixWord, tailWord_1073163, baseEnd_1073163] using wordTrace_append hprefix tailTrace_1073163
  have hstable : (prefixWord ++ tailWord_1073163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073163).length < 2 ^ (prefixWord ++ tailWord_1073163).sum := by decide
  have hdescent : baseEnd_1073163 < baseStart_1073163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073183 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1073183 : Nat := 118140960795 + 1073183 * 2 ^ 59
def prefixEnd_1073183 : Nat := 4983230072969 + 3 ^ 40 * 1073183 * 2
def baseEnd_1073183 : Nat := 551058709234179900277027

theorem tailTrace_1073183 : CollatzResearch.WordTrace tailWord_1073183 prefixEnd_1073183 551058709234179900277027 := by
  unfold tailWord_1073183
  simp only [CollatzResearch.WordTrace]
  refine ⟨39142199671048750909440203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26094799780699167272960135 39142199671048750909440203)
  ·
    refine ⟨58713299506573126364160305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39142199671048750909440203 58713299506573126364160305)
    ·
      refine ⟨44034974629929844773120229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58713299506573126364160305 44034974629929844773120229)
      ·
        refine ⟨8256557743111845894960043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44034974629929844773120229 8256557743111845894960043)
        ·
          refine ⟨12384836614667768842440065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8256557743111845894960043 12384836614667768842440065)
          ·
            refine ⟨9288627461000826631830049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12384836614667768842440065 9288627461000826631830049)
            ·
              refine ⟨6966470595750619973872537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9288627461000826631830049 6966470595750619973872537)
              ·
                refine ⟨5224852946812964980404403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6966470595750619973872537 5224852946812964980404403)
                ·
                  refine ⟨7837279420219447470606605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5224852946812964980404403 7837279420219447470606605)
                  ·
                    refine ⟨2938979782582292801477477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7837279420219447470606605 2938979782582292801477477)
                    ·
                      refine ⟨551058709234179900277027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2938979782582292801477477 551058709234179900277027)
                      ·
                        rfl

theorem cell23_1073183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1073183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073183 prefixEnd_1073183 := by exact prefixLift 1073183
  have htrace : WordTrace (prefixWord ++ tailWord_1073183) baseStart_1073183 baseEnd_1073183 := by
    simpa [prefixWord, tailWord_1073183, baseEnd_1073183] using wordTrace_append hprefix tailTrace_1073183
  have hstable : (prefixWord ++ tailWord_1073183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073183).length < 2 ^ (prefixWord ++ tailWord_1073183).sum := by decide
  have hdescent : baseEnd_1073183 < baseStart_1073183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073200 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4]
def baseStart_1073200 : Nat := 118140960795 + 1073200 * 2 ^ 59
def prefixEnd_1073200 : Nat := 4983230072969 + 3 ^ 40 * 1073200 * 2
def baseEnd_1073200 : Nat := 551067438405306333764449

theorem tailTrace_1073200 : CollatzResearch.WordTrace tailWord_1073200 prefixEnd_1073200 551067438405306333764449 := by
  unfold tailWord_1073200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19571409855993581406404527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26095213141324775208539369 19571409855993581406404527)
  ·
    refine ⟨29357114783990372109606791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19571409855993581406404527 29357114783990372109606791)
    ·
      refine ⟨44035672175985558164410187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29357114783990372109606791 44035672175985558164410187)
      ·
        refine ⟨66053508263978337246615281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44035672175985558164410187 66053508263978337246615281)
        ·
          refine ⟨49540131197983752934961461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66053508263978337246615281 49540131197983752934961461)
          ·
            refine ⟨4644387299810976837652637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49540131197983752934961461 4644387299810976837652637)
            ·
              refine ⟨1741645237429116314119739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4644387299810976837652637 1741645237429116314119739)
              ·
                refine ⟨2612467856143674471179609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741645237429116314119739 2612467856143674471179609)
                ·
                  refine ⟨1959350892107755853384707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612467856143674471179609 1959350892107755853384707)
                  ·
                    refine ⟨2939026338161633780077061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1959350892107755853384707 2939026338161633780077061)
                    ·
                      refine ⟨551067438405306333764449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2939026338161633780077061 551067438405306333764449)
                      ·
                        rfl

theorem cell23_1073200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_1073200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073200 prefixEnd_1073200 := by exact prefixLift 1073200
  have htrace : WordTrace (prefixWord ++ tailWord_1073200) baseStart_1073200 baseEnd_1073200 := by
    simpa [prefixWord, tailWord_1073200, baseEnd_1073200] using wordTrace_append hprefix tailTrace_1073200
  have hstable : (prefixWord ++ tailWord_1073200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073200).length < 2 ^ (prefixWord ++ tailWord_1073200).sum := by decide
  have hdescent : baseEnd_1073200 < baseStart_1073200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073213 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1073213 : Nat := 118140960795 + 1073213 * 2 ^ 59
def prefixEnd_1073213 : Nat := 4983230072969 + 3 ^ 40 * 1073213 * 2
def baseEnd_1073213 : Nat := 551074113653814782901889

theorem tailTrace_1073213 : CollatzResearch.WordTrace tailWord_1073213 prefixEnd_1073213 551074113653814782901889 := by
  unfold tailWord_1073213
  simp only [CollatzResearch.WordTrace]
  refine ⟨39143293860940066033032293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26095529240626710688688195 39143293860940066033032293)
  ·
    refine ⟨7339367598926262381193555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39143293860940066033032293 7339367598926262381193555)
    ·
      refine ⟨11009051398389393571790333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7339367598926262381193555 11009051398389393571790333)
      ·
        refine ⟨4128394274396022589421375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11009051398389393571790333 4128394274396022589421375)
        ·
          refine ⟨6192591411594033884132063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128394274396022589421375 6192591411594033884132063)
          ·
            refine ⟨9288887117391050826198095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6192591411594033884132063 9288887117391050826198095)
            ·
              refine ⟨13933330676086576239297143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9288887117391050826198095 13933330676086576239297143)
              ·
                refine ⟨20899996014129864358945715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13933330676086576239297143 20899996014129864358945715)
                ·
                  refine ⟨31349994021194796538418573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20899996014129864358945715 31349994021194796538418573)
                  ·
                    refine ⟨11756247757948048701906965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31349994021194796538418573 11756247757948048701906965)
                    ·
                      refine ⟨551074113653814782901889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11756247757948048701906965 551074113653814782901889)
                      ·
                        rfl

theorem cell23_1073213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1073213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073213 prefixEnd_1073213 := by exact prefixLift 1073213
  have htrace : WordTrace (prefixWord ++ tailWord_1073213) baseStart_1073213 baseEnd_1073213 := by
    simpa [prefixWord, tailWord_1073213, baseEnd_1073213] using wordTrace_append hprefix tailTrace_1073213
  have hstable : (prefixWord ++ tailWord_1073213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073213).length < 2 ^ (prefixWord ++ tailWord_1073213).sum := by decide
  have hdescent : baseEnd_1073213 < baseStart_1073213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073217 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_1073217 : Nat := 118140960795 + 1073217 * 2 ^ 59
def prefixEnd_1073217 : Nat := 4983230072969 + 3 ^ 40 * 1073217 * 2
def baseEnd_1073217 : Nat := 551076167576432767251871

theorem tailTrace_1073217 : CollatzResearch.WordTrace tailWord_1073217 prefixEnd_1073217 551076167576432767251871 := by
  unfold tailWord_1073217
  simp only [CollatzResearch.WordTrace]
  refine ⟨39143439752925574716177905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26095626501950383144118603 39143439752925574716177905)
  ·
    refine ⟨29357579814694181037133429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39143439752925574716177905 29357579814694181037133429)
    ·
      refine ⟨2752273107627579472231259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29357579814694181037133429 2752273107627579472231259)
      ·
        refine ⟨4128409661441369208346889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752273107627579472231259 4128409661441369208346889)
        ·
          refine ⟨3096307246081026906260167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4128409661441369208346889 3096307246081026906260167)
          ·
            refine ⟨4644460869121540359390251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096307246081026906260167 4644460869121540359390251)
            ·
              refine ⟨6966691303682310539085377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644460869121540359390251 6966691303682310539085377)
              ·
                refine ⟨5225018477761732904314033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6966691303682310539085377 5225018477761732904314033)
                ·
                  refine ⟨3918763858321299678235525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5225018477761732904314033 3918763858321299678235525)
                  ·
                    refine ⟨734768223435243689669161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918763858321299678235525 734768223435243689669161)
                    ·
                      refine ⟨551076167576432767251871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 734768223435243689669161 551076167576432767251871)
                      ·
                        rfl

theorem cell23_1073217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_1073217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073217 prefixEnd_1073217 := by exact prefixLift 1073217
  have htrace : WordTrace (prefixWord ++ tailWord_1073217) baseStart_1073217 baseEnd_1073217 := by
    simpa [prefixWord, tailWord_1073217, baseEnd_1073217] using wordTrace_append hprefix tailTrace_1073217
  have hstable : (prefixWord ++ tailWord_1073217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073217).length < 2 ^ (prefixWord ++ tailWord_1073217).sum := by decide
  have hdescent : baseEnd_1073217 < baseStart_1073217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073223 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 8]
def baseStart_1073223 : Nat := 118140960795 + 1073223 * 2 ^ 59
def prefixEnd_1073223 : Nat := 4983230072969 + 3 ^ 40 * 1073223 * 2
def baseEnd_1073223 : Nat := 61231027606706638197427

theorem tailTrace_1073223 : CollatzResearch.WordTrace tailWord_1073223 prefixEnd_1073223 61231027606706638197427 := by
  unfold tailWord_1073223
  simp only [CollatzResearch.WordTrace]
  refine ⟨39143658590903837740896323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26095772393935891827264215 39143658590903837740896323)
  ·
    refine ⟨58715487886355756611344485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39143658590903837740896323 58715487886355756611344485)
    ·
      refine ⟨11009153978691704364627091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58715487886355756611344485 11009153978691704364627091)
      ·
        refine ⟨16513730968037556546940637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11009153978691704364627091 16513730968037556546940637)
        ·
          refine ⟨6192649113014083705102739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16513730968037556546940637 6192649113014083705102739)
          ·
            refine ⟨9288973669521125557654109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6192649113014083705102739 9288973669521125557654109)
            ·
              refine ⟨3483365126070422084120291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9288973669521125557654109 3483365126070422084120291)
              ·
                refine ⟨5225047689105633126180437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3483365126070422084120291 5225047689105633126180437)
                ·
                  refine ⟨61231027606706638197427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5225047689105633126180437 61231027606706638197427)
                  ·
                    rfl

theorem cell23_1073223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 8].length) (baseStart_1073223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073223 prefixEnd_1073223 := by exact prefixLift 1073223
  have htrace : WordTrace (prefixWord ++ tailWord_1073223) baseStart_1073223 baseEnd_1073223 := by
    simpa [prefixWord, tailWord_1073223, baseEnd_1073223] using wordTrace_append hprefix tailTrace_1073223
  have hstable : (prefixWord ++ tailWord_1073223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073223).length < 2 ^ (prefixWord ++ tailWord_1073223).sum := by decide
  have hdescent : baseEnd_1073223 < baseStart_1073223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073277 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_1073277 : Nat := 118140960795 + 1073277 * 2 ^ 59
def prefixEnd_1073277 : Nat := 4983230072969 + 3 ^ 40 * 1073277 * 2
def baseEnd_1073277 : Nat := 551106976415702532501595

theorem tailTrace_1073277 : CollatzResearch.WordTrace tailWord_1073277 prefixEnd_1073277 551106976415702532501595 := by
  unfold tailWord_1073277
  simp only [CollatzResearch.WordTrace]
  refine ⟨39145628132708204963362085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26097085421805469975574723 39145628132708204963362085)
  ·
    refine ⟨7339805274882788430630391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39145628132708204963362085 7339805274882788430630391)
    ·
      refine ⟨11009707912324182645945587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7339805274882788430630391 11009707912324182645945587)
      ·
        refine ⟨16514561868486273968918381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11009707912324182645945587 16514561868486273968918381)
        ·
          refine ⟨6192960700682352738344393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16514561868486273968918381 6192960700682352738344393)
          ·
            refine ⟨4644720525511764553758295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6192960700682352738344393 4644720525511764553758295)
            ·
              refine ⟨6967080788267646830637443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644720525511764553758295 6967080788267646830637443)
              ·
                refine ⟨10450621182401470245956165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6967080788267646830637443 10450621182401470245956165)
                ·
                  refine ⟨1959491471700275671116781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10450621182401470245956165 1959491471700275671116781)
                  ·
                    refine ⟨734809301887603376668793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1959491471700275671116781 734809301887603376668793)
                    ·
                      refine ⟨551106976415702532501595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 734809301887603376668793 551106976415702532501595)
                      ·
                        rfl

theorem cell23_1073277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_1073277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073277 prefixEnd_1073277 := by exact prefixLift 1073277
  have htrace : WordTrace (prefixWord ++ tailWord_1073277) baseStart_1073277 baseEnd_1073277 := by
    simpa [prefixWord, tailWord_1073277, baseEnd_1073277] using wordTrace_append hprefix tailTrace_1073277
  have hstable : (prefixWord ++ tailWord_1073277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073277).length < 2 ^ (prefixWord ++ tailWord_1073277).sum := by decide
  have hdescent : baseEnd_1073277 < baseStart_1073277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073304 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 1, 5]
def baseStart_1073304 : Nat := 118140960795 + 1073304 * 2 ^ 59
def prefixEnd_1073304 : Nat := 4983230072969 + 3 ^ 40 * 1073304 * 2
def baseEnd_1073304 : Nat := 183706946797791308954657

theorem tailTrace_1073304 : CollatzResearch.WordTrace tailWord_1073304 prefixEnd_1073304 183706946797791308954657 := by
  unfold tailWord_1073304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19573306451805194287297483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26097741935740259049729977 19573306451805194287297483)
  ·
    refine ⟨29359959677707791430946225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19573306451805194287297483 29359959677707791430946225)
    ·
      refine ⟨22019969758280843573209669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29359959677707791430946225 22019969758280843573209669)
      ·
        refine ⟨4128744329677658169976813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22019969758280843573209669 4128744329677658169976813)
        ·
          refine ⟨1548279123629121813741305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4128744329677658169976813 1548279123629121813741305)
          ·
            refine ⟨1161209342721841360305979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1548279123629121813741305 1161209342721841360305979)
            ·
              refine ⟨1741814014082762040458969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161209342721841360305979 1741814014082762040458969)
              ·
                refine ⟨1306360510562071530344227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741814014082762040458969 1306360510562071530344227)
                ·
                  refine ⟨1959540765843107295516341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306360510562071530344227 1959540765843107295516341)
                  ·
                    refine ⟨183706946797791308954657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1959540765843107295516341 183706946797791308954657)
                    ·
                      rfl

theorem cell23_1073304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_1073304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073304 prefixEnd_1073304 := by exact prefixLift 1073304
  have htrace : WordTrace (prefixWord ++ tailWord_1073304) baseStart_1073304 baseEnd_1073304 := by
    simpa [prefixWord, tailWord_1073304, baseEnd_1073304] using wordTrace_append hprefix tailTrace_1073304
  have hstable : (prefixWord ++ tailWord_1073304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073304).length < 2 ^ (prefixWord ++ tailWord_1073304).sum := by decide
  have hdescent : baseEnd_1073304 < baseStart_1073304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073363 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10]
def baseStart_1073363 : Nat := 118140960795 + 1073363 * 2 ^ 59
def prefixEnd_1073363 : Nat := 4983230072969 + 3 ^ 40 * 1073363 * 2
def baseEnd_1073363 : Nat := 551151135751989196026199

theorem tailTrace_1073363 : CollatzResearch.WordTrace tailWord_1073363 prefixEnd_1073363 551151135751989196026199 := by
  unfold tailWord_1073363
  simp only [CollatzResearch.WordTrace]
  refine ⟨39148764810396641650992743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26099176540264427767328495 39148764810396641650992743)
  ·
    refine ⟨58723147215594962476489115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39148764810396641650992743 58723147215594962476489115)
    ·
      refine ⟨88084720823392443714733673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58723147215594962476489115 88084720823392443714733673)
      ·
        refine ⟨66063540617544332786050255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88084720823392443714733673 66063540617544332786050255)
        ·
          refine ⟨99095310926316499179075383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66063540617544332786050255 99095310926316499179075383)
          ·
            refine ⟨148642966389474748768613075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99095310926316499179075383 148642966389474748768613075)
            ·
              refine ⟨222964449584212123152919613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148642966389474748768613075 222964449584212123152919613)
              ·
                refine ⟨83611668594079546182344855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222964449584212123152919613 83611668594079546182344855)
                ·
                  refine ⟨125417502891119319273517283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83611668594079546182344855 125417502891119319273517283)
                  ·
                    refine ⟨188126254336678978910275925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125417502891119319273517283 188126254336678978910275925)
                    ·
                      refine ⟨551151135751989196026199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 188126254336678978910275925 551151135751989196026199)
                      ·
                        rfl

theorem cell23_1073363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_1073363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073363 prefixEnd_1073363 := by exact prefixLift 1073363
  have htrace : WordTrace (prefixWord ++ tailWord_1073363) baseStart_1073363 baseEnd_1073363 := by
    simpa [prefixWord, tailWord_1073363, baseEnd_1073363] using wordTrace_append hprefix tailTrace_1073363
  have hstable : (prefixWord ++ tailWord_1073363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073363).length < 2 ^ (prefixWord ++ tailWord_1073363).sum := by decide
  have hdescent : baseEnd_1073363 < baseStart_1073363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073391 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 3]
def baseStart_1073391 : Nat := 118140960795 + 1073391 * 2 ^ 59
def prefixEnd_1073391 : Nat := 4983230072969 + 3 ^ 40 * 1073391 * 2
def baseEnd_1073391 : Nat := 551165513210315086476071

theorem tailTrace_1073391 : CollatzResearch.WordTrace tailWord_1073391 prefixEnd_1073391 551165513210315086476071 := by
  unfold tailWord_1073391
  simp only [CollatzResearch.WordTrace]
  refine ⟨39149786054295202433012027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26099857369530134955341351 39149786054295202433012027)
  ·
    refine ⟨58724679081442803649518041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39149786054295202433012027 58724679081442803649518041)
    ·
      refine ⟨44043509311082102737138531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58724679081442803649518041 44043509311082102737138531)
      ·
        refine ⟨66065263966623154105707797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44043509311082102737138531 66065263966623154105707797)
        ·
          refine ⟨3096809248435460348705053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66065263966623154105707797 3096809248435460348705053)
          ·
            refine ⟨1161303468163297630764395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3096809248435460348705053 1161303468163297630764395)
            ·
              refine ⟨1741955202244946446146593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161303468163297630764395 1741955202244946446146593)
              ·
                refine ⟨1306466401683709834609945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741955202244946446146593 1306466401683709834609945)
                ·
                  refine ⟨979849801262782375957459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1306466401683709834609945 979849801262782375957459)
                  ·
                    refine ⟨1469774701894173563936189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 979849801262782375957459 1469774701894173563936189)
                    ·
                      refine ⟨551165513210315086476071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1469774701894173563936189 551165513210315086476071)
                      ·
                        rfl

theorem cell23_1073391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 3].length) (baseStart_1073391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073391 prefixEnd_1073391 := by exact prefixLift 1073391
  have htrace : WordTrace (prefixWord ++ tailWord_1073391) baseStart_1073391 baseEnd_1073391 := by
    simpa [prefixWord, tailWord_1073391, baseEnd_1073391] using wordTrace_append hprefix tailTrace_1073391
  have hstable : (prefixWord ++ tailWord_1073391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073391).length < 2 ^ (prefixWord ++ tailWord_1073391).sum := by decide
  have hdescent : baseEnd_1073391 < baseStart_1073391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073400 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_1073400 : Nat := 118140960795 + 1073400 * 2 ^ 59
def prefixEnd_1073400 : Nat := 4983230072969 + 3 ^ 40 * 1073400 * 2
def baseEnd_1073400 : Nat := 551170134536205551263529

theorem tailTrace_1073400 : CollatzResearch.WordTrace tailWord_1073400 prefixEnd_1073400 551170134536205551263529 := by
  unfold tailWord_1073400
  simp only [CollatzResearch.WordTrace]
  refine ⟨19575057155631298485044827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26100076207508397980059769 19575057155631298485044827)
  ·
    refine ⟨29362585733446947727567241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19575057155631298485044827 29362585733446947727567241)
    ·
      refine ⟨22021939300085210795675431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29362585733446947727567241 22021939300085210795675431)
      ·
        refine ⟨33032908950127816193513147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22021939300085210795675431 33032908950127816193513147)
        ·
          refine ⟨49549363425191724290269721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33032908950127816193513147 49549363425191724290269721)
          ·
            refine ⟨37162022568893793217702291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49549363425191724290269721 37162022568893793217702291)
            ·
              refine ⟨55743033853340689826553437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37162022568893793217702291 55743033853340689826553437)
              ·
                refine ⟨20903637695002758684957539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55743033853340689826553437 20903637695002758684957539)
                ·
                  refine ⟨31355456542504138027436309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20903637695002758684957539 31355456542504138027436309)
                  ·
                    refine ⟨1469787025429881470036077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31355456542504138027436309 1469787025429881470036077)
                    ·
                      refine ⟨551170134536205551263529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1469787025429881470036077 551170134536205551263529)
                      ·
                        rfl

theorem cell23_1073400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_1073400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073400 prefixEnd_1073400 := by exact prefixLift 1073400
  have htrace : WordTrace (prefixWord ++ tailWord_1073400) baseStart_1073400 baseEnd_1073400 := by
    simpa [prefixWord, tailWord_1073400, baseEnd_1073400] using wordTrace_append hprefix tailTrace_1073400
  have hstable : (prefixWord ++ tailWord_1073400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073400).length < 2 ^ (prefixWord ++ tailWord_1073400).sum := by decide
  have hdescent : baseEnd_1073400 < baseStart_1073400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073420 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 7]
def baseStart_1073420 : Nat := 118140960795 + 1073420 * 2 ^ 59
def prefixEnd_1073420 : Nat := 4983230072969 + 3 ^ 40 * 1073420 * 2
def baseEnd_1073420 : Nat := 61242267127699497001493

theorem tailTrace_1073420 : CollatzResearch.WordTrace tailWord_1073420 prefixEnd_1073420 61242267127699497001493 := by
  unfold tailWord_1073420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19575421885595070192908857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26100562514126760257211809 19575421885595070192908857)
  ·
    refine ⟨14681566414196302644681643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19575421885595070192908857 14681566414196302644681643)
    ·
      refine ⟨22022349621294453967022465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14681566414196302644681643 22022349621294453967022465)
      ·
        refine ⟨16516762215970840475266849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22022349621294453967022465 16516762215970840475266849)
        ·
          refine ⟨12387571661978130356450137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16516762215970840475266849 12387571661978130356450137)
          ·
            refine ⟨9290678746483597767337603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12387571661978130356450137 9290678746483597767337603)
            ·
              refine ⟨13936018119725396651006405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9290678746483597767337603 13936018119725396651006405)
              ·
                refine ⟨2613003397448511872063701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13936018119725396651006405 2613003397448511872063701)
                ·
                  refine ⟨61242267127699497001493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2613003397448511872063701 61242267127699497001493)
                  ·
                    rfl

theorem cell23_1073420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_1073420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073420 prefixEnd_1073420 := by exact prefixLift 1073420
  have htrace : WordTrace (prefixWord ++ tailWord_1073420) baseStart_1073420 baseEnd_1073420 := by
    simpa [prefixWord, tailWord_1073420, baseEnd_1073420] using wordTrace_append hprefix tailTrace_1073420
  have hstable : (prefixWord ++ tailWord_1073420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073420).length < 2 ^ (prefixWord ++ tailWord_1073420).sum := by decide
  have hdescent : baseEnd_1073420 < baseStart_1073420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073465 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1073465 : Nat := 118140960795 + 1073465 * 2 ^ 59
def prefixEnd_1073465 : Nat := 4983230072969 + 3 ^ 40 * 1073465 * 2
def baseEnd_1073465 : Nat := 551203510778747796950731

theorem tailTrace_1073465 : CollatzResearch.WordTrace tailWord_1073465 prefixEnd_1073465 551203510778747796950731 := by
  unfold tailWord_1073465
  simp only [CollatzResearch.WordTrace]
  refine ⟨39152485056027113071205849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26101656704018075380803899 39152485056027113071205849)
  ·
    refine ⟨29364363792020334803404387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39152485056027113071205849 29364363792020334803404387)
    ·
      refine ⟨44046545688030502205106581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29364363792020334803404387 44046545688030502205106581)
      ·
        refine ⟨2064681829126429790864371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44046545688030502205106581 2064681829126429790864371)
        ·
          refine ⟨3097022743689644686296557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064681829126429790864371 3097022743689644686296557)
          ·
            refine ⟨1161383528883616757361209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3097022743689644686296557 1161383528883616757361209)
            ·
              refine ⟨871037646662712568020907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161383528883616757361209 871037646662712568020907)
              ·
                refine ⟨1306556469994068852031361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871037646662712568020907 1306556469994068852031361)
                ·
                  refine ⟨979917352495551639023521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1306556469994068852031361 979917352495551639023521)
                  ·
                    refine ⟨734938014371663729267641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 979917352495551639023521 734938014371663729267641)
                    ·
                      refine ⟨551203510778747796950731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 734938014371663729267641 551203510778747796950731)
                      ·
                        rfl

theorem cell23_1073465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1073465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073465 prefixEnd_1073465 := by exact prefixLift 1073465
  have htrace : WordTrace (prefixWord ++ tailWord_1073465) baseStart_1073465 baseEnd_1073465 := by
    simpa [prefixWord, tailWord_1073465, baseEnd_1073465] using wordTrace_append hprefix tailTrace_1073465
  have hstable : (prefixWord ++ tailWord_1073465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073465).length < 2 ^ (prefixWord ++ tailWord_1073465).sum := by decide
  have hdescent : baseEnd_1073465 < baseStart_1073465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073480 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1073480 : Nat := 118140960795 + 1073480 * 2 ^ 59
def prefixEnd_1073480 : Nat := 4983230072969 + 3 ^ 40 * 1073480 * 2
def baseEnd_1073480 : Nat := 183737070996188412754387

theorem tailTrace_1073480 : CollatzResearch.WordTrace tailWord_1073480 prefixEnd_1073480 183737070996188412754387 := by
  unfold tailWord_1073480
  simp only [CollatzResearch.WordTrace]
  refine ⟨19576516075486385316500947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26102021433981847088667929 19576516075486385316500947)
  ·
    refine ⟨29364774113229577974751421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19576516075486385316500947 29364774113229577974751421)
    ·
      refine ⟨11011790292461091740531783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29364774113229577974751421 11011790292461091740531783)
      ·
        refine ⟨16517685438691637610797675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11011790292461091740531783 16517685438691637610797675)
        ·
          refine ⟨24776528158037456416196513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16517685438691637610797675 24776528158037456416196513)
          ·
            refine ⟨18582396118528092312147385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24776528158037456416196513 18582396118528092312147385)
            ·
              refine ⟨13936797088896069234110539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18582396118528092312147385 13936797088896069234110539)
              ·
                refine ⟨20905195633344103851165809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13936797088896069234110539 20905195633344103851165809)
                ·
                  refine ⟨15678896725008077888374357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20905195633344103851165809 15678896725008077888374357)
                  ·
                    refine ⟨183737070996188412754387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15678896725008077888374357 183737070996188412754387)
                    ·
                      rfl

theorem cell23_1073480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1073480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073480 prefixEnd_1073480 := by exact prefixLift 1073480
  have htrace : WordTrace (prefixWord ++ tailWord_1073480) baseStart_1073480 baseEnd_1073480 := by
    simpa [prefixWord, tailWord_1073480, baseEnd_1073480] using wordTrace_append hprefix tailTrace_1073480
  have hstable : (prefixWord ++ tailWord_1073480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073480).length < 2 ^ (prefixWord ++ tailWord_1073480).sum := by decide
  have hdescent : baseEnd_1073480 < baseStart_1073480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073487 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 3, 6, 2]
def baseStart_1073487 : Nat := 118140960795 + 1073487 * 2 ^ 59
def prefixEnd_1073487 : Nat := 4983230072969 + 3 ^ 40 * 1073487 * 2
def baseEnd_1073487 : Nat := 551214807353146710875629

theorem tailTrace_1073487 : CollatzResearch.WordTrace tailWord_1073487 prefixEnd_1073487 551214807353146710875629 := by
  unfold tailWord_1073487
  simp only [CollatzResearch.WordTrace]
  refine ⟨39153287461947410828506715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26102191641298273885671143 39153287461947410828506715)
  ·
    refine ⟨58729931192921116242760073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39153287461947410828506715 58729931192921116242760073)
    ·
      refine ⟨44047448394690837182070055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58729931192921116242760073 44047448394690837182070055)
      ·
        refine ⟨66071172592036255773105083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44047448394690837182070055 66071172592036255773105083)
        ·
          refine ⟨99106758888054383659657625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66071172592036255773105083 99106758888054383659657625)
          ·
            refine ⟨74330069166040787744743219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99106758888054383659657625 74330069166040787744743219)
            ·
              refine ⟨111495103749061181617114829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74330069166040787744743219 111495103749061181617114829)
              ·
                refine ⟨41810663905897943106418061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111495103749061181617114829 41810663905897943106418061)
                ·
                  refine ⟨15678998964711728664906773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41810663905897943106418061 15678998964711728664906773)
                  ·
                    refine ⟨734953076470862281167505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15678998964711728664906773 734953076470862281167505)
                    ·
                      refine ⟨551214807353146710875629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 734953076470862281167505 551214807353146710875629)
                      ·
                        rfl

theorem cell23_1073487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6, 2].length) (baseStart_1073487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073487 prefixEnd_1073487 := by exact prefixLift 1073487
  have htrace : WordTrace (prefixWord ++ tailWord_1073487) baseStart_1073487 baseEnd_1073487 := by
    simpa [prefixWord, tailWord_1073487, baseEnd_1073487] using wordTrace_append hprefix tailTrace_1073487
  have hstable : (prefixWord ++ tailWord_1073487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073487).length < 2 ^ (prefixWord ++ tailWord_1073487).sum := by decide
  have hdescent : baseEnd_1073487 < baseStart_1073487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073571 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 3]
def baseStart_1073571 : Nat := 118140960795 + 1073571 * 2 ^ 59
def prefixEnd_1073571 : Nat := 4983230072969 + 3 ^ 40 * 1073571 * 2
def baseEnd_1073571 : Nat := 551257939728124382225243

theorem tailTrace_1073571 : CollatzResearch.WordTrace tailWord_1073571 prefixEnd_1073571 551257939728124382225243 := by
  unfold tailWord_1073571
  simp only [CollatzResearch.WordTrace]
  refine ⟨39156351193643093174564567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26104234129095395449709711 39156351193643093174564567)
  ·
    refine ⟨58734526790464639761846851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39156351193643093174564567 58734526790464639761846851)
    ·
      refine ⟨88101790185696959642770277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58734526790464639761846851 88101790185696959642770277)
      ·
        refine ⟨16519085659818179933019427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88101790185696959642770277 16519085659818179933019427)
        ·
          refine ⟨24778628489727269899529141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16519085659818179933019427 24778628489727269899529141)
          ·
            refine ⟨2322996420911931553080857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24778628489727269899529141 2322996420911931553080857)
            ·
              refine ⟨1742247315683948664810643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2322996420911931553080857 1742247315683948664810643)
              ·
                refine ⟨2613370973525922997215965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742247315683948664810643 2613370973525922997215965)
                ·
                  refine ⟨980014115072221123955987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2613370973525922997215965 980014115072221123955987)
                  ·
                    refine ⟨1470021172608331685933981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 980014115072221123955987 1470021172608331685933981)
                    ·
                      refine ⟨551257939728124382225243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470021172608331685933981 551257939728124382225243)
                      ·
                        rfl

theorem cell23_1073571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_1073571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073571 prefixEnd_1073571 := by exact prefixLift 1073571
  have htrace : WordTrace (prefixWord ++ tailWord_1073571) baseStart_1073571 baseEnd_1073571 := by
    simpa [prefixWord, tailWord_1073571, baseEnd_1073571] using wordTrace_append hprefix tailTrace_1073571
  have hstable : (prefixWord ++ tailWord_1073571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073571).length < 2 ^ (prefixWord ++ tailWord_1073571).sum := by decide
  have hdescent : baseEnd_1073571 < baseStart_1073571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073577 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_1073577 : Nat := 118140960795 + 1073577 * 2 ^ 59
def prefixEnd_1073577 : Nat := 4983230072969 + 3 ^ 40 * 1073577 * 2
def baseEnd_1073577 : Nat := 551261020612051358750215

theorem tailTrace_1073577 : CollatzResearch.WordTrace tailWord_1073577 prefixEnd_1073577 551261020612051358750215 := by
  unfold tailWord_1073577
  simp only [CollatzResearch.WordTrace]
  refine ⟨39156570031621356199282985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26104380021080904132855323 39156570031621356199282985)
  ·
    refine ⟨29367427523716017149462239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39156570031621356199282985 29367427523716017149462239)
    ·
      refine ⟨44051141285574025724193359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29367427523716017149462239 44051141285574025724193359)
      ·
        refine ⟨66076711928361038586290039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44051141285574025724193359 66076711928361038586290039)
        ·
          refine ⟨99115067892541557879435059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66076711928361038586290039 99115067892541557879435059)
          ·
            refine ⟨148672601838812336819152589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99115067892541557879435059 148672601838812336819152589)
            ·
              refine ⟨55752225689554626307182221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148672601838812336819152589 55752225689554626307182221)
              ·
                refine ⟨20907084633582984865193333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55752225689554626307182221 20907084633582984865193333)
                ·
                  refine ⟨1960039184398404831111875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20907084633582984865193333 1960039184398404831111875)
                  ·
                    refine ⟨2940058776597607246667813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960039184398404831111875 2940058776597607246667813)
                    ·
                      refine ⟨551261020612051358750215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2940058776597607246667813 551261020612051358750215)
                      ·
                        rfl

theorem cell23_1073577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_1073577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073577 prefixEnd_1073577 := by exact prefixLift 1073577
  have htrace : WordTrace (prefixWord ++ tailWord_1073577) baseStart_1073577 baseEnd_1073577 := by
    simpa [prefixWord, tailWord_1073577, baseEnd_1073577] using wordTrace_append hprefix tailTrace_1073577
  have hstable : (prefixWord ++ tailWord_1073577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073577).length < 2 ^ (prefixWord ++ tailWord_1073577).sum := by decide
  have hdescent : baseEnd_1073577 < baseStart_1073577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073614 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_1073614 : Nat := 118140960795 + 1073614 * 2 ^ 59
def prefixEnd_1073614 : Nat := 4983230072969 + 3 ^ 40 * 1073614 * 2
def baseEnd_1073614 : Nat := 551280019396267713987545

theorem tailTrace_1073614 : CollatzResearch.WordTrace tailWord_1073614 prefixEnd_1073614 551280019396267713987545 := by
  unfold tailWord_1073614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894739941560913939797487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26105279688324874345586597 4894739941560913939797487)
  ·
    refine ⟨7342109912341370909696231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4894739941560913939797487 7342109912341370909696231)
    ·
      refine ⟨11013164868512056364544347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7342109912341370909696231 11013164868512056364544347)
      ·
        refine ⟨16519747302768084546816521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11013164868512056364544347 16519747302768084546816521)
        ·
          refine ⟨12389810477076063410112391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16519747302768084546816521 12389810477076063410112391)
          ·
            refine ⟨18584715715614095115168587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12389810477076063410112391 18584715715614095115168587)
            ·
              refine ⟨27877073573421142672752881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18584715715614095115168587 27877073573421142672752881)
              ·
                refine ⟨20907805180065857004564661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27877073573421142672752881 20907805180065857004564661)
                ·
                  refine ⟨1960106735631174094177937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20907805180065857004564661 1960106735631174094177937)
                  ·
                    refine ⟨1470080051723380570633453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1960106735631174094177937 1470080051723380570633453)
                    ·
                      refine ⟨551280019396267713987545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470080051723380570633453 551280019396267713987545)
                      ·
                        rfl

theorem cell23_1073614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_1073614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073614 prefixEnd_1073614 := by exact prefixLift 1073614
  have htrace : WordTrace (prefixWord ++ tailWord_1073614) baseStart_1073614 baseEnd_1073614 := by
    simpa [prefixWord, tailWord_1073614, baseEnd_1073614] using wordTrace_append hprefix tailTrace_1073614
  have hstable : (prefixWord ++ tailWord_1073614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073614).length < 2 ^ (prefixWord ++ tailWord_1073614).sum := by decide
  have hdescent : baseEnd_1073614 < baseStart_1073614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073622 : List Nat := [5, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_1073622 : Nat := 118140960795 + 1073622 * 2 ^ 59
def prefixEnd_1073622 : Nat := 4983230072969 + 3 ^ 40 * 1073622 * 2
def baseEnd_1073622 : Nat := 551284127241503682687509

theorem tailTrace_1073622 : CollatzResearch.WordTrace tailWord_1073622 prefixEnd_1073622 551284127241503682687509 := by
  unfold tailWord_1073622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447388207278645555291945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26105474210972219256447413 2447388207278645555291945)
  ·
    refine ⟨1835541155458984166468959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2447388207278645555291945 1835541155458984166468959)
    ·
      refine ⟨2753311733188476249703439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835541155458984166468959 2753311733188476249703439)
      ·
        refine ⟨4129967599782714374555159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753311733188476249703439 4129967599782714374555159)
        ·
          refine ⟨6194951399674071561832739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129967599782714374555159 6194951399674071561832739)
          ·
            refine ⟨9292427099511107342749109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194951399674071561832739 9292427099511107342749109)
            ·
              refine ⟨871165040579166313382729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9292427099511107342749109 871165040579166313382729)
              ·
                refine ⟨653373780434374735037047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871165040579166313382729 653373780434374735037047)
                ·
                  refine ⟨980060670651562102555571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653373780434374735037047 980060670651562102555571)
                  ·
                    refine ⟨1470091005977343153833357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 980060670651562102555571 1470091005977343153833357)
                    ·
                      refine ⟨551284127241503682687509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470091005977343153833357 551284127241503682687509)
                      ·
                        rfl

theorem cell23_1073622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_1073622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073622 prefixEnd_1073622 := by exact prefixLift 1073622
  have htrace : WordTrace (prefixWord ++ tailWord_1073622) baseStart_1073622 baseEnd_1073622 := by
    simpa [prefixWord, tailWord_1073622, baseEnd_1073622] using wordTrace_append hprefix tailTrace_1073622
  have hstable : (prefixWord ++ tailWord_1073622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073622).length < 2 ^ (prefixWord ++ tailWord_1073622).sum := by decide
  have hdescent : baseEnd_1073622 < baseStart_1073622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073644 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_1073644 : Nat := 118140960795 + 1073644 * 2 ^ 59
def prefixEnd_1073644 : Nat := 4983230072969 + 3 ^ 40 * 1073644 * 2
def baseEnd_1073644 : Nat := 551295423815902596612407

theorem tailTrace_1073644 : CollatzResearch.WordTrace tailWord_1073644 prefixEnd_1073644 551295423815902596612407 := by
  unfold tailWord_1073644
  simp only [CollatzResearch.WordTrace]
  refine ⟨19579506861189313320985993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26106009148252417761314657 19579506861189313320985993)
  ·
    refine ⟨14684630145891984990739495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19579506861189313320985993 14684630145891984990739495)
    ·
      refine ⟨22026945218837977486109243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14684630145891984990739495 22026945218837977486109243)
      ·
        refine ⟨33040417828256966229163865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22026945218837977486109243 33040417828256966229163865)
        ·
          refine ⟨24780313371192724671872899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33040417828256966229163865 24780313371192724671872899)
          ·
            refine ⟨37170470056789087007809349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24780313371192724671872899 37170470056789087007809349)
            ·
              refine ⟨6969463135647953813964253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37170470056789087007809349 6969463135647953813964253)
              ·
                refine ⟨2613548675867982680236595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6969463135647953813964253 2613548675867982680236595)
                ·
                  refine ⟨3920323013801974020354893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613548675867982680236595 3920323013801974020354893)
                  ·
                    refine ⟨1470121130175740257633085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3920323013801974020354893 1470121130175740257633085)
                    ·
                      refine ⟨551295423815902596612407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470121130175740257633085 551295423815902596612407)
                      ·
                        rfl

theorem cell23_1073644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_1073644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073644 prefixEnd_1073644 := by exact prefixLift 1073644
  have htrace : WordTrace (prefixWord ++ tailWord_1073644) baseStart_1073644 baseEnd_1073644 := by
    simpa [prefixWord, tailWord_1073644, baseEnd_1073644] using wordTrace_append hprefix tailTrace_1073644
  have hstable : (prefixWord ++ tailWord_1073644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073644).length < 2 ^ (prefixWord ++ tailWord_1073644).sum := by decide
  have hdescent : baseEnd_1073644 < baseStart_1073644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073657 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_1073657 : Nat := 118140960795 + 1073657 * 2 ^ 59
def prefixEnd_1073657 : Nat := 4983230072969 + 3 ^ 40 * 1073657 * 2
def baseEnd_1073657 : Nat := 551302099064411045749847

theorem tailTrace_1073657 : CollatzResearch.WordTrace tailWord_1073657 prefixEnd_1073657 551302099064411045749847 := by
  unfold tailWord_1073657
  simp only [CollatzResearch.WordTrace]
  refine ⟨39159487871331529862195225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26106325247554353241463483 39159487871331529862195225)
  ·
    refine ⟨29369615903498647396646419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39159487871331529862195225 29369615903498647396646419)
    ·
      refine ⟨44054423855247971094969629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29369615903498647396646419 44054423855247971094969629)
      ·
        refine ⟨16520408945717989160613611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44054423855247971094969629 16520408945717989160613611)
        ·
          refine ⟨24780613418576983740920417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16520408945717989160613611 24780613418576983740920417)
          ·
            refine ⟨18585460063932737805690313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24780613418576983740920417 18585460063932737805690313)
            ·
              refine ⟨13939095047949553354267735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18585460063932737805690313 13939095047949553354267735)
              ·
                refine ⟨20908642571924330031401603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13939095047949553354267735 20908642571924330031401603)
                ·
                  refine ⟨31362963857886495047102405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20908642571924330031401603 31362963857886495047102405)
                  ·
                    refine ⟨5880555723353717821331701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31362963857886495047102405 5880555723353717821331701)
                    ·
                      refine ⟨551302099064411045749847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5880555723353717821331701 551302099064411045749847)
                      ·
                        rfl

theorem cell23_1073657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1073657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073657 prefixEnd_1073657 := by exact prefixLift 1073657
  have htrace : WordTrace (prefixWord ++ tailWord_1073657) baseStart_1073657 baseEnd_1073657 := by
    simpa [prefixWord, tailWord_1073657, baseEnd_1073657] using wordTrace_append hprefix tailTrace_1073657
  have hstable : (prefixWord ++ tailWord_1073657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073657).length < 2 ^ (prefixWord ++ tailWord_1073657).sum := by decide
  have hdescent : baseEnd_1073657 < baseStart_1073657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073678 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_1073678 : Nat := 118140960795 + 1073678 * 2 ^ 59
def prefixEnd_1073678 : Nat := 4983230072969 + 3 ^ 40 * 1073678 * 2
def baseEnd_1073678 : Nat := 551312882158155463587251

theorem tailTrace_1073678 : CollatzResearch.WordTrace tailWord_1073678 prefixEnd_1073678 551312882158155463587251 := by
  unfold tailWord_1073678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895031725531931306088711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26106835869503633632473125 4895031725531931306088711)
  ·
    refine ⟨7342547588297896959133067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4895031725531931306088711 7342547588297896959133067)
    ·
      refine ⟨11013821382446845438699601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7342547588297896959133067 11013821382446845438699601)
      ·
        refine ⟨8260366036835134079024701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11013821382446845438699601 8260366036835134079024701)
        ·
          refine ⟨3097637263813175279634263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8260366036835134079024701 3097637263813175279634263)
          ·
            refine ⟨4646455895719762919451395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097637263813175279634263 4646455895719762919451395)
            ·
              refine ⟨6969683843579644379177093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4646455895719762919451395 6969683843579644379177093)
              ·
                refine ⟨1306815720671183321095705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6969683843579644379177093 1306815720671183321095705)
                ·
                  refine ⟨980111790503387490821779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1306815720671183321095705 980111790503387490821779)
                  ·
                    refine ⟨1470167685755081236232669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 980111790503387490821779 1470167685755081236232669)
                    ·
                      refine ⟨551312882158155463587251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470167685755081236232669 551312882158155463587251)
                      ·
                        rfl

theorem cell23_1073678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_1073678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073678 prefixEnd_1073678 := by exact prefixLift 1073678
  have htrace : WordTrace (prefixWord ++ tailWord_1073678) baseStart_1073678 baseEnd_1073678 := by
    simpa [prefixWord, tailWord_1073678, baseEnd_1073678] using wordTrace_append hprefix tailTrace_1073678
  have hstable : (prefixWord ++ tailWord_1073678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073678).length < 2 ^ (prefixWord ++ tailWord_1073678).sum := by decide
  have hdescent : baseEnd_1073678 < baseStart_1073678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073701 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 1, 4, 2]
def baseStart_1073701 : Nat := 118140960795 + 1073701 * 2 ^ 59
def prefixEnd_1073701 : Nat := 4983230072969 + 3 ^ 40 * 1073701 * 2
def baseEnd_1073701 : Nat := 551324692213208873599645

theorem tailTrace_1073701 : CollatzResearch.WordTrace tailWord_1073701 prefixEnd_1073701 551324692213208873599645 := by
  unfold tailWord_1073701
  simp only [CollatzResearch.WordTrace]
  refine ⟨39161092683172125376796957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26107395122114750251197971 39161092683172125376796957)
  ·
    refine ⟨14685409756189547016298859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39161092683172125376796957 14685409756189547016298859)
    ·
      refine ⟨22028114634284320524448289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14685409756189547016298859 22028114634284320524448289)
      ·
        refine ⟨16521085975713240393336217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22028114634284320524448289 16521085975713240393336217)
        ·
          refine ⟨12390814481784930295002163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16521085975713240393336217 12390814481784930295002163)
          ·
            refine ⟨18586221722677395442503245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12390814481784930295002163 18586221722677395442503245)
            ·
              refine ⟨6969833146004023290938717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18586221722677395442503245 6969833146004023290938717)
              ·
                refine ⟨2613687429751508734102019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6969833146004023290938717 2613687429751508734102019)
                ·
                  refine ⟨3920531144627263101153029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613687429751508734102019 3920531144627263101153029)
                  ·
                    refine ⟨735099589617611831466193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920531144627263101153029 735099589617611831466193)
                    ·
                      refine ⟨551324692213208873599645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735099589617611831466193 551324692213208873599645)
                      ·
                        rfl

theorem cell23_1073701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_1073701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073701 prefixEnd_1073701 := by exact prefixLift 1073701
  have htrace : WordTrace (prefixWord ++ tailWord_1073701) baseStart_1073701 baseEnd_1073701 := by
    simpa [prefixWord, tailWord_1073701, baseEnd_1073701] using wordTrace_append hprefix tailTrace_1073701
  have hstable : (prefixWord ++ tailWord_1073701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073701).length < 2 ^ (prefixWord ++ tailWord_1073701).sum := by decide
  have hdescent : baseEnd_1073701 < baseStart_1073701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073735 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_1073735 : Nat := 118140960795 + 1073735 * 2 ^ 59
def prefixEnd_1073735 : Nat := 4983230072969 + 3 ^ 40 * 1073735 * 2
def baseEnd_1073735 : Nat := 551342150555461740574489

theorem tailTrace_1073735 : CollatzResearch.WordTrace tailWord_1073735 prefixEnd_1073735 551342150555461740574489 := by
  unfold tailWord_1073735
  simp only [CollatzResearch.WordTrace]
  refine ⟨39162332765048949183534659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26108221843365966122356439 39162332765048949183534659)
  ·
    refine ⟨58743499147573423775301989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39162332765048949183534659 58743499147573423775301989)
    ·
      refine ⟨11014406090170016957869123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58743499147573423775301989 11014406090170016957869123)
      ·
        refine ⟨16521609135255025436803685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11014406090170016957869123 16521609135255025436803685)
        ·
          refine ⟨3097801712860317269400691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16521609135255025436803685 3097801712860317269400691)
          ·
            refine ⟨4646702569290475904101037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097801712860317269400691 4646702569290475904101037)
            ·
              refine ⟨1742513463483928464037889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4646702569290475904101037 1742513463483928464037889)
              ·
                refine ⟨1306885097612946348028417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742513463483928464037889 1306885097612946348028417)
                ·
                  refine ⟨980163823209709761021313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1306885097612946348028417 980163823209709761021313)
                  ·
                    refine ⟨735122867407282320765985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 980163823209709761021313 735122867407282320765985)
                    ·
                      refine ⟨551342150555461740574489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735122867407282320765985 551342150555461740574489)
                      ·
                        rfl

theorem cell23_1073735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_1073735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073735 prefixEnd_1073735 := by exact prefixLift 1073735
  have htrace : WordTrace (prefixWord ++ tailWord_1073735) baseStart_1073735 baseEnd_1073735 := by
    simpa [prefixWord, tailWord_1073735, baseEnd_1073735] using wordTrace_append hprefix tailTrace_1073735
  have hstable : (prefixWord ++ tailWord_1073735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073735).length < 2 ^ (prefixWord ++ tailWord_1073735).sum := by decide
  have hdescent : baseEnd_1073735 < baseStart_1073735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073741 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1073741 : Nat := 118140960795 + 1073741 * 2 ^ 59
def prefixEnd_1073741 : Nat := 4983230072969 + 3 ^ 40 * 1073741 * 2
def baseEnd_1073741 : Nat := 61260581271043190788829

theorem tailTrace_1073741 : CollatzResearch.WordTrace tailWord_1073741 prefixEnd_1073741 61260581271043190788829 := by
  unfold tailWord_1073741
  simp only [CollatzResearch.WordTrace]
  refine ⟨39162551603027212208253077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26108367735351474805502051 39162551603027212208253077)
  ·
    refine ⟨1835744606391900572261863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39162551603027212208253077 1835744606391900572261863)
    ·
      refine ⟨2753616909587850858392795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835744606391900572261863 2753616909587850858392795)
      ·
        refine ⟨4130425364381776287589193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753616909587850858392795 4130425364381776287589193)
        ·
          refine ⟨3097819023286332215691895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4130425364381776287589193 3097819023286332215691895)
          ·
            refine ⟨4646728534929498323537843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097819023286332215691895 4646728534929498323537843)
            ·
              refine ⟨6970092802394247485306765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4646728534929498323537843 6970092802394247485306765)
              ·
                refine ⟨2613784800897842806990037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6970092802394247485306765 2613784800897842806990037)
                ·
                  refine ⟨61260581271043190788829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2613784800897842806990037 61260581271043190788829)
                  ·
                    rfl

theorem cell23_1073741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1073741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073741 prefixEnd_1073741 := by exact prefixLift 1073741
  have htrace : WordTrace (prefixWord ++ tailWord_1073741) baseStart_1073741 baseEnd_1073741 := by
    simpa [prefixWord, tailWord_1073741, baseEnd_1073741] using wordTrace_append hprefix tailTrace_1073741
  have hstable : (prefixWord ++ tailWord_1073741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073741).length < 2 ^ (prefixWord ++ tailWord_1073741).sum := by decide
  have hdescent : baseEnd_1073741 < baseStart_1073741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073791 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 2, 4, 2]
def baseStart_1073791 : Nat := 118140960795 + 1073791 * 2 ^ 59
def prefixEnd_1073791 : Nat := 4983230072969 + 3 ^ 40 * 1073791 * 2
def baseEnd_1073791 : Nat := 551370905472113521474231

theorem tailTrace_1073791 : CollatzResearch.WordTrace tailWord_1073791 prefixEnd_1073791 551370905472113521474231 := by
  unfold tailWord_1073791
  simp only [CollatzResearch.WordTrace]
  refine ⟨39164375252846070747573227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26109583501897380498382151 39164375252846070747573227)
  ·
    refine ⟨58746562879269106121359841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39164375252846070747573227 58746562879269106121359841)
    ·
      refine ⟨44059922159451829591019881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58746562879269106121359841 44059922159451829591019881)
      ·
        refine ⟨33044941619588872193264911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44059922159451829591019881 33044941619588872193264911)
        ·
          refine ⟨49567412429383308289897367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33044941619588872193264911 49567412429383308289897367)
          ·
            refine ⟨74351118644074962434846051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49567412429383308289897367 74351118644074962434846051)
            ·
              refine ⟨111526677966112443652269077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74351118644074962434846051 111526677966112443652269077)
              ·
                refine ⟨5227813029661520796200113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111526677966112443652269077 5227813029661520796200113)
                ·
                  refine ⟨3920859772246140597150085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5227813029661520796200113 3920859772246140597150085)
                  ·
                    refine ⟨735161207296151361965641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920859772246140597150085 735161207296151361965641)
                    ·
                      refine ⟨551370905472113521474231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735161207296151361965641 551370905472113521474231)
                      ·
                        rfl

theorem cell23_1073791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_1073791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073791 prefixEnd_1073791 := by exact prefixLift 1073791
  have htrace : WordTrace (prefixWord ++ tailWord_1073791) baseStart_1073791 baseEnd_1073791 := by
    simpa [prefixWord, tailWord_1073791, baseEnd_1073791] using wordTrace_append hprefix tailTrace_1073791
  have hstable : (prefixWord ++ tailWord_1073791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073791).length < 2 ^ (prefixWord ++ tailWord_1073791).sum := by decide
  have hdescent : baseEnd_1073791 < baseStart_1073791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073804 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1073804 : Nat := 118140960795 + 1073804 * 2 ^ 59
def prefixEnd_1073804 : Nat := 4983230072969 + 3 ^ 40 * 1073804 * 2
def baseEnd_1073804 : Nat := 551377580720621970611671

theorem tailTrace_1073804 : CollatzResearch.WordTrace tailWord_1073804 prefixEnd_1073804 551377580720621970611671 := by
  unfold tailWord_1073804
  simp only [CollatzResearch.WordTrace]
  refine ⟨19582424700899486983898233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26109899601199315978530977 19582424700899486983898233)
  ·
    refine ⟨14686818525674615237923675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19582424700899486983898233 14686818525674615237923675)
    ·
      refine ⟨22030227788511922856885513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14686818525674615237923675 22030227788511922856885513)
      ·
        refine ⟨16522670841383942142664135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22030227788511922856885513 16522670841383942142664135)
        ·
          refine ⟨24784006262075913213996203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16522670841383942142664135 24784006262075913213996203)
          ·
            refine ⟨37176009393113869820994305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24784006262075913213996203 37176009393113869820994305)
            ·
              refine ⟨27882007044835402365745729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37176009393113869820994305 27882007044835402365745729)
              ·
                refine ⟨20911505283626551774309297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27882007044835402365745729 20911505283626551774309297)
                ·
                  refine ⟨15683628962719913830731973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20911505283626551774309297 15683628962719913830731973)
                  ·
                    refine ⟨2940680430509983843262245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15683628962719913830731973 2940680430509983843262245)
                    ·
                      refine ⟨551377580720621970611671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2940680430509983843262245 551377580720621970611671)
                      ·
                        rfl

theorem cell23_1073804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1073804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073804 prefixEnd_1073804 := by exact prefixLift 1073804
  have htrace : WordTrace (prefixWord ++ tailWord_1073804) baseStart_1073804 baseEnd_1073804 := by
    simpa [prefixWord, tailWord_1073804, baseEnd_1073804] using wordTrace_append hprefix tailTrace_1073804
  have hstable : (prefixWord ++ tailWord_1073804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073804).length < 2 ^ (prefixWord ++ tailWord_1073804).sum := by decide
  have hdescent : baseEnd_1073804 < baseStart_1073804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073828 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1073828 : Nat := 118140960795 + 1073828 * 2 ^ 59
def prefixEnd_1073828 : Nat := 4983230072969 + 3 ^ 40 * 1073828 * 2
def baseEnd_1073828 : Nat := 551389904256329876711561

theorem tailTrace_1073828 : CollatzResearch.WordTrace tailWord_1073828 prefixEnd_1073828 551389904256329876711561 := by
  unfold tailWord_1073828
  simp only [CollatzResearch.WordTrace]
  refine ⟨19582862376856013033335069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26110483169141350711113425 19582862376856013033335069)
  ·
    refine ⟨7343573391321004887500651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19582862376856013033335069 7343573391321004887500651)
    ·
      refine ⟨11015360086981507331250977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7343573391321004887500651 11015360086981507331250977)
      ·
        refine ⟨8261520065236130498438233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11015360086981507331250977 8261520065236130498438233)
        ·
          refine ⟨6196140048927097873828675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8261520065236130498438233 6196140048927097873828675)
          ·
            refine ⟨9294210073390646810743013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6196140048927097873828675 9294210073390646810743013)
            ·
              refine ⟨1742664388760746277014315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9294210073390646810743013 1742664388760746277014315)
              ·
                refine ⟨2613996583141119415521473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742664388760746277014315 2613996583141119415521473)
                ·
                  refine ⟨1960497437355839561641105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2613996583141119415521473 1960497437355839561641105)
                  ·
                    refine ⟨1470373078016879671230829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1960497437355839561641105 1470373078016879671230829)
                    ·
                      refine ⟨551389904256329876711561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470373078016879671230829 551389904256329876711561)
                      ·
                        rfl

theorem cell23_1073828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1073828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073828 prefixEnd_1073828 := by exact prefixLift 1073828
  have htrace : WordTrace (prefixWord ++ tailWord_1073828) baseStart_1073828 baseEnd_1073828 := by
    simpa [prefixWord, tailWord_1073828, baseEnd_1073828] using wordTrace_append hprefix tailTrace_1073828
  have hstable : (prefixWord ++ tailWord_1073828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073828).length < 2 ^ (prefixWord ++ tailWord_1073828).sum := by decide
  have hdescent : baseEnd_1073828 < baseStart_1073828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073851 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 5, 5, 2]
def baseStart_1073851 : Nat := 118140960795 + 1073851 * 2 ^ 59
def prefixEnd_1073851 : Nat := 4983230072969 + 3 ^ 40 * 1073851 * 2
def baseEnd_1073851 : Nat := 551401714311383286723955

theorem tailTrace_1073851 : CollatzResearch.WordTrace tailWord_1073851 prefixEnd_1073851 551401714311383286723955 := by
  unfold tailWord_1073851
  simp only [CollatzResearch.WordTrace]
  refine ⟨39166563632628700994757407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26111042421752467329838271 39166563632628700994757407)
  ·
    refine ⟨58749845448943051492136111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39166563632628700994757407 58749845448943051492136111)
    ·
      refine ⟨88124768173414577238204167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58749845448943051492136111 88124768173414577238204167)
      ·
        refine ⟨132187152260121865857306251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88124768173414577238204167 132187152260121865857306251)
        ·
          refine ⟨198280728390182798785959377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132187152260121865857306251 198280728390182798785959377)
          ·
            refine ⟨148710546292637099089469533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198280728390182798785959377 148710546292637099089469533)
            ·
              refine ⟨55766454859738912158551075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148710546292637099089469533 55766454859738912158551075)
              ·
                refine ⟨83649682289608368237826613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55766454859738912158551075 83649682289608368237826613)
                ·
                  refine ⟨7842157714650784522296245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83649682289608368237826613 7842157714650784522296245)
                  ·
                    refine ⟨735202285748511048965273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7842157714650784522296245 735202285748511048965273)
                    ·
                      refine ⟨551401714311383286723955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735202285748511048965273 551401714311383286723955)
                      ·
                        rfl

theorem cell23_1073851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5, 2].length) (baseStart_1073851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073851 prefixEnd_1073851 := by exact prefixLift 1073851
  have htrace : WordTrace (prefixWord ++ tailWord_1073851) baseStart_1073851 baseEnd_1073851 := by
    simpa [prefixWord, tailWord_1073851, baseEnd_1073851] using wordTrace_append hprefix tailTrace_1073851
  have hstable : (prefixWord ++ tailWord_1073851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073851).length < 2 ^ (prefixWord ++ tailWord_1073851).sum := by decide
  have hdescent : baseEnd_1073851 < baseStart_1073851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073881 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_1073881 : Nat := 118140960795 + 1073881 * 2 ^ 59
def prefixEnd_1073881 : Nat := 4983230072969 + 3 ^ 40 * 1073881 * 2
def baseEnd_1073881 : Nat := 551417118731018169348817

theorem tailTrace_1073881 : CollatzResearch.WordTrace tailWord_1073881 prefixEnd_1073881 551417118731018169348817 := by
  unfold tailWord_1073881
  simp only [CollatzResearch.WordTrace]
  refine ⟨39167657822520016118349497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26111771881680010745566331 39167657822520016118349497)
  ·
    refine ⟨29375743366890012088762123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39167657822520016118349497 29375743366890012088762123)
    ·
      refine ⟨44063615050335018133143185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29375743366890012088762123 44063615050335018133143185)
      ·
        refine ⟨33047711287751263599857389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44063615050335018133143185 33047711287751263599857389)
        ·
          refine ⟨12392891732906723849946521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33047711287751263599857389 12392891732906723849946521)
          ·
            refine ⟨9294668799680042887459891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12392891732906723849946521 9294668799680042887459891)
            ·
              refine ⟨13942003199520064331189837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9294668799680042887459891 13942003199520064331189837)
              ·
                refine ⟨5228251199820024124196189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13942003199520064331189837 5228251199820024124196189)
                ·
                  refine ⟨1960594199932509046573571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5228251199820024124196189 1960594199932509046573571)
                  ·
                    refine ⟨2940891299898763569860357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960594199932509046573571 2940891299898763569860357)
                    ·
                      refine ⟨551417118731018169348817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2940891299898763569860357 551417118731018169348817)
                      ·
                        rfl

theorem cell23_1073881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_1073881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073881 prefixEnd_1073881 := by exact prefixLift 1073881
  have htrace : WordTrace (prefixWord ++ tailWord_1073881) baseStart_1073881 baseEnd_1073881 := by
    simpa [prefixWord, tailWord_1073881, baseEnd_1073881] using wordTrace_append hprefix tailTrace_1073881
  have hstable : (prefixWord ++ tailWord_1073881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073881).length < 2 ^ (prefixWord ++ tailWord_1073881).sum := by decide
  have hdescent : baseEnd_1073881 < baseStart_1073881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073892 : List Nat := [2, 3, 1, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_1073892 : Nat := 118140960795 + 1073892 * 2 ^ 59
def prefixEnd_1073892 : Nat := 4983230072969 + 3 ^ 40 * 1073892 * 2
def baseEnd_1073892 : Nat := 551422767018217626311267

theorem tailTrace_1073892 : CollatzResearch.WordTrace tailWord_1073892 prefixEnd_1073892 551422767018217626311267 := by
  unfold tailWord_1073892
  simp only [CollatzResearch.WordTrace]
  refine ⟨19584029512740082498499965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26112039350320109997999953 19584029512740082498499965)
  ·
    refine ⟨7344011067277530936937487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19584029512740082498499965 7344011067277530936937487)
    ·
      refine ⟨11016016600916296405406231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7344011067277530936937487 11016016600916296405406231)
      ·
        refine ⟨16524024901374444608109347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11016016600916296405406231 16524024901374444608109347)
        ·
          refine ⟨24786037352061666912164021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16524024901374444608109347 24786037352061666912164021)
          ·
            refine ⟨2323691001755781273015377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24786037352061666912164021 2323691001755781273015377)
            ·
              refine ⟨1742768251316835954761533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323691001755781273015377 1742768251316835954761533)
              ·
                refine ⟨653538094243813483035575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742768251316835954761533 653538094243813483035575)
                ·
                  refine ⟨980307141365720224553363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653538094243813483035575 980307141365720224553363)
                  ·
                    refine ⟨1470460712048580336830045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 980307141365720224553363 1470460712048580336830045)
                    ·
                      refine ⟨551422767018217626311267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470460712048580336830045 551422767018217626311267)
                      ·
                        rfl

theorem cell23_1073892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_1073892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073892 prefixEnd_1073892 := by exact prefixLift 1073892
  have htrace : WordTrace (prefixWord ++ tailWord_1073892) baseStart_1073892 baseEnd_1073892 := by
    simpa [prefixWord, tailWord_1073892, baseEnd_1073892] using wordTrace_append hprefix tailTrace_1073892
  have hstable : (prefixWord ++ tailWord_1073892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073892).length < 2 ^ (prefixWord ++ tailWord_1073892).sum := by decide
  have hdescent : baseEnd_1073892 < baseStart_1073892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073904 : List Nat := [2, 1, 1, 1, 3, 1, 14]
def baseStart_1073904 : Nat := 118140960795 + 1073904 * 2 ^ 59
def prefixEnd_1073904 : Nat := 4983230072969 + 3 ^ 40 * 1073904 * 2
def baseEnd_1073904 : Nat := 6807764552914463942731

theorem tailTrace_1073904 : CollatzResearch.WordTrace tailWord_1073904 prefixEnd_1073904 6807764552914463942731 := by
  unfold tailWord_1073904
  simp only [CollatzResearch.WordTrace]
  refine ⟨19584248350718345523218383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26112331134291127364291177 19584248350718345523218383)
  ·
    refine ⟨29376372526077518284827575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19584248350718345523218383 29376372526077518284827575)
    ·
      refine ⟨44064558789116277427241363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29376372526077518284827575 44064558789116277427241363)
      ·
        refine ⟨66096838183674416140862045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44064558789116277427241363 66096838183674416140862045)
        ·
          refine ⟨24786314318877906052823267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66096838183674416140862045 24786314318877906052823267)
          ·
            refine ⟨37179471478316859079234901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24786314318877906052823267 37179471478316859079234901)
            ·
              refine ⟨6807764552914463942731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 37179471478316859079234901 6807764552914463942731)
              ·
                rfl

theorem cell23_1073904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 14].length) (baseStart_1073904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073904 prefixEnd_1073904 := by exact prefixLift 1073904
  have htrace : WordTrace (prefixWord ++ tailWord_1073904) baseStart_1073904 baseEnd_1073904 := by
    simpa [prefixWord, tailWord_1073904, baseEnd_1073904] using wordTrace_append hprefix tailTrace_1073904
  have hstable : (prefixWord ++ tailWord_1073904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073904).length < 2 ^ (prefixWord ++ tailWord_1073904).sum := by decide
  have hdescent : baseEnd_1073904 < baseStart_1073904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073918 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1073918 : Nat := 118140960795 + 1073918 * 2 ^ 59
def prefixEnd_1073918 : Nat := 4983230072969 + 3 ^ 40 * 1073918 * 2
def baseEnd_1073918 : Nat := 551436117515234524586147

theorem tailTrace_1073918 : CollatzResearch.WordTrace tailWord_1073918 prefixEnd_1073918 551436117515234524586147 := by
  unfold tailWord_1073918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896125915423246429680801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26112671548923980958297605 4896125915423246429680801)
  ·
    refine ⟨3672094436567434822260601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4896125915423246429680801 3672094436567434822260601)
    ·
      refine ⟨2754070827425576116695451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3672094436567434822260601 2754070827425576116695451)
      ·
        refine ⟨4131106241138364175043177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754070827425576116695451 4131106241138364175043177)
        ·
          refine ⟨3098329680853773131282383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4131106241138364175043177 3098329680853773131282383)
          ·
            refine ⟨4647494521280659696923575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098329680853773131282383 4647494521280659696923575)
            ·
              refine ⟨6971241781920989545385363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4647494521280659696923575 6971241781920989545385363)
              ·
                refine ⟨10456862672881484318078045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6971241781920989545385363 10456862672881484318078045)
                ·
                  refine ⟨3921323502330556619279267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10456862672881484318078045 3921323502330556619279267)
                  ·
                    refine ⟨5881985253495834928918901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3921323502330556619279267 5881985253495834928918901)
                    ·
                      refine ⟨551436117515234524586147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5881985253495834928918901 551436117515234524586147)
                      ·
                        rfl

theorem cell23_1073918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1073918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073918 prefixEnd_1073918 := by exact prefixLift 1073918
  have htrace : WordTrace (prefixWord ++ tailWord_1073918) baseStart_1073918 baseEnd_1073918 := by
    simpa [prefixWord, tailWord_1073918, baseEnd_1073918] using wordTrace_append hprefix tailTrace_1073918
  have hstable : (prefixWord ++ tailWord_1073918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073918).length < 2 ^ (prefixWord ++ tailWord_1073918).sum := by decide
  have hdescent : baseEnd_1073918 < baseStart_1073918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073928 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_1073928 : Nat := 118140960795 + 1073928 * 2 ^ 59
def prefixEnd_1073928 : Nat := 4983230072969 + 3 ^ 40 * 1073928 * 2
def baseEnd_1073928 : Nat := 551441252321779485461101

theorem tailTrace_1073928 : CollatzResearch.WordTrace tailWord_1073928 prefixEnd_1073928 551441252321779485461101 := by
  unfold tailWord_1073928
  simp only [CollatzResearch.WordTrace]
  refine ⟨19584686026674871572655219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26112914702233162096873625 19584686026674871572655219)
  ·
    refine ⟨29377029040012307358982829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19584686026674871572655219 29377029040012307358982829)
    ·
      refine ⟨11016385890004615259618561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29377029040012307358982829 11016385890004615259618561)
      ·
        refine ⟨8262289417503461444713921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11016385890004615259618561 8262289417503461444713921)
        ·
          refine ⟨6196717063127596083535441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262289417503461444713921 6196717063127596083535441)
          ·
            refine ⟨4647537797345697062651581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6196717063127596083535441 4647537797345697062651581)
            ·
              refine ⟨1742826674004636398494343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4647537797345697062651581 1742826674004636398494343)
              ·
                refine ⟨2614240011006954597741515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742826674004636398494343 2614240011006954597741515)
                ·
                  refine ⟨3921360016510431896612273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614240011006954597741515 3921360016510431896612273)
                  ·
                    refine ⟨2941020012382823922459205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3921360016510431896612273 2941020012382823922459205)
                    ·
                      refine ⟨551441252321779485461101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2941020012382823922459205 551441252321779485461101)
                      ·
                        rfl

theorem cell23_1073928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_1073928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1073928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1073928 prefixEnd_1073928 := by exact prefixLift 1073928
  have htrace : WordTrace (prefixWord ++ tailWord_1073928) baseStart_1073928 baseEnd_1073928 := by
    simpa [prefixWord, tailWord_1073928, baseEnd_1073928] using wordTrace_append hprefix tailTrace_1073928
  have hstable : (prefixWord ++ tailWord_1073928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073928).length < 2 ^ (prefixWord ++ tailWord_1073928).sum := by decide
  have hdescent : baseEnd_1073928 < baseStart_1073928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074005 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_1074005 : Nat := 118140960795 + 1074005 * 2 ^ 59
def prefixEnd_1074005 : Nat := 4983230072969 + 3 ^ 40 * 1074005 * 2
def baseEnd_1074005 : Nat := 551480790332175684198247

theorem tailTrace_1074005 : CollatzResearch.WordTrace tailWord_1074005 prefixEnd_1074005 551480790332175684198247 := by
  unfold tailWord_1074005
  simp only [CollatzResearch.WordTrace]
  refine ⟨39172180474070785295863469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26114786982713856863908979 39172180474070785295863469)
  ·
    refine ⟨14689567677776544485948801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39172180474070785295863469 14689567677776544485948801)
    ·
      refine ⟨11017175758332408364461601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14689567677776544485948801 11017175758332408364461601)
      ·
        refine ⟨8262881818749306273346201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11017175758332408364461601 8262881818749306273346201)
        ·
          refine ⟨6197161364061979705009651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262881818749306273346201 6197161364061979705009651)
          ·
            refine ⟨9295742046092969557514477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6197161364061979705009651 9295742046092969557514477)
            ·
              refine ⟨3485903267284863584067929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9295742046092969557514477 3485903267284863584067929)
              ·
                refine ⟨2614427450463647688050947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485903267284863584067929 2614427450463647688050947)
                ·
                  refine ⟨3921641175695471532076421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614427450463647688050947 3921641175695471532076421)
                  ·
                    refine ⟨735307720442900912264329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3921641175695471532076421 735307720442900912264329)
                    ·
                      refine ⟨551480790332175684198247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735307720442900912264329 551480790332175684198247)
                      ·
                        rfl

theorem cell23_1074005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_1074005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074005 prefixEnd_1074005 := by exact prefixLift 1074005
  have htrace : WordTrace (prefixWord ++ tailWord_1074005) baseStart_1074005 baseEnd_1074005 := by
    simpa [prefixWord, tailWord_1074005, baseEnd_1074005] using wordTrace_append hprefix tailTrace_1074005
  have hstable : (prefixWord ++ tailWord_1074005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074005).length < 2 ^ (prefixWord ++ tailWord_1074005).sum := by decide
  have hdescent : baseEnd_1074005 < baseStart_1074005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074021 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1074021 : Nat := 118140960795 + 1074021 * 2 ^ 59
def prefixEnd_1074021 : Nat := 4983230072969 + 3 ^ 40 * 1074021 * 2
def baseEnd_1074021 : Nat := 551489006022647621598173

theorem tailTrace_1074021 : CollatzResearch.WordTrace tailWord_1074021 prefixEnd_1074021 551489006022647621598173 := by
  unfold tailWord_1074021
  simp only [CollatzResearch.WordTrace]
  refine ⟨39172764042012820028445917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26115176028008546685630611 39172764042012820028445917)
  ·
    refine ⟨14689786515754807510667219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39172764042012820028445917 14689786515754807510667219)
    ·
      refine ⟨22034679773632211266000829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14689786515754807510667219 22034679773632211266000829)
      ·
        refine ⟨8263004915112079224750311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22034679773632211266000829 8263004915112079224750311)
        ·
          refine ⟨12394507372668118837125467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8263004915112079224750311 12394507372668118837125467)
          ·
            refine ⟨18591761059002178255688201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12394507372668118837125467 18591761059002178255688201)
            ·
              refine ⟨13943820794251633691766151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18591761059002178255688201 13943820794251633691766151)
              ·
                refine ⟨20915731191377450537649227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13943820794251633691766151 20915731191377450537649227)
                ·
                  refine ⟨31373596787066175806473841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20915731191377450537649227 31373596787066175806473841)
                  ·
                    refine ⟨23530197590299631854855381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31373596787066175806473841 23530197590299631854855381)
                    ·
                      refine ⟨551489006022647621598173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23530197590299631854855381 551489006022647621598173)
                      ·
                        rfl

theorem cell23_1074021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1074021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074021 prefixEnd_1074021 := by exact prefixLift 1074021
  have htrace : WordTrace (prefixWord ++ tailWord_1074021) baseStart_1074021 baseEnd_1074021 := by
    simpa [prefixWord, tailWord_1074021, baseEnd_1074021] using wordTrace_append hprefix tailTrace_1074021
  have hstable : (prefixWord ++ tailWord_1074021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074021).length < 2 ^ (prefixWord ++ tailWord_1074021).sum := by decide
  have hdescent : baseEnd_1074021 < baseStart_1074021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074105 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 3, 4]
def baseStart_1074105 : Nat := 118140960795 + 1074105 * 2 ^ 59
def prefixEnd_1074105 : Nat := 4983230072969 + 3 ^ 40 * 1074105 * 2
def baseEnd_1074105 : Nat := 183844046132541764315929

theorem tailTrace_1074105 : CollatzResearch.WordTrace tailWord_1074105 prefixEnd_1074105 183844046132541764315929 := by
  unfold tailWord_1074105
  simp only [CollatzResearch.WordTrace]
  refine ⟨39175827773708502374503769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26117218515805668249669179 39175827773708502374503769)
  ·
    refine ⟨29381870830281376780877827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39175827773708502374503769 29381870830281376780877827)
    ·
      refine ⟨44072806245422065171316741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29381870830281376780877827 44072806245422065171316741)
      ·
        refine ⟨8263651171016637219621889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44072806245422065171316741 8263651171016637219621889)
        ·
          refine ⟨6197738378262477914716417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8263651171016637219621889 6197738378262477914716417)
          ·
            refine ⟨4648303783696858436037313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6197738378262477914716417 4648303783696858436037313)
            ·
              refine ⟨3486227837772643827027985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4648303783696858436037313 3486227837772643827027985)
              ·
                refine ⟨2614670878329482870270989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486227837772643827027985 2614670878329482870270989)
                ·
                  refine ⟨980501579373556076351621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2614670878329482870270989 980501579373556076351621)
                  ·
                    refine ⟨183844046132541764315929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 980501579373556076351621 183844046132541764315929)
                    ·
                      rfl

theorem cell23_1074105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_1074105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074105 prefixEnd_1074105 := by exact prefixLift 1074105
  have htrace : WordTrace (prefixWord ++ tailWord_1074105) baseStart_1074105 baseEnd_1074105 := by
    simpa [prefixWord, tailWord_1074105, baseEnd_1074105] using wordTrace_append hprefix tailTrace_1074105
  have hstable : (prefixWord ++ tailWord_1074105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074105).length < 2 ^ (prefixWord ++ tailWord_1074105).sum := by decide
  have hdescent : baseEnd_1074105 < baseStart_1074105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074132 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1074132 : Nat := 118140960795 + 1074132 * 2 ^ 59
def prefixEnd_1074132 : Nat := 4983230072969 + 3 ^ 40 * 1074132 * 2
def baseEnd_1074132 : Nat := 551546002375296687310163

theorem tailTrace_1074132 : CollatzResearch.WordTrace tailWord_1074132 prefixEnd_1074132 551546002375296687310163 := by
  unfold tailWord_1074132
  simp only [CollatzResearch.WordTrace]
  refine ⟨19588406272305342992868325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26117875029740457323824433 19588406272305342992868325)
  ·
    refine ⟨3672826176057251811162811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19588406272305342992868325 3672826176057251811162811)
    ·
      refine ⟨5509239264085877716744217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672826176057251811162811 5509239264085877716744217)
      ·
        refine ⟨4131929448064408287558163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5509239264085877716744217 4131929448064408287558163)
        ·
          refine ⟨6197894172096612431337245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4131929448064408287558163 6197894172096612431337245)
          ·
            refine ⟨2324210314536229661751467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6197894172096612431337245 2324210314536229661751467)
            ·
              refine ⟨3486315471804344492627201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2324210314536229661751467 3486315471804344492627201)
              ·
                refine ⟨2614736603853258369470401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486315471804344492627201 2614736603853258369470401)
                ·
                  refine ⟨1961052452889943777102801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2614736603853258369470401 1961052452889943777102801)
                  ·
                    refine ⟨1470789339667457832827101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1961052452889943777102801 1470789339667457832827101)
                    ·
                      refine ⟨551546002375296687310163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470789339667457832827101 551546002375296687310163)
                      ·
                        rfl

theorem cell23_1074132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1074132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074132 prefixEnd_1074132 := by exact prefixLift 1074132
  have htrace : WordTrace (prefixWord ++ tailWord_1074132) baseStart_1074132 baseEnd_1074132 := by
    simpa [prefixWord, tailWord_1074132, baseEnd_1074132] using wordTrace_append hprefix tailTrace_1074132
  have hstable : (prefixWord ++ tailWord_1074132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074132).length < 2 ^ (prefixWord ++ tailWord_1074132).sum := by decide
  have hdescent : baseEnd_1074132 < baseStart_1074132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074172 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_1074172 : Nat := 118140960795 + 1074172 * 2 ^ 59
def prefixEnd_1074172 : Nat := 4983230072969 + 3 ^ 40 * 1074172 * 2
def baseEnd_1074172 : Nat := 551566541601476530809979

theorem tailTrace_1074172 : CollatzResearch.WordTrace tailWord_1074172 prefixEnd_1074172 551566541601476530809979 := by
  unfold tailWord_1074172
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589135732232886408596385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26118847642977181878128513 19589135732232886408596385)
  ·
    refine ⟨14691851799174664806447289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19589135732232886408596385 14691851799174664806447289)
    ·
      refine ⟨11018888849380998604835467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14691851799174664806447289 11018888849380998604835467)
      ·
        refine ⟨16528333274071497907253201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11018888849380998604835467 16528333274071497907253201)
        ·
          refine ⟨12396249955553623430439901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16528333274071497907253201 12396249955553623430439901)
          ·
            refine ⟨4648593733332608786414963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12396249955553623430439901 4648593733332608786414963)
            ·
              refine ⟨6972890599998913179622445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648593733332608786414963 6972890599998913179622445)
              ·
                refine ⟨2614833974999592442358417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6972890599998913179622445 2614833974999592442358417)
                ·
                  refine ⟨1961125481249694331768813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2614833974999592442358417 1961125481249694331768813)
                  ·
                    refine ⟨735422055468635374413305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961125481249694331768813 735422055468635374413305)
                    ·
                      refine ⟨551566541601476530809979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735422055468635374413305 551566541601476530809979)
                      ·
                        rfl

theorem cell23_1074172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_1074172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074172 prefixEnd_1074172 := by exact prefixLift 1074172
  have htrace : WordTrace (prefixWord ++ tailWord_1074172) baseStart_1074172 baseEnd_1074172 := by
    simpa [prefixWord, tailWord_1074172, baseEnd_1074172] using wordTrace_append hprefix tailTrace_1074172
  have hstable : (prefixWord ++ tailWord_1074172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074172).length < 2 ^ (prefixWord ++ tailWord_1074172).sum := by decide
  have hdescent : baseEnd_1074172 < baseStart_1074172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074185 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 4]
def baseStart_1074185 : Nat := 118140960795 + 1074185 * 2 ^ 59
def prefixEnd_1074185 : Nat := 4983230072969 + 3 ^ 40 * 1074185 * 2
def baseEnd_1074185 : Nat := 551573216849984979947419

theorem tailTrace_1074185 : CollatzResearch.WordTrace tailWord_1074185 prefixEnd_1074185 551573216849984979947419 := by
  unfold tailWord_1074185
  simp only [CollatzResearch.WordTrace]
  refine ⟨39178745613418676037416009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26119163742279117358277339 39178745613418676037416009)
  ·
    refine ⟨29384059210064007028062007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39178745613418676037416009 29384059210064007028062007)
    ·
      refine ⟨44076088815096010542093011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29384059210064007028062007 44076088815096010542093011)
      ·
        refine ⟨66114133222644015813139517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44076088815096010542093011 66114133222644015813139517)
        ·
          refine ⟨24792799958491505929927319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66114133222644015813139517 24792799958491505929927319)
          ·
            refine ⟨37189199937737258894890979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24792799958491505929927319 37189199937737258894890979)
            ·
              refine ⟨55783799906605888342336469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37189199937737258894890979 55783799906605888342336469)
              ·
                refine ⟨1307432810311075508023511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55783799906605888342336469 1307432810311075508023511)
                ·
                  refine ⟨1961149215466613262035267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307432810311075508023511 1961149215466613262035267)
                  ·
                    refine ⟨2941723823199919893052901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1961149215466613262035267 2941723823199919893052901)
                    ·
                      refine ⟨551573216849984979947419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2941723823199919893052901 551573216849984979947419)
                      ·
                        rfl

theorem cell23_1074185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_1074185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074185 prefixEnd_1074185 := by exact prefixLift 1074185
  have htrace : WordTrace (prefixWord ++ tailWord_1074185) baseStart_1074185 baseEnd_1074185 := by
    simpa [prefixWord, tailWord_1074185, baseEnd_1074185] using wordTrace_append hprefix tailTrace_1074185
  have hstable : (prefixWord ++ tailWord_1074185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074185).length < 2 ^ (prefixWord ++ tailWord_1074185).sum := by decide
  have hdescent : baseEnd_1074185 < baseStart_1074185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074212 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_1074212 : Nat := 118140960795 + 1074212 * 2 ^ 59
def prefixEnd_1074212 : Nat := 4983230072969 + 3 ^ 40 * 1074212 * 2
def baseEnd_1074212 : Nat := 183862360275885458103265

theorem tailTrace_1074212 : CollatzResearch.WordTrace tailWord_1074212 prefixEnd_1074212 183862360275885458103265 := by
  unfold tailWord_1074212
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589865192160429824324445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26119820256213906432432593 19589865192160429824324445)
  ·
    refine ⟨7346199447060161184121667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19589865192160429824324445 7346199447060161184121667)
    ·
      refine ⟨11019299170590241776182501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7346199447060161184121667 11019299170590241776182501)
      ·
        refine ⟨2066118594485670333034219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11019299170590241776182501 2066118594485670333034219)
        ·
          refine ⟨3099177891728505499551329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2066118594485670333034219 3099177891728505499551329)
          ·
            refine ⟨2324383418796379124663497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3099177891728505499551329 2324383418796379124663497)
            ·
              refine ⟨1743287564097284343497623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2324383418796379124663497 1743287564097284343497623)
              ·
                refine ⟨2614931346145926515246435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743287564097284343497623 2614931346145926515246435)
                ·
                  refine ⟨3922397019218889772869653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614931346145926515246435 3922397019218889772869653)
                  ·
                    refine ⟨183862360275885458103265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3922397019218889772869653 183862360275885458103265)
                    ·
                      rfl

theorem cell23_1074212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_1074212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074212 prefixEnd_1074212 := by exact prefixLift 1074212
  have htrace : WordTrace (prefixWord ++ tailWord_1074212) baseStart_1074212 baseEnd_1074212 := by
    simpa [prefixWord, tailWord_1074212, baseEnd_1074212] using wordTrace_append hprefix tailTrace_1074212
  have hstable : (prefixWord ++ tailWord_1074212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074212).length < 2 ^ (prefixWord ++ tailWord_1074212).sum := by decide
  have hdescent : baseEnd_1074212 < baseStart_1074212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074222 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1074222 : Nat := 118140960795 + 1074222 * 2 ^ 59
def prefixEnd_1074222 : Nat := 4983230072969 + 3 ^ 40 * 1074222 * 2
def baseEnd_1074222 : Nat := 551592215634201335184749

theorem tailTrace_1074222 : CollatzResearch.WordTrace tailWord_1074222 prefixEnd_1074222 551592215634201335184749 := by
  unfold tailWord_1074222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4897511889285578919564115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26120063409523087571008613 4897511889285578919564115)
  ·
    refine ⟨7346267833928368379346173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4897511889285578919564115 7346267833928368379346173)
    ·
      refine ⟨2754850437723138142254815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7346267833928368379346173 2754850437723138142254815)
      ·
        refine ⟨4132275656584707213382223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754850437723138142254815 4132275656584707213382223)
        ·
          refine ⟨6198413484877060820073335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132275656584707213382223 6198413484877060820073335)
          ·
            refine ⟨9297620227315591230110003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6198413484877060820073335 9297620227315591230110003)
            ·
              refine ⟨13946430340973386845165005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9297620227315591230110003 13946430340973386845165005)
              ·
                refine ⟨5229911377865020066936877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13946430340973386845165005 5229911377865020066936877)
                ·
                  refine ⟨1961216766699382525101329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5229911377865020066936877 1961216766699382525101329)
                  ·
                    refine ⟨1470912575024536893825997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1961216766699382525101329 1470912575024536893825997)
                    ·
                      refine ⟨551592215634201335184749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1470912575024536893825997 551592215634201335184749)
                      ·
                        rfl

theorem cell23_1074222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1074222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074222 prefixEnd_1074222 := by exact prefixLift 1074222
  have htrace : WordTrace (prefixWord ++ tailWord_1074222) baseStart_1074222 baseEnd_1074222 := by
    simpa [prefixWord, tailWord_1074222, baseEnd_1074222] using wordTrace_append hprefix tailTrace_1074222
  have hstable : (prefixWord ++ tailWord_1074222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074222).length < 2 ^ (prefixWord ++ tailWord_1074222).sum := by decide
  have hdescent : baseEnd_1074222 < baseStart_1074222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074225 : List Nat := [1, 2, 2, 3, 1, 2, 5, 7]
def baseStart_1074225 : Nat := 118140960795 + 1074225 * 2 ^ 59
def prefixEnd_1074225 : Nat := 4983230072969 + 3 ^ 40 * 1074225 * 2
def baseEnd_1074225 : Nat := 20429398373191289757305

theorem tailTrace_1074225 : CollatzResearch.WordTrace tailWord_1074225 prefixEnd_1074225 20429398373191289757305 := by
  unfold tailWord_1074225
  simp only [CollatzResearch.WordTrace]
  refine ⟨39180204533273762868872129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26120136355515841912581419 39180204533273762868872129)
  ·
    refine ⟨29385153399955322151654097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39180204533273762868872129 29385153399955322151654097)
    ·
      refine ⟨22038865049966491613740573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29385153399955322151654097 22038865049966491613740573)
      ·
        refine ⟨8264574393737434355152715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22038865049966491613740573 8264574393737434355152715)
        ·
          refine ⟨12396861590606151532729073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8264574393737434355152715 12396861590606151532729073)
          ·
            refine ⟨9297646192954613649546805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12396861590606151532729073 9297646192954613649546805)
            ·
              refine ⟨871654330589495029645013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9297646192954613649546805 871654330589495029645013)
              ·
                refine ⟨20429398373191289757305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 871654330589495029645013 20429398373191289757305)
                ·
                  rfl

theorem cell23_1074225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 7].length) (baseStart_1074225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074225 prefixEnd_1074225 := by exact prefixLift 1074225
  have htrace : WordTrace (prefixWord ++ tailWord_1074225) baseStart_1074225 baseEnd_1074225 := by
    simpa [prefixWord, tailWord_1074225, baseEnd_1074225] using wordTrace_append hprefix tailTrace_1074225
  have hstable : (prefixWord ++ tailWord_1074225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074225).length < 2 ^ (prefixWord ++ tailWord_1074225).sum := by decide
  have hdescent : baseEnd_1074225 < baseStart_1074225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074236 : List Nat := [2, 2, 2, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_1074236 : Nat := 118140960795 + 1074236 * 2 ^ 59
def prefixEnd_1074236 : Nat := 4983230072969 + 3 ^ 40 * 1074236 * 2
def baseEnd_1074236 : Nat := 551599404363364280409685

theorem tailTrace_1074236 : CollatzResearch.WordTrace tailWord_1074236 prefixEnd_1074236 551599404363364280409685 := by
  unfold tailWord_1074236
  simp only [CollatzResearch.WordTrace]
  refine ⟨19590302868116955873761281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26120403824155941165015041 19590302868116955873761281)
  ·
    refine ⟨14692727151087716905320961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19590302868116955873761281 14692727151087716905320961)
    ·
      refine ⟨11019545363315787678990721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14692727151087716905320961 11019545363315787678990721)
      ·
        refine ⟨8264659022486840759243041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11019545363315787678990721 8264659022486840759243041)
        ·
          refine ⟨6198494266865130569432281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8264659022486840759243041 6198494266865130569432281)
          ·
            refine ⟨4648870700148847927074211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6198494266865130569432281 4648870700148847927074211)
            ·
              refine ⟨6973306050223271890611317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648870700148847927074211 6973306050223271890611317)
              ·
                refine ⟨653747442208431739744811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6973306050223271890611317 653747442208431739744811)
                ·
                  refine ⟨980621163312647609617217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653747442208431739744811 980621163312647609617217)
                  ·
                    refine ⟨735465872484485707212913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 980621163312647609617217 735465872484485707212913)
                    ·
                      refine ⟨551599404363364280409685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735465872484485707212913 551599404363364280409685)
                      ·
                        rfl

theorem cell23_1074236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_1074236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074236 prefixEnd_1074236 := by exact prefixLift 1074236
  have htrace : WordTrace (prefixWord ++ tailWord_1074236) baseStart_1074236 baseEnd_1074236 := by
    simpa [prefixWord, tailWord_1074236, baseEnd_1074236] using wordTrace_append hprefix tailTrace_1074236
  have hstable : (prefixWord ++ tailWord_1074236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074236).length < 2 ^ (prefixWord ++ tailWord_1074236).sum := by decide
  have hdescent : baseEnd_1074236 < baseStart_1074236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074246 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1074246 : Nat := 118140960795 + 1074246 * 2 ^ 59
def prefixEnd_1074246 : Nat := 4983230072969 + 3 ^ 40 * 1074246 * 2
def baseEnd_1074246 : Nat := 183868179723303080428213

theorem tailTrace_1074246 : CollatzResearch.WordTrace tailWord_1074246 prefixEnd_1074246 183868179723303080428213 := by
  unfold tailWord_1074246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224405327068677607980831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26120646977465122303591061 1224405327068677607980831)
  ·
    refine ⟨1836607990603016411971247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1224405327068677607980831 1836607990603016411971247)
    ·
      refine ⟨2754911985904524617956871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1836607990603016411971247 2754911985904524617956871)
      ·
        refine ⟨4132367978856786926935307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754911985904524617956871 4132367978856786926935307)
        ·
          refine ⟨6198551968285180390402961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132367978856786926935307 6198551968285180390402961)
          ·
            refine ⟨4648913976213885292802221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6198551968285180390402961 4648913976213885292802221)
            ·
              refine ⟨1743342741080206984800833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4648913976213885292802221 1743342741080206984800833)
              ·
                refine ⟨1307507055810155238600625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743342741080206984800833 1307507055810155238600625)
                ·
                  refine ⟨980630291857616428950469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1307507055810155238600625 980630291857616428950469)
                  ·
                    refine ⟨183868179723303080428213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 980630291857616428950469 183868179723303080428213)
                    ·
                      rfl

theorem cell23_1074246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1074246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074246 prefixEnd_1074246 := by exact prefixLift 1074246
  have htrace : WordTrace (prefixWord ++ tailWord_1074246) baseStart_1074246 baseEnd_1074246 := by
    simpa [prefixWord, tailWord_1074246, baseEnd_1074246] using wordTrace_append hprefix tailTrace_1074246
  have hstable : (prefixWord ++ tailWord_1074246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074246).length < 2 ^ (prefixWord ++ tailWord_1074246).sum := by decide
  have hdescent : baseEnd_1074246 < baseStart_1074246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074253 : List Nat := [1, 6, 1, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_1074253 : Nat := 118140960795 + 1074253 * 2 ^ 59
def prefixEnd_1074253 : Nat := 4983230072969 + 3 ^ 40 * 1074253 * 2
def baseEnd_1074253 : Nat := 551608133534490713897107

theorem tailTrace_1074253 : CollatzResearch.WordTrace tailWord_1074253 prefixEnd_1074253 551608133534490713897107 := by
  unfold tailWord_1074253
  simp only [CollatzResearch.WordTrace]
  refine ⟨39181225777172323650891413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26120817184781549100594275 39181225777172323650891413)
  ·
    refine ⟨1836619958304952671135535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39181225777172323650891413 1836619958304952671135535)
    ·
      refine ⟨2754929937457429006703303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1836619958304952671135535 2754929937457429006703303)
      ·
        refine ⟨4132394906186143510054955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754929937457429006703303 4132394906186143510054955)
        ·
          refine ⟨6198592359279215265082433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132394906186143510054955 6198592359279215265082433)
          ·
            refine ⟨4648944269459411448811825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6198592359279215265082433 4648944269459411448811825)
            ·
              refine ⟨3486708202094558586608869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4648944269459411448811825 3486708202094558586608869)
              ·
                refine ⟨653757787892729734989163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3486708202094558586608869 653757787892729734989163)
                ·
                  refine ⟨980636681839094602483745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653757787892729734989163 980636681839094602483745)
                  ·
                    refine ⟨735477511379320951862809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 980636681839094602483745 735477511379320951862809)
                    ·
                      refine ⟨551608133534490713897107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735477511379320951862809 551608133534490713897107)
                      ·
                        rfl

theorem cell23_1074253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_1074253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074253 prefixEnd_1074253 := by exact prefixLift 1074253
  have htrace : WordTrace (prefixWord ++ tailWord_1074253) baseStart_1074253 baseEnd_1074253 := by
    simpa [prefixWord, tailWord_1074253, baseEnd_1074253] using wordTrace_append hprefix tailTrace_1074253
  have hstable : (prefixWord ++ tailWord_1074253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074253).length < 2 ^ (prefixWord ++ tailWord_1074253).sum := by decide
  have hdescent : baseEnd_1074253 < baseStart_1074253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074279 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_1074279 : Nat := 118140960795 + 1074279 * 2 ^ 59
def prefixEnd_1074279 : Nat := 4983230072969 + 3 ^ 40 * 1074279 * 2
def baseEnd_1074279 : Nat := 551621484031507612171987

theorem tailTrace_1074279 : CollatzResearch.WordTrace tailWord_1074279 prefixEnd_1074279 551621484031507612171987 := by
  unfold tailWord_1074279
  simp only [CollatzResearch.WordTrace]
  refine ⟨39182174075078130091337891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26121449383385420060891927 39182174075078130091337891)
  ·
    refine ⟨58773261112617195137006837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39182174075078130091337891 58773261112617195137006837)
    ·
      refine ⟨5509993229307862044094391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58773261112617195137006837 5509993229307862044094391)
      ·
        refine ⟨8264989843961793066141587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5509993229307862044094391 8264989843961793066141587)
        ·
          refine ⟨12397484765942689599212381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8264989843961793066141587 12397484765942689599212381)
          ·
            refine ⟨4649056787228508599704643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12397484765942689599212381 4649056787228508599704643)
            ·
              refine ⟨6973585180842762899556965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4649056787228508599704643 6973585180842762899556965)
              ·
                refine ⟨1307547221408018043666931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6973585180842762899556965 1307547221408018043666931)
                ·
                  refine ⟨1961320832112027065500397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307547221408018043666931 1961320832112027065500397)
                  ·
                    refine ⟨735495312042010149562649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961320832112027065500397 735495312042010149562649)
                    ·
                      refine ⟨551621484031507612171987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735495312042010149562649 551621484031507612171987)
                      ·
                        rfl

theorem cell23_1074279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_1074279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074279 prefixEnd_1074279 := by exact prefixLift 1074279
  have htrace : WordTrace (prefixWord ++ tailWord_1074279) baseStart_1074279 baseEnd_1074279 := by
    simpa [prefixWord, tailWord_1074279, baseEnd_1074279] using wordTrace_append hprefix tailTrace_1074279
  have hstable : (prefixWord ++ tailWord_1074279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074279).length < 2 ^ (prefixWord ++ tailWord_1074279).sum := by decide
  have hdescent : baseEnd_1074279 < baseStart_1074279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074295 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1074295 : Nat := 118140960795 + 1074295 * 2 ^ 59
def prefixEnd_1074295 : Nat := 4983230072969 + 3 ^ 40 * 1074295 * 2
def baseEnd_1074295 : Nat := 551629699721979549571913

theorem tailTrace_1074295 : CollatzResearch.WordTrace tailWord_1074295 prefixEnd_1074295 551629699721979549571913 := by
  unfold tailWord_1074295
  simp only [CollatzResearch.WordTrace]
  refine ⟨39182757643020164823920339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26121838428680109882613559 39182757643020164823920339)
  ·
    refine ⟨58774136464530247235880509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39182757643020164823920339 58774136464530247235880509)
    ·
      refine ⟨22040301174198842713455191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58774136464530247235880509 22040301174198842713455191)
      ·
        refine ⟨33060451761298264070182787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22040301174198842713455191 33060451761298264070182787)
        ·
          refine ⟨49590677641947396105274181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33060451761298264070182787 49590677641947396105274181)
          ·
            refine ⟨9298252057865136769738909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49590677641947396105274181 9298252057865136769738909)
            ·
              refine ⟨3486844521699426288652091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9298252057865136769738909 3486844521699426288652091)
              ·
                refine ⟨5230266782549139432978137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3486844521699426288652091 5230266782549139432978137)
                ·
                  refine ⟨3922700086911854574733603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5230266782549139432978137 3922700086911854574733603)
                  ·
                    refine ⟨5884050130367781862100405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3922700086911854574733603 5884050130367781862100405)
                    ·
                      refine ⟨551629699721979549571913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5884050130367781862100405 551629699721979549571913)
                      ·
                        rfl

theorem cell23_1074295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1074295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074295 prefixEnd_1074295 := by exact prefixLift 1074295
  have htrace : WordTrace (prefixWord ++ tailWord_1074295) baseStart_1074295 baseEnd_1074295 := by
    simpa [prefixWord, tailWord_1074295, baseEnd_1074295] using wordTrace_append hprefix tailTrace_1074295
  have hstable : (prefixWord ++ tailWord_1074295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074295).length < 2 ^ (prefixWord ++ tailWord_1074295).sum := by decide
  have hdescent : baseEnd_1074295 < baseStart_1074295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074355 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5]
def baseStart_1074355 : Nat := 118140960795 + 1074355 * 2 ^ 59
def prefixEnd_1074355 : Nat := 4983230072969 + 3 ^ 40 * 1074355 * 2
def baseEnd_1074355 : Nat := 551660508561249314821637

theorem tailTrace_1074355 : CollatzResearch.WordTrace tailWord_1074355 prefixEnd_1074355 551660508561249314821637 := by
  unfold tailWord_1074355
  simp only [CollatzResearch.WordTrace]
  refine ⟨39184946022802795071104519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26123297348535196714069679 39184946022802795071104519)
  ·
    refine ⟨58777419034204192606656779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39184946022802795071104519 58777419034204192606656779)
    ·
      refine ⟨88166128551306288909985169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58777419034204192606656779 88166128551306288909985169)
      ·
        refine ⟨66124596413479716682488877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88166128551306288909985169 66124596413479716682488877)
        ·
          refine ⟨24796723655054893755933329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66124596413479716682488877 24796723655054893755933329)
          ·
            refine ⟨18597542741291170316949997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24796723655054893755933329 18597542741291170316949997)
            ·
              refine ⟨6974078527984188868856249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18597542741291170316949997 6974078527984188868856249)
              ·
                refine ⟨5230558895988141651642187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6974078527984188868856249 5230558895988141651642187)
                ·
                  refine ⟨7845838343982212477463281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5230558895988141651642187 7845838343982212477463281)
                  ·
                    refine ⟨5884378757986659358097461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7845838343982212477463281 5884378757986659358097461)
                    ·
                      refine ⟨551660508561249314821637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5884378757986659358097461 551660508561249314821637)
                      ·
                        rfl

theorem cell23_1074355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_1074355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074355 prefixEnd_1074355 := by exact prefixLift 1074355
  have htrace : WordTrace (prefixWord ++ tailWord_1074355) baseStart_1074355 baseEnd_1074355 := by
    simpa [prefixWord, tailWord_1074355, baseEnd_1074355] using wordTrace_append hprefix tailTrace_1074355
  have hstable : (prefixWord ++ tailWord_1074355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074355).length < 2 ^ (prefixWord ++ tailWord_1074355).sum := by decide
  have hdescent : baseEnd_1074355 < baseStart_1074355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074366 : List Nat := [4, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_1074366 : Nat := 118140960795 + 1074366 * 2 ^ 59
def prefixEnd_1074366 : Nat := 4983230072969 + 3 ^ 40 * 1074366 * 2
def baseEnd_1074366 : Nat := 61296239649827641309343

theorem tailTrace_1074366 : CollatzResearch.WordTrace tailWord_1074366 prefixEnd_1074366 61296239649827641309343 := by
  unfold tailWord_1074366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4898168403220367993719369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26123564817175295966503301 4898168403220367993719369)
  ·
    refine ⟨3673626302415275995289527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4898168403220367993719369 3673626302415275995289527)
    ·
      refine ⟨5510439453622913992934291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3673626302415275995289527 5510439453622913992934291)
      ·
        refine ⟨8265659180434370989401437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510439453622913992934291 8265659180434370989401437)
        ·
          refine ⟨3099622192662889121025539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8265659180434370989401437 3099622192662889121025539)
          ·
            refine ⟨4649433288994333681538309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099622192662889121025539 4649433288994333681538309)
            ·
              refine ⟨871768741686437565288433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4649433288994333681538309 871768741686437565288433)
              ·
                refine ⟨653826556264828173966325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871768741686437565288433 653826556264828173966325)
                ·
                  refine ⟨61296239649827641309343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 653826556264828173966325 61296239649827641309343)
                  ·
                    rfl

theorem cell23_1074366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_1074366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074366 prefixEnd_1074366 := by exact prefixLift 1074366
  have htrace : WordTrace (prefixWord ++ tailWord_1074366) baseStart_1074366 baseEnd_1074366 := by
    simpa [prefixWord, tailWord_1074366, baseEnd_1074366] using wordTrace_append hprefix tailTrace_1074366
  have hstable : (prefixWord ++ tailWord_1074366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074366).length < 2 ^ (prefixWord ++ tailWord_1074366).sum := by decide
  have hdescent : baseEnd_1074366 < baseStart_1074366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074425 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_1074425 : Nat := 118140960795 + 1074425 * 2 ^ 59
def prefixEnd_1074425 : Nat := 4983230072969 + 3 ^ 40 * 1074425 * 2
def baseEnd_1074425 : Nat := 551696452207064040946315

theorem tailTrace_1074425 : CollatzResearch.WordTrace tailWord_1074425 prefixEnd_1074425 551696452207064040946315 := by
  unfold tailWord_1074425
  simp only [CollatzResearch.WordTrace]
  refine ⟨39187499132549197026152729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26124999421699464684101819 39187499132549197026152729)
  ·
    refine ⟨29390624349411897769614547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39187499132549197026152729 29390624349411897769614547)
    ·
      refine ⟨44085936524117846654421821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29390624349411897769614547 44085936524117846654421821)
      ·
        refine ⟨16532226196544192495408183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44085936524117846654421821 16532226196544192495408183)
        ·
          refine ⟨24798339294816288743112275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16532226196544192495408183 24798339294816288743112275)
          ·
            refine ⟨37197508942224433114668413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24798339294816288743112275 37197508942224433114668413)
            ·
              refine ⟨13949065853334162418000655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37197508942224433114668413 13949065853334162418000655)
              ·
                refine ⟨20923598780001243627000983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13949065853334162418000655 20923598780001243627000983)
                ·
                  refine ⟨31385398170001865440501475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20923598780001243627000983 31385398170001865440501475)
                  ·
                    refine ⟨47078097255002798160752213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31385398170001865440501475 47078097255002798160752213)
                    ·
                      refine ⟨551696452207064040946315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 47078097255002798160752213 551696452207064040946315)
                      ·
                        rfl

theorem cell23_1074425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_1074425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074425 prefixEnd_1074425 := by exact prefixLift 1074425
  have htrace : WordTrace (prefixWord ++ tailWord_1074425) baseStart_1074425 baseEnd_1074425 := by
    simpa [prefixWord, tailWord_1074425, baseEnd_1074425] using wordTrace_append hprefix tailTrace_1074425
  have hstable : (prefixWord ++ tailWord_1074425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074425).length < 2 ^ (prefixWord ++ tailWord_1074425).sum := by decide
  have hdescent : baseEnd_1074425 < baseStart_1074425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074449 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_1074449 : Nat := 118140960795 + 1074449 * 2 ^ 59
def prefixEnd_1074449 : Nat := 4983230072969 + 3 ^ 40 * 1074449 * 2
def baseEnd_1074449 : Nat := 551708775742771947046205

theorem tailTrace_1074449 : CollatzResearch.WordTrace tailWord_1074449 prefixEnd_1074449 551708775742771947046205 := by
  unfold tailWord_1074449
  simp only [CollatzResearch.WordTrace]
  refine ⟨39188374484462249125026401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26125582989641499416684267 39188374484462249125026401)
  ·
    refine ⟨29391280863346686843769801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39188374484462249125026401 29391280863346686843769801)
    ·
      refine ⟨22043460647510015132827351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29391280863346686843769801 22043460647510015132827351)
      ·
        refine ⟨33065190971265022699241027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22043460647510015132827351 33065190971265022699241027)
        ·
          refine ⟨49597786456897534048861541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33065190971265022699241027 49597786456897534048861541)
          ·
            refine ⟨9299584960668287634161539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49597786456897534048861541 9299584960668287634161539)
            ·
              refine ⟨13949377441002431451242309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9299584960668287634161539 13949377441002431451242309)
              ·
                refine ⟨2615508270187955897107933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13949377441002431451242309 2615508270187955897107933)
                ·
                  refine ⟨980815601320483461415475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2615508270187955897107933 980815601320483461415475)
                  ·
                    refine ⟨1471223401980725192123213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 980815601320483461415475 1471223401980725192123213)
                    ·
                      refine ⟨551708775742771947046205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1471223401980725192123213 551708775742771947046205)
                      ·
                        rfl

theorem cell23_1074449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_1074449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074449 prefixEnd_1074449 := by exact prefixLift 1074449
  have htrace : WordTrace (prefixWord ++ tailWord_1074449) baseStart_1074449 baseEnd_1074449 := by
    simpa [prefixWord, tailWord_1074449, baseEnd_1074449] using wordTrace_append hprefix tailTrace_1074449
  have hstable : (prefixWord ++ tailWord_1074449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074449).length < 2 ^ (prefixWord ++ tailWord_1074449).sum := by decide
  have hdescent : baseEnd_1074449 < baseStart_1074449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074459 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 2, 3, 2]
def baseStart_1074459 : Nat := 118140960795 + 1074459 * 2 ^ 59
def prefixEnd_1074459 : Nat := 4983230072969 + 3 ^ 40 * 1074459 * 2
def baseEnd_1074459 : Nat := 551713910549316907921159

theorem tailTrace_1074459 : CollatzResearch.WordTrace tailWord_1074459 prefixEnd_1074459 551713910549316907921159 := by
  unfold tailWord_1074459
  simp only [CollatzResearch.WordTrace]
  refine ⟨39188739214426020832890431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26125826142950680555260287 39188739214426020832890431)
  ·
    refine ⟨58783108821639031249335647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39188739214426020832890431 58783108821639031249335647)
    ·
      refine ⟨88174663232458546874003471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58783108821639031249335647 88174663232458546874003471)
      ·
        refine ⟨132261994848687820311005207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88174663232458546874003471 132261994848687820311005207)
        ·
          refine ⟨198392992273031730466507811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132261994848687820311005207 198392992273031730466507811)
          ·
            refine ⟨297589488409547595699761717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198392992273031730466507811 297589488409547595699761717)
            ·
              refine ⟨27899014538395087096852661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 297589488409547595699761717 27899014538395087096852661)
              ·
                refine ⟨2615532612974539415329937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27899014538395087096852661 2615532612974539415329937)
                ·
                  refine ⟨1961649459730904561497453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2615532612974539415329937 1961649459730904561497453)
                  ·
                    refine ⟨735618547399089210561545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961649459730904561497453 735618547399089210561545)
                    ·
                      refine ⟨551713910549316907921159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735618547399089210561545 551713910549316907921159)
                      ·
                        rfl

theorem cell23_1074459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3, 2].length) (baseStart_1074459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074459 prefixEnd_1074459 := by exact prefixLift 1074459
  have htrace : WordTrace (prefixWord ++ tailWord_1074459) baseStart_1074459 baseEnd_1074459 := by
    simpa [prefixWord, tailWord_1074459, baseEnd_1074459] using wordTrace_append hprefix tailTrace_1074459
  have hstable : (prefixWord ++ tailWord_1074459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074459).length < 2 ^ (prefixWord ++ tailWord_1074459).sum := by decide
  have hdescent : baseEnd_1074459 < baseStart_1074459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074469 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_1074469 : Nat := 118140960795 + 1074469 * 2 ^ 59
def prefixEnd_1074469 : Nat := 4983230072969 + 3 ^ 40 * 1074469 * 2
def baseEnd_1074469 : Nat := 183906348451953956265371

theorem tailTrace_1074469 : CollatzResearch.WordTrace tailWord_1074469 prefixEnd_1074469 183906348451953956265371 := by
  unfold tailWord_1074469
  simp only [CollatzResearch.WordTrace]
  refine ⟨39189103944389792540754461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26126069296259861693836307 39189103944389792540754461)
  ·
    refine ⟨14695913979146172202782923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39189103944389792540754461 14695913979146172202782923)
    ·
      refine ⟨22043870968719258304174385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14695913979146172202782923 22043870968719258304174385)
      ·
        refine ⟨16532903226539443728130789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22043870968719258304174385 16532903226539443728130789)
        ·
          refine ⟨3099919354976145699024523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16532903226539443728130789 3099919354976145699024523)
          ·
            refine ⟨4649879032464218548536785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099919354976145699024523 4649879032464218548536785)
            ·
              refine ⟨3487409274348163911402589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649879032464218548536785 3487409274348163911402589)
              ·
                refine ⟨1307778477880561466775971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3487409274348163911402589 1307778477880561466775971)
                ·
                  refine ⟨1961667716820842200163957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307778477880561466775971 1961667716820842200163957)
                  ·
                    refine ⟨183906348451953956265371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1961667716820842200163957 183906348451953956265371)
                    ·
                      rfl

theorem cell23_1074469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_1074469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074469 prefixEnd_1074469 := by exact prefixLift 1074469
  have htrace : WordTrace (prefixWord ++ tailWord_1074469) baseStart_1074469 baseEnd_1074469 := by
    simpa [prefixWord, tailWord_1074469, baseEnd_1074469] using wordTrace_append hprefix tailTrace_1074469
  have hstable : (prefixWord ++ tailWord_1074469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074469).length < 2 ^ (prefixWord ++ tailWord_1074469).sum := by decide
  have hdescent : baseEnd_1074469 < baseStart_1074469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074506 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_1074506 : Nat := 118140960795 + 1074506 * 2 ^ 59
def prefixEnd_1074506 : Nat := 4983230072969 + 3 ^ 40 * 1074506 * 2
def baseEnd_1074506 : Nat := 551738044140078224033443

theorem tailTrace_1074506 : CollatzResearch.WordTrace tailWord_1074506 prefixEnd_1074506 551738044140078224033443 := by
  unfold tailWord_1074506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9797613361313936964962843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26126968963503831906567581 9797613361313936964962843)
  ·
    refine ⟨14696420041970905447444265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9797613361313936964962843 14696420041970905447444265)
    ·
      refine ⟨11022315031478179085583199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14696420041970905447444265 11022315031478179085583199)
      ·
        refine ⟨16533472547217268628374799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11022315031478179085583199 16533472547217268628374799)
        ·
          refine ⟨24800208820825902942562199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16533472547217268628374799 24800208820825902942562199)
          ·
            refine ⟨37200313231238854413843299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24800208820825902942562199 37200313231238854413843299)
            ·
              refine ⟨55800469846858281620764949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37200313231238854413843299 55800469846858281620764949)
              ·
                refine ⟨2615647024071481950973357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55800469846858281620764949 2615647024071481950973357)
                ·
                  refine ⟨980867634026805731615009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2615647024071481950973357 980867634026805731615009)
                  ·
                    refine ⟨735650725520104298711257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 980867634026805731615009 735650725520104298711257)
                    ·
                      refine ⟨551738044140078224033443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735650725520104298711257 551738044140078224033443)
                      ·
                        rfl

theorem cell23_1074506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_1074506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074506 prefixEnd_1074506 := by exact prefixLift 1074506
  have htrace : WordTrace (prefixWord ++ tailWord_1074506) baseStart_1074506 baseEnd_1074506 := by
    simpa [prefixWord, tailWord_1074506, baseEnd_1074506] using wordTrace_append hprefix tailTrace_1074506
  have hstable : (prefixWord ++ tailWord_1074506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074506).length < 2 ^ (prefixWord ++ tailWord_1074506).sum := by decide
  have hdescent : baseEnd_1074506 < baseStart_1074506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074519 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1074519 : Nat := 118140960795 + 1074519 * 2 ^ 59
def prefixEnd_1074519 : Nat := 4983230072969 + 3 ^ 40 * 1074519 * 2
def baseEnd_1074519 : Nat := 551744719388586673170883

theorem tailTrace_1074519 : CollatzResearch.WordTrace tailWord_1074519 prefixEnd_1074519 551744719388586673170883 := by
  unfold tailWord_1074519
  simp only [CollatzResearch.WordTrace]
  refine ⟨39190927594208651080074611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26127285062805767386716407 39190927594208651080074611)
  ·
    refine ⟨58786391391312976620111917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39190927594208651080074611 58786391391312976620111917)
    ·
      refine ⟨22044896771742366232541969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58786391391312976620111917 22044896771742366232541969)
      ·
        refine ⟨16533672578806774674406477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22044896771742366232541969 16533672578806774674406477)
        ·
          refine ⟨6200127217052540502902429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16533672578806774674406477 6200127217052540502902429)
          ·
            refine ⟨2325047706394702688588411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6200127217052540502902429 2325047706394702688588411)
            ·
              refine ⟨3487571559592054032882617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325047706394702688588411 3487571559592054032882617)
              ·
                refine ⟨2615678669694040524661963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3487571559592054032882617 2615678669694040524661963)
                ·
                  refine ⟨3923518004541060786992945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615678669694040524661963 3923518004541060786992945)
                  ·
                    refine ⟨2942638503405795590244709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923518004541060786992945 2942638503405795590244709)
                    ·
                      refine ⟨551744719388586673170883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2942638503405795590244709 551744719388586673170883)
                      ·
                        rfl

theorem cell23_1074519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1074519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074519 prefixEnd_1074519 := by exact prefixLift 1074519
  have htrace : WordTrace (prefixWord ++ tailWord_1074519) baseStart_1074519 baseEnd_1074519 := by
    simpa [prefixWord, tailWord_1074519, baseEnd_1074519] using wordTrace_append hprefix tailTrace_1074519
  have hstable : (prefixWord ++ tailWord_1074519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074519).length < 2 ^ (prefixWord ++ tailWord_1074519).sum := by decide
  have hdescent : baseEnd_1074519 < baseStart_1074519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074540 : List Nat := [2, 2, 1, 1, 5, 2, 1, 4, 1, 2, 2]
def baseStart_1074540 : Nat := 118140960795 + 1074540 * 2 ^ 59
def prefixEnd_1074540 : Nat := 4983230072969 + 3 ^ 40 * 1074540 * 2
def baseEnd_1074540 : Nat := 551755502482331091008287

theorem tailTrace_1074540 : CollatzResearch.WordTrace tailWord_1074540 prefixEnd_1074540 551755502482331091008287 := by
  unfold tailWord_1074540
  simp only [CollatzResearch.WordTrace]
  refine ⟨19595846763566285833294537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26127795684755047777726049 19595846763566285833294537)
  ·
    refine ⟨14696885072674714374970903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19595846763566285833294537 14696885072674714374970903)
    ·
      refine ⟨22045327609012071562456355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14696885072674714374970903 22045327609012071562456355)
      ·
        refine ⟨33067991413518107343684533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22045327609012071562456355 33067991413518107343684533)
        ·
          refine ⟨3100124195017322563470425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33067991413518107343684533 3100124195017322563470425)
          ·
            refine ⟨2325093146262991922602819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3100124195017322563470425 2325093146262991922602819)
            ·
              refine ⟨3487639719394487883904229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325093146262991922602819 3487639719394487883904229)
              ·
                refine ⟨653932447386466478232043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3487639719394487883904229 653932447386466478232043)
                ·
                  refine ⟨980898671079699717348065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653932447386466478232043 980898671079699717348065)
                  ·
                    refine ⟨735674003309774788011049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 980898671079699717348065 735674003309774788011049)
                    ·
                      refine ⟨551755502482331091008287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735674003309774788011049 551755502482331091008287)
                      ·
                        rfl

theorem cell23_1074540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_1074540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074540 prefixEnd_1074540 := by exact prefixLift 1074540
  have htrace : WordTrace (prefixWord ++ tailWord_1074540) baseStart_1074540 baseEnd_1074540 := by
    simpa [prefixWord, tailWord_1074540, baseEnd_1074540] using wordTrace_append hprefix tailTrace_1074540
  have hstable : (prefixWord ++ tailWord_1074540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074540).length < 2 ^ (prefixWord ++ tailWord_1074540).sum := by decide
  have hdescent : baseEnd_1074540 < baseStart_1074540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074556 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_1074556 : Nat := 118140960795 + 1074556 * 2 ^ 59
def prefixEnd_1074556 : Nat := 4983230072969 + 3 ^ 40 * 1074556 * 2
def baseEnd_1074556 : Nat := 551763718172803028408213

theorem tailTrace_1074556 : CollatzResearch.WordTrace tailWord_1074556 prefixEnd_1074556 551763718172803028408213 := by
  unfold tailWord_1074556
  simp only [CollatzResearch.WordTrace]
  refine ⟨19596138547537303199585761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26128184730049737599447681 19596138547537303199585761)
  ·
    refine ⟨14697103910652977399689321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19596138547537303199585761 14697103910652977399689321)
    ·
      refine ⟨11022827932989733049766991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14697103910652977399689321 11022827932989733049766991)
      ·
        refine ⟨16534241899484599574650487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11022827932989733049766991 16534241899484599574650487)
        ·
          refine ⟨24801362849226899361975731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16534241899484599574650487 24801362849226899361975731)
          ·
            refine ⟨37202044273840349042963597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24801362849226899361975731 37202044273840349042963597)
            ·
              refine ⟨13950766602690130891111349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37202044273840349042963597 13950766602690130891111349)
              ·
                refine ⟨1307884369002199771041689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13950766602690130891111349 1307884369002199771041689)
                ·
                  refine ⟨980913276751649828281267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1307884369002199771041689 980913276751649828281267)
                  ·
                    refine ⟨1471369915127474742421901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 980913276751649828281267 1471369915127474742421901)
                    ·
                      refine ⟨551763718172803028408213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1471369915127474742421901 551763718172803028408213)
                      ·
                        rfl

theorem cell23_1074556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_1074556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074556 prefixEnd_1074556 := by exact prefixLift 1074556
  have htrace : WordTrace (prefixWord ++ tailWord_1074556) baseStart_1074556 baseEnd_1074556 := by
    simpa [prefixWord, tailWord_1074556, baseEnd_1074556] using wordTrace_append hprefix tailTrace_1074556
  have hstable : (prefixWord ++ tailWord_1074556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074556).length < 2 ^ (prefixWord ++ tailWord_1074556).sum := by decide
  have hdescent : baseEnd_1074556 < baseStart_1074556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074572 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_1074572 : Nat := 118140960795 + 1074572 * 2 ^ 59
def prefixEnd_1074572 : Nat := 4983230072969 + 3 ^ 40 * 1074572 * 2
def baseEnd_1074572 : Nat := 183923977954424988602713

theorem tailTrace_1074572 : CollatzResearch.WordTrace tailWord_1074572 prefixEnd_1074572 183923977954424988602713 := by
  unfold tailWord_1074572
  simp only [CollatzResearch.WordTrace]
  refine ⟨19596430331508320565876985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26128573775344427421169313 19596430331508320565876985)
  ·
    refine ⟨14697322748631240424407739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19596430331508320565876985 14697322748631240424407739)
    ·
      refine ⟨22045984122946860636611609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14697322748631240424407739 22045984122946860636611609)
      ·
        refine ⟨16534488092210145477458707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22045984122946860636611609 16534488092210145477458707)
        ·
          refine ⟨24801732138315218216188061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16534488092210145477458707 24801732138315218216188061)
          ·
            refine ⟨9300649551868206831070523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24801732138315218216188061 9300649551868206831070523)
            ·
              refine ⟨13950974327802310246605785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9300649551868206831070523 13950974327802310246605785)
              ·
                refine ⟨10463230745851732684954339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13950974327802310246605785 10463230745851732684954339)
                ·
                  refine ⟨15694846118777599027431509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10463230745851732684954339 15694846118777599027431509)
                  ·
                    refine ⟨183923977954424988602713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15694846118777599027431509 183923977954424988602713)
                    ·
                      rfl

theorem cell23_1074572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_1074572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074572 prefixEnd_1074572 := by exact prefixLift 1074572
  have htrace : WordTrace (prefixWord ++ tailWord_1074572) baseStart_1074572 baseEnd_1074572 := by
    simpa [prefixWord, tailWord_1074572, baseEnd_1074572] using wordTrace_append hprefix tailTrace_1074572
  have hstable : (prefixWord ++ tailWord_1074572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074572).length < 2 ^ (prefixWord ++ tailWord_1074572).sum := by decide
  have hdescent : baseEnd_1074572 < baseStart_1074572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074589 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1074589 : Nat := 118140960795 + 1074589 * 2 ^ 59
def prefixEnd_1074589 : Nat := 4983230072969 + 3 ^ 40 * 1074589 * 2
def baseEnd_1074589 : Nat := 183926887678133799765187

theorem tailTrace_1074589 : CollatzResearch.WordTrace tailWord_1074589 prefixEnd_1074589 183926887678133799765187 := by
  unfold tailWord_1074589
  simp only [CollatzResearch.WordTrace]
  refine ⟨39193480703955053035122821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26128987135970035356748547 39193480703955053035122821)
  ·
    refine ⟨7348777631991572444085529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39193480703955053035122821 7348777631991572444085529)
    ·
      refine ⟨5511583223993679333064147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7348777631991572444085529 5511583223993679333064147)
      ·
        refine ⟨8267374835990518999596221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5511583223993679333064147 8267374835990518999596221)
        ·
          refine ⟨3100265563496444624848583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8267374835990518999596221 3100265563496444624848583)
          ·
            refine ⟨4650398345244666937272875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100265563496444624848583 4650398345244666937272875)
            ·
              refine ⟨6975597517867000405909313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650398345244666937272875 6975597517867000405909313)
              ·
                refine ⟨5231698138400250304431985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6975597517867000405909313 5231698138400250304431985)
                ·
                  refine ⟨3923773603800187728323989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5231698138400250304431985 3923773603800187728323989)
                  ·
                    refine ⟨183926887678133799765187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3923773603800187728323989 183926887678133799765187)
                    ·
                      rfl

theorem cell23_1074589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1074589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074589 prefixEnd_1074589 := by exact prefixLift 1074589
  have htrace : WordTrace (prefixWord ++ tailWord_1074589) baseStart_1074589 baseEnd_1074589 := by
    simpa [prefixWord, tailWord_1074589, baseEnd_1074589] using wordTrace_append hprefix tailTrace_1074589
  have hstable : (prefixWord ++ tailWord_1074589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074589).length < 2 ^ (prefixWord ++ tailWord_1074589).sum := by decide
  have hdescent : baseEnd_1074589 < baseStart_1074589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074590 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1074590 : Nat := 118140960795 + 1074590 * 2 ^ 59
def prefixEnd_1074590 : Nat := 4983230072969 + 3 ^ 40 * 1074590 * 2
def baseEnd_1074590 : Nat := 551781176515055895383057

theorem tailTrace_1074590 : CollatzResearch.WordTrace tailWord_1074590 prefixEnd_1074590 551781176515055895383057 := by
  unfold tailWord_1074590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899189647118928775738653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26129011451300953470606149 4899189647118928775738653)
  ·
    refine ⟨1837196117669598290901995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4899189647118928775738653 1837196117669598290901995)
    ·
      refine ⟨2755794176504397436352993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1837196117669598290901995 2755794176504397436352993)
      ·
        refine ⟨2066845632378298077264745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2755794176504397436352993 2066845632378298077264745)
        ·
          refine ⟨1550134224283723557948559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2066845632378298077264745 1550134224283723557948559)
          ·
            refine ⟨2325201336425585336922839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550134224283723557948559 2325201336425585336922839)
            ·
              refine ⟨3487802004638378005384259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325201336425585336922839 3487802004638378005384259)
              ·
                refine ⟨5231703006957567008076389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487802004638378005384259 5231703006957567008076389)
                ·
                  refine ⟨980944313804543814014323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5231703006957567008076389 980944313804543814014323)
                  ·
                    refine ⟨1471416470706815721021485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 980944313804543814014323 1471416470706815721021485)
                    ·
                      refine ⟨551781176515055895383057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1471416470706815721021485 551781176515055895383057)
                      ·
                        rfl

theorem cell23_1074590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1074590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074590 prefixEnd_1074590 := by exact prefixLift 1074590
  have htrace : WordTrace (prefixWord ++ tailWord_1074590) baseStart_1074590 baseEnd_1074590 := by
    simpa [prefixWord, tailWord_1074590, baseEnd_1074590] using wordTrace_append hprefix tailTrace_1074590
  have hstable : (prefixWord ++ tailWord_1074590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074590).length < 2 ^ (prefixWord ++ tailWord_1074590).sum := by decide
  have hdescent : baseEnd_1074590 < baseStart_1074590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074609 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1074609 : Nat := 118140960795 + 1074609 * 2 ^ 59
def prefixEnd_1074609 : Nat := 4983230072969 + 3 ^ 40 * 1074609 * 2
def baseEnd_1074609 : Nat := 551790932647491321045469

theorem tailTrace_1074609 : CollatzResearch.WordTrace tailWord_1074609 prefixEnd_1074609 551790932647491321045469 := by
  unfold tailWord_1074609
  simp only [CollatzResearch.WordTrace]
  refine ⟨39194210163882596450850881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26129473442588397633900587 39194210163882596450850881)
  ·
    refine ⟨29395657622911947338138161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39194210163882596450850881 29395657622911947338138161)
    ·
      refine ⟨22046743217183960503603621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29395657622911947338138161 22046743217183960503603621)
      ·
        refine ⟨4133764353221992594425679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22046743217183960503603621 4133764353221992594425679)
        ·
          refine ⟨6200646529832988891638519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4133764353221992594425679 6200646529832988891638519)
          ·
            refine ⟨9300969794749483337457779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6200646529832988891638519 9300969794749483337457779)
            ·
              refine ⟨13951454692124225006186669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9300969794749483337457779 13951454692124225006186669)
              ·
                refine ⟨5231795509546584377320001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13951454692124225006186669 5231795509546584377320001)
                ·
                  refine ⟨3923846632159938282990001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5231795509546584377320001 3923846632159938282990001)
                  ·
                    refine ⟨2942884974119953712242501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923846632159938282990001 2942884974119953712242501)
                    ·
                      refine ⟨551790932647491321045469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2942884974119953712242501 551790932647491321045469)
                      ·
                        rfl

theorem cell23_1074609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1074609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074609 prefixEnd_1074609 := by exact prefixLift 1074609
  have htrace : WordTrace (prefixWord ++ tailWord_1074609) baseStart_1074609 baseEnd_1074609 := by
    simpa [prefixWord, tailWord_1074609, baseEnd_1074609] using wordTrace_append hprefix tailTrace_1074609
  have hstable : (prefixWord ++ tailWord_1074609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074609).length < 2 ^ (prefixWord ++ tailWord_1074609).sum := by decide
  have hdescent : baseEnd_1074609 < baseStart_1074609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074613 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_1074613 : Nat := 118140960795 + 1074613 * 2 ^ 59
def prefixEnd_1074613 : Nat := 4983230072969 + 3 ^ 40 * 1074613 * 2
def baseEnd_1074613 : Nat := 551792986570109305395451

theorem tailTrace_1074613 : CollatzResearch.WordTrace tailWord_1074613 prefixEnd_1074613 551792986570109305395451 := by
  unfold tailWord_1074613
  simp only [CollatzResearch.WordTrace]
  refine ⟨39194356055868105133996493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26129570703912070089330995 39194356055868105133996493)
  ·
    refine ⟨14697883520950539425248685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39194356055868105133996493 14697883520950539425248685)
    ·
      refine ⟨5511706320356452284468257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14697883520950539425248685 5511706320356452284468257)
      ·
        refine ⟨4133779740267339213351193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5511706320356452284468257 4133779740267339213351193)
        ·
          refine ⟨3100334805200504410013395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4133779740267339213351193 3100334805200504410013395)
          ·
            refine ⟨4650502207800756615020093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100334805200504410013395 4650502207800756615020093)
            ·
              refine ⟨1743938327925283730632535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4650502207800756615020093 1743938327925283730632535)
              ·
                refine ⟨2615907491887925595948803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743938327925283730632535 2615907491887925595948803)
                ·
                  refine ⟨3923861237831888393923205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615907491887925595948803 3923861237831888393923205)
                  ·
                    refine ⟨735723982093479073860601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3923861237831888393923205 735723982093479073860601)
                    ·
                      refine ⟨551792986570109305395451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735723982093479073860601 551792986570109305395451)
                      ·
                        rfl

theorem cell23_1074613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_1074613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074613 prefixEnd_1074613 := by exact prefixLift 1074613
  have htrace : WordTrace (prefixWord ++ tailWord_1074613) baseStart_1074613 baseEnd_1074613 := by
    simpa [prefixWord, tailWord_1074613, baseEnd_1074613] using wordTrace_append hprefix tailTrace_1074613
  have hstable : (prefixWord ++ tailWord_1074613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074613).length < 2 ^ (prefixWord ++ tailWord_1074613).sum := by decide
  have hdescent : baseEnd_1074613 < baseStart_1074613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074649 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 4, 5]
def baseStart_1074649 : Nat := 118140960795 + 1074649 * 2 ^ 59
def prefixEnd_1074649 : Nat := 4983230072969 + 3 ^ 40 * 1074649 * 2
def baseEnd_1074649 : Nat := 183937157291223721515095

theorem tailTrace_1074649 : CollatzResearch.WordTrace tailWord_1074649 prefixEnd_1074649 183937157291223721515095 := by
  unfold tailWord_1074649
  simp only [CollatzResearch.WordTrace]
  refine ⟨39195669083737683282307001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26130446055825122188204667 39195669083737683282307001)
  ·
    refine ⟨29396751812803262461730251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39195669083737683282307001 29396751812803262461730251)
    ·
      refine ⟨44095127719204893692595377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29396751812803262461730251 44095127719204893692595377)
      ·
        refine ⟨33071345789403670269446533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44095127719204893692595377 33071345789403670269446533)
        ·
          refine ⟨6200877335513188175521225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33071345789403670269446533 6200877335513188175521225)
          ·
            refine ⟨4650658001634891131640919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6200877335513188175521225 4650658001634891131640919)
            ·
              refine ⟨6975987002452336697461379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650658001634891131640919 6975987002452336697461379)
              ·
                refine ⟨10463980503678505046192069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6975987002452336697461379 10463980503678505046192069)
                ·
                  refine ⟨1961996344439719696161013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10463980503678505046192069 1961996344439719696161013)
                  ·
                    refine ⟨183937157291223721515095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1961996344439719696161013 183937157291223721515095)
                    ·
                      rfl

theorem cell23_1074649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_1074649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074649 prefixEnd_1074649 := by exact prefixLift 1074649
  have htrace : WordTrace (prefixWord ++ tailWord_1074649) baseStart_1074649 baseEnd_1074649 := by
    simpa [prefixWord, tailWord_1074649, baseEnd_1074649] using wordTrace_append hprefix tailTrace_1074649
  have hstable : (prefixWord ++ tailWord_1074649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074649).length < 2 ^ (prefixWord ++ tailWord_1074649).sum := by decide
  have hdescent : baseEnd_1074649 < baseStart_1074649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074659 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1074659 : Nat := 118140960795 + 1074659 * 2 ^ 59
def prefixEnd_1074659 : Nat := 4983230072969 + 3 ^ 40 * 1074659 * 2
def baseEnd_1074659 : Nat := 551816606680216125420239

theorem tailTrace_1074659 : CollatzResearch.WordTrace tailWord_1074659 prefixEnd_1074659 551816606680216125420239 := by
  unfold tailWord_1074659
  simp only [CollatzResearch.WordTrace]
  refine ⟨39196033813701454990171031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26130689209134303326780687 39196033813701454990171031)
  ·
    refine ⟨58794050720552182485256547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39196033813701454990171031 58794050720552182485256547)
    ·
      refine ⟨88191076080828273727884821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58794050720552182485256547 88191076080828273727884821)
      ·
        refine ⟨4133956691288825330994601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88191076080828273727884821 4133956691288825330994601)
        ·
          refine ⟨3100467518466618998245951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4133956691288825330994601 3100467518466618998245951)
          ·
            refine ⟨4650701277699928497368927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100467518466618998245951 4650701277699928497368927)
            ·
              refine ⟨6976051916549892746053391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650701277699928497368927 6976051916549892746053391)
              ·
                refine ⟨10464077874824839119080087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6976051916549892746053391 10464077874824839119080087)
                ·
                  refine ⟨15696116812237258678620131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10464077874824839119080087 15696116812237258678620131)
                  ·
                    refine ⟨23544175218355888017930197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15696116812237258678620131 23544175218355888017930197)
                    ·
                      refine ⟨551816606680216125420239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23544175218355888017930197 551816606680216125420239)
                      ·
                        rfl

theorem cell23_1074659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1074659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074659 prefixEnd_1074659 := by exact prefixLift 1074659
  have htrace : WordTrace (prefixWord ++ tailWord_1074659) baseStart_1074659 baseEnd_1074659 := by
    simpa [prefixWord, tailWord_1074659, baseEnd_1074659] using wordTrace_append hprefix tailTrace_1074659
  have hstable : (prefixWord ++ tailWord_1074659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074659).length < 2 ^ (prefixWord ++ tailWord_1074659).sum := by decide
  have hdescent : baseEnd_1074659 < baseStart_1074659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074753 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1074753 : Nat := 118140960795 + 1074753 * 2 ^ 59
def prefixEnd_1074753 : Nat := 4983230072969 + 3 ^ 40 * 1074753 * 2
def baseEnd_1074753 : Nat := 551864873861738757644807

theorem tailTrace_1074753 : CollatzResearch.WordTrace tailWord_1074753 prefixEnd_1074753 551864873861738757644807 := by
  unfold tailWord_1074753
  simp only [CollatzResearch.WordTrace]
  refine ⟨39199462275360909044092913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26132974850240606029395275 39199462275360909044092913)
  ·
    refine ⟨29399596706520681783069685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39199462275360909044092913 29399596706520681783069685)
    ·
      refine ⟨2756212191236313917162783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29399596706520681783069685 2756212191236313917162783)
      ·
        refine ⟨4134318286854470875744175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756212191236313917162783 4134318286854470875744175)
        ·
          refine ⟨6201477430281706313616263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4134318286854470875744175 6201477430281706313616263)
          ·
            refine ⟨9302216145422559470424395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6201477430281706313616263 9302216145422559470424395)
            ·
              refine ⟨13953324218133839205636593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9302216145422559470424395 13953324218133839205636593)
              ·
                refine ⟨10464993163600379404227445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13953324218133839205636593 10464993163600379404227445)
                ·
                  refine ⟨981093109087535569146323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10464993163600379404227445 981093109087535569146323)
                  ·
                    refine ⟨1471639663631303353719485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 981093109087535569146323 1471639663631303353719485)
                    ·
                      refine ⟨551864873861738757644807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1471639663631303353719485 551864873861738757644807)
                      ·
                        rfl

theorem cell23_1074753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1074753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074753 prefixEnd_1074753 := by exact prefixLift 1074753
  have htrace : WordTrace (prefixWord ++ tailWord_1074753) baseStart_1074753 baseEnd_1074753 := by
    simpa [prefixWord, tailWord_1074753, baseEnd_1074753] using wordTrace_append hprefix tailTrace_1074753
  have hstable : (prefixWord ++ tailWord_1074753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074753).length < 2 ^ (prefixWord ++ tailWord_1074753).sum := by decide
  have hdescent : baseEnd_1074753 < baseStart_1074753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074770 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_1074770 : Nat := 118140960795 + 1074770 * 2 ^ 59
def prefixEnd_1074770 : Nat := 4983230072969 + 3 ^ 40 * 1074770 * 2
def baseEnd_1074770 : Nat := 551873603032865191132229

theorem tailTrace_1074770 : CollatzResearch.WordTrace tailWord_1074770 prefixEnd_1074770 551873603032865191132229 := by
  unfold tailWord_1074770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9800020579074830236865441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26133388210866213964974509 9800020579074830236865441)
  ·
    refine ⟨7350015434306122677649081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9800020579074830236865441 7350015434306122677649081)
    ·
      refine ⟨5512511575729592008236811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7350015434306122677649081 5512511575729592008236811)
      ·
        refine ⟨8268767363594388012355217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5512511575729592008236811 8268767363594388012355217)
        ·
          refine ⟨6201575522695791009266413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8268767363594388012355217 6201575522695791009266413)
          ·
            refine ⟨2325590821010921628474905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6201575522695791009266413 2325590821010921628474905)
            ·
              refine ⟨1744193115758191221356179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325590821010921628474905 1744193115758191221356179)
              ·
                refine ⟨2616289673637286832034269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744193115758191221356179 2616289673637286832034269)
                ·
                  refine ⟨981108627613982562012851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2616289673637286832034269 981108627613982562012851)
                  ·
                    refine ⟨1471662941420973843019277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 981108627613982562012851 1471662941420973843019277)
                    ·
                      refine ⟨551873603032865191132229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1471662941420973843019277 551873603032865191132229)
                      ·
                        rfl

theorem cell23_1074770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_1074770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074770 prefixEnd_1074770 := by exact prefixLift 1074770
  have htrace : WordTrace (prefixWord ++ tailWord_1074770) baseStart_1074770 baseEnd_1074770 := by
    simpa [prefixWord, tailWord_1074770, baseEnd_1074770] using wordTrace_append hprefix tailTrace_1074770
  have hstable : (prefixWord ++ tailWord_1074770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074770).length < 2 ^ (prefixWord ++ tailWord_1074770).sum := by decide
  have hdescent : baseEnd_1074770 < baseStart_1074770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074813 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_1074813 : Nat := 118140960795 + 1074813 * 2 ^ 59
def prefixEnd_1074813 : Nat := 4983230072969 + 3 ^ 40 * 1074813 * 2
def baseEnd_1074813 : Nat := 551895682701008522894531

theorem tailTrace_1074813 : CollatzResearch.WordTrace tailWord_1074813 prefixEnd_1074813 551895682701008522894531 := by
  unfold tailWord_1074813
  simp only [CollatzResearch.WordTrace]
  refine ⟨39201650655143539291277093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26134433770095692860851395 39201650655143539291277093)
  ·
    refine ⟨7350309497839413617114455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39201650655143539291277093 7350309497839413617114455)
    ·
      refine ⟨11025464246759120425671683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7350309497839413617114455 11025464246759120425671683)
      ·
        refine ⟨16538196370138680638507525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11025464246759120425671683 16538196370138680638507525)
        ·
          refine ⟨3100911819401002619720161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16538196370138680638507525 3100911819401002619720161)
          ·
            refine ⟨2325683864550751964790121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3100911819401002619720161 2325683864550751964790121)
            ·
              refine ⟨1744262898413063973592591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325683864550751964790121 1744262898413063973592591)
              ·
                refine ⟨2616394347619595960388887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744262898413063973592591 2616394347619595960388887)
                ·
                  refine ⟨3924591521429393940583331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616394347619595960388887 3924591521429393940583331)
                  ·
                    refine ⟨5886887282144090910874997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3924591521429393940583331 5886887282144090910874997)
                    ·
                      refine ⟨551895682701008522894531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5886887282144090910874997 551895682701008522894531)
                      ·
                        rfl

theorem cell23_1074813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_1074813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074813 prefixEnd_1074813 := by exact prefixLift 1074813
  have htrace : WordTrace (prefixWord ++ tailWord_1074813) baseStart_1074813 baseEnd_1074813 := by
    simpa [prefixWord, tailWord_1074813, baseEnd_1074813] using wordTrace_append hprefix tailTrace_1074813
  have hstable : (prefixWord ++ tailWord_1074813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074813).length < 2 ^ (prefixWord ++ tailWord_1074813).sum := by decide
  have hdescent : baseEnd_1074813 < baseStart_1074813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074906 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 9]
def baseStart_1074906 : Nat := 118140960795 + 1074906 * 2 ^ 59
def prefixEnd_1074906 : Nat := 4983230072969 + 3 ^ 40 * 1074906 * 2
def baseEnd_1074906 : Nat := 61327048489097406559067

theorem tailTrace_1074906 : CollatzResearch.WordTrace tailWord_1074906 prefixEnd_1074906 61327048489097406559067 := by
  unfold tailWord_1074906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801260660951654043603143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26136695095871077449608381 9801260660951654043603143)
  ·
    refine ⟨14701890991427481065404715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9801260660951654043603143 14701890991427481065404715)
    ·
      refine ⟨22052836487141221598107073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14701890991427481065404715 22052836487141221598107073)
      ·
        refine ⟨16539627365355916198580305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22052836487141221598107073 16539627365355916198580305)
        ·
          refine ⟨12404720524016937148935229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16539627365355916198580305 12404720524016937148935229)
          ·
            refine ⟨4651770196506351430850711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12404720524016937148935229 4651770196506351430850711)
            ·
              refine ⟨6977655294759527146276067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651770196506351430850711 6977655294759527146276067)
              ·
                refine ⟨10466482942139290719414101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6977655294759527146276067 10466482942139290719414101)
                ·
                  refine ⟨61327048489097406559067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10466482942139290719414101 61327048489097406559067)
                  ·
                    rfl

theorem cell23_1074906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_1074906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074906 prefixEnd_1074906 := by exact prefixLift 1074906
  have htrace : WordTrace (prefixWord ++ tailWord_1074906) baseStart_1074906 baseEnd_1074906 := by
    simpa [prefixWord, tailWord_1074906, baseEnd_1074906] using wordTrace_append hprefix tailTrace_1074906
  have hstable : (prefixWord ++ tailWord_1074906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074906).length < 2 ^ (prefixWord ++ tailWord_1074906).sum := by decide
  have hdescent : baseEnd_1074906 < baseStart_1074906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074923 : List Nat := [1, 1, 1, 1, 2, 4, 3, 5, 5]
def baseStart_1074923 : Nat := 118140960795 + 1074923 * 2 ^ 59
def prefixEnd_1074923 : Nat := 4983230072969 + 3 ^ 40 * 1074923 * 2
def baseEnd_1074923 : Nat := 61328018397000343613225

theorem tailTrace_1074923 : CollatzResearch.WordTrace tailWord_1074923 prefixEnd_1074923 61328018397000343613225 := by
  unfold tailWord_1074923
  simp only [CollatzResearch.WordTrace]
  refine ⟨39205662684745028077781423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26137108456496685385187615 39205662684745028077781423)
  ·
    refine ⟨58808494027117542116672135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39205662684745028077781423 58808494027117542116672135)
    ·
      refine ⟨88212741040676313175008203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58808494027117542116672135 88212741040676313175008203)
      ·
        refine ⟨132319111561014469762512305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88212741040676313175008203 132319111561014469762512305)
        ·
          refine ⟨99239333670760852321884229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132319111561014469762512305 99239333670760852321884229)
          ·
            refine ⟨18607375063267659810353293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99239333670760852321884229 18607375063267659810353293)
            ·
              refine ⟨6977765648725372428882485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18607375063267659810353293 6977765648725372428882485)
              ·
                refine ⟨654165529568003665207733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6977765648725372428882485 654165529568003665207733)
                ·
                  refine ⟨61328018397000343613225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 654165529568003665207733 61328018397000343613225)
                  ·
                    rfl

theorem cell23_1074923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 5].length) (baseStart_1074923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074923 prefixEnd_1074923 := by exact prefixLift 1074923
  have htrace : WordTrace (prefixWord ++ tailWord_1074923) baseStart_1074923 baseEnd_1074923 := by
    simpa [prefixWord, tailWord_1074923, baseEnd_1074923] using wordTrace_append hprefix tailTrace_1074923
  have hstable : (prefixWord ++ tailWord_1074923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074923).length < 2 ^ (prefixWord ++ tailWord_1074923).sum := by decide
  have hdescent : baseEnd_1074923 < baseStart_1074923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074934 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_1074934 : Nat := 118140960795 + 1074934 * 2 ^ 59
def prefixEnd_1074934 : Nat := 4983230072969 + 3 ^ 40 * 1074934 * 2
def baseEnd_1074934 : Nat := 551957813860202549481475

theorem tailTrace_1074934 : CollatzResearch.WordTrace tailWord_1074934 prefixEnd_1074934 551957813860202549481475 := by
  unfold tailWord_1074934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450378992981573559776991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26137375925136784637621237 2450378992981573559776991)
  ·
    refine ⟨3675568489472360339665487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2450378992981573559776991 3675568489472360339665487)
    ·
      refine ⟨5513352734208540509498231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3675568489472360339665487 5513352734208540509498231)
      ·
        refine ⟨8270029101312810764247347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5513352734208540509498231 8270029101312810764247347)
        ·
          refine ⟨12405043651969216146371021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8270029101312810764247347 12405043651969216146371021)
          ·
            refine ⟨4651891369488456054889133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12405043651969216146371021 4651891369488456054889133)
            ·
              refine ⟨1744459263558171020583425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4651891369488456054889133 1744459263558171020583425)
              ·
                refine ⟨1308344447668628265437569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744459263558171020583425 1308344447668628265437569)
                ·
                  refine ⟨981258335751471199078177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1308344447668628265437569 981258335751471199078177)
                  ·
                    refine ⟨735943751813603399308633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 981258335751471199078177 735943751813603399308633)
                    ·
                      refine ⟨551957813860202549481475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735943751813603399308633 551957813860202549481475)
                      ·
                        rfl

theorem cell23_1074934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_1074934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074934 prefixEnd_1074934 := by exact prefixLift 1074934
  have htrace : WordTrace (prefixWord ++ tailWord_1074934) baseStart_1074934 baseEnd_1074934 := by
    simpa [prefixWord, tailWord_1074934, baseEnd_1074934] using wordTrace_append hprefix tailTrace_1074934
  have hstable : (prefixWord ++ tailWord_1074934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074934).length < 2 ^ (prefixWord ++ tailWord_1074934).sum := by decide
  have hdescent : baseEnd_1074934 < baseStart_1074934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074943 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 7, 2]
def baseStart_1074943 : Nat := 118140960795 + 1074943 * 2 ^ 59
def prefixEnd_1074943 : Nat := 4983230072969 + 3 ^ 40 * 1074943 * 2
def baseEnd_1074943 : Nat := 551962435186093014268933

theorem tailTrace_1074943 : CollatzResearch.WordTrace tailWord_1074943 prefixEnd_1074943 551962435186093014268933 := by
  unfold tailWord_1074943
  simp only [CollatzResearch.WordTrace]
  refine ⟨39206392144672571493509483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26137594763115047662339655 39206392144672571493509483)
  ·
    refine ⟨58809588217008857240264225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39206392144672571493509483 58809588217008857240264225)
    ·
      refine ⟨44107191162756642930198169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58809588217008857240264225 44107191162756642930198169)
      ·
        refine ⟨33080393372067482197648627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44107191162756642930198169 33080393372067482197648627)
        ·
          refine ⟨49620590058101223296472941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33080393372067482197648627 49620590058101223296472941)
          ·
            refine ⟨18607721271787958736177353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49620590058101223296472941 18607721271787958736177353)
            ·
              refine ⟨13955790953840969052133015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18607721271787958736177353 13955790953840969052133015)
              ·
                refine ⟨20933686430761453578199523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13955790953840969052133015 20933686430761453578199523)
                ·
                  refine ⟨31400529646142180367299285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20933686430761453578199523 31400529646142180367299285)
                  ·
                    refine ⟨735949913581457352358577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31400529646142180367299285 735949913581457352358577)
                    ·
                      refine ⟨551962435186093014268933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735949913581457352358577 551962435186093014268933)
                      ·
                        rfl

theorem cell23_1074943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_1074943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074943 prefixEnd_1074943 := by exact prefixLift 1074943
  have htrace : WordTrace (prefixWord ++ tailWord_1074943) baseStart_1074943 baseEnd_1074943 := by
    simpa [prefixWord, tailWord_1074943, baseEnd_1074943] using wordTrace_append hprefix tailTrace_1074943
  have hstable : (prefixWord ++ tailWord_1074943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074943).length < 2 ^ (prefixWord ++ tailWord_1074943).sum := by decide
  have hdescent : baseEnd_1074943 < baseStart_1074943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074951 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1074951 : Nat := 118140960795 + 1074951 * 2 ^ 59
def prefixEnd_1074951 : Nat := 4983230072969 + 3 ^ 40 * 1074951 * 2
def baseEnd_1074951 : Nat := 551966543031328982968897

theorem tailTrace_1074951 : CollatzResearch.WordTrace tailWord_1074951 prefixEnd_1074951 551966543031328982968897 := by
  unfold tailWord_1074951
  simp only [CollatzResearch.WordTrace]
  refine ⟨39206683928643588859800707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26137789285762392573200471 39206683928643588859800707)
  ·
    refine ⟨58810025892965383289701061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39206683928643588859800707 58810025892965383289701061)
    ·
      refine ⟨11026879854931009366818949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58810025892965383289701061 11026879854931009366818949)
      ·
        refine ⟨2067539972799564256278553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11026879854931009366818949 2067539972799564256278553)
        ·
          refine ⟨1550654979599673192208915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067539972799564256278553 1550654979599673192208915)
          ·
            refine ⟨2325982469399509788313373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550654979599673192208915 2325982469399509788313373)
            ·
              refine ⟨872243426024816170617515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2325982469399509788313373 872243426024816170617515)
              ·
                refine ⟨1308365139037224255926273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872243426024816170617515 1308365139037224255926273)
                ·
                  refine ⟨981273854277918191944705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1308365139037224255926273 981273854277918191944705)
                  ·
                    refine ⟨735955390708438643958529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 981273854277918191944705 735955390708438643958529)
                    ·
                      refine ⟨551966543031328982968897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 735955390708438643958529 551966543031328982968897)
                      ·
                        rfl

theorem cell23_1074951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1074951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1074951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1074951 prefixEnd_1074951 := by exact prefixLift 1074951
  have htrace : WordTrace (prefixWord ++ tailWord_1074951) baseStart_1074951 baseEnd_1074951 := by
    simpa [prefixWord, tailWord_1074951, baseEnd_1074951] using wordTrace_append hprefix tailTrace_1074951
  have hstable : (prefixWord ++ tailWord_1074951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074951).length < 2 ^ (prefixWord ++ tailWord_1074951).sum := by decide
  have hdescent : baseEnd_1074951 < baseStart_1074951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075000 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 3, 4]
def baseStart_1075000 : Nat := 118140960795 + 1075000 * 2 ^ 59
def prefixEnd_1075000 : Nat := 4983230072969 + 3 ^ 40 * 1075000 * 2
def baseEnd_1075000 : Nat := 183997234527799763752057

theorem tailTrace_1075000 : CollatzResearch.WordTrace tailWord_1075000 prefixEnd_1075000 183997234527799763752057 := by
  unfold tailWord_1075000
  simp only [CollatzResearch.WordTrace]
  refine ⟨19604235552733035114167227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26138980736977380152222969 19604235552733035114167227)
  ·
    refine ⟨29406353329099552671250841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19604235552733035114167227 29406353329099552671250841)
    ·
      refine ⟨22054764996824664503438131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29406353329099552671250841 22054764996824664503438131)
      ·
        refine ⟨33082147495236996755157197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22054764996824664503438131 33082147495236996755157197)
        ·
          refine ⟨12405805310713873783183949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33082147495236996755157197 12405805310713873783183949)
          ·
            refine ⟨4652176991517702668693981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12405805310713873783183949 4652176991517702668693981)
            ·
              refine ⟨1744566371819138500760243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4652176991517702668693981 1744566371819138500760243)
              ·
                refine ⟨2616849557728707751140365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744566371819138500760243 2616849557728707751140365)
                ·
                  refine ⟨981318584148265406677637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2616849557728707751140365 981318584148265406677637)
                  ·
                    refine ⟨183997234527799763752057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 981318584148265406677637 183997234527799763752057)
                    ·
                      rfl

theorem cell23_1075000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_1075000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075000 prefixEnd_1075000 := by exact prefixLift 1075000
  have htrace : WordTrace (prefixWord ++ tailWord_1075000) baseStart_1075000 baseEnd_1075000 := by
    simpa [prefixWord, tailWord_1075000, baseEnd_1075000] using wordTrace_append hprefix tailTrace_1075000
  have hstable : (prefixWord ++ tailWord_1075000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075000).length < 2 ^ (prefixWord ++ tailWord_1075000).sum := by decide
  have hdescent : baseEnd_1075000 < baseStart_1075000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075013 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 6]
def baseStart_1075013 : Nat := 118140960795 + 1075013 * 2 ^ 59
def prefixEnd_1075013 : Nat := 4983230072969 + 3 ^ 40 * 1075013 * 2
def baseEnd_1075013 : Nat := 61333153203545304488179

theorem tailTrace_1075013 : CollatzResearch.WordTrace tailWord_1075013 prefixEnd_1075013 61333153203545304488179 := by
  unfold tailWord_1075013
  simp only [CollatzResearch.WordTrace]
  refine ⟨39208945254418973448557693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26139296836279315632371795 39208945254418973448557693)
  ·
    refine ⟨14703354470407115043209135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39208945254418973448557693 14703354470407115043209135)
    ·
      refine ⟨22055031705610672564813703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14703354470407115043209135 22055031705610672564813703)
      ·
        refine ⟨33082547558416008847220555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22055031705610672564813703 33082547558416008847220555)
        ·
          refine ⟨49623821337624013270830833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33082547558416008847220555 49623821337624013270830833)
          ·
            refine ⟨37217866003218009953123125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49623821337624013270830833 37217866003218009953123125)
            ·
              refine ⟨3489174937801688433105293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37217866003218009953123125 3489174937801688433105293)
              ·
                refine ⟨1308440601675633162414485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3489174937801688433105293 1308440601675633162414485)
                ·
                  refine ⟨61333153203545304488179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1308440601675633162414485 61333153203545304488179)
                  ·
                    rfl

theorem cell23_1075013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_1075013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075013 prefixEnd_1075013 := by exact prefixLift 1075013
  have htrace : WordTrace (prefixWord ++ tailWord_1075013) baseStart_1075013 baseEnd_1075013 := by
    simpa [prefixWord, tailWord_1075013, baseEnd_1075013] using wordTrace_append hprefix tailTrace_1075013
  have hstable : (prefixWord ++ tailWord_1075013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075013).length < 2 ^ (prefixWord ++ tailWord_1075013).sum := by decide
  have hdescent : baseEnd_1075013 < baseStart_1075013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075097 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 1, 1, 4]
def baseStart_1075097 : Nat := 118140960795 + 1075097 * 2 ^ 59
def prefixEnd_1075097 : Nat := 4983230072969 + 3 ^ 40 * 1075097 * 2
def baseEnd_1075097 : Nat := 552041511206885411743225

theorem tailTrace_1075097 : CollatzResearch.WordTrace tailWord_1075097 prefixEnd_1075097 552041511206885411743225 := by
  unfold tailWord_1075097
  simp only [CollatzResearch.WordTrace]
  refine ⟨39212008986114655794615545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26141339324076437196410363 39212008986114655794615545)
  ·
    refine ⟨29409006739585991845961659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39212008986114655794615545 29409006739585991845961659)
    ·
      refine ⟨44113510109378987768942489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29409006739585991845961659 44113510109378987768942489)
      ·
        refine ⟨33085132582034240826706867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44113510109378987768942489 33085132582034240826706867)
        ·
          refine ⟨49627698873051361240060301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33085132582034240826706867 49627698873051361240060301)
          ·
            refine ⟨18610387077394260465022613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49627698873051361240060301 18610387077394260465022613)
            ·
              refine ⟨872361894252855959297935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18610387077394260465022613 872361894252855959297935)
              ·
                refine ⟨1308542841379283938946903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872361894252855959297935 1308542841379283938946903)
                ·
                  refine ⟨1962814262068925908420355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308542841379283938946903 1962814262068925908420355)
                  ·
                    refine ⟨2944221393103388862630533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1962814262068925908420355 2944221393103388862630533)
                    ·
                      refine ⟨552041511206885411743225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2944221393103388862630533 552041511206885411743225)
                      ·
                        rfl

theorem cell23_1075097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_1075097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075097 prefixEnd_1075097 := by exact prefixLift 1075097
  have htrace : WordTrace (prefixWord ++ tailWord_1075097) baseStart_1075097 baseEnd_1075097 := by
    simpa [prefixWord, tailWord_1075097, baseEnd_1075097] using wordTrace_append hprefix tailTrace_1075097
  have hstable : (prefixWord ++ tailWord_1075097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075097).length < 2 ^ (prefixWord ++ tailWord_1075097).sum := by decide
  have hdescent : baseEnd_1075097 < baseStart_1075097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075130 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_1075130 : Nat := 118140960795 + 1075130 * 2 ^ 59
def prefixEnd_1075130 : Nat := 4983230072969 + 3 ^ 40 * 1075130 * 2
def baseEnd_1075130 : Nat := 552058456068483782630573

theorem tailTrace_1075130 : CollatzResearch.WordTrace tailWord_1075130 prefixEnd_1075130 552058456068483782630573 := by
  unfold tailWord_1075130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9803303148748775607641711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26142141729996734953711229 9803303148748775607641711)
  ·
    refine ⟨14704954723123163411462567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9803303148748775607641711 14704954723123163411462567)
    ·
      refine ⟨22057432084684745117193851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14704954723123163411462567 22057432084684745117193851)
      ·
        refine ⟨33086148127027117675790777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22057432084684745117193851 33086148127027117675790777)
        ·
          refine ⟨24814611095270338256843083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33086148127027117675790777 24814611095270338256843083)
          ·
            refine ⟨37221916642905507385264625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24814611095270338256843083 37221916642905507385264625)
            ·
              refine ⟨27916437482179130538948469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37221916642905507385264625 27916437482179130538948469)
              ·
                refine ⟨2617166013954293488026419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27916437482179130538948469 2617166013954293488026419)
                ·
                  refine ⟨3925749020931440232039629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617166013954293488026419 3925749020931440232039629)
                  ·
                    refine ⟨1472155882849290087014861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3925749020931440232039629 1472155882849290087014861)
                    ·
                      refine ⟨552058456068483782630573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1472155882849290087014861 552058456068483782630573)
                      ·
                        rfl

theorem cell23_1075130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_1075130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075130 prefixEnd_1075130 := by exact prefixLift 1075130
  have htrace : WordTrace (prefixWord ++ tailWord_1075130) baseStart_1075130 baseEnd_1075130 := by
    simpa [prefixWord, tailWord_1075130, baseEnd_1075130] using wordTrace_append hprefix tailTrace_1075130
  have hstable : (prefixWord ++ tailWord_1075130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075130).length < 2 ^ (prefixWord ++ tailWord_1075130).sum := by decide
  have hdescent : baseEnd_1075130 < baseStart_1075130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075134 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1075134 : Nat := 118140960795 + 1075134 * 2 ^ 59
def prefixEnd_1075134 : Nat := 4983230072969 + 3 ^ 40 * 1075134 * 2
def baseEnd_1075134 : Nat := 552060509991101766980555

theorem tailTrace_1075134 : CollatzResearch.WordTrace tailWord_1075134 prefixEnd_1075134 552060509991101766980555 := by
  unfold tailWord_1075134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901669810872576389214057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26142238991320407409141637 4901669810872576389214057)
  ·
    refine ⟨3676252358154432291910543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4901669810872576389214057 3676252358154432291910543)
    ·
      refine ⟨5514378537231648437865815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3676252358154432291910543 5514378537231648437865815)
      ·
        refine ⟨8271567805847472656798723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5514378537231648437865815 8271567805847472656798723)
        ·
          refine ⟨12407351708771208985198085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8271567805847472656798723 12407351708771208985198085)
          ·
            refine ⟨2326378445394601684724641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12407351708771208985198085 2326378445394601684724641)
            ·
              refine ⟨1744783834045951263543481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2326378445394601684724641 1744783834045951263543481)
              ·
                refine ⟨1308587875534463447657611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744783834045951263543481 1308587875534463447657611)
                ·
                  refine ⟨1962881813301695171486417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308587875534463447657611 1962881813301695171486417)
                  ·
                    refine ⟨1472161359976271378614813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1962881813301695171486417 1472161359976271378614813)
                    ·
                      refine ⟨552060509991101766980555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1472161359976271378614813 552060509991101766980555)
                      ·
                        rfl

theorem cell23_1075134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1075134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075134 prefixEnd_1075134 := by exact prefixLift 1075134
  have htrace : WordTrace (prefixWord ++ tailWord_1075134) baseStart_1075134 baseEnd_1075134 := by
    simpa [prefixWord, tailWord_1075134, baseEnd_1075134] using wordTrace_append hprefix tailTrace_1075134
  have hstable : (prefixWord ++ tailWord_1075134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075134).length < 2 ^ (prefixWord ++ tailWord_1075134).sum := by decide
  have hdescent : baseEnd_1075134 < baseStart_1075134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075148 : List Nat := [2, 2, 1, 4, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1075148 : Nat := 118140960795 + 1075148 * 2 ^ 59
def prefixEnd_1075148 : Nat := 4983230072969 + 3 ^ 40 * 1075148 * 2
def baseEnd_1075148 : Nat := 552067698720264712205491

theorem tailTrace_1075148 : CollatzResearch.WordTrace tailWord_1075148 prefixEnd_1075148 552067698720264712205491 := by
  unfold tailWord_1075148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19606934554464945752361049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26142579405953261003148065 19606934554464945752361049)
  ·
    refine ⟨14705200915848709314270787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19606934554464945752361049 14705200915848709314270787)
    ·
      refine ⟨22057801373773063971406181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14705200915848709314270787 22057801373773063971406181)
      ·
        refine ⟨4135837757582449494638659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22057801373773063971406181 4135837757582449494638659)
        ·
          refine ⟨6203756636373674241957989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4135837757582449494638659 6203756636373674241957989)
          ·
            refine ⟨1163204369320063920367123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6203756636373674241957989 1163204369320063920367123)
            ·
              refine ⟨1744806553980095880550685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163204369320063920367123 1744806553980095880550685)
              ·
                refine ⟨654302457742535955206507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1744806553980095880550685 654302457742535955206507)
                ·
                  refine ⟨981453686613803932809761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654302457742535955206507 981453686613803932809761)
                  ·
                    refine ⟨736090264960352949607321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 981453686613803932809761 736090264960352949607321)
                    ·
                      refine ⟨552067698720264712205491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736090264960352949607321 552067698720264712205491)
                      ·
                        rfl

theorem cell23_1075148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1075148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075148 prefixEnd_1075148 := by exact prefixLift 1075148
  have htrace : WordTrace (prefixWord ++ tailWord_1075148) baseStart_1075148 baseEnd_1075148 := by
    simpa [prefixWord, tailWord_1075148, baseEnd_1075148] using wordTrace_append hprefix tailTrace_1075148
  have hstable : (prefixWord ++ tailWord_1075148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075148).length < 2 ^ (prefixWord ++ tailWord_1075148).sum := by decide
  have hdescent : baseEnd_1075148 < baseStart_1075148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075165 : List Nat := [1, 4, 3, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_1075165 : Nat := 118140960795 + 1075165 * 2 ^ 59
def prefixEnd_1075165 : Nat := 4983230072969 + 3 ^ 40 * 1075165 * 2
def baseEnd_1075165 : Nat := 552076427891391145692913

theorem tailTrace_1075165 : CollatzResearch.WordTrace tailWord_1075165 prefixEnd_1075165 552076427891391145692913 := by
  unfold tailWord_1075165
  simp only [CollatzResearch.WordTrace]
  refine ⟨39214489149868303408090949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26142992766578868938727299 39214489149868303408090949)
  ·
    refine ⟨7352716715600306889017053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39214489149868303408090949 7352716715600306889017053)
    ·
      refine ⟨2757268768350115083381395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7352716715600306889017053 2757268768350115083381395)
      ·
        refine ⟨4135903152525172625072093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2757268768350115083381395 4135903152525172625072093)
        ·
          refine ⟨1550963682196939734402035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4135903152525172625072093 1550963682196939734402035)
          ·
            refine ⟨2326445523295409601603053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550963682196939734402035 2326445523295409601603053)
            ·
              refine ⟨872417071235778600601145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326445523295409601603053 872417071235778600601145)
              ·
                refine ⟨654312803426833950450859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872417071235778600601145 654312803426833950450859)
                ·
                  refine ⟨981469205140250925676289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654312803426833950450859 981469205140250925676289)
                  ·
                    refine ⟨736101903855188194257217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 981469205140250925676289 736101903855188194257217)
                    ·
                      refine ⟨552076427891391145692913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736101903855188194257217 552076427891391145692913)
                      ·
                        rfl

theorem cell23_1075165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_1075165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075165 prefixEnd_1075165 := by exact prefixLift 1075165
  have htrace : WordTrace (prefixWord ++ tailWord_1075165) baseStart_1075165 baseEnd_1075165 := by
    simpa [prefixWord, tailWord_1075165, baseEnd_1075165] using wordTrace_append hprefix tailTrace_1075165
  have hstable : (prefixWord ++ tailWord_1075165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075165).length < 2 ^ (prefixWord ++ tailWord_1075165).sum := by decide
  have hdescent : baseEnd_1075165 < baseStart_1075165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075237 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_1075237 : Nat := 118140960795 + 1075237 * 2 ^ 59
def prefixEnd_1075237 : Nat := 4983230072969 + 3 ^ 40 * 1075237 * 2
def baseEnd_1075237 : Nat := 552113398498514863992581

theorem tailTrace_1075237 : CollatzResearch.WordTrace tailWord_1075237 prefixEnd_1075237 552113398498514863992581 := by
  unfold tailWord_1075237
  simp only [CollatzResearch.WordTrace]
  refine ⟨39217115205607459704711965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26144743470404973136474643 39217115205607459704711965)
  ·
    refine ⟨14706418202102797389266987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39217115205607459704711965 14706418202102797389266987)
    ·
      refine ⟨22059627303154196083900481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14706418202102797389266987 22059627303154196083900481)
      ·
        refine ⟨16544720477365647062925361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22059627303154196083900481 16544720477365647062925361)
        ·
          refine ⟨12408540358024235297194021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16544720477365647062925361 12408540358024235297194021)
          ·
            refine ⟨2326601317129544118223879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12408540358024235297194021 2326601317129544118223879)
            ·
              refine ⟨3489901975694316177335819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326601317129544118223879 3489901975694316177335819)
              ·
                refine ⟨5234852963541474266003729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489901975694316177335819 5234852963541474266003729)
                ·
                  refine ⟨3926139722656105699502797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5234852963541474266003729 3926139722656105699502797)
                  ·
                    refine ⟨1472302395996039637313549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3926139722656105699502797 1472302395996039637313549)
                    ·
                      refine ⟨552113398498514863992581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1472302395996039637313549 552113398498514863992581)
                      ·
                        rfl

theorem cell23_1075237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_1075237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075237 prefixEnd_1075237 := by exact prefixLift 1075237
  have htrace : WordTrace (prefixWord ++ tailWord_1075237) baseStart_1075237 baseEnd_1075237 := by
    simpa [prefixWord, tailWord_1075237, baseEnd_1075237] using wordTrace_append hprefix tailTrace_1075237
  have hstable : (prefixWord ++ tailWord_1075237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075237).length < 2 ^ (prefixWord ++ tailWord_1075237).sum := by decide
  have hdescent : baseEnd_1075237 < baseStart_1075237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075257 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 1, 7]
def baseStart_1075257 : Nat := 118140960795 + 1075257 * 2 ^ 59
def prefixEnd_1075257 : Nat := 4983230072969 + 3 ^ 40 * 1075257 * 2
def baseEnd_1075257 : Nat := 184041222703868261914163

theorem tailTrace_1075257 : CollatzResearch.WordTrace tailWord_1075257 prefixEnd_1075257 184041222703868261914163 := by
  unfold tailWord_1075257
  simp only [CollatzResearch.WordTrace]
  refine ⟨39217844665535003120440025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26145229777023335413626683 39217844665535003120440025)
  ·
    refine ⟨29413383499151252340330019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39217844665535003120440025 29413383499151252340330019)
    ·
      refine ⟨44120075248726878510495029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29413383499151252340330019 44120075248726878510495029)
      ·
        refine ⟨4136257054568144860358909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44120075248726878510495029 4136257054568144860358909)
        ·
          refine ⟨1551096395463054322634591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4136257054568144860358909 1551096395463054322634591)
          ·
            refine ⟨2326644593194581483951887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551096395463054322634591 2326644593194581483951887)
            ·
              refine ⟨3489966889791872225927831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326644593194581483951887 3489966889791872225927831)
              ·
                refine ⟨5234950334687808338891747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489966889791872225927831 5234950334687808338891747)
                ·
                  refine ⟨7852425502031712508337621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5234950334687808338891747 7852425502031712508337621)
                  ·
                    refine ⟨184041222703868261914163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7852425502031712508337621 184041222703868261914163)
                    ·
                      rfl

theorem cell23_1075257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_1075257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075257 prefixEnd_1075257 := by exact prefixLift 1075257
  have htrace : WordTrace (prefixWord ++ tailWord_1075257) baseStart_1075257 baseEnd_1075257 := by
    simpa [prefixWord, tailWord_1075257, baseEnd_1075257] using wordTrace_append hprefix tailTrace_1075257
  have hstable : (prefixWord ++ tailWord_1075257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075257).length < 2 ^ (prefixWord ++ tailWord_1075257).sum := by decide
  have hdescent : baseEnd_1075257 < baseStart_1075257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075287 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 3, 4]
def baseStart_1075287 : Nat := 118140960795 + 1075287 * 2 ^ 59
def prefixEnd_1075287 : Nat := 4983230072969 + 3 ^ 40 * 1075287 * 2
def baseEnd_1075287 : Nat := 184046357510413222789117

theorem tailTrace_1075287 : CollatzResearch.WordTrace tailWord_1075287 prefixEnd_1075287 184046357510413222789117 := by
  unfold tailWord_1075287
  simp only [CollatzResearch.WordTrace]
  refine ⟨39218938855426318244032115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26145959236950878829354743 39218938855426318244032115)
  ·
    refine ⟨58828408283139477366048173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39218938855426318244032115 58828408283139477366048173)
    ·
      refine ⟨22060653106177304012268065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58828408283139477366048173 22060653106177304012268065)
      ·
        refine ⟨16545489829632978009201049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22060653106177304012268065 16545489829632978009201049)
        ·
          refine ⟨12409117372224733506900787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16545489829632978009201049 12409117372224733506900787)
          ·
            refine ⟨18613676058337100260351181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12409117372224733506900787 18613676058337100260351181)
            ·
              refine ⟨6980128521876412597631693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18613676058337100260351181 6980128521876412597631693)
              ·
                refine ⟨2617548195703654724111885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6980128521876412597631693 2617548195703654724111885)
                ·
                  refine ⟨981580573388870521541957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2617548195703654724111885 981580573388870521541957)
                  ·
                    refine ⟨184046357510413222789117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 981580573388870521541957 184046357510413222789117)
                    ·
                      rfl

theorem cell23_1075287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_1075287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075287 prefixEnd_1075287 := by exact prefixLift 1075287
  have htrace : WordTrace (prefixWord ++ tailWord_1075287) baseStart_1075287 baseEnd_1075287 := by
    simpa [prefixWord, tailWord_1075287, baseEnd_1075287] using wordTrace_append hprefix tailTrace_1075287
  have hstable : (prefixWord ++ tailWord_1075287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075287).length < 2 ^ (prefixWord ++ tailWord_1075287).sum := by decide
  have hdescent : baseEnd_1075287 < baseStart_1075287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075290 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1075290 : Nat := 118140960795 + 1075290 * 2 ^ 59
def prefixEnd_1075290 : Nat := 4983230072969 + 3 ^ 40 * 1075290 * 2
def baseEnd_1075290 : Nat := 552140612973203156629837

theorem tailTrace_1075290 : CollatzResearch.WordTrace tailWord_1075290 prefixEnd_1075290 552140612973203156629837 := by
  unfold tailWord_1075290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804762068603862439097831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26146032182943633170927549 9804762068603862439097831)
  ·
    refine ⟨14707143102905793658646747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9804762068603862439097831 14707143102905793658646747)
    ·
      refine ⟨22060714654358690487970121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14707143102905793658646747 22060714654358690487970121)
      ·
        refine ⟨16545535990769017865977591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22060714654358690487970121 16545535990769017865977591)
        ·
          refine ⟨24818303986153526798966387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16545535990769017865977591 24818303986153526798966387)
          ·
            refine ⟨37227455979230290198449581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24818303986153526798966387 37227455979230290198449581)
            ·
              refine ⟨13960295992211358824418593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37227455979230290198449581 13960295992211358824418593)
              ·
                refine ⟨10470221994158519118313945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13960295992211358824418593 10470221994158519118313945)
                ·
                  refine ⟨7852666495618889338735459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10470221994158519118313945 7852666495618889338735459)
                  ·
                    refine ⟨11778999743428334008103189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7852666495618889338735459 11778999743428334008103189)
                    ·
                      refine ⟨552140612973203156629837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11778999743428334008103189 552140612973203156629837)
                      ·
                        rfl

theorem cell23_1075290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1075290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075290 prefixEnd_1075290 := by exact prefixLift 1075290
  have htrace : WordTrace (prefixWord ++ tailWord_1075290) baseStart_1075290 baseEnd_1075290 := by
    simpa [prefixWord, tailWord_1075290, baseEnd_1075290] using wordTrace_append hprefix tailTrace_1075290
  have hstable : (prefixWord ++ tailWord_1075290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075290).length < 2 ^ (prefixWord ++ tailWord_1075290).sum := by decide
  have hdescent : baseEnd_1075290 < baseStart_1075290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075321 : List Nat := [1, 2, 1, 3, 4, 1, 3, 3, 1, 4]
def baseStart_1075321 : Nat := 118140960795 + 1075321 * 2 ^ 59
def prefixEnd_1075321 : Nat := 4983230072969 + 3 ^ 40 * 1075321 * 2
def baseEnd_1075321 : Nat := 184052176957830845114065

theorem tailTrace_1075321 : CollatzResearch.WordTrace tailWord_1075321 prefixEnd_1075321 184052176957830845114065 := by
  unfold tailWord_1075321
  simp only [CollatzResearch.WordTrace]
  refine ⟨39220178937303142050769817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26146785958202094700513211 39220178937303142050769817)
  ·
    refine ⟨29415134202977356538077363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39220178937303142050769817 29415134202977356538077363)
    ·
      refine ⟨44122701304466034807116045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29415134202977356538077363 44122701304466034807116045)
      ·
        refine ⟨16546012989174763052668517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44122701304466034807116045 16546012989174763052668517)
        ·
          refine ⟨3102377435470268072375347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16546012989174763052668517 3102377435470268072375347)
          ·
            refine ⟨4653566153205402108563021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102377435470268072375347 4653566153205402108563021)
            ·
              refine ⟨1745087307452025790711133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4653566153205402108563021 1745087307452025790711133)
              ·
                refine ⟨654407740294509671516675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1745087307452025790711133 654407740294509671516675)
                ·
                  refine ⟨981611610441764507275013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654407740294509671516675 981611610441764507275013)
                  ·
                    refine ⟨184052176957830845114065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 981611610441764507275013 184052176957830845114065)
                    ·
                      rfl

theorem cell23_1075321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 4].length) (baseStart_1075321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075321 prefixEnd_1075321 := by exact prefixLift 1075321
  have htrace : WordTrace (prefixWord ++ tailWord_1075321) baseStart_1075321 baseEnd_1075321 := by
    simpa [prefixWord, tailWord_1075321, baseEnd_1075321] using wordTrace_append hprefix tailTrace_1075321
  have hstable : (prefixWord ++ tailWord_1075321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075321).length < 2 ^ (prefixWord ++ tailWord_1075321).sum := by decide
  have hdescent : baseEnd_1075321 < baseStart_1075321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075338 : List Nat := [3, 1, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_1075338 : Nat := 118140960795 + 1075338 * 2 ^ 59
def prefixEnd_1075338 : Nat := 4983230072969 + 3 ^ 40 * 1075338 * 2
def baseEnd_1075338 : Nat := 184055086681539656276539

theorem tailTrace_1075338 : CollatzResearch.WordTrace tailWord_1075338 prefixEnd_1075338 184055086681539656276539 := by
  unfold tailWord_1075338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9805199744560388488534667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26147199318827702636092445 9805199744560388488534667)
  ·
    refine ⟨14707799616840582732802001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9805199744560388488534667 14707799616840582732802001)
    ·
      refine ⟨11030849712630437049601501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14707799616840582732802001 11030849712630437049601501)
      ·
        refine ⟨4136568642236413893600563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11030849712630437049601501 4136568642236413893600563)
        ·
          refine ⟨6204852963354620840400845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4136568642236413893600563 6204852963354620840400845)
          ·
            refine ⟨2326819861257982815150317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6204852963354620840400845 2326819861257982815150317)
            ·
              refine ⟨872557447971743555681369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326819861257982815150317 872557447971743555681369)
              ·
                refine ⟨654418085978807666761027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872557447971743555681369 654418085978807666761027)
                ·
                  refine ⟨981627128968211500141541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654418085978807666761027 981627128968211500141541)
                  ·
                    refine ⟨184055086681539656276539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 981627128968211500141541 184055086681539656276539)
                    ·
                      rfl

theorem cell23_1075338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_1075338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075338 prefixEnd_1075338 := by exact prefixLift 1075338
  have htrace : WordTrace (prefixWord ++ tailWord_1075338) baseStart_1075338 baseEnd_1075338 := by
    simpa [prefixWord, tailWord_1075338, baseEnd_1075338] using wordTrace_append hprefix tailTrace_1075338
  have hstable : (prefixWord ++ tailWord_1075338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075338).length < 2 ^ (prefixWord ++ tailWord_1075338).sum := by decide
  have hdescent : baseEnd_1075338 < baseStart_1075338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075340 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1075340 : Nat := 118140960795 + 1075340 * 2 ^ 59
def prefixEnd_1075340 : Nat := 4983230072969 + 3 ^ 40 * 1075340 * 2
def baseEnd_1075340 : Nat := 552166287005927961004607

theorem tailTrace_1075340 : CollatzResearch.WordTrace tailWord_1075340 prefixEnd_1075340 552166287005927961004607 := by
  unfold tailWord_1075340
  simp only [CollatzResearch.WordTrace]
  refine ⟨19610435962117154147855737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26147247949489538863807649 19610435962117154147855737)
  ·
    refine ⟨14707826971587865610891803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19610435962117154147855737 14707826971587865610891803)
    ·
      refine ⟨22061740457381798416337705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14707826971587865610891803 22061740457381798416337705)
      ·
        refine ⟨16546305343036348812253279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22061740457381798416337705 16546305343036348812253279)
        ·
          refine ⟨24819458014554523218379919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16546305343036348812253279 24819458014554523218379919)
          ·
            refine ⟨37229187021831784827569879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24819458014554523218379919 37229187021831784827569879)
            ·
              refine ⟨55843780532747677241354819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37229187021831784827569879 55843780532747677241354819)
              ·
                refine ⟨83765670799121515862032229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55843780532747677241354819 83765670799121515862032229)
                ·
                  refine ⟨15706063274835284224131043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83765670799121515862032229 15706063274835284224131043)
                  ·
                    refine ⟨23559094912252926336196565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15706063274835284224131043 23559094912252926336196565)
                    ·
                      refine ⟨552166287005927961004607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23559094912252926336196565 552166287005927961004607)
                      ·
                        rfl

theorem cell23_1075340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1075340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075340 prefixEnd_1075340 := by exact prefixLift 1075340
  have htrace : WordTrace (prefixWord ++ tailWord_1075340) baseStart_1075340 baseEnd_1075340 := by
    simpa [prefixWord, tailWord_1075340, baseEnd_1075340] using wordTrace_append hprefix tailTrace_1075340
  have hstable : (prefixWord ++ tailWord_1075340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075340).length < 2 ^ (prefixWord ++ tailWord_1075340).sum := by decide
  have hdescent : baseEnd_1075340 < baseStart_1075340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075351 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 6]
def baseStart_1075351 : Nat := 118140960795 + 1075351 * 2 ^ 59
def prefixEnd_1075351 : Nat := 4983230072969 + 3 ^ 40 * 1075351 * 2
def baseEnd_1075351 : Nat := 61352437254791935329673

theorem tailTrace_1075351 : CollatzResearch.WordTrace tailWord_1075351 prefixEnd_1075351 61352437254791935329673 := by
  unfold tailWord_1075351
  simp only [CollatzResearch.WordTrace]
  refine ⟨39221273127194457174361907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26147515418129638116241271 39221273127194457174361907)
  ·
    refine ⟨58831909690791685761542861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39221273127194457174361907 58831909690791685761542861)
    ·
      refine ⟨22061966134046882160578573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58831909690791685761542861 22061966134046882160578573)
      ·
        refine ⟨8273237300267580810216965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22061966134046882160578573 8273237300267580810216965)
        ·
          refine ⟨1551231993800171401915681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8273237300267580810216965 1551231993800171401915681)
          ·
            refine ⟨1163423995350128551436761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551231993800171401915681 1163423995350128551436761)
            ·
              refine ⟨872567996512596413577571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163423995350128551436761 872567996512596413577571)
              ·
                refine ⟨1308851994768894620366357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872567996512596413577571 1308851994768894620366357)
                ·
                  refine ⟨61352437254791935329673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1308851994768894620366357 61352437254791935329673)
                  ·
                    rfl

theorem cell23_1075351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 6].length) (baseStart_1075351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075351 prefixEnd_1075351 := by exact prefixLift 1075351
  have htrace : WordTrace (prefixWord ++ tailWord_1075351) baseStart_1075351 baseEnd_1075351 := by
    simpa [prefixWord, tailWord_1075351, baseEnd_1075351] using wordTrace_append hprefix tailTrace_1075351
  have hstable : (prefixWord ++ tailWord_1075351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075351).length < 2 ^ (prefixWord ++ tailWord_1075351).sum := by decide
  have hdescent : baseEnd_1075351 < baseStart_1075351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075364 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_1075364 : Nat := 118140960795 + 1075364 * 2 ^ 59
def prefixEnd_1075364 : Nat := 4983230072969 + 3 ^ 40 * 1075364 * 2
def baseEnd_1075364 : Nat := 184059536847211955701499

theorem tailTrace_1075364 : CollatzResearch.WordTrace tailWord_1075364 prefixEnd_1075364 184059536847211955701499 := by
  unfold tailWord_1075364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19610873638073680197292573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26147831517431573596390097 19610873638073680197292573)
  ·
    refine ⟨7354077614277630073984715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19610873638073680197292573 7354077614277630073984715)
    ·
      refine ⟨11031116421416445110977073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7354077614277630073984715 11031116421416445110977073)
      ·
        refine ⟨8273337316062333833232805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11031116421416445110977073 8273337316062333833232805)
        ·
          refine ⟨1551250746761687593731151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8273337316062333833232805 1551250746761687593731151)
          ·
            refine ⟨2326876120142531390596727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551250746761687593731151 2326876120142531390596727)
            ·
              refine ⟨3490314180213797085895091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326876120142531390596727 3490314180213797085895091)
              ·
                refine ⟨5235471270320695628842637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490314180213797085895091 5235471270320695628842637)
                ·
                  refine ⟨1963301726370260860815989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5235471270320695628842637 1963301726370260860815989)
                  ·
                    refine ⟨184059536847211955701499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1963301726370260860815989 184059536847211955701499)
                    ·
                      rfl

theorem cell23_1075364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_1075364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075364 prefixEnd_1075364 := by exact prefixLift 1075364
  have htrace : WordTrace (prefixWord ++ tailWord_1075364) baseStart_1075364 baseEnd_1075364 := by
    simpa [prefixWord, tailWord_1075364, baseEnd_1075364] using wordTrace_append hprefix tailTrace_1075364
  have hstable : (prefixWord ++ tailWord_1075364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075364).length < 2 ^ (prefixWord ++ tailWord_1075364).sum := by decide
  have hdescent : baseEnd_1075364 < baseStart_1075364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075421 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1075421 : Nat := 118140960795 + 1075421 * 2 ^ 59
def prefixEnd_1075421 : Nat := 4983230072969 + 3 ^ 40 * 1075421 * 2
def baseEnd_1075421 : Nat := 552207878938942144091735

theorem tailTrace_1075421 : CollatzResearch.WordTrace tailWord_1075421 prefixEnd_1075421 552207878938942144091735 := by
  unfold tailWord_1075421
  simp only [CollatzResearch.WordTrace]
  refine ⟨39223826236940859129410117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26149217491293906086273411 39223826236940859129410117)
  ·
    refine ⟨7354467419426411086764397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39223826236940859129410117 7354467419426411086764397)
    ·
      refine ⟨2757925282284904157536649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7354467419426411086764397 2757925282284904157536649)
      ·
        refine ⟨2068443961713678118152487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2757925282284904157536649 2068443961713678118152487)
        ·
          refine ⟨3102665942570517177228731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068443961713678118152487 3102665942570517177228731)
          ·
            refine ⟨4653998913855775765843097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102665942570517177228731 4653998913855775765843097)
            ·
              refine ⟨3490499185391831824382323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653998913855775765843097 3490499185391831824382323)
              ·
                refine ⟨5235748778087747736573485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490499185391831824382323 5235748778087747736573485)
                ·
                  refine ⟨1963405791782905401215057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5235748778087747736573485 1963405791782905401215057)
                  ·
                    refine ⟨1472554343837179050911293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1963405791782905401215057 1472554343837179050911293)
                    ·
                      refine ⟨552207878938942144091735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1472554343837179050911293 552207878938942144091735)
                      ·
                        rfl

theorem cell23_1075421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1075421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075421 prefixEnd_1075421 := by exact prefixLift 1075421
  have htrace : WordTrace (prefixWord ++ tailWord_1075421) baseStart_1075421 baseEnd_1075421 := by
    simpa [prefixWord, tailWord_1075421, baseEnd_1075421] using wordTrace_append hprefix tailTrace_1075421
  have hstable : (prefixWord ++ tailWord_1075421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075421).length < 2 ^ (prefixWord ++ tailWord_1075421).sum := by decide
  have hdescent : baseEnd_1075421 < baseStart_1075421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075434 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1075434 : Nat := 118140960795 + 1075434 * 2 ^ 59
def prefixEnd_1075434 : Nat := 4983230072969 + 3 ^ 40 * 1075434 * 2
def baseEnd_1075434 : Nat := 552214554187450593229175

theorem tailTrace_1075434 : CollatzResearch.WordTrace tailWord_1075434 prefixEnd_1075434 552214554187450593229175 := by
  unfold tailWord_1075434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9806075096473440587408339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26149533590595841566422237 9806075096473440587408339)
  ·
    refine ⟨14709112644710160881112509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9806075096473440587408339 14709112644710160881112509)
    ·
      refine ⟨5515917241766310330417191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14709112644710160881112509 5515917241766310330417191)
      ·
        refine ⟨8273875862649465495625787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5515917241766310330417191 8273875862649465495625787)
        ·
          refine ⟨12410813793974198243438681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8273875862649465495625787 12410813793974198243438681)
          ·
            refine ⟨9308110345480648682579011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12410813793974198243438681 9308110345480648682579011)
            ·
              refine ⟨13962165518220973023868517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308110345480648682579011 13962165518220973023868517)
              ·
                refine ⟨2617906034666432441975347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13962165518220973023868517 2617906034666432441975347)
                ·
                  refine ⟨3926859051999648662963021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617906034666432441975347 3926859051999648662963021)
                  ·
                    refine ⟨1472572144499868248611133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3926859051999648662963021 1472572144499868248611133)
                    ·
                      refine ⟨552214554187450593229175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1472572144499868248611133 552214554187450593229175)
                      ·
                        rfl

theorem cell23_1075434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1075434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075434 prefixEnd_1075434 := by exact prefixLift 1075434
  have htrace : WordTrace (prefixWord ++ tailWord_1075434) baseStart_1075434 baseEnd_1075434 := by
    simpa [prefixWord, tailWord_1075434, baseEnd_1075434] using wordTrace_append hprefix tailTrace_1075434
  have hstable : (prefixWord ++ tailWord_1075434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075434).length < 2 ^ (prefixWord ++ tailWord_1075434).sum := by decide
  have hdescent : baseEnd_1075434 < baseStart_1075434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075467 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 2, 6]
def baseStart_1075467 : Nat := 118140960795 + 1075467 * 2 ^ 59
def prefixEnd_1075467 : Nat := 4983230072969 + 3 ^ 40 * 1075467 * 2
def baseEnd_1075467 : Nat := 184077166349682988038841

theorem tailTrace_1075467 : CollatzResearch.WordTrace tailWord_1075467 prefixEnd_1075467 184077166349682988038841 := by
  unfold tailWord_1075467
  simp only [CollatzResearch.WordTrace]
  refine ⟨39225503994774208985584655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26150335996516139323723103 39225503994774208985584655)
  ·
    refine ⟨58838255992161313478376983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39225503994774208985584655 58838255992161313478376983)
    ·
      refine ⟨88257383988241970217565475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58838255992161313478376983 88257383988241970217565475)
      ·
        refine ⟨132386075982362955326348213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88257383988241970217565475 132386075982362955326348213)
        ·
          refine ⟨12411194623346527061845145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132386075982362955326348213 12411194623346527061845145)
          ·
            refine ⟨9308395967509895296383859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12411194623346527061845145 9308395967509895296383859)
            ·
              refine ⟨13962593951264842944575789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308395967509895296383859 13962593951264842944575789)
              ·
                refine ⟨5235972731724316104215921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13962593951264842944575789 5235972731724316104215921)
                ·
                  refine ⟨3926979548793237078161941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5235972731724316104215921 3926979548793237078161941)
                  ·
                    refine ⟨184077166349682988038841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3926979548793237078161941 184077166349682988038841)
                    ·
                      rfl

theorem cell23_1075467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 6].length) (baseStart_1075467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075467 prefixEnd_1075467 := by exact prefixLift 1075467
  have htrace : WordTrace (prefixWord ++ tailWord_1075467) baseStart_1075467 baseEnd_1075467 := by
    simpa [prefixWord, tailWord_1075467, baseEnd_1075467] using wordTrace_append hprefix tailTrace_1075467
  have hstable : (prefixWord ++ tailWord_1075467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075467).length < 2 ^ (prefixWord ++ tailWord_1075467).sum := by decide
  have hdescent : baseEnd_1075467 < baseStart_1075467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075468 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 2, 1, 3]
def baseStart_1075468 : Nat := 118140960795 + 1075468 * 2 ^ 59
def prefixEnd_1075468 : Nat := 4983230072969 + 3 ^ 40 * 1075468 * 2
def baseEnd_1075468 : Nat := 552232012529703460204019

theorem tailTrace_1075468 : CollatzResearch.WordTrace tailWord_1075468 prefixEnd_1075468 552232012529703460204019 := by
  unfold tailWord_1075468
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612770233885293078185529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26150360311847057437580705 19612770233885293078185529)
  ·
    refine ⟨14709577675413969808639147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19612770233885293078185529 14709577675413969808639147)
    ·
      refine ⟨22064366513120954712958721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14709577675413969808639147 22064366513120954712958721)
      ·
        refine ⟨16548274884840716034719041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22064366513120954712958721 16548274884840716034719041)
        ·
          refine ⟨12411206163630537026039281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16548274884840716034719041 12411206163630537026039281)
          ·
            refine ⟨9308404622722902769529461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12411206163630537026039281 9308404622722902769529461)
            ·
              refine ⟨872662933380272134643387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9308404622722902769529461 872662933380272134643387)
              ·
                refine ⟨1308994400070408201965081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872662933380272134643387 1308994400070408201965081)
                ·
                  refine ⟨981745800052806151473811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1308994400070408201965081 981745800052806151473811)
                  ·
                    refine ⟨1472618700079209227210717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 981745800052806151473811 1472618700079209227210717)
                    ·
                      refine ⟨552232012529703460204019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1472618700079209227210717 552232012529703460204019)
                      ·
                        rfl

theorem cell23_1075468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_1075468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075468 prefixEnd_1075468 := by exact prefixLift 1075468
  have htrace : WordTrace (prefixWord ++ tailWord_1075468) baseStart_1075468 baseEnd_1075468 := by
    simpa [prefixWord, tailWord_1075468, baseEnd_1075468] using wordTrace_append hprefix tailTrace_1075468
  have hstable : (prefixWord ++ tailWord_1075468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075468).length < 2 ^ (prefixWord ++ tailWord_1075468).sum := by decide
  have hdescent : baseEnd_1075468 < baseStart_1075468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075491 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 6, 2, 2]
def baseStart_1075491 : Nat := 118140960795 + 1075491 * 2 ^ 59
def prefixEnd_1075491 : Nat := 4983230072969 + 3 ^ 40 * 1075491 * 2
def baseEnd_1075491 : Nat := 552243822584756870216413

theorem tailTrace_1075491 : CollatzResearch.WordTrace tailWord_1075491 prefixEnd_1075491 552243822584756870216413 := by
  unfold tailWord_1075491
  simp only [CollatzResearch.WordTrace]
  refine ⟨39226379346687261084458327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26150919564458174056305551 39226379346687261084458327)
  ·
    refine ⟨58839569020030891626687491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39226379346687261084458327 58839569020030891626687491)
    ·
      refine ⟨88259353530046337440031237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58839569020030891626687491 88259353530046337440031237)
      ·
        refine ⟨16548628786883688270005857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88259353530046337440031237 16548628786883688270005857)
        ·
          refine ⟨12411471590162766202504393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16548628786883688270005857 12411471590162766202504393)
          ·
            refine ⟨9308603692622074651878295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12411471590162766202504393 9308603692622074651878295)
            ·
              refine ⟨13962905538933111977817443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308603692622074651878295 13962905538933111977817443)
              ·
                refine ⟨20944358308399667966726165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13962905538933111977817443 20944358308399667966726165)
                ·
                  refine ⟨981766795706234435940289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20944358308399667966726165 981766795706234435940289)
                  ·
                    refine ⟨736325096779675826955217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 981766795706234435940289 736325096779675826955217)
                    ·
                      refine ⟨552243822584756870216413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736325096779675826955217 552243822584756870216413)
                      ·
                        rfl

theorem cell23_1075491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_1075491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075491 prefixEnd_1075491 := by exact prefixLift 1075491
  have htrace : WordTrace (prefixWord ++ tailWord_1075491) baseStart_1075491 baseEnd_1075491 := by
    simpa [prefixWord, tailWord_1075491, baseEnd_1075491] using wordTrace_append hprefix tailTrace_1075491
  have hstable : (prefixWord ++ tailWord_1075491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075491).length < 2 ^ (prefixWord ++ tailWord_1075491).sum := by decide
  have hdescent : baseEnd_1075491 < baseStart_1075491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075507 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7]
def baseStart_1075507 : Nat := 118140960795 + 1075507 * 2 ^ 59
def prefixEnd_1075507 : Nat := 4983230072969 + 3 ^ 40 * 1075507 * 2
def baseEnd_1075507 : Nat := 552252038275228807616339

theorem tailTrace_1075507 : CollatzResearch.WordTrace tailWord_1075507 prefixEnd_1075507 552252038275228807616339 := by
  unfold tailWord_1075507
  simp only [CollatzResearch.WordTrace]
  refine ⟨39226962914629295817040775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26151308609752863878027183 39226962914629295817040775)
  ·
    refine ⟨58840444371943943725561163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39226962914629295817040775 58840444371943943725561163)
    ·
      refine ⟨88260666557915915588341745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58840444371943943725561163 88260666557915915588341745)
      ·
        refine ⟨66195499918436936691256309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88260666557915915588341745 66195499918436936691256309)
        ·
          refine ⟨6205828117353462814805279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66195499918436936691256309 6205828117353462814805279)
          ·
            refine ⟨9308742176030194222207919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6205828117353462814805279 9308742176030194222207919)
            ·
              refine ⟨13963113264045291333311879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308742176030194222207919 13963113264045291333311879)
              ·
                refine ⟨20944669896067936999967819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13963113264045291333311879 20944669896067936999967819)
                ·
                  refine ⟨31417004844101905499951729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20944669896067936999967819 31417004844101905499951729)
                  ·
                    refine ⟨23562753633076429124963797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31417004844101905499951729 23562753633076429124963797)
                    ·
                      refine ⟨552252038275228807616339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23562753633076429124963797 552252038275228807616339)
                      ·
                        rfl

theorem cell23_1075507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_1075507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075507 prefixEnd_1075507 := by exact prefixLift 1075507
  have htrace : WordTrace (prefixWord ++ tailWord_1075507) baseStart_1075507 baseEnd_1075507 := by
    simpa [prefixWord, tailWord_1075507, baseEnd_1075507] using wordTrace_append hprefix tailTrace_1075507
  have hstable : (prefixWord ++ tailWord_1075507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075507).length < 2 ^ (prefixWord ++ tailWord_1075507).sum := by decide
  have hdescent : baseEnd_1075507 < baseStart_1075507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075514 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 7]
def baseStart_1075514 : Nat := 118140960795 + 1075514 * 2 ^ 59
def prefixEnd_1075514 : Nat := 4983230072969 + 3 ^ 40 * 1075514 * 2
def baseEnd_1075514 : Nat := 61361736959978920025423

theorem tailTrace_1075514 : CollatzResearch.WordTrace tailWord_1075514 prefixEnd_1075514 61361736959978920025423 := by
  unfold tailWord_1075514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9806804556400984003136399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26151478817069290675030397 9806804556400984003136399)
  ·
    refine ⟨14710206834601476004704599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9806804556400984003136399 14710206834601476004704599)
    ·
      refine ⟨22065310251902214007056899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14710206834601476004704599 22065310251902214007056899)
      ·
        refine ⟨33097965377853321010585349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22065310251902214007056899 33097965377853321010585349)
        ·
          refine ⟨6205868508347497689484753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33097965377853321010585349 6205868508347497689484753)
          ·
            refine ⟨4654401381260623267113565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6205868508347497689484753 4654401381260623267113565)
            ·
              refine ⟨1745400517972733725167587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4654401381260623267113565 1745400517972733725167587)
              ·
                refine ⟨2618100776959100587751381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1745400517972733725167587 2618100776959100587751381)
                ·
                  refine ⟨61361736959978920025423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2618100776959100587751381 61361736959978920025423)
                  ·
                    rfl

theorem cell23_1075514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_1075514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075514 prefixEnd_1075514 := by exact prefixLift 1075514
  have htrace : WordTrace (prefixWord ++ tailWord_1075514) baseStart_1075514 baseEnd_1075514 := by
    simpa [prefixWord, tailWord_1075514, baseEnd_1075514] using wordTrace_append hprefix tailTrace_1075514
  have hstable : (prefixWord ++ tailWord_1075514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075514).length < 2 ^ (prefixWord ++ tailWord_1075514).sum := by decide
  have hdescent : baseEnd_1075514 < baseStart_1075514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075581 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_1075581 : Nat := 118140960795 + 1075581 * 2 ^ 59
def prefixEnd_1075581 : Nat := 4983230072969 + 3 ^ 40 * 1075581 * 2
def baseEnd_1075581 : Nat := 552290035843661518090999

theorem tailTrace_1075581 : CollatzResearch.WordTrace tailWord_1075581 prefixEnd_1075581 552290035843661518090999 := by
  unfold tailWord_1075581
  simp only [CollatzResearch.WordTrace]
  refine ⟨39229661916361206455234597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26153107944240804303489731 39229661916361206455234597)
  ·
    refine ⟨7355561609317726210356487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39229661916361206455234597 7355561609317726210356487)
    ·
      refine ⟨11033342413976589315534731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7355561609317726210356487 11033342413976589315534731)
      ·
        refine ⟨16550013620964883973302097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11033342413976589315534731 16550013620964883973302097)
        ·
          refine ⟨12412510215723662979976573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16550013620964883973302097 12412510215723662979976573)
          ·
            refine ⟨4654691330896373617491215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12412510215723662979976573 4654691330896373617491215)
            ·
              refine ⟨6982036996344560426236823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4654691330896373617491215 6982036996344560426236823)
              ·
                refine ⟨10473055494516840639355235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6982036996344560426236823 10473055494516840639355235)
                ·
                  refine ⟨15709583241775260959032853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10473055494516840639355235 15709583241775260959032853)
                  ·
                    refine ⟨736386714458215357454665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15709583241775260959032853 736386714458215357454665)
                    ·
                      refine ⟨552290035843661518090999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736386714458215357454665 552290035843661518090999)
                      ·
                        rfl

theorem cell23_1075581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_1075581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075581 prefixEnd_1075581 := by exact prefixLift 1075581
  have htrace : WordTrace (prefixWord ++ tailWord_1075581) baseStart_1075581 baseEnd_1075581 := by
    simpa [prefixWord, tailWord_1075581, baseEnd_1075581] using wordTrace_append hprefix tailTrace_1075581
  have hstable : (prefixWord ++ tailWord_1075581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075581).length < 2 ^ (prefixWord ++ tailWord_1075581).sum := by decide
  have hdescent : baseEnd_1075581 < baseStart_1075581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075591 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 3, 4]
def baseStart_1075591 : Nat := 118140960795 + 1075591 * 2 ^ 59
def prefixEnd_1075591 : Nat := 4983230072969 + 3 ^ 40 * 1075591 * 2
def baseEnd_1075591 : Nat := 184098390216735492988651

theorem tailTrace_1075591 : CollatzResearch.WordTrace tailWord_1075591 prefixEnd_1075591 184098390216735492988651 := by
  unfold tailWord_1075591
  simp only [CollatzResearch.WordTrace]
  refine ⟨39230026646324978163098627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26153351097549985442065751 39230026646324978163098627)
  ·
    refine ⟨58845039969487467244647941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39230026646324978163098627 58845039969487467244647941)
    ·
      refine ⟨11033444994278900108371489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58845039969487467244647941 11033444994278900108371489)
      ·
        refine ⟨8275083745709175081278617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11033444994278900108371489 8275083745709175081278617)
        ·
          refine ⟨6206312809281881310958963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8275083745709175081278617 6206312809281881310958963)
          ·
            refine ⟨9309469213922821966438445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6206312809281881310958963 9309469213922821966438445)
            ·
              refine ⟨3491050955221058237414417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9309469213922821966438445 3491050955221058237414417)
              ·
                refine ⟨2618288216415793678060813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491050955221058237414417 2618288216415793678060813)
                ·
                  refine ⟨981858081155922629272805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2618288216415793678060813 981858081155922629272805)
                  ·
                    refine ⟨184098390216735492988651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 981858081155922629272805 184098390216735492988651)
                    ·
                      rfl

theorem cell23_1075591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_1075591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075591 prefixEnd_1075591 := by exact prefixLift 1075591
  have htrace : WordTrace (prefixWord ++ tailWord_1075591) baseStart_1075591 baseEnd_1075591 := by
    simpa [prefixWord, tailWord_1075591, baseEnd_1075591] using wordTrace_append hprefix tailTrace_1075591
  have hstable : (prefixWord ++ tailWord_1075591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075591).length < 2 ^ (prefixWord ++ tailWord_1075591).sum := by decide
  have hdescent : baseEnd_1075591 < baseStart_1075591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075598 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1075598 : Nat := 118140960795 + 1075598 * 2 ^ 59
def prefixEnd_1075598 : Nat := 4983230072969 + 3 ^ 40 * 1075598 * 2
def baseEnd_1075598 : Nat := 552298765014787951578421

theorem tailTrace_1075598 : CollatzResearch.WordTrace tailWord_1075598 prefixEnd_1075598 552298765014787951578421 := by
  unfold tailWord_1075598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903785244662452294825431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26153521304866412239068965 4903785244662452294825431)
  ·
    refine ⟨7355677866993678442238147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4903785244662452294825431 7355677866993678442238147)
    ·
      refine ⟨11033516800490517663357221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7355677866993678442238147 11033516800490517663357221)
      ·
        refine ⟨2068784400091972061879479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11033516800490517663357221 2068784400091972061879479)
        ·
          refine ⟨3103176600137958092819219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068784400091972061879479 3103176600137958092819219)
          ·
            refine ⟨4654764900206937139228829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103176600137958092819219 4654764900206937139228829)
            ·
              refine ⟨1745536837577601427210811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4654764900206937139228829 1745536837577601427210811)
              ·
                refine ⟨2618305256366402140816217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1745536837577601427210811 2618305256366402140816217)
                ·
                  refine ⟨1963728942274801605612163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2618305256366402140816217 1963728942274801605612163)
                  ·
                    refine ⟨2945593413412202408418245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1963728942274801605612163 2945593413412202408418245)
                    ·
                      refine ⟨552298765014787951578421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2945593413412202408418245 552298765014787951578421)
                      ·
                        rfl

theorem cell23_1075598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1075598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075598 prefixEnd_1075598 := by exact prefixLift 1075598
  have htrace : WordTrace (prefixWord ++ tailWord_1075598) baseStart_1075598 baseEnd_1075598 := by
    simpa [prefixWord, tailWord_1075598, baseEnd_1075598] using wordTrace_append hprefix tailTrace_1075598
  have hstable : (prefixWord ++ tailWord_1075598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075598).length < 2 ^ (prefixWord ++ tailWord_1075598).sum := by decide
  have hdescent : baseEnd_1075598 < baseStart_1075598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075658 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_1075658 : Nat := 118140960795 + 1075658 * 2 ^ 59
def prefixEnd_1075658 : Nat := 4983230072969 + 3 ^ 40 * 1075658 * 2
def baseEnd_1075658 : Nat := 552329573854057716828145

theorem tailTrace_1075658 : CollatzResearch.WordTrace tailWord_1075658 prefixEnd_1075658 552329573854057716828145 := by
  unfold tailWord_1075658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9808117584270562151446907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26154980224721499070525085 9808117584270562151446907)
  ·
    refine ⟨14712176376405843227170361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9808117584270562151446907 14712176376405843227170361)
    ·
      refine ⟨11034132282304382420377771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14712176376405843227170361 11034132282304382420377771)
      ·
        refine ⟨16551198423456573630566657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11034132282304382420377771 16551198423456573630566657)
        ·
          refine ⟨12413398817592430222924993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16551198423456573630566657 12413398817592430222924993)
          ·
            refine ⟨9310049113194322667193745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12413398817592430222924993 9310049113194322667193745)
            ·
              refine ⟨6982536834895742000395309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9310049113194322667193745 6982536834895742000395309)
              ·
                refine ⟨2618451313085903250148241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6982536834895742000395309 2618451313085903250148241)
                ·
                  refine ⟨1963838484814427437611181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2618451313085903250148241 1963838484814427437611181)
                  ·
                    refine ⟨736439431805410289104193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963838484814427437611181 736439431805410289104193)
                    ·
                      refine ⟨552329573854057716828145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736439431805410289104193 552329573854057716828145)
                      ·
                        rfl

theorem cell23_1075658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_1075658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075658 prefixEnd_1075658 := by exact prefixLift 1075658
  have htrace : WordTrace (prefixWord ++ tailWord_1075658) baseStart_1075658 baseEnd_1075658 := by
    simpa [prefixWord, tailWord_1075658, baseEnd_1075658] using wordTrace_append hprefix tailTrace_1075658
  have hstable : (prefixWord ++ tailWord_1075658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075658).length < 2 ^ (prefixWord ++ tailWord_1075658).sum := by decide
  have hdescent : baseEnd_1075658 < baseStart_1075658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075668 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1075668 : Nat := 118140960795 + 1075668 * 2 ^ 59
def prefixEnd_1075668 : Nat := 4983230072969 + 3 ^ 40 * 1075668 * 2
def baseEnd_1075668 : Nat := 184111569553534225901033

theorem tailTrace_1075668 : CollatzResearch.WordTrace tailWord_1075668 prefixEnd_1075668 184111569553534225901033 := by
  unfold tailWord_1075668
  simp only [CollatzResearch.WordTrace]
  refine ⟨19616417533523010156825829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26155223378030680209101105 19616417533523010156825829)
  ·
    refine ⟨3678078287535564404404843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19616417533523010156825829 3678078287535564404404843)
    ·
      refine ⟨5517117431303346606607265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3678078287535564404404843 5517117431303346606607265)
      ·
        refine ⟨4137838073477509954955449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5517117431303346606607265 4137838073477509954955449)
        ·
          refine ⟨3103378555108132466216587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4137838073477509954955449 3103378555108132466216587)
          ·
            refine ⟨4655067832662198699324881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103378555108132466216587 4655067832662198699324881)
            ·
              refine ⟨3491300874496649024493661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4655067832662198699324881 3491300874496649024493661)
              ·
                refine ⟨1309237827936243384185123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3491300874496649024493661 1309237827936243384185123)
                ·
                  refine ⟨1963856741904365076277685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309237827936243384185123 1963856741904365076277685)
                  ·
                    refine ⟨184111569553534225901033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1963856741904365076277685 184111569553534225901033)
                    ·
                      rfl

theorem cell23_1075668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1075668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075668 prefixEnd_1075668 := by exact prefixLift 1075668
  have htrace : WordTrace (prefixWord ++ tailWord_1075668) baseStart_1075668 baseEnd_1075668 := by
    simpa [prefixWord, tailWord_1075668, baseEnd_1075668] using wordTrace_append hprefix tailTrace_1075668
  have hstable : (prefixWord ++ tailWord_1075668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075668).length < 2 ^ (prefixWord ++ tailWord_1075668).sum := by decide
  have hdescent : baseEnd_1075668 < baseStart_1075668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075681 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1075681 : Nat := 118140960795 + 1075681 * 2 ^ 59
def prefixEnd_1075681 : Nat := 4983230072969 + 3 ^ 40 * 1075681 * 2
def baseEnd_1075681 : Nat := 184113794636370375613513

theorem tailTrace_1075681 : CollatzResearch.WordTrace tailWord_1075681 prefixEnd_1075681 184113794636370375613513 := by
  unfold tailWord_1075681
  simp only [CollatzResearch.WordTrace]
  refine ⟨39233309215998923533874897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26155539477332615689249931 39233309215998923533874897)
  ·
    refine ⟨29424981911999192650406173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39233309215998923533874897 29424981911999192650406173)
    ·
      refine ⟨11034368216999697243902315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29424981911999192650406173 11034368216999697243902315)
      ·
        refine ⟨16551552325499545865853473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11034368216999697243902315 16551552325499545865853473)
        ·
          refine ⟨12413664244124659399390105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16551552325499545865853473 12413664244124659399390105)
          ·
            refine ⟨9310248183093494549542579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12413664244124659399390105 9310248183093494549542579)
            ·
              refine ⟨13965372274640241824313869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9310248183093494549542579 13965372274640241824313869)
              ·
                refine ⟨5237014602990090684117701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13965372274640241824313869 5237014602990090684117701)
                ·
                  refine ⟨981940238060642003272069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5237014602990090684117701 981940238060642003272069)
                  ·
                    refine ⟨184113794636370375613513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 981940238060642003272069 184113794636370375613513)
                    ·
                      rfl

theorem cell23_1075681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1075681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075681 prefixEnd_1075681 := by exact prefixLift 1075681
  have htrace : WordTrace (prefixWord ++ tailWord_1075681) baseStart_1075681 baseEnd_1075681 := by
    simpa [prefixWord, tailWord_1075681, baseEnd_1075681] using wordTrace_append hprefix tailTrace_1075681
  have hstable : (prefixWord ++ tailWord_1075681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075681).length < 2 ^ (prefixWord ++ tailWord_1075681).sum := by decide
  have hdescent : baseEnd_1075681 < baseStart_1075681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075691 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 3]
def baseStart_1075691 : Nat := 118140960795 + 1075691 * 2 ^ 59
def prefixEnd_1075691 : Nat := 4983230072969 + 3 ^ 40 * 1075691 * 2
def baseEnd_1075691 : Nat := 552346518715656087715493

theorem tailTrace_1075691 : CollatzResearch.WordTrace tailWord_1075691 prefixEnd_1075691 552346518715656087715493 := by
  unfold tailWord_1075691
  simp only [CollatzResearch.WordTrace]
  refine ⟨39233673945962695241738927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26155782630641796827825951 39233673945962695241738927)
  ·
    refine ⟨58850510918944042862608391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39233673945962695241738927 58850510918944042862608391)
    ·
      refine ⟨88275766378416064293912587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58850510918944042862608391 88275766378416064293912587)
      ·
        refine ⟨132413649567624096440868881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88275766378416064293912587 132413649567624096440868881)
        ·
          refine ⟨99310237175718072330651661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132413649567624096440868881 99310237175718072330651661)
          ·
            refine ⟨37241338940894277123994373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99310237175718072330651661 37241338940894277123994373)
            ·
              refine ⟨6982751051417676960748945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37241338940894277123994373 6982751051417676960748945)
              ·
                refine ⟨5237063288563257720561709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6982751051417676960748945 5237063288563257720561709)
                ·
                  refine ⟨1963898733211221645210641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5237063288563257720561709 1963898733211221645210641)
                  ·
                    refine ⟨1472924049908416233907981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1963898733211221645210641 1472924049908416233907981)
                    ·
                      refine ⟨552346518715656087715493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1472924049908416233907981 552346518715656087715493)
                      ·
                        rfl

theorem cell23_1075691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 3].length) (baseStart_1075691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075691 prefixEnd_1075691 := by exact prefixLift 1075691
  have htrace : WordTrace (prefixWord ++ tailWord_1075691) baseStart_1075691 baseEnd_1075691 := by
    simpa [prefixWord, tailWord_1075691, baseEnd_1075691] using wordTrace_append hprefix tailTrace_1075691
  have hstable : (prefixWord ++ tailWord_1075691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075691).length < 2 ^ (prefixWord ++ tailWord_1075691).sum := by decide
  have hdescent : baseEnd_1075691 < baseStart_1075691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075722 : List Nat := [3, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_1075722 : Nat := 118140960795 + 1075722 * 2 ^ 59
def prefixEnd_1075722 : Nat := 4983230072969 + 3 ^ 40 * 1075722 * 2
def baseEnd_1075722 : Nat := 552362436615945466427851

theorem tailTrace_1075722 : CollatzResearch.WordTrace tailWord_1075722 prefixEnd_1075722 552362436615945466427851 := by
  unfold tailWord_1075722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9808701152212596884029355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26156536405900258357411613 9808701152212596884029355)
  ·
    refine ⟨14713051728318895326044033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9808701152212596884029355 14713051728318895326044033)
    ·
      refine ⟨11034788796239171494533025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14713051728318895326044033 11034788796239171494533025)
      ·
        refine ⟨8276091597179378620899769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11034788796239171494533025 8276091597179378620899769)
        ·
          refine ⟨6207068697884533965674827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8276091597179378620899769 6207068697884533965674827)
          ·
            refine ⟨9310603046826800948512241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6207068697884533965674827 9310603046826800948512241)
            ·
              refine ⟨6982952285120100711384181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9310603046826800948512241 6982952285120100711384181)
              ·
                refine ⟨654651776730009441692267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6982952285120100711384181 654651776730009441692267)
                ·
                  refine ⟨981977665095014162538401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654651776730009441692267 981977665095014162538401)
                  ·
                    refine ⟨736483248821260621903801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 981977665095014162538401 736483248821260621903801)
                    ·
                      refine ⟨552362436615945466427851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736483248821260621903801 552362436615945466427851)
                      ·
                        rfl

theorem cell23_1075722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_1075722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075722 prefixEnd_1075722 := by exact prefixLift 1075722
  have htrace : WordTrace (prefixWord ++ tailWord_1075722) baseStart_1075722 baseEnd_1075722 := by
    simpa [prefixWord, tailWord_1075722, baseEnd_1075722] using wordTrace_append hprefix tailTrace_1075722
  have hstable : (prefixWord ++ tailWord_1075722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075722).length < 2 ^ (prefixWord ++ tailWord_1075722).sum := by decide
  have hdescent : baseEnd_1075722 < baseStart_1075722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075732 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1075732 : Nat := 118140960795 + 1075732 * 2 ^ 59
def prefixEnd_1075732 : Nat := 4983230072969 + 3 ^ 40 * 1075732 * 2
def baseEnd_1075732 : Nat := 184122523807496809100935

theorem tailTrace_1075732 : CollatzResearch.WordTrace tailWord_1075732 prefixEnd_1075732 184122523807496809100935 := by
  unfold tailWord_1075732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19617584669407079621990725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26156779559209439495987633 19617584669407079621990725)
  ·
    refine ⟨3678297125513827429123261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19617584669407079621990725 3678297125513827429123261)
    ·
      refine ⟨1379361422067685285921223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3678297125513827429123261 1379361422067685285921223)
      ·
        refine ⟨2069042133101527928881835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379361422067685285921223 2069042133101527928881835)
        ·
          refine ⟨3103563199652291893322753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069042133101527928881835 3103563199652291893322753)
          ·
            refine ⟨2327672399739218919992065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3103563199652291893322753 2327672399739218919992065)
            ·
              refine ⟨1745754299804414189994049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2327672399739218919992065 1745754299804414189994049)
              ·
                refine ⟨1309315724853310642495537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745754299804414189994049 1309315724853310642495537)
                ·
                  refine ⟨981986793639982981871653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1309315724853310642495537 981986793639982981871653)
                  ·
                    refine ⟨184122523807496809100935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 981986793639982981871653 184122523807496809100935)
                    ·
                      rfl

theorem cell23_1075732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1075732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075732 prefixEnd_1075732 := by exact prefixLift 1075732
  have htrace : WordTrace (prefixWord ++ tailWord_1075732) baseStart_1075732 baseEnd_1075732 := by
    simpa [prefixWord, tailWord_1075732, baseEnd_1075732] using wordTrace_append hprefix tailTrace_1075732
  have hstable : (prefixWord ++ tailWord_1075732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075732).length < 2 ^ (prefixWord ++ tailWord_1075732).sum := by decide
  have hdescent : baseEnd_1075732 < baseStart_1075732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075738 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_1075738 : Nat := 118140960795 + 1075738 * 2 ^ 59
def prefixEnd_1075738 : Nat := 4983230072969 + 3 ^ 40 * 1075738 * 2
def baseEnd_1075738 : Nat := 552370652306417403827777

theorem tailTrace_1075738 : CollatzResearch.WordTrace tailWord_1075738 prefixEnd_1075738 552370652306417403827777 := by
  unfold tailWord_1075738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9808847044198105567174967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26156925451194948179133245 9808847044198105567174967)
  ·
    refine ⟨14713270566297158350762451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9808847044198105567174967 14713270566297158350762451)
    ·
      refine ⟨22069905849445737526143677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14713270566297158350762451 22069905849445737526143677)
      ·
        refine ⟨8276214693542151572303879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22069905849445737526143677 8276214693542151572303879)
        ·
          refine ⟨12414322040313227358455819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8276214693542151572303879 12414322040313227358455819)
          ·
            refine ⟨18621483060469841037683729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12414322040313227358455819 18621483060469841037683729)
            ·
              refine ⟨13966112295352380778262797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18621483060469841037683729 13966112295352380778262797)
              ·
                refine ⟨5237292110757142791848549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13966112295352380778262797 5237292110757142791848549)
                ·
                  refine ⟨981992270766964273471603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5237292110757142791848549 981992270766964273471603)
                  ·
                    refine ⟨1472988406150446410207405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 981992270766964273471603 1472988406150446410207405)
                    ·
                      refine ⟨552370652306417403827777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1472988406150446410207405 552370652306417403827777)
                      ·
                        rfl

theorem cell23_1075738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_1075738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075738 prefixEnd_1075738 := by exact prefixLift 1075738
  have htrace : WordTrace (prefixWord ++ tailWord_1075738) baseStart_1075738 baseEnd_1075738 := by
    simpa [prefixWord, tailWord_1075738, baseEnd_1075738] using wordTrace_append hprefix tailTrace_1075738
  have hstable : (prefixWord ++ tailWord_1075738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075738).length < 2 ^ (prefixWord ++ tailWord_1075738).sum := by decide
  have hdescent : baseEnd_1075738 < baseStart_1075738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075741 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1075741 : Nat := 118140960795 + 1075741 * 2 ^ 59
def prefixEnd_1075741 : Nat := 4983230072969 + 3 ^ 40 * 1075741 * 2
def baseEnd_1075741 : Nat := 184124064249460297363421

theorem tailTrace_1075741 : CollatzResearch.WordTrace tailWord_1075741 prefixEnd_1075741 184124064249460297363421 := by
  unfold tailWord_1075741
  simp only [CollatzResearch.WordTrace]
  refine ⟨39235497595781553781059077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26156998397187702520706051 39235497595781553781059077)
  ·
    refine ⟨7356655799209041333948577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39235497595781553781059077 7356655799209041333948577)
    ·
      refine ⟨5517491849406781000461433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7356655799209041333948577 5517491849406781000461433)
      ·
        refine ⟨4138118887055085750346075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5517491849406781000461433 4138118887055085750346075)
        ·
          refine ⟨6207178330582628625519113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138118887055085750346075 6207178330582628625519113)
          ·
            refine ⟨4655383747936971469139335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6207178330582628625519113 4655383747936971469139335)
            ·
              refine ⟨6983075621905457203709003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655383747936971469139335 6983075621905457203709003)
              ·
                refine ⟨10474613432858185805563505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6983075621905457203709003 10474613432858185805563505)
                ·
                  refine ⟨7855960074643639354172629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10474613432858185805563505 7855960074643639354172629)
                  ·
                    refine ⟨184124064249460297363421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7855960074643639354172629 184124064249460297363421)
                    ·
                      rfl

theorem cell23_1075741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1075741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075741 prefixEnd_1075741 := by exact prefixLift 1075741
  have htrace : WordTrace (prefixWord ++ tailWord_1075741) baseStart_1075741 baseEnd_1075741 := by
    simpa [prefixWord, tailWord_1075741, baseEnd_1075741] using wordTrace_append hprefix tailTrace_1075741
  have hstable : (prefixWord ++ tailWord_1075741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075741).length < 2 ^ (prefixWord ++ tailWord_1075741).sum := by decide
  have hdescent : baseEnd_1075741 < baseStart_1075741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075765 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_1075765 : Nat := 118140960795 + 1075765 * 2 ^ 59
def prefixEnd_1075765 : Nat := 4983230072969 + 3 ^ 40 * 1075765 * 2
def baseEnd_1075765 : Nat := 552384516284088798190153

theorem tailTrace_1075765 : CollatzResearch.WordTrace tailWord_1075765 prefixEnd_1075765 552384516284088798190153 := by
  unfold tailWord_1075765
  simp only [CollatzResearch.WordTrace]
  refine ⟨39236372947694605879932749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26157581965129737253288499 39236372947694605879932749)
  ·
    refine ⟨14713639855385477204974781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39236372947694605879932749 14713639855385477204974781)
    ·
      refine ⟨5517614945769553951865543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14713639855385477204974781 5517614945769553951865543)
      ·
        refine ⟨8276422418654330927798315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5517614945769553951865543 8276422418654330927798315)
        ·
          refine ⟨12414633627981496391697473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8276422418654330927798315 12414633627981496391697473)
          ·
            refine ⟨9310975220986122293773105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12414633627981496391697473 9310975220986122293773105)
            ·
              refine ⟨6983231415739591720329829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9310975220986122293773105 6983231415739591720329829)
              ·
                refine ⟨1309355890451173447561843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6983231415739591720329829 1309355890451173447561843)
                ·
                  refine ⟨1964033835676760171342765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309355890451173447561843 1964033835676760171342765)
                  ·
                    refine ⟨736512688378785064253537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1964033835676760171342765 736512688378785064253537)
                    ·
                      refine ⟨552384516284088798190153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736512688378785064253537 552384516284088798190153)
                      ·
                        rfl

theorem cell23_1075765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_1075765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075765 prefixEnd_1075765 := by exact prefixLift 1075765
  have htrace : WordTrace (prefixWord ++ tailWord_1075765) baseStart_1075765 baseEnd_1075765 := by
    simpa [prefixWord, tailWord_1075765, baseEnd_1075765] using wordTrace_append hprefix tailTrace_1075765
  have hstable : (prefixWord ++ tailWord_1075765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075765).length < 2 ^ (prefixWord ++ tailWord_1075765).sum := by decide
  have hdescent : baseEnd_1075765 < baseStart_1075765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075789 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1075789 : Nat := 118140960795 + 1075789 * 2 ^ 59
def prefixEnd_1075789 : Nat := 4983230072969 + 3 ^ 40 * 1075789 * 2
def baseEnd_1075789 : Nat := 552396839819796704290043

theorem tailTrace_1075789 : CollatzResearch.WordTrace tailWord_1075789 prefixEnd_1075789 552396839819796704290043 := by
  unfold tailWord_1075789
  simp only [CollatzResearch.WordTrace]
  refine ⟨39237248299607657978806421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26158165533071771985870947 39237248299607657978806421)
  ·
    refine ⟨1839246014044108967756551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39237248299607657978806421 1839246014044108967756551)
    ·
      refine ⟨2758869021066163451634827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1839246014044108967756551 2758869021066163451634827)
      ·
        refine ⟨4138303531599245177452241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2758869021066163451634827 4138303531599245177452241)
        ·
          refine ⟨3103727648699433883089181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4138303531599245177452241 3103727648699433883089181)
          ·
            refine ⟨1163897868262287706158443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3103727648699433883089181 1163897868262287706158443)
            ·
              refine ⟨1745846802393431559237665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163897868262287706158443 1745846802393431559237665)
              ·
                refine ⟨1309385101795073669428249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745846802393431559237665 1309385101795073669428249)
                ·
                  refine ⟨982038826346305252071187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1309385101795073669428249 982038826346305252071187)
                  ·
                    refine ⟨1473058239519457878106781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 982038826346305252071187 1473058239519457878106781)
                    ·
                      refine ⟨552396839819796704290043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1473058239519457878106781 552396839819796704290043)
                      ·
                        rfl

theorem cell23_1075789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1075789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075789 prefixEnd_1075789 := by exact prefixLift 1075789
  have htrace : WordTrace (prefixWord ++ tailWord_1075789) baseStart_1075789 baseEnd_1075789 := by
    simpa [prefixWord, tailWord_1075789, baseEnd_1075789] using wordTrace_append hprefix tailTrace_1075789
  have hstable : (prefixWord ++ tailWord_1075789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075789).length < 2 ^ (prefixWord ++ tailWord_1075789).sum := by decide
  have hdescent : baseEnd_1075789 < baseStart_1075789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075791 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_1075791 : Nat := 118140960795 + 1075791 * 2 ^ 59
def prefixEnd_1075791 : Nat := 4983230072969 + 3 ^ 40 * 1075791 * 2
def baseEnd_1075791 : Nat := 552397866781105696465033

theorem tailTrace_1075791 : CollatzResearch.WordTrace tailWord_1075791 prefixEnd_1075791 552397866781105696465033 := by
  unfold tailWord_1075791
  simp only [CollatzResearch.WordTrace]
  refine ⟨39237321245600412320379227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26158214163733608213586151 39237321245600412320379227)
  ·
    refine ⟨58855981868400618480568841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39237321245600412320379227 58855981868400618480568841)
    ·
      refine ⟨44141986401300463860426631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58855981868400618480568841 44141986401300463860426631)
      ·
        refine ⟨66212979601950695790639947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44141986401300463860426631 66212979601950695790639947)
        ·
          refine ⟨99319469402926043685959921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66212979601950695790639947 99319469402926043685959921)
          ·
            refine ⟨74489602052194532764469941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99319469402926043685959921 74489602052194532764469941)
            ·
              refine ⟨6983400192393237446669057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74489602052194532764469941 6983400192393237446669057)
              ·
                refine ⟨5237550144294928085001793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6983400192393237446669057 5237550144294928085001793)
                ·
                  refine ⟨3928162608221196063751345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5237550144294928085001793 3928162608221196063751345)
                  ·
                    refine ⟨2946121956165897047813509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928162608221196063751345 2946121956165897047813509)
                    ·
                      refine ⟨552397866781105696465033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2946121956165897047813509 552397866781105696465033)
                      ·
                        rfl

theorem cell23_1075791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_1075791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075791 prefixEnd_1075791 := by exact prefixLift 1075791
  have htrace : WordTrace (prefixWord ++ tailWord_1075791) baseStart_1075791 baseEnd_1075791 := by
    simpa [prefixWord, tailWord_1075791, baseEnd_1075791] using wordTrace_append hprefix tailTrace_1075791
  have hstable : (prefixWord ++ tailWord_1075791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075791).length < 2 ^ (prefixWord ++ tailWord_1075791).sum := by decide
  have hdescent : baseEnd_1075791 < baseStart_1075791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075806 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1075806 : Nat := 118140960795 + 1075806 * 2 ^ 59
def prefixEnd_1075806 : Nat := 4983230072969 + 3 ^ 40 * 1075806 * 2
def baseEnd_1075806 : Nat := 552405568990923137777465

theorem tailTrace_1075806 : CollatzResearch.WordTrace tailWord_1075806 prefixEnd_1075806 552405568990923137777465 := by
  unfold tailWord_1075806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904733542568258735271909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26158578893697379921450181 4904733542568258735271909)
  ·
    refine ⟨919637539231548512863483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4904733542568258735271909 919637539231548512863483)
    ·
      refine ⟨1379456308847322769295225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919637539231548512863483 1379456308847322769295225)
      ·
        refine ⟨1034592231635492076971419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1379456308847322769295225 1034592231635492076971419)
        ·
          refine ⟨1551888347453238115457129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034592231635492076971419 1551888347453238115457129)
          ·
            refine ⟨1163916260589928586592847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551888347453238115457129 1163916260589928586592847)
            ·
              refine ⟨1745874390884892879889271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163916260589928586592847 1745874390884892879889271)
              ·
                refine ⟨2618811586327339319833907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1745874390884892879889271 2618811586327339319833907)
                ·
                  refine ⟨3928217379491008979750861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618811586327339319833907 3928217379491008979750861)
                  ·
                    refine ⟨1473081517309128367406573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3928217379491008979750861 1473081517309128367406573)
                    ·
                      refine ⟨552405568990923137777465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1473081517309128367406573 552405568990923137777465)
                      ·
                        rfl

theorem cell23_1075806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1075806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075806 prefixEnd_1075806 := by exact prefixLift 1075806
  have htrace : WordTrace (prefixWord ++ tailWord_1075806) baseStart_1075806 baseEnd_1075806 := by
    simpa [prefixWord, tailWord_1075806, baseEnd_1075806] using wordTrace_append hprefix tailTrace_1075806
  have hstable : (prefixWord ++ tailWord_1075806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075806).length < 2 ^ (prefixWord ++ tailWord_1075806).sum := by decide
  have hdescent : baseEnd_1075806 < baseStart_1075806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075831 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 1, 7]
def baseStart_1075831 : Nat := 118140960795 + 1075831 * 2 ^ 59
def prefixEnd_1075831 : Nat := 4983230072969 + 3 ^ 40 * 1075831 * 2
def baseEnd_1075831 : Nat := 184139468669095179988283

theorem tailTrace_1075831 : CollatzResearch.WordTrace tailWord_1075831 prefixEnd_1075831 184139468669095179988283 := by
  unfold tailWord_1075831
  simp only [CollatzResearch.WordTrace]
  refine ⟨39238780165455499151835347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26159186776970332767890231 39238780165455499151835347)
  ·
    refine ⟨58858170248183248727753021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39238780165455499151835347 58858170248183248727753021)
    ·
      refine ⟨22071813843068718272907383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58858170248183248727753021 22071813843068718272907383)
      ·
        refine ⟨33107720764603077409361075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22071813843068718272907383 33107720764603077409361075)
        ·
          refine ⟨49661581146904616114041613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33107720764603077409361075 49661581146904616114041613)
          ·
            refine ⟨18623092930089231042765605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49661581146904616114041613 18623092930089231042765605)
            ·
              refine ⟨3491829924391730820518551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18623092930089231042765605 3491829924391730820518551)
              ·
                refine ⟨5237744886587596230777827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3491829924391730820518551 5237744886587596230777827)
                ·
                  refine ⟨7856617329881394346166741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5237744886587596230777827 7856617329881394346166741)
                  ·
                    refine ⟨184139468669095179988283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7856617329881394346166741 184139468669095179988283)
                    ·
                      rfl

theorem cell23_1075831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_1075831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075831 prefixEnd_1075831 := by exact prefixLift 1075831
  have htrace : WordTrace (prefixWord ++ tailWord_1075831) baseStart_1075831 baseEnd_1075831 := by
    simpa [prefixWord, tailWord_1075831, baseEnd_1075831] using wordTrace_append hprefix tailTrace_1075831
  have hstable : (prefixWord ++ tailWord_1075831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075831).length < 2 ^ (prefixWord ++ tailWord_1075831).sum := by decide
  have hdescent : baseEnd_1075831 < baseStart_1075831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075851 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4]
def baseStart_1075851 : Nat := 118140960795 + 1075851 * 2 ^ 59
def prefixEnd_1075851 : Nat := 4983230072969 + 3 ^ 40 * 1075851 * 2
def baseEnd_1075851 : Nat := 552428675620375461714757

theorem tailTrace_1075851 : CollatzResearch.WordTrace tailWord_1075851 prefixEnd_1075851 552428675620375461714757 := by
  unfold tailWord_1075851
  simp only [CollatzResearch.WordTrace]
  refine ⟨39239509625383042567563407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26159673083588695045042271 39239509625383042567563407)
  ·
    refine ⟨58859264438074563851345111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39239509625383042567563407 58859264438074563851345111)
    ·
      refine ⟨88288896657111845777017667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58859264438074563851345111 88288896657111845777017667)
      ·
        refine ⟨132433344985667768665526501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88288896657111845777017667 132433344985667768665526501)
        ·
          refine ⟨24831252184812706624786219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132433344985667768665526501 24831252184812706624786219)
          ·
            refine ⟨37246878277219059937179329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24831252184812706624786219 37246878277219059937179329)
            ·
              refine ⟨27935158707914294952884497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37246878277219059937179329 27935158707914294952884497)
              ·
                refine ⟨20951369030935721214663373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27935158707914294952884497 20951369030935721214663373)
                ·
                  refine ⟨7856763386600895455498765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20951369030935721214663373 7856763386600895455498765)
                  ·
                    refine ⟨2946286269975335795812037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7856763386600895455498765 2946286269975335795812037)
                    ·
                      refine ⟨552428675620375461714757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2946286269975335795812037 552428675620375461714757)
                      ·
                        rfl

theorem cell23_1075851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_1075851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075851 prefixEnd_1075851 := by exact prefixLift 1075851
  have htrace : WordTrace (prefixWord ++ tailWord_1075851) baseStart_1075851 baseEnd_1075851 := by
    simpa [prefixWord, tailWord_1075851, baseEnd_1075851] using wordTrace_append hprefix tailTrace_1075851
  have hstable : (prefixWord ++ tailWord_1075851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075851).length < 2 ^ (prefixWord ++ tailWord_1075851).sum := by decide
  have hdescent : baseEnd_1075851 < baseStart_1075851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075858 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1075858 : Nat := 118140960795 + 1075858 * 2 ^ 59
def prefixEnd_1075858 : Nat := 4983230072969 + 3 ^ 40 * 1075858 * 2
def baseEnd_1075858 : Nat := 552432269984956934327225

theorem tailTrace_1075858 : CollatzResearch.WordTrace tailWord_1075858 prefixEnd_1075858 552432269984956934327225 := by
  unfold tailWord_1075858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9809941234089420690767057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26159843290905121842045485 9809941234089420690767057)
  ·
    refine ⟨7357455925567065518075293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9809941234089420690767057 7357455925567065518075293)
    ·
      refine ⟨2759045972087649569278235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7357455925567065518075293 2759045972087649569278235)
      ·
        refine ⟨4138568958131474353917353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2759045972087649569278235 4138568958131474353917353)
        ·
          refine ⟨3103926718598605765438015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4138568958131474353917353 3103926718598605765438015)
          ·
            refine ⟨4655890077897908648157023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103926718598605765438015 4655890077897908648157023)
            ·
              refine ⟨6983835116846862972235535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655890077897908648157023 6983835116846862972235535)
              ·
                refine ⟨10475752675270294458353303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6983835116846862972235535 10475752675270294458353303)
                ·
                  refine ⟨15713629012905441687529955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10475752675270294458353303 15713629012905441687529955)
                  ·
                    refine ⟨23570443519358162531294933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15713629012905441687529955 23570443519358162531294933)
                    ·
                      refine ⟨552432269984956934327225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23570443519358162531294933 552432269984956934327225)
                      ·
                        rfl

theorem cell23_1075858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1075858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075858 prefixEnd_1075858 := by exact prefixLift 1075858
  have htrace : WordTrace (prefixWord ++ tailWord_1075858) baseStart_1075858 baseEnd_1075858 := by
    simpa [prefixWord, tailWord_1075858, baseEnd_1075858] using wordTrace_append hprefix tailTrace_1075858
  have hstable : (prefixWord ++ tailWord_1075858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075858).length < 2 ^ (prefixWord ++ tailWord_1075858).sum := by decide
  have hdescent : baseEnd_1075858 < baseStart_1075858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075881 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_1075881 : Nat := 118140960795 + 1075881 * 2 ^ 59
def prefixEnd_1075881 : Nat := 4983230072969 + 3 ^ 40 * 1075881 * 2
def baseEnd_1075881 : Nat := 552444080040010344339619

theorem tailTrace_1075881 : CollatzResearch.WordTrace tailWord_1075881 prefixEnd_1075881 552444080040010344339619 := by
  unfold tailWord_1075881
  simp only [CollatzResearch.WordTrace]
  refine ⟨39240603815274357691155497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26160402543516238460770331 39240603815274357691155497)
  ·
    refine ⟨29430452861455768268366623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39240603815274357691155497 29430452861455768268366623)
    ·
      refine ⟨44145679292183652402549935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29430452861455768268366623 44145679292183652402549935)
      ·
        refine ⟨66218518938275478603824903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44145679292183652402549935 66218518938275478603824903)
        ·
          refine ⟨99327778407413217905737355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66218518938275478603824903 99327778407413217905737355)
          ·
            refine ⟨148991667611119826858606033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99327778407413217905737355 148991667611119826858606033)
            ·
              refine ⟨111743750708339870143954525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148991667611119826858606033 111743750708339870143954525)
              ·
                refine ⟨41903906515627451303982947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111743750708339870143954525 41903906515627451303982947)
                ·
                  refine ⟨62855859773441176955974421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41903906515627451303982947 62855859773441176955974421)
                  ·
                    refine ⟨2946368426880055169811301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62855859773441176955974421 2946368426880055169811301)
                    ·
                      refine ⟨552444080040010344339619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2946368426880055169811301 552444080040010344339619)
                      ·
                        rfl

theorem cell23_1075881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_1075881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075881 prefixEnd_1075881 := by exact prefixLift 1075881
  have htrace : WordTrace (prefixWord ++ tailWord_1075881) baseStart_1075881 baseEnd_1075881 := by
    simpa [prefixWord, tailWord_1075881, baseEnd_1075881] using wordTrace_append hprefix tailTrace_1075881
  have hstable : (prefixWord ++ tailWord_1075881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075881).length < 2 ^ (prefixWord ++ tailWord_1075881).sum := by decide
  have hdescent : baseEnd_1075881 < baseStart_1075881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075885 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1075885 : Nat := 118140960795 + 1075885 * 2 ^ 59
def prefixEnd_1075885 : Nat := 4983230072969 + 3 ^ 40 * 1075885 * 2
def baseEnd_1075885 : Nat := 552446133962628328689601

theorem tailTrace_1075885 : CollatzResearch.WordTrace tailWord_1075885 prefixEnd_1075885 552446133962628328689601 := by
  unfold tailWord_1075885
  simp only [CollatzResearch.WordTrace]
  refine ⟨39240749707259866374301109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26160499804839910916200739 39240749707259866374301109)
  ·
    refine ⟨3678820285055612472590729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39240749707259866374301109 3678820285055612472590729)
    ·
      refine ⟨2759115213791709354443047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3678820285055612472590729 2759115213791709354443047)
      ·
        refine ⟨4138672820687564031664571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2759115213791709354443047 4138672820687564031664571)
        ·
          refine ⟨6208009231031346047496857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138672820687564031664571 6208009231031346047496857)
          ·
            refine ⟨4656006923273509535622643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6208009231031346047496857 4656006923273509535622643)
            ·
              refine ⟨6984010384910264303433965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656006923273509535622643 6984010384910264303433965)
              ·
                refine ⟨2619003894341349113787737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6984010384910264303433965 2619003894341349113787737)
                ·
                  refine ⟨1964252920756011835340803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619003894341349113787737 1964252920756011835340803)
                  ·
                    refine ⟨2946379381134017753011205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1964252920756011835340803 2946379381134017753011205)
                    ·
                      refine ⟨552446133962628328689601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2946379381134017753011205 552446133962628328689601)
                      ·
                        rfl

theorem cell23_1075885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1075885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075885 prefixEnd_1075885 := by exact prefixLift 1075885
  have htrace : WordTrace (prefixWord ++ tailWord_1075885) baseStart_1075885 baseEnd_1075885 := by
    simpa [prefixWord, tailWord_1075885, baseEnd_1075885] using wordTrace_append hprefix tailTrace_1075885
  have hstable : (prefixWord ++ tailWord_1075885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075885).length < 2 ^ (prefixWord ++ tailWord_1075885).sum := by decide
  have hdescent : baseEnd_1075885 < baseStart_1075885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075912 : List Nat := [2, 1, 3, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1075912 : Nat := 118140960795 + 1075912 * 2 ^ 59
def prefixEnd_1075912 : Nat := 4983230072969 + 3 ^ 40 * 1075912 * 2
def baseEnd_1075912 : Nat := 184153332646766574350659

theorem tailTrace_1075912 : CollatzResearch.WordTrace tailWord_1075912 prefixEnd_1075912 184153332646766574350659 := by
  unfold tailWord_1075912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19620867239081024992766995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26161156318774699990355993 19620867239081024992766995)
  ·
    refine ⟨29431300858621537489150493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19620867239081024992766995 29431300858621537489150493)
    ·
      refine ⟨11036737821983076558431435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29431300858621537489150493 11036737821983076558431435)
      ·
        refine ⟨16555106732974614837647153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11036737821983076558431435 16555106732974614837647153)
        ·
          refine ⟨12416330049730961128235365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16555106732974614837647153 12416330049730961128235365)
          ·
            refine ⟨2328061884324555211544131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12416330049730961128235365 2328061884324555211544131)
            ·
              refine ⟨3492092826486832817316197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328061884324555211544131 3492092826486832817316197)
              ·
                refine ⟨654767404966281153246787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3492092826486832817316197 654767404966281153246787)
                ·
                  refine ⟨982151107449421729870181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654767404966281153246787 982151107449421729870181)
                  ·
                    refine ⟨184153332646766574350659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982151107449421729870181 184153332646766574350659)
                    ·
                      rfl

theorem cell23_1075912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1075912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075912 prefixEnd_1075912 := by exact prefixLift 1075912
  have htrace : WordTrace (prefixWord ++ tailWord_1075912) baseStart_1075912 baseEnd_1075912 := by
    simpa [prefixWord, tailWord_1075912, baseEnd_1075912] using wordTrace_append hprefix tailTrace_1075912
  have hstable : (prefixWord ++ tailWord_1075912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075912).length < 2 ^ (prefixWord ++ tailWord_1075912).sum := by decide
  have hdescent : baseEnd_1075912 < baseStart_1075912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075935 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 3]
def baseStart_1075935 : Nat := 118140960795 + 1075935 * 2 ^ 59
def prefixEnd_1075935 : Nat := 4983230072969 + 3 ^ 40 * 1075935 * 2
def baseEnd_1075935 : Nat := 552471807995353133064371

theorem tailTrace_1075935 : CollatzResearch.WordTrace tailWord_1075935 prefixEnd_1075935 552471807995353133064371 := by
  unfold tailWord_1075935
  simp only [CollatzResearch.WordTrace]
  refine ⟨39242573357078724913621259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26161715571385816609080839 39242573357078724913621259)
  ·
    refine ⟨58863860035618087370431889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39242573357078724913621259 58863860035618087370431889)
    ·
      refine ⟨44147895026713565527823917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58863860035618087370431889 44147895026713565527823917)
      ·
        refine ⟨16555460635017587072933969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44147895026713565527823917 16555460635017587072933969)
        ·
          refine ⟨12416595476263190304700477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16555460635017587072933969 12416595476263190304700477)
          ·
            refine ⟨4656223303598696364262679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12416595476263190304700477 4656223303598696364262679)
            ·
              refine ⟨6984334955398044546394019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656223303598696364262679 6984334955398044546394019)
              ·
                refine ⟨10476502433097066819591029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6984334955398044546394019 10476502433097066819591029)
                ·
                  refine ⟨982172103102850014336659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10476502433097066819591029 982172103102850014336659)
                  ·
                    refine ⟨1473258154654275021504989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 982172103102850014336659 1473258154654275021504989)
                    ·
                      refine ⟨552471807995353133064371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1473258154654275021504989 552471807995353133064371)
                      ·
                        rfl

theorem cell23_1075935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_1075935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075935 prefixEnd_1075935 := by exact prefixLift 1075935
  have htrace : WordTrace (prefixWord ++ tailWord_1075935) baseStart_1075935 baseEnd_1075935 := by
    simpa [prefixWord, tailWord_1075935, baseEnd_1075935] using wordTrace_append hprefix tailTrace_1075935
  have hstable : (prefixWord ++ tailWord_1075935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075935).length < 2 ^ (prefixWord ++ tailWord_1075935).sum := by decide
  have hdescent : baseEnd_1075935 < baseStart_1075935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075985 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 2, 4]
def baseStart_1075985 : Nat := 118140960795 + 1075985 * 2 ^ 59
def prefixEnd_1075985 : Nat := 4983230072969 + 3 ^ 40 * 1075985 * 2
def baseEnd_1075985 : Nat := 184165827342692645813047

theorem tailTrace_1075985 : CollatzResearch.WordTrace tailWord_1075985 prefixEnd_1075985 184165827342692645813047 := by
  unfold tailWord_1075985
  simp only [CollatzResearch.WordTrace]
  refine ⟨39244397006897583452941409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26162931337931722301960939 39244397006897583452941409)
  ·
    refine ⟨29433297755173187589706057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39244397006897583452941409 29433297755173187589706057)
    ·
      refine ⟨22074973316379890692279543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29433297755173187589706057 22074973316379890692279543)
      ·
        refine ⟨33112459974569836038419315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22074973316379890692279543 33112459974569836038419315)
        ·
          refine ⟨49668689961854754057628973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33112459974569836038419315 49668689961854754057628973)
          ·
            refine ⟨18625758735695532771610865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49668689961854754057628973 18625758735695532771610865)
            ·
              refine ⟨13969319051771649578708149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18625758735695532771610865 13969319051771649578708149)
              ·
                refine ⟨1309623661103592148003889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13969319051771649578708149 1309623661103592148003889)
                ·
                  refine ⟨982217745827694111002917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1309623661103592148003889 982217745827694111002917)
                  ·
                    refine ⟨184165827342692645813047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982217745827694111002917 184165827342692645813047)
                    ·
                      rfl

theorem cell23_1075985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_1075985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1075985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1075985 prefixEnd_1075985 := by exact prefixLift 1075985
  have htrace : WordTrace (prefixWord ++ tailWord_1075985) baseStart_1075985 baseEnd_1075985 := by
    simpa [prefixWord, tailWord_1075985, baseEnd_1075985] using wordTrace_append hprefix tailTrace_1075985
  have hstable : (prefixWord ++ tailWord_1075985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075985).length < 2 ^ (prefixWord ++ tailWord_1075985).sum := by decide
  have hdescent : baseEnd_1075985 < baseStart_1075985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076026 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2]
def baseStart_1076026 : Nat := 118140960795 + 1076026 * 2 ^ 59
def prefixEnd_1076026 : Nat := 4983230072969 + 3 ^ 40 * 1076026 * 2
def baseEnd_1076026 : Nat := 552518534734912277026453

theorem tailTrace_1076026 : CollatzResearch.WordTrace tailWord_1076026 prefixEnd_1076026 552518534734912277026453 := by
  unfold tailWord_1076026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811473099937261863795983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26163928266499364970122621 9811473099937261863795983)
  ·
    refine ⟨14717209649905892795693975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9811473099937261863795983 14717209649905892795693975)
    ·
      refine ⟨22075814474858839193540963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14717209649905892795693975 22075814474858839193540963)
      ·
        refine ⟨33113721712288258790311445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22075814474858839193540963 33113721712288258790311445)
        ·
          refine ⟨1552205705263512130795849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33113721712288258790311445 1552205705263512130795849)
          ·
            refine ⟨1164154278947634098096887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1552205705263512130795849 1164154278947634098096887)
            ·
              refine ⟨1746231418421451147145331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164154278947634098096887 1746231418421451147145331)
              ·
                refine ⟨2619347127632176720717997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746231418421451147145331 2619347127632176720717997)
                ·
                  refine ⟨982255172862066270269249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2619347127632176720717997 982255172862066270269249)
                  ·
                    refine ⟨736691379646549702701937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 982255172862066270269249 736691379646549702701937)
                    ·
                      refine ⟨552518534734912277026453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736691379646549702701937 552518534734912277026453)
                      ·
                        rfl

theorem cell23_1076026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_1076026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076026 prefixEnd_1076026 := by exact prefixLift 1076026
  have htrace : WordTrace (prefixWord ++ tailWord_1076026) baseStart_1076026 baseEnd_1076026 := by
    simpa [prefixWord, tailWord_1076026, baseEnd_1076026] using wordTrace_append hprefix tailTrace_1076026
  have hstable : (prefixWord ++ tailWord_1076026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076026).length < 2 ^ (prefixWord ++ tailWord_1076026).sum := by decide
  have hdescent : baseEnd_1076026 < baseStart_1076026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076028 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_1076028 : Nat := 118140960795 + 1076028 * 2 ^ 59
def prefixEnd_1076028 : Nat := 4983230072969 + 3 ^ 40 * 1076028 * 2
def baseEnd_1076028 : Nat := 184173187232073756400481

theorem tailTrace_1076028 : CollatzResearch.WordTrace tailWord_1076028 prefixEnd_1076028 184173187232073756400481 := by
  unfold tailWord_1076028
  simp only [CollatzResearch.WordTrace]
  refine ⟨19622982672870900898378369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26163976897161201197837825 19622982672870900898378369)
  ·
    refine ⟨14717237004653175673783777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19622982672870900898378369 14717237004653175673783777)
    ·
      refine ⟨11037927753489881755337833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14717237004653175673783777 11037927753489881755337833)
      ·
        refine ⟨8278445815117411316503375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11037927753489881755337833 8278445815117411316503375)
        ·
          refine ⟨12417668722676116974755063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278445815117411316503375 12417668722676116974755063)
          ·
            refine ⟨18626503084014175462132595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12417668722676116974755063 18626503084014175462132595)
            ·
              refine ⟨27939754626021263193198893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18626503084014175462132595 27939754626021263193198893)
              ·
                refine ⟨10477407984757973697449585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27939754626021263193198893 10477407984757973697449585)
                ·
                  refine ⟨7858055988568480273087189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10477407984757973697449585 7858055988568480273087189)
                  ·
                    refine ⟨184173187232073756400481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7858055988568480273087189 184173187232073756400481)
                    ·
                      rfl

theorem cell23_1076028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_1076028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076028 prefixEnd_1076028 := by exact prefixLift 1076028
  have htrace : WordTrace (prefixWord ++ tailWord_1076028) baseStart_1076028 baseEnd_1076028 := by
    simpa [prefixWord, tailWord_1076028, baseEnd_1076028] using wordTrace_append hprefix tailTrace_1076028
  have hstable : (prefixWord ++ tailWord_1076028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076028).length < 2 ^ (prefixWord ++ tailWord_1076028).sum := by decide
  have hdescent : baseEnd_1076028 < baseStart_1076028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076036 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1076036 : Nat := 118140960795 + 1076036 * 2 ^ 59
def prefixEnd_1076036 : Nat := 4983230072969 + 3 ^ 40 * 1076036 * 2
def baseEnd_1076036 : Nat := 184174556513819079300469

theorem tailTrace_1076036 : CollatzResearch.WordTrace tailWord_1076036 prefixEnd_1076036 184174556513819079300469 := by
  unfold tailWord_1076036
  simp only [CollatzResearch.WordTrace]
  refine ⟨19623128564856409581523981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26164171419808546108698641 19623128564856409581523981)
  ·
    refine ⟨7358673211821153593071493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19623128564856409581523981 7358673211821153593071493)
    ·
      refine ⟨1379751227216466298700905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7358673211821153593071493 1379751227216466298700905)
      ·
        refine ⟨1034813420412349724025679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1379751227216466298700905 1034813420412349724025679)
        ·
          refine ⟨1552220130618524586038519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034813420412349724025679 1552220130618524586038519)
          ·
            refine ⟨2328330195927786879057779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552220130618524586038519 2328330195927786879057779)
            ·
              refine ⟨3492495293891680318586669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328330195927786879057779 3492495293891680318586669)
              ·
                refine ⟨1309685735209380119470001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3492495293891680318586669 1309685735209380119470001)
                ·
                  refine ⟨982264301407035089602501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1309685735209380119470001 982264301407035089602501)
                  ·
                    refine ⟨184174556513819079300469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982264301407035089602501 184174556513819079300469)
                    ·
                      rfl

theorem cell23_1076036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1076036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076036 prefixEnd_1076036 := by exact prefixLift 1076036
  have htrace : WordTrace (prefixWord ++ tailWord_1076036) baseStart_1076036 baseEnd_1076036 := by
    simpa [prefixWord, tailWord_1076036, baseEnd_1076036] using wordTrace_append hprefix tailTrace_1076036
  have hstable : (prefixWord ++ tailWord_1076036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076036).length < 2 ^ (prefixWord ++ tailWord_1076036).sum := by decide
  have hdescent : baseEnd_1076036 < baseStart_1076036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076099 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 2, 2, 2]
def baseStart_1076099 : Nat := 118140960795 + 1076099 * 2 ^ 59
def prefixEnd_1076099 : Nat := 4983230072969 + 3 ^ 40 * 1076099 * 2
def baseEnd_1076099 : Nat := 552556018822690491413617

theorem tailTrace_1076099 : CollatzResearch.WordTrace tailWord_1076099 prefixEnd_1076099 552556018822690491413617 := by
  unfold tailWord_1076099
  simp only [CollatzResearch.WordTrace]
  refine ⟨39248554928484580922591351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26165703285656387281727567 39248554928484580922591351)
  ·
    refine ⟨58872832392726871383887027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39248554928484580922591351 58872832392726871383887027)
    ·
      refine ⟨88309248589090307075830541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58872832392726871383887027 88309248589090307075830541)
      ·
        refine ⟨33115968220908865153436453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88309248589090307075830541 33115968220908865153436453)
        ·
          refine ⟨6209244041420412216269335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33115968220908865153436453 6209244041420412216269335)
          ·
            refine ⟨9313866062130618324404003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6209244041420412216269335 9313866062130618324404003)
            ·
              refine ⟨13970799093195927486606005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9313866062130618324404003 13970799093195927486606005)
              ·
                refine ⟨1309762414987118201869313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13970799093195927486606005 1309762414987118201869313)
                ·
                  refine ⟨982321811240338651401985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1309762414987118201869313 982321811240338651401985)
                  ·
                    refine ⟨736741358430253988551489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 982321811240338651401985 736741358430253988551489)
                    ·
                      refine ⟨552556018822690491413617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736741358430253988551489 552556018822690491413617)
                      ·
                        rfl

theorem cell23_1076099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_1076099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076099 prefixEnd_1076099 := by exact prefixLift 1076099
  have htrace : WordTrace (prefixWord ++ tailWord_1076099) baseStart_1076099 baseEnd_1076099 := by
    simpa [prefixWord, tailWord_1076099, baseEnd_1076099] using wordTrace_append hprefix tailTrace_1076099
  have hstable : (prefixWord ++ tailWord_1076099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076099).length < 2 ^ (prefixWord ++ tailWord_1076099).sum := by decide
  have hdescent : baseEnd_1076099 < baseStart_1076099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076105 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 7]
def baseStart_1076105 : Nat := 118140960795 + 1076105 * 2 ^ 59
def prefixEnd_1076105 : Nat := 4983230072969 + 3 ^ 40 * 1076105 * 2
def baseEnd_1076105 : Nat := 61395455522957496437621

theorem tailTrace_1076105 : CollatzResearch.WordTrace tailWord_1076105 prefixEnd_1076105 61395455522957496437621 := by
  unfold tailWord_1076105
  simp only [CollatzResearch.WordTrace]
  refine ⟨39248773766462843947309769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26165849177641895964873179 39248773766462843947309769)
  ·
    refine ⟨29436580324847132960482327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39248773766462843947309769 29436580324847132960482327)
    ·
      refine ⟨44154870487270699440723491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29436580324847132960482327 44154870487270699440723491)
      ·
        refine ⟨66232305730906049161085237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44154870487270699440723491 66232305730906049161085237)
        ·
          refine ⟨6209278662272442108851741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66232305730906049161085237 6209278662272442108851741)
          ·
            refine ⟨2328479498352165790819403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6209278662272442108851741 2328479498352165790819403)
            ·
              refine ⟨3492719247528248686229105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328479498352165790819403 3492719247528248686229105)
              ·
                refine ⟨2619539435646186514671829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3492719247528248686229105 2619539435646186514671829)
                ·
                  refine ⟨61395455522957496437621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2619539435646186514671829 61395455522957496437621)
                  ·
                    rfl

theorem cell23_1076105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_1076105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076105 prefixEnd_1076105 := by exact prefixLift 1076105
  have htrace : WordTrace (prefixWord ++ tailWord_1076105) baseStart_1076105 baseEnd_1076105 := by
    simpa [prefixWord, tailWord_1076105, baseEnd_1076105] using wordTrace_append hprefix tailTrace_1076105
  have hstable : (prefixWord ++ tailWord_1076105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076105).length < 2 ^ (prefixWord ++ tailWord_1076105).sum := by decide
  have hdescent : baseEnd_1076105 < baseStart_1076105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076172 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1076172 : Nat := 118140960795 + 1076172 * 2 ^ 59
def prefixEnd_1076172 : Nat := 4983230072969 + 3 ^ 40 * 1076172 * 2
def baseEnd_1076172 : Nat := 552593502910468705800781

theorem tailTrace_1076172 : CollatzResearch.WordTrace tailWord_1076172 prefixEnd_1076172 552593502910468705800781 := by
  unfold tailWord_1076172
  simp only [CollatzResearch.WordTrace]
  refine ⟨19625608728610057194999385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26167478304813409593332513 19625608728610057194999385)
  ·
    refine ⟨14719206546457542896249539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19625608728610057194999385 14719206546457542896249539)
    ·
      refine ⟨22078809819686314344374309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14719206546457542896249539 22078809819686314344374309)
      ·
        refine ⟨4139776841191183939570183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22078809819686314344374309 4139776841191183939570183)
        ·
          refine ⟨6209665261786775909355275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4139776841191183939570183 6209665261786775909355275)
          ·
            refine ⟨9314497892680163864032913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6209665261786775909355275 9314497892680163864032913)
            ·
              refine ⟨6985873419510122898024685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9314497892680163864032913 6985873419510122898024685)
              ·
                refine ⟨2619702532316296086759257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6985873419510122898024685 2619702532316296086759257)
                ·
                  refine ⟨1964776899237222065069443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619702532316296086759257 1964776899237222065069443)
                  ·
                    refine ⟨2947165348855833097604165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1964776899237222065069443 2947165348855833097604165)
                    ·
                      refine ⟨552593502910468705800781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2947165348855833097604165 552593502910468705800781)
                      ·
                        rfl

theorem cell23_1076172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1076172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076172 prefixEnd_1076172 := by exact prefixLift 1076172
  have htrace : WordTrace (prefixWord ++ tailWord_1076172) baseStart_1076172 baseEnd_1076172 := by
    simpa [prefixWord, tailWord_1076172, baseEnd_1076172] using wordTrace_append hprefix tailTrace_1076172
  have hstable : (prefixWord ++ tailWord_1076172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076172).length < 2 ^ (prefixWord ++ tailWord_1076172).sum := by decide
  have hdescent : baseEnd_1076172 < baseStart_1076172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076189 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1076189 : Nat := 118140960795 + 1076189 * 2 ^ 59
def prefixEnd_1076189 : Nat := 4983230072969 + 3 ^ 40 * 1076189 * 2
def baseEnd_1076189 : Nat := 552602232081595139288203

theorem tailTrace_1076189 : CollatzResearch.WordTrace tailWord_1076189 prefixEnd_1076189 552602232081595139288203 := by
  unfold tailWord_1076189
  simp only [CollatzResearch.WordTrace]
  refine ⟨39251837498158526293367621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26167891665439017528911747 39251837498158526293367621)
  ·
    refine ⟨7359719530904723680006429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39251837498158526293367621 7359719530904723680006429)
    ·
      refine ⟨2759894824089271380002411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7359719530904723680006429 2759894824089271380002411)
      ·
        refine ⟨4139842236133907070003617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2759894824089271380002411 4139842236133907070003617)
        ·
          refine ⟨3104881677100430302502713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4139842236133907070003617 3104881677100430302502713)
          ·
            refine ⟨2328661257825322726877035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104881677100430302502713 2328661257825322726877035)
            ·
              refine ⟨3492991886737984090315553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328661257825322726877035 3492991886737984090315553)
              ·
                refine ⟨2619743915053488067736665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3492991886737984090315553 2619743915053488067736665)
                ·
                  refine ⟨1964807936290116050802499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619743915053488067736665 1964807936290116050802499)
                  ·
                    refine ⟨2947211904435174076203749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1964807936290116050802499 2947211904435174076203749)
                    ·
                      refine ⟨552602232081595139288203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2947211904435174076203749 552602232081595139288203)
                      ·
                        rfl

theorem cell23_1076189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1076189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076189 prefixEnd_1076189 := by exact prefixLift 1076189
  have htrace : WordTrace (prefixWord ++ tailWord_1076189) baseStart_1076189 baseEnd_1076189 := by
    simpa [prefixWord, tailWord_1076189, baseEnd_1076189] using wordTrace_append hprefix tailTrace_1076189
  have hstable : (prefixWord ++ tailWord_1076189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076189).length < 2 ^ (prefixWord ++ tailWord_1076189).sum := by decide
  have hdescent : baseEnd_1076189 < baseStart_1076189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076195 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 8]
def baseStart_1076195 : Nat := 118140960795 + 1076195 * 2 ^ 59
def prefixEnd_1076195 : Nat := 4983230072969 + 3 ^ 40 * 1076195 * 2
def baseEnd_1076195 : Nat := 61400590329502457312575

theorem tailTrace_1076195 : CollatzResearch.WordTrace tailWord_1076195 prefixEnd_1076195 61400590329502457312575 := by
  unfold tailWord_1076195
  simp only [CollatzResearch.WordTrace]
  refine ⟨39252056336136789318086039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26168037557424526212057359 39252056336136789318086039)
  ·
    refine ⟨58878084504205183977129059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39252056336136789318086039 58878084504205183977129059)
    ·
      refine ⟨88317126756307775965693589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58878084504205183977129059 88317126756307775965693589)
      ·
        refine ⟨4139865316701926998391887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88317126756307775965693589 4139865316701926998391887)
        ·
          refine ⟨6209797975052890497587831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4139865316701926998391887 6209797975052890497587831)
          ·
            refine ⟨9314696962579335746381747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6209797975052890497587831 9314696962579335746381747)
            ·
              refine ⟨13972045443869003619572621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9314696962579335746381747 13972045443869003619572621)
              ·
                refine ⟨5239517041450876357339733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13972045443869003619572621 5239517041450876357339733)
                ·
                  refine ⟨61400590329502457312575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5239517041450876357339733 61400590329502457312575)
                  ·
                    rfl

theorem cell23_1076195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 8].length) (baseStart_1076195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076195 prefixEnd_1076195 := by exact prefixLift 1076195
  have htrace : WordTrace (prefixWord ++ tailWord_1076195) baseStart_1076195 baseEnd_1076195 := by
    simpa [prefixWord, tailWord_1076195, baseEnd_1076195] using wordTrace_append hprefix tailTrace_1076195
  have hstable : (prefixWord ++ tailWord_1076195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076195).length < 2 ^ (prefixWord ++ tailWord_1076195).sum := by decide
  have hdescent : baseEnd_1076195 < baseStart_1076195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076199 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 3, 4]
def baseStart_1076199 : Nat := 118140960795 + 1076199 * 2 ^ 59
def prefixEnd_1076199 : Nat := 4983230072969 + 3 ^ 40 * 1076199 * 2
def baseEnd_1076199 : Nat := 184202455629380033387719

theorem tailTrace_1076199 : CollatzResearch.WordTrace tailWord_1076199 prefixEnd_1076199 184202455629380033387719 := by
  unfold tailWord_1076199
  simp only [CollatzResearch.WordTrace]
  refine ⟨39252202228122298001231651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26168134818748198667487767 39252202228122298001231651)
  ·
    refine ⟨58878303342183447001847477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39252202228122298001231651 58878303342183447001847477)
    ·
      refine ⟨5519840938329698156423201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58878303342183447001847477 5519840938329698156423201)
      ·
        refine ⟨4139880703747273617317401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5519840938329698156423201 4139880703747273617317401)
        ·
          refine ⟨3104910527810455212988051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4139880703747273617317401 3104910527810455212988051)
          ·
            refine ⟨4657365791715682819482077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104910527810455212988051 4657365791715682819482077)
            ·
              refine ⟨1746512171893381057305779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4657365791715682819482077 1746512171893381057305779)
              ·
                refine ⟨2619768257840071585958669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746512171893381057305779 2619768257840071585958669)
                ·
                  refine ⟨982413096690026844734501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2619768257840071585958669 982413096690026844734501)
                  ·
                    refine ⟨184202455629380033387719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982413096690026844734501 184202455629380033387719)
                    ·
                      rfl

theorem cell23_1076199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_1076199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076199 prefixEnd_1076199 := by exact prefixLift 1076199
  have htrace : WordTrace (prefixWord ++ tailWord_1076199) baseStart_1076199 baseEnd_1076199 := by
    simpa [prefixWord, tailWord_1076199, baseEnd_1076199] using wordTrace_append hprefix tailTrace_1076199
  have hstable : (prefixWord ++ tailWord_1076199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076199).length < 2 ^ (prefixWord ++ tailWord_1076199).sum := by decide
  have hdescent : baseEnd_1076199 < baseStart_1076199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076249 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 2, 3, 2]
def baseStart_1076249 : Nat := 118140960795 + 1076249 * 2 ^ 59
def prefixEnd_1076249 : Nat := 4983230072969 + 3 ^ 40 * 1076249 * 2
def baseEnd_1076249 : Nat := 552633040920864904537927

theorem tailTrace_1076249 : CollatzResearch.WordTrace tailWord_1076249 prefixEnd_1076249 552633040920864904537927 := by
  unfold tailWord_1076249
  simp only [CollatzResearch.WordTrace]
  refine ⟨39254025877941156540551801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26169350585294104360367867 39254025877941156540551801)
  ·
    refine ⟨29440519408455867405413851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39254025877941156540551801 29440519408455867405413851)
    ·
      refine ⟨44160779112683801108120777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29440519408455867405413851 44160779112683801108120777)
      ·
        refine ⟨33120584334512850831090583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44160779112683801108120777 33120584334512850831090583)
        ·
          refine ⟨49680876501769276246635875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33120584334512850831090583 49680876501769276246635875)
          ·
            refine ⟨74521314752653914369953813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49680876501769276246635875 74521314752653914369953813)
            ·
              refine ⟨3493186629030652236091585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74521314752653914369953813 3493186629030652236091585)
              ·
                refine ⟨2619889971772989177068689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3493186629030652236091585 2619889971772989177068689)
                ·
                  refine ⟨1964917478829741882801517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619889971772989177068689 1964917478829741882801517)
                  ·
                    refine ⟨736844054561153206050569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1964917478829741882801517 736844054561153206050569)
                    ·
                      refine ⟨552633040920864904537927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 736844054561153206050569 552633040920864904537927)
                      ·
                        rfl

theorem cell23_1076249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_1076249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076249 prefixEnd_1076249 := by exact prefixLift 1076249
  have htrace : WordTrace (prefixWord ++ tailWord_1076249) baseStart_1076249 baseEnd_1076249 := by
    simpa [prefixWord, tailWord_1076249, baseEnd_1076249] using wordTrace_append hprefix tailTrace_1076249
  have hstable : (prefixWord ++ tailWord_1076249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076249).length < 2 ^ (prefixWord ++ tailWord_1076249).sum := by decide
  have hdescent : baseEnd_1076249 < baseStart_1076249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076272 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 1, 6]
def baseStart_1076272 : Nat := 118140960795 + 1076272 * 2 ^ 59
def prefixEnd_1076272 : Nat := 4983230072969 + 3 ^ 40 * 1076272 * 2
def baseEnd_1076272 : Nat := 184214950325306104850107

theorem tailTrace_1076272 : CollatzResearch.WordTrace tailWord_1076272 prefixEnd_1076272 184214950325306104850107 := by
  unfold tailWord_1076272
  simp only [CollatzResearch.WordTrace]
  refine ⟨19627432378428915734319535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26169909837905220979092713 19627432378428915734319535)
  ·
    refine ⟨29441148567643373601479303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19627432378428915734319535 29441148567643373601479303)
    ·
      refine ⟨44161722851465060402218955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29441148567643373601479303 44161722851465060402218955)
      ·
        refine ⟨66242584277197590603328433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44161722851465060402218955 66242584277197590603328433)
        ·
          refine ⟨49681938207898192952496325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66242584277197590603328433 49681938207898192952496325)
          ·
            refine ⟨9315363413980911178593061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49681938207898192952496325 9315363413980911178593061)
            ·
              refine ⟨1746630640121420845986199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9315363413980911178593061 1746630640121420845986199)
              ·
                refine ⟨2619945960182131268979299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746630640121420845986199 2619945960182131268979299)
                ·
                  refine ⟨3929918940273196903468949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619945960182131268979299 3929918940273196903468949)
                  ·
                    refine ⟨184214950325306104850107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3929918940273196903468949 184214950325306104850107)
                    ·
                      rfl

theorem cell23_1076272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_1076272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076272 prefixEnd_1076272 := by exact prefixLift 1076272
  have htrace : WordTrace (prefixWord ++ tailWord_1076272) baseStart_1076272 baseEnd_1076272 := by
    simpa [prefixWord, tailWord_1076272, baseEnd_1076272] using wordTrace_append hprefix tailTrace_1076272
  have hstable : (prefixWord ++ tailWord_1076272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076272).length < 2 ^ (prefixWord ++ tailWord_1076272).sum := by decide
  have hdescent : baseEnd_1076272 < baseStart_1076272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076306 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1076306 : Nat := 118140960795 + 1076306 * 2 ^ 59
def prefixEnd_1076306 : Nat := 4983230072969 + 3 ^ 40 * 1076306 * 2
def baseEnd_1076306 : Nat := 184220769772723727175055

theorem tailTrace_1076306 : CollatzResearch.WordTrace tailWord_1076306 prefixEnd_1076306 184220769772723727175055 := by
  unfold tailWord_1076306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814026209683663818844193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26170736559156436850251181 9814026209683663818844193)
  ·
    refine ⟨7360519657262747864133145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9814026209683663818844193 7360519657262747864133145)
    ·
      refine ⟨5520389742947060898099859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7360519657262747864133145 5520389742947060898099859)
      ·
        refine ⟨8280584614420591347149789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5520389742947060898099859 8280584614420591347149789)
        ·
          refine ⟨3105219230407721755181171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8280584614420591347149789 3105219230407721755181171)
          ·
            refine ⟨4657828845611582632771757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105219230407721755181171 4657828845611582632771757)
            ·
              refine ⟨1746685817104343487289409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4657828845611582632771757 1746685817104343487289409)
              ·
                refine ⟨1310014362828257615467057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746685817104343487289409 1310014362828257615467057)
                ·
                  refine ⟨982510772121193211600293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1310014362828257615467057 982510772121193211600293)
                  ·
                    refine ⟨184220769772723727175055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982510772121193211600293 184220769772723727175055)
                    ·
                      rfl

theorem cell23_1076306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1076306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076306 prefixEnd_1076306 := by exact prefixLift 1076306
  have htrace : WordTrace (prefixWord ++ tailWord_1076306) baseStart_1076306 baseEnd_1076306 := by
    simpa [prefixWord, tailWord_1076306, baseEnd_1076306] using wordTrace_append hprefix tailTrace_1076306
  have hstable : (prefixWord ++ tailWord_1076306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076306).length < 2 ^ (prefixWord ++ tailWord_1076306).sum := by decide
  have hdescent : baseEnd_1076306 < baseStart_1076306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076329 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 3]
def baseStart_1076329 : Nat := 118140960795 + 1076329 * 2 ^ 59
def prefixEnd_1076329 : Nat := 4983230072969 + 3 ^ 40 * 1076329 * 2
def baseEnd_1076329 : Nat := 552674119373224591537559

theorem tailTrace_1076329 : CollatzResearch.WordTrace tailWord_1076329 prefixEnd_1076329 552674119373224591537559 := by
  unfold tailWord_1076329
  simp only [CollatzResearch.WordTrace]
  refine ⟨39256943717651330203464041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26171295811767553468976027 39256943717651330203464041)
  ·
    refine ⟨29442707788238497652598031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39256943717651330203464041 29442707788238497652598031)
    ·
      refine ⟨44164061682357746478897047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29442707788238497652598031 44164061682357746478897047)
      ·
        refine ⟨66246092523536619718345571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44164061682357746478897047 66246092523536619718345571)
        ·
          refine ⟨99369138785304929577518357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66246092523536619718345571 99369138785304929577518357)
          ·
            refine ⟨4657928380561168573946173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99369138785304929577518357 4657928380561168573946173)
            ·
              refine ⟨1746723142710438215229815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4657928380561168573946173 1746723142710438215229815)
              ·
                refine ⟨2620084714065657322844723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746723142710438215229815 2620084714065657322844723)
                ·
                  refine ⟨3930127071098485984267085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620084714065657322844723 3930127071098485984267085)
                  ·
                    refine ⟨1473797651661932244100157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3930127071098485984267085 1473797651661932244100157)
                    ·
                      refine ⟨552674119373224591537559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1473797651661932244100157 552674119373224591537559)
                      ·
                        rfl

theorem cell23_1076329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_1076329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076329 prefixEnd_1076329 := by exact prefixLift 1076329
  have htrace : WordTrace (prefixWord ++ tailWord_1076329) baseStart_1076329 baseEnd_1076329 := by
    simpa [prefixWord, tailWord_1076329, baseEnd_1076329] using wordTrace_append hprefix tailTrace_1076329
  have hstable : (prefixWord ++ tailWord_1076329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076329).length < 2 ^ (prefixWord ++ tailWord_1076329).sum := by decide
  have hdescent : baseEnd_1076329 < baseStart_1076329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076350 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1076350 : Nat := 118140960795 + 1076350 * 2 ^ 59
def prefixEnd_1076350 : Nat := 4983230072969 + 3 ^ 40 * 1076350 * 2
def baseEnd_1076350 : Nat := 552684902466969009374963

theorem tailTrace_1076350 : CollatzResearch.WordTrace tailWord_1076350 prefixEnd_1076350 552684902466969009374963 := by
  unfold tailWord_1076350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4907213706321906348747313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26171806433716833859985669 4907213706321906348747313)
  ·
    refine ⟨3680410279741429761560485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4907213706321906348747313 3680410279741429761560485)
    ·
      refine ⟨690076927451518080292591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3680410279741429761560485 690076927451518080292591)
      ·
        refine ⟨1035115391177277120438887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 690076927451518080292591 1035115391177277120438887)
        ·
          refine ⟨1552673086765915680658331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1035115391177277120438887 1552673086765915680658331)
          ·
            refine ⟨2329009630148873520987497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552673086765915680658331 2329009630148873520987497)
            ·
              refine ⟨1746757222611655140740623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2329009630148873520987497 1746757222611655140740623)
              ·
                refine ⟨2620135833917482711110935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746757222611655140740623 2620135833917482711110935)
                ·
                  refine ⟨3930203750876224066666403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620135833917482711110935 3930203750876224066666403)
                  ·
                    refine ⟨5895305626314336099999605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3930203750876224066666403 5895305626314336099999605)
                    ·
                      refine ⟨552684902466969009374963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5895305626314336099999605 552684902466969009374963)
                      ·
                        rfl

theorem cell23_1076350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1076350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076350 prefixEnd_1076350 := by exact prefixLift 1076350
  have htrace : WordTrace (prefixWord ++ tailWord_1076350) baseStart_1076350 baseEnd_1076350 := by
    simpa [prefixWord, tailWord_1076350, baseEnd_1076350] using wordTrace_append hprefix tailTrace_1076350
  have hstable : (prefixWord ++ tailWord_1076350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076350).length < 2 ^ (prefixWord ++ tailWord_1076350).sum := by decide
  have hdescent : baseEnd_1076350 < baseStart_1076350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076380 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_1076380 : Nat := 118140960795 + 1076380 * 2 ^ 59
def prefixEnd_1076380 : Nat := 4983230072969 + 3 ^ 40 * 1076380 * 2
def baseEnd_1076380 : Nat := 552700306886603891999825

theorem tailTrace_1076380 : CollatzResearch.WordTrace tailWord_1076380 prefixEnd_1076380 552700306886603891999825 := by
  unfold tailWord_1076380
  simp only [CollatzResearch.WordTrace]
  refine ⟨19629401920233282956785297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26172535893644377275713729 19629401920233282956785297)
  ·
    refine ⟨14722051440174962217588973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19629401920233282956785297 14722051440174962217588973)
    ·
      refine ⟨5520769290065610831595865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14722051440174962217588973 5520769290065610831595865)
      ·
        refine ⟨4140576967549208123696899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5520769290065610831595865 4140576967549208123696899)
        ·
          refine ⟨6210865451323812185545349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4140576967549208123696899 6210865451323812185545349)
          ·
            refine ⟨1164537272123214784789753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6210865451323812185545349 1164537272123214784789753)
            ·
              refine ⟨873402954092411088592315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164537272123214784789753 873402954092411088592315)
              ·
                refine ⟨1310104431138616632888473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873402954092411088592315 1310104431138616632888473)
                ·
                  refine ⟨982578323353962474666355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1310104431138616632888473 982578323353962474666355)
                  ·
                    refine ⟨1473867485030943711999533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 982578323353962474666355 1473867485030943711999533)
                    ·
                      refine ⟨552700306886603891999825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1473867485030943711999533 552700306886603891999825)
                      ·
                        rfl

theorem cell23_1076380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_1076380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076380 prefixEnd_1076380 := by exact prefixLift 1076380
  have htrace : WordTrace (prefixWord ++ tailWord_1076380) baseStart_1076380 baseEnd_1076380 := by
    simpa [prefixWord, tailWord_1076380, baseEnd_1076380] using wordTrace_append hprefix tailTrace_1076380
  have hstable : (prefixWord ++ tailWord_1076380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076380).length < 2 ^ (prefixWord ++ tailWord_1076380).sum := by decide
  have hdescent : baseEnd_1076380 < baseStart_1076380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076426 : List Nat := [3, 1, 2, 1, 3, 3, 1, 4, 5]
def baseStart_1076426 : Nat := 118140960795 + 1076426 * 2 ^ 59
def prefixEnd_1076426 : Nat := 4983230072969 + 3 ^ 40 * 1076426 * 2
def baseEnd_1076426 : Nat := 61413769666301190224957

theorem tailTrace_1076426 : CollatzResearch.WordTrace tailWord_1076426 prefixEnd_1076426 61413769666301190224957 := by
  unfold tailWord_1076426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815120399574978942436283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26173654398866610513163421 9815120399574978942436283)
  ·
    refine ⟨14722680599362468413654425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9815120399574978942436283 14722680599362468413654425)
    ·
      refine ⟨11042010449521851310240819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14722680599362468413654425 11042010449521851310240819)
      ·
        refine ⟨16563015674282776965361229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11042010449521851310240819 16563015674282776965361229)
        ·
          refine ⟨6211130877856041362010461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16563015674282776965361229 6211130877856041362010461)
          ·
            refine ⟨2329174079196015510753923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6211130877856041362010461 2329174079196015510753923)
            ·
              refine ⟨3493761118794023266130885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2329174079196015510753923 3493761118794023266130885)
              ·
                refine ⟨655080209773879362399541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3493761118794023266130885 655080209773879362399541)
                ·
                  refine ⟨61413769666301190224957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 655080209773879362399541 61413769666301190224957)
                  ·
                    rfl

theorem cell23_1076426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_1076426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076426 prefixEnd_1076426 := by exact prefixLift 1076426
  have htrace : WordTrace (prefixWord ++ tailWord_1076426) baseStart_1076426 baseEnd_1076426 := by
    simpa [prefixWord, tailWord_1076426, baseEnd_1076426] using wordTrace_append hprefix tailTrace_1076426
  have hstable : (prefixWord ++ tailWord_1076426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076426).length < 2 ^ (prefixWord ++ tailWord_1076426).sum := by decide
  have hdescent : baseEnd_1076426 < baseStart_1076426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076459 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4]
def baseStart_1076459 : Nat := 118140960795 + 1076459 * 2 ^ 59
def prefixEnd_1076459 : Nat := 4983230072969 + 3 ^ 40 * 1076459 * 2
def baseEnd_1076459 : Nat := 552740871858309082911961

theorem tailTrace_1076459 : CollatzResearch.WordTrace tailWord_1076459 prefixEnd_1076459 552740871858309082911961 := by
  unfold tailWord_1076459
  simp only [CollatzResearch.WordTrace]
  refine ⟨39261685207180362405696431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26174456804786908270464287 39261685207180362405696431)
  ·
    refine ⟨58892527810770543608544647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39261685207180362405696431 58892527810770543608544647)
    ·
      refine ⟨88338791716155815412816971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58892527810770543608544647 88338791716155815412816971)
      ·
        refine ⟨132508187574233723119225457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88338791716155815412816971 132508187574233723119225457)
        ·
          refine ⟨99381140680675292339419093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132508187574233723119225457 99381140680675292339419093)
          ·
            refine ⟨2329245484703327164205135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 99381140680675292339419093 2329245484703327164205135)
            ·
              refine ⟨3493868227054990746307703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2329245484703327164205135 3493868227054990746307703)
              ·
                refine ⟨5240802340582486119461555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493868227054990746307703 5240802340582486119461555)
                ·
                  refine ⟨7861203510873729179192333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5240802340582486119461555 7861203510873729179192333)
                  ·
                    refine ⟨2947951316577648442197125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7861203510873729179192333 2947951316577648442197125)
                    ·
                      refine ⟨552740871858309082911961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2947951316577648442197125 552740871858309082911961)
                      ·
                        rfl

theorem cell23_1076459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4].length) (baseStart_1076459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076459 prefixEnd_1076459 := by exact prefixLift 1076459
  have htrace : WordTrace (prefixWord ++ tailWord_1076459) baseStart_1076459 baseEnd_1076459 := by
    simpa [prefixWord, tailWord_1076459, baseEnd_1076459] using wordTrace_append hprefix tailTrace_1076459
  have hstable : (prefixWord ++ tailWord_1076459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076459).length < 2 ^ (prefixWord ++ tailWord_1076459).sum := by decide
  have hdescent : baseEnd_1076459 < baseStart_1076459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076520 : List Nat := [2, 1, 5, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1076520 : Nat := 118140960795 + 1076520 * 2 ^ 59
def prefixEnd_1076520 : Nat := 4983230072969 + 3 ^ 40 * 1076520 * 2
def baseEnd_1076520 : Nat := 184257398059411114749727

theorem tailTrace_1076520 : CollatzResearch.WordTrace tailWord_1076520 prefixEnd_1076520 184257398059411114749727 := by
  unfold tailWord_1076520
  simp only [CollatzResearch.WordTrace]
  refine ⟨19631955029979684911833507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26175940039972913215778009 19631955029979684911833507)
  ·
    refine ⟨29447932544969527367750261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19631955029979684911833507 29447932544969527367750261)
    ·
      refine ⟨2760743676090893190726587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29447932544969527367750261 2760743676090893190726587)
      ·
        refine ⟨4141115514136339786089881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760743676090893190726587 4141115514136339786089881)
        ·
          refine ⟨3105836635602254839567411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4141115514136339786089881 3105836635602254839567411)
          ·
            refine ⟨4658754953403382259351117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105836635602254839567411 4658754953403382259351117)
            ·
              refine ⟨1747033107526268347256669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4658754953403382259351117 1747033107526268347256669)
              ·
                refine ⟨655137415322350630221251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1747033107526268347256669 655137415322350630221251)
                ·
                  refine ⟨982706122983525945331877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655137415322350630221251 982706122983525945331877)
                  ·
                    refine ⟨184257398059411114749727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982706122983525945331877 184257398059411114749727)
                    ·
                      rfl

theorem cell23_1076520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1076520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076520 prefixEnd_1076520 := by exact prefixLift 1076520
  have htrace : WordTrace (prefixWord ++ tailWord_1076520) baseStart_1076520 baseEnd_1076520 := by
    simpa [prefixWord, tailWord_1076520, baseEnd_1076520] using wordTrace_append hprefix tailTrace_1076520
  have hstable : (prefixWord ++ tailWord_1076520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076520).length < 2 ^ (prefixWord ++ tailWord_1076520).sum := by decide
  have hdescent : baseEnd_1076520 < baseStart_1076520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076537 : List Nat := [1, 2, 1, 6, 2, 1, 3, 2, 1, 4]
def baseStart_1076537 : Nat := 118140960795 + 1076537 * 2 ^ 59
def prefixEnd_1076537 : Nat := 4983230072969 + 3 ^ 40 * 1076537 * 2
def baseEnd_1076537 : Nat := 184260307783119925912201

theorem tailTrace_1076537 : CollatzResearch.WordTrace tailWord_1076537 prefixEnd_1076537 184260307783119925912201 := by
  unfold tailWord_1076537
  simp only [CollatzResearch.WordTrace]
  refine ⟨39264530100897781727035865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26176353400598521151357243 39264530100897781727035865)
  ·
    refine ⟨29448397575673336295276899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39264530100897781727035865 29448397575673336295276899)
    ·
      refine ⟨44172596363510004442915349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29448397575673336295276899 44172596363510004442915349)
      ·
        refine ⟨2070590454539531458261657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44172596363510004442915349 2070590454539531458261657)
        ·
          refine ⟨1552942840904648593696243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2070590454539531458261657 1552942840904648593696243)
          ·
            refine ⟨2329414261356972890544365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552942840904648593696243 2329414261356972890544365)
            ·
              refine ⟨873530348008864833954137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2329414261356972890544365 873530348008864833954137)
              ·
                refine ⟨655147761006648625465603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873530348008864833954137 655147761006648625465603)
                ·
                  refine ⟨982721641509972938198405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655147761006648625465603 982721641509972938198405)
                  ·
                    refine ⟨184260307783119925912201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982721641509972938198405 184260307783119925912201)
                    ·
                      rfl

theorem cell23_1076537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 4].length) (baseStart_1076537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076537 prefixEnd_1076537 := by exact prefixLift 1076537
  have htrace : WordTrace (prefixWord ++ tailWord_1076537) baseStart_1076537 baseEnd_1076537 := by
    simpa [prefixWord, tailWord_1076537, baseEnd_1076537] using wordTrace_append hprefix tailTrace_1076537
  have hstable : (prefixWord ++ tailWord_1076537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076537).length < 2 ^ (prefixWord ++ tailWord_1076537).sum := by decide
  have hdescent : baseEnd_1076537 < baseStart_1076537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076543 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 3]
def baseStart_1076543 : Nat := 118140960795 + 1076543 * 2 ^ 59
def prefixEnd_1076543 : Nat := 4983230072969 + 3 ^ 40 * 1076543 * 2
def baseEnd_1076543 : Nat := 552784004233286754261575

theorem tailTrace_1076543 : CollatzResearch.WordTrace tailWord_1076543 prefixEnd_1076543 552784004233286754261575 := by
  unfold tailWord_1076543
  simp only [CollatzResearch.WordTrace]
  refine ⟨39264748938876044751754283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26176499292584029834502855 39264748938876044751754283)
  ·
    refine ⟨58897123408314067127631425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39264748938876044751754283 58897123408314067127631425)
    ·
      refine ⟨44172842556235550345723569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58897123408314067127631425 44172842556235550345723569)
      ·
        refine ⟨33129631917176662759292677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44172842556235550345723569 33129631917176662759292677)
        ·
          refine ⟨6211805984470624267367377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33129631917176662759292677 6211805984470624267367377)
          ·
            refine ⟨4658854488352968200525533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6211805984470624267367377 4658854488352968200525533)
            ·
              refine ⟨1747070433132363075197075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4658854488352968200525533 1747070433132363075197075)
              ·
                refine ⟨2620605649698544612795613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747070433132363075197075 2620605649698544612795613)
                ·
                  refine ⟨982727118636954229798355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2620605649698544612795613 982727118636954229798355)
                  ·
                    refine ⟨1474090677955431344697533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 982727118636954229798355 1474090677955431344697533)
                    ·
                      refine ⟨552784004233286754261575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474090677955431344697533 552784004233286754261575)
                      ·
                        rfl

theorem cell23_1076543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_1076543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076543 prefixEnd_1076543 := by exact prefixLift 1076543
  have htrace : WordTrace (prefixWord ++ tailWord_1076543) baseStart_1076543 baseEnd_1076543 := by
    simpa [prefixWord, tailWord_1076543, baseEnd_1076543] using wordTrace_append hprefix tailTrace_1076543
  have hstable : (prefixWord ++ tailWord_1076543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076543).length < 2 ^ (prefixWord ++ tailWord_1076543).sum := by decide
  have hdescent : baseEnd_1076543 < baseStart_1076543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076569 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_1076569 : Nat := 118140960795 + 1076569 * 2 ^ 59
def prefixEnd_1076569 : Nat := 4983230072969 + 3 ^ 40 * 1076569 * 2
def baseEnd_1076569 : Nat := 552797354730303652536455

theorem tailTrace_1076569 : CollatzResearch.WordTrace tailWord_1076569 prefixEnd_1076569 552797354730303652536455 := by
  unfold tailWord_1076569
  simp only [CollatzResearch.WordTrace]
  refine ⟨39265697236781851192200761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26177131491187900794800507 39265697236781851192200761)
  ·
    refine ⟨29449272927586388394150571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39265697236781851192200761 29449272927586388394150571)
    ·
      refine ⟨44173909391379582591225857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29449272927586388394150571 44173909391379582591225857)
      ·
        refine ⟨33130432043534686943419393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44173909391379582591225857 33130432043534686943419393)
        ·
          refine ⟨24847824032651015207564545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33130432043534686943419393 24847824032651015207564545)
          ·
            refine ⟨18635868024488261405673409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24847824032651015207564545 18635868024488261405673409)
            ·
              refine ⟨13976901018366196054255057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18635868024488261405673409 13976901018366196054255057)
              ·
                refine ⟨10482675763774647040691293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13976901018366196054255057 10482675763774647040691293)
                ·
                  refine ⟨3931003411415492640259235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10482675763774647040691293 3931003411415492640259235)
                  ·
                    refine ⟨5896505117123238960388853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3931003411415492640259235 5896505117123238960388853)
                    ·
                      refine ⟨552797354730303652536455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5896505117123238960388853 552797354730303652536455)
                      ·
                        rfl

theorem cell23_1076569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_1076569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076569 prefixEnd_1076569 := by exact prefixLift 1076569
  have htrace : WordTrace (prefixWord ++ tailWord_1076569) baseStart_1076569 baseEnd_1076569 := by
    simpa [prefixWord, tailWord_1076569, baseEnd_1076569] using wordTrace_append hprefix tailTrace_1076569
  have hstable : (prefixWord ++ tailWord_1076569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076569).length < 2 ^ (prefixWord ++ tailWord_1076569).sum := by decide
  have hdescent : baseEnd_1076569 < baseStart_1076569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076576 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 1, 6]
def baseStart_1076576 : Nat := 118140960795 + 1076576 * 2 ^ 59
def prefixEnd_1076576 : Nat := 4983230072969 + 3 ^ 40 * 1076576 * 2
def baseEnd_1076576 : Nat := 184266983031628375049641

theorem tailTrace_1076576 : CollatzResearch.WordTrace tailWord_1076576 prefixEnd_1076576 184266983031628375049641 := by
  unfold tailWord_1076576
  simp only [CollatzResearch.WordTrace]
  refine ⟨19632976273878245693852791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26177301698504327591803721 19632976273878245693852791)
  ·
    refine ⟨29449464410817368540779187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19632976273878245693852791 29449464410817368540779187)
    ·
      refine ⟨44174196616226052811168781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29449464410817368540779187 44174196616226052811168781)
      ·
        refine ⟨16565323731084769804188293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44174196616226052811168781 16565323731084769804188293)
        ·
          refine ⟨3105998199578394338285305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16565323731084769804188293 3105998199578394338285305)
          ·
            refine ⟨2329498649683795753713979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3105998199578394338285305 2329498649683795753713979)
            ·
              refine ⟨3494247974525693630570969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2329498649683795753713979 3494247974525693630570969)
              ·
                refine ⟨2620685980894270222928227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3494247974525693630570969 2620685980894270222928227)
                ·
                  refine ⟨3931028971341405334392341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620685980894270222928227 3931028971341405334392341)
                  ·
                    refine ⟨184266983031628375049641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3931028971341405334392341 184266983031628375049641)
                    ·
                      rfl

theorem cell23_1076576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_1076576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076576 prefixEnd_1076576 := by exact prefixLift 1076576
  have htrace : WordTrace (prefixWord ++ tailWord_1076576) baseStart_1076576 baseEnd_1076576 := by
    simpa [prefixWord, tailWord_1076576, baseEnd_1076576] using wordTrace_append hprefix tailTrace_1076576
  have hstable : (prefixWord ++ tailWord_1076576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076576).length < 2 ^ (prefixWord ++ tailWord_1076576).sum := by decide
  have hdescent : baseEnd_1076576 < baseStart_1076576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076589 : List Nat := [1, 5, 1, 1, 1, 14]
def baseStart_1076589 : Nat := 118140960795 + 1076589 * 2 ^ 59
def prefixEnd_1076589 : Nat := 4983230072969 + 3 ^ 40 * 1076589 * 2
def baseEnd_1076589 : Nat := 2274928495240302774841

theorem tailTrace_1076589 : CollatzResearch.WordTrace tailWord_1076589 prefixEnd_1076589 2274928495240302774841 := by
  unfold tailWord_1076589
  simp only [CollatzResearch.WordTrace]
  refine ⟨39266426696709394607928821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26177617797806263071952547 39266426696709394607928821)
  ·
    refine ⟨3681227502816505744493327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39266426696709394607928821 3681227502816505744493327)
    ·
      refine ⟨5521841254224758616739991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3681227502816505744493327 5521841254224758616739991)
      ·
        refine ⟨8282761881337137925109987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5521841254224758616739991 8282761881337137925109987)
        ·
          refine ⟨12424142822005706887664981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8282761881337137925109987 12424142822005706887664981)
          ·
            refine ⟨2274928495240302774841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 12424142822005706887664981 2274928495240302774841)
            ·
              rfl

theorem cell23_1076589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 14].length) (baseStart_1076589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076589 prefixEnd_1076589 := by exact prefixLift 1076589
  have htrace : WordTrace (prefixWord ++ tailWord_1076589) baseStart_1076589 baseEnd_1076589 := by
    simpa [prefixWord, tailWord_1076589, baseEnd_1076589] using wordTrace_append hprefix tailTrace_1076589
  have hstable : (prefixWord ++ tailWord_1076589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076589).length < 2 ^ (prefixWord ++ tailWord_1076589).sum := by decide
  have hdescent : baseEnd_1076589 < baseStart_1076589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076610 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1076610 : Nat := 118140960795 + 1076610 * 2 ^ 59
def prefixEnd_1076610 : Nat := 4983230072969 + 3 ^ 40 * 1076610 * 2
def baseEnd_1076610 : Nat := 184272802479045997374589

theorem tailTrace_1076610 : CollatzResearch.WordTrace tailWord_1076610 prefixEnd_1076610 184272802479045997374589 := by
  unfold tailWord_1076610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9816798157408328798610821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26178128419755543462962189 9816798157408328798610821)
  ·
    refine ⟨1840649654514061649739529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9816798157408328798610821 1840649654514061649739529)
    ·
      refine ⟨1380487240885546237304647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1840649654514061649739529 1380487240885546237304647)
      ·
        refine ⟨2070730861328319355956971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380487240885546237304647 2070730861328319355956971)
        ·
          refine ⟨3106096291992479033935457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070730861328319355956971 3106096291992479033935457)
          ·
            refine ⟨2329572218994359275451593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106096291992479033935457 2329572218994359275451593)
            ·
              refine ⟨1747179164245769456588695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2329572218994359275451593 1747179164245769456588695)
              ·
                refine ⟨2620768746368654184883043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747179164245769456588695 2620768746368654184883043)
                ·
                  refine ⟨3931153119552981277324565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620768746368654184883043 3931153119552981277324565)
                  ·
                    refine ⟨184272802479045997374589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3931153119552981277324565 184272802479045997374589)
                    ·
                      rfl

theorem cell23_1076610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1076610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076610 prefixEnd_1076610 := by exact prefixLift 1076610
  have htrace : WordTrace (prefixWord ++ tailWord_1076610) baseStart_1076610 baseEnd_1076610 := by
    simpa [prefixWord, tailWord_1076610, baseEnd_1076610] using wordTrace_append hprefix tailTrace_1076610
  have hstable : (prefixWord ++ tailWord_1076610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076610).length < 2 ^ (prefixWord ++ tailWord_1076610).sum := by decide
  have hdescent : baseEnd_1076610 < baseStart_1076610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076619 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 2, 7]
def baseStart_1076619 : Nat := 118140960795 + 1076619 * 2 ^ 59
def prefixEnd_1076619 : Nat := 4983230072969 + 3 ^ 40 * 1076619 * 2
def baseEnd_1076619 : Nat := 184274342921009485637075

theorem tailTrace_1076619 : CollatzResearch.WordTrace tailWord_1076619 prefixEnd_1076619 184274342921009485637075 := by
  unfold tailWord_1076619
  simp only [CollatzResearch.WordTrace]
  refine ⟨39267520886600709731520911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26178347257733806487680607 39267520886600709731520911)
  ·
    refine ⟨58901281329901064597281367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39267520886600709731520911 58901281329901064597281367)
    ·
      refine ⟨88351921994851596895922051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58901281329901064597281367 88351921994851596895922051)
      ·
        refine ⟨132527882992277395343883077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88351921994851596895922051 132527882992277395343883077)
        ·
          refine ⟨24848978061052011626978077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132527882992277395343883077 24848978061052011626978077)
          ·
            refine ⟨9318366772894504360116779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24848978061052011626978077 9318366772894504360116779)
            ·
              refine ⟨13977550159341756540175169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9318366772894504360116779 13977550159341756540175169)
              ·
                refine ⟨10483162619506317405131377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13977550159341756540175169 10483162619506317405131377)
                ·
                  refine ⟨7862371964629738053848533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10483162619506317405131377 7862371964629738053848533)
                  ·
                    refine ⟨184274342921009485637075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7862371964629738053848533 184274342921009485637075)
                    ·
                      rfl

theorem cell23_1076619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_1076619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076619 prefixEnd_1076619 := by exact prefixLift 1076619
  have htrace : WordTrace (prefixWord ++ tailWord_1076619) baseStart_1076619 baseEnd_1076619 := by
    simpa [prefixWord, tailWord_1076619, baseEnd_1076619] using wordTrace_append hprefix tailTrace_1076619
  have hstable : (prefixWord ++ tailWord_1076619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076619).length < 2 ^ (prefixWord ++ tailWord_1076619).sum := by decide
  have hdescent : baseEnd_1076619 < baseStart_1076619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076637 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_1076637 : Nat := 118140960795 + 1076637 * 2 ^ 59
def prefixEnd_1076637 : Nat := 4983230072969 + 3 ^ 40 * 1076637 * 2
def baseEnd_1076637 : Nat := 552832271414809386486143

theorem tailTrace_1076637 : CollatzResearch.WordTrace tailWord_1076637 prefixEnd_1076637 552832271414809386486143 := by
  unfold tailWord_1076637
  simp only [CollatzResearch.WordTrace]
  refine ⟨39268177400535498805676165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26178784933690332537117443 39268177400535498805676165)
  ·
    refine ⟨7362783262600406026064281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39268177400535498805676165 7362783262600406026064281)
    ·
      refine ⟨5522087446950304519548211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7362783262600406026064281 5522087446950304519548211)
      ·
        refine ⟨8283131170425456779322317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5522087446950304519548211 8283131170425456779322317)
        ·
          refine ⟨3106174188909546292245869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8283131170425456779322317 3106174188909546292245869)
          ·
            refine ⟨1164815320841079859592201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3106174188909546292245869 1164815320841079859592201)
            ·
              refine ⟨873611490630809894694151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164815320841079859592201 873611490630809894694151)
              ·
                refine ⟨1310417235946214842041227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873611490630809894694151 1310417235946214842041227)
                ·
                  refine ⟨1965625853919322263061841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310417235946214842041227 1965625853919322263061841)
                  ·
                    refine ⟨1474219390439491697296381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1965625853919322263061841 1474219390439491697296381)
                    ·
                      refine ⟨552832271414809386486143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474219390439491697296381 552832271414809386486143)
                      ·
                        rfl

theorem cell23_1076637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_1076637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076637 prefixEnd_1076637 := by exact prefixLift 1076637
  have htrace : WordTrace (prefixWord ++ tailWord_1076637) baseStart_1076637 baseEnd_1076637 := by
    simpa [prefixWord, tailWord_1076637, baseEnd_1076637] using wordTrace_append hprefix tailTrace_1076637
  have hstable : (prefixWord ++ tailWord_1076637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076637).length < 2 ^ (prefixWord ++ tailWord_1076637).sum := by decide
  have hdescent : baseEnd_1076637 < baseStart_1076637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076686 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_1076686 : Nat := 118140960795 + 1076686 * 2 ^ 59
def prefixEnd_1076686 : Nat := 4983230072969 + 3 ^ 40 * 1076686 * 2
def baseEnd_1076686 : Nat := 552857431966879694773417

theorem tailTrace_1076686 : CollatzResearch.WordTrace tailWord_1076686 prefixEnd_1076686 552857431966879694773417 := by
  unfold tailWord_1076686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908745572169747521776239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26179976384905320116139941 4908745572169747521776239)
  ·
    refine ⟨7363118358254621282664359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4908745572169747521776239 7363118358254621282664359)
    ·
      refine ⟨11044677537381931923996539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7363118358254621282664359 11044677537381931923996539)
      ·
        refine ⟨16567016306072897885994809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11044677537381931923996539 16567016306072897885994809)
        ·
          refine ⟨12425262229554673414496107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16567016306072897885994809 12425262229554673414496107)
          ·
            refine ⟨18637893344332010121744161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12425262229554673414496107 18637893344332010121744161)
            ·
              refine ⟨13978420008249007591308121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18637893344332010121744161 13978420008249007591308121)
              ·
                refine ⟨10483815006186755693481091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13978420008249007591308121 10483815006186755693481091)
                ·
                  refine ⟨15725722509280133540221637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10483815006186755693481091 15725722509280133540221637)
                  ·
                    refine ⟨2948572970490025038791557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15725722509280133540221637 2948572970490025038791557)
                    ·
                      refine ⟨552857431966879694773417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2948572970490025038791557 552857431966879694773417)
                      ·
                        rfl

theorem cell23_1076686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_1076686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076686 prefixEnd_1076686 := by exact prefixLift 1076686
  have htrace : WordTrace (prefixWord ++ tailWord_1076686) baseStart_1076686 baseEnd_1076686 := by
    simpa [prefixWord, tailWord_1076686, baseEnd_1076686] using wordTrace_append hprefix tailTrace_1076686
  have hstable : (prefixWord ++ tailWord_1076686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076686).length < 2 ^ (prefixWord ++ tailWord_1076686).sum := by decide
  have hdescent : baseEnd_1076686 < baseStart_1076686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076743 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 2, 5]
def baseStart_1076743 : Nat := 118140960795 + 1076743 * 2 ^ 59
def prefixEnd_1076743 : Nat := 4983230072969 + 3 ^ 40 * 1076743 * 2
def baseEnd_1076743 : Nat := 184295566788061990586885

theorem tailTrace_1076743 : CollatzResearch.WordTrace tailWord_1076743 prefixEnd_1076743 184295566788061990586885 := by
  unfold tailWord_1076743
  simp only [CollatzResearch.WordTrace]
  refine ⟨39272043538151478909034883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26181362358767652606023255 39272043538151478909034883)
  ·
    refine ⟨58908065307227218363552325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39272043538151478909034883 58908065307227218363552325)
    ·
      refine ⟨11045262245105103443166061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58908065307227218363552325 11045262245105103443166061)
      ·
        refine ⟨4141973341914413791187273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11045262245105103443166061 4141973341914413791187273)
        ·
          refine ⟨3106480006435810343390455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4141973341914413791187273 3106480006435810343390455)
          ·
            refine ⟨4659720009653715515085683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106480006435810343390455 4659720009653715515085683)
            ·
              refine ⟨6989580014480573272628525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659720009653715515085683 6989580014480573272628525)
              ·
                refine ⟨2621092505430214977235697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6989580014480573272628525 2621092505430214977235697)
                ·
                  refine ⟨1965819379072661232926773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621092505430214977235697 1965819379072661232926773)
                  ·
                    refine ⟨184295566788061990586885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1965819379072661232926773 184295566788061990586885)
                    ·
                      rfl

theorem cell23_1076743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_1076743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076743 prefixEnd_1076743 := by exact prefixLift 1076743
  have htrace : WordTrace (prefixWord ++ tailWord_1076743) baseStart_1076743 baseEnd_1076743 := by
    simpa [prefixWord, tailWord_1076743, baseEnd_1076743] using wordTrace_append hprefix tailTrace_1076743
  have hstable : (prefixWord ++ tailWord_1076743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076743).length < 2 ^ (prefixWord ++ tailWord_1076743).sum := by decide
  have hdescent : baseEnd_1076743 < baseStart_1076743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076773 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_1076773 : Nat := 118140960795 + 1076773 * 2 ^ 59
def prefixEnd_1076773 : Nat := 4983230072969 + 3 ^ 40 * 1076773 * 2
def baseEnd_1076773 : Nat := 184300701594606951461839

theorem tailTrace_1076773 : CollatzResearch.WordTrace tailWord_1076773 prefixEnd_1076773 184300701594606951461839 := by
  unfold tailWord_1076773
  simp only [CollatzResearch.WordTrace]
  refine ⟨39273137728042794032626973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26182091818695196021751315 39273137728042794032626973)
  ·
    refine ⟨14727426648016047762235115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39273137728042794032626973 14727426648016047762235115)
    ·
      refine ⟨22091139972024071643352673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14727426648016047762235115 22091139972024071643352673)
      ·
        refine ⟨16568354979018053732514505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22091139972024071643352673 16568354979018053732514505)
        ·
          refine ⟨12426266234263540299385879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16568354979018053732514505 12426266234263540299385879)
          ·
            refine ⟨18639399351395310449078819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12426266234263540299385879 18639399351395310449078819)
            ·
              refine ⟨27959099027092965673618229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18639399351395310449078819 27959099027092965673618229)
              ·
                refine ⟨2621165533789965531901709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27959099027092965673618229 2621165533789965531901709)
                ·
                  refine ⟨982937075171237074463141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2621165533789965531901709 982937075171237074463141)
                  ·
                    refine ⟨184300701594606951461839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982937075171237074463141 184300701594606951461839)
                    ·
                      rfl

theorem cell23_1076773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_1076773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076773 prefixEnd_1076773 := by exact prefixLift 1076773
  have htrace : WordTrace (prefixWord ++ tailWord_1076773) baseStart_1076773 baseEnd_1076773 := by
    simpa [prefixWord, tailWord_1076773, baseEnd_1076773] using wordTrace_append hprefix tailTrace_1076773
  have hstable : (prefixWord ++ tailWord_1076773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076773).length < 2 ^ (prefixWord ++ tailWord_1076773).sum := by decide
  have hdescent : baseEnd_1076773 < baseStart_1076773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076786 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 10]
def baseStart_1076786 : Nat := 118140960795 + 1076786 * 2 ^ 59
def prefixEnd_1076786 : Nat := 4983230072969 + 3 ^ 40 * 1076786 * 2
def baseEnd_1076786 : Nat := 61434308892481033724773

theorem tailTrace_1076786 : CollatzResearch.WordTrace tailWord_1076786 prefixEnd_1076786 61434308892481033724773 := by
  unfold tailWord_1076786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818402969248924313212553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26182407917997131501900141 9818402969248924313212553)
  ·
    refine ⟨7363802226936693234909415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9818402969248924313212553 7363802226936693234909415)
    ·
      refine ⟨11045703340405039852364123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7363802226936693234909415 11045703340405039852364123)
      ·
        refine ⟨16568555010607559778546185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11045703340405039852364123 16568555010607559778546185)
        ·
          refine ⟨12426416257955669833909639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16568555010607559778546185 12426416257955669833909639)
          ·
            refine ⟨18639624386933504750864459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12426416257955669833909639 18639624386933504750864459)
            ·
              refine ⟨27959436580400257126296689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18639624386933504750864459 27959436580400257126296689)
              ·
                refine ⟨20969577435300192844722517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27959436580400257126296689 20969577435300192844722517)
                ·
                  refine ⟨61434308892481033724773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20969577435300192844722517 61434308892481033724773)
                  ·
                    rfl

theorem cell23_1076786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_1076786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076786 prefixEnd_1076786 := by exact prefixLift 1076786
  have htrace : WordTrace (prefixWord ++ tailWord_1076786) baseStart_1076786 baseEnd_1076786 := by
    simpa [prefixWord, tailWord_1076786, baseEnd_1076786] using wordTrace_append hprefix tailTrace_1076786
  have hstable : (prefixWord ++ tailWord_1076786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076786).length < 2 ^ (prefixWord ++ tailWord_1076786).sum := by decide
  have hdescent : baseEnd_1076786 < baseStart_1076786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076797 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1076797 : Nat := 118140960795 + 1076797 * 2 ^ 59
def prefixEnd_1076797 : Nat := 4983230072969 + 3 ^ 40 * 1076797 * 2
def baseEnd_1076797 : Nat := 552914428319528760485407

theorem tailTrace_1076797 : CollatzResearch.WordTrace tailWord_1076797 prefixEnd_1076797 552914428319528760485407 := by
  unfold tailWord_1076797
  simp only [CollatzResearch.WordTrace]
  refine ⟨39274013079955846131500645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26182675386637230754333763 39274013079955846131500645)
  ·
    refine ⟨7363877452491721149656371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39274013079955846131500645 7363877452491721149656371)
    ·
      refine ⟨11045816178737581724484557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7363877452491721149656371 11045816178737581724484557)
      ·
        refine ⟨4142181067026593146681709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11045816178737581724484557 4142181067026593146681709)
        ·
          refine ⟨1553317900134972430005641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4142181067026593146681709 1553317900134972430005641)
          ·
            refine ⟨1164988425101229322504231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1553317900134972430005641 1164988425101229322504231)
            ·
              refine ⟨1747482637651843983756347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164988425101229322504231 1747482637651843983756347)
              ·
                refine ⟨2621223956477765975634521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747482637651843983756347 2621223956477765975634521)
                ·
                  refine ⟨1965917967358324481725891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621223956477765975634521 1965917967358324481725891)
                  ·
                    refine ⟨2948876951037486722588837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1965917967358324481725891 2948876951037486722588837)
                    ·
                      refine ⟨552914428319528760485407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2948876951037486722588837 552914428319528760485407)
                      ·
                        rfl

theorem cell23_1076797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1076797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076797 prefixEnd_1076797 := by exact prefixLift 1076797
  have htrace : WordTrace (prefixWord ++ tailWord_1076797) baseStart_1076797 baseEnd_1076797 := by
    simpa [prefixWord, tailWord_1076797, baseEnd_1076797] using wordTrace_append hprefix tailTrace_1076797
  have hstable : (prefixWord ++ tailWord_1076797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076797).length < 2 ^ (prefixWord ++ tailWord_1076797).sum := by decide
  have hdescent : baseEnd_1076797 < baseStart_1076797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076850 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_1076850 : Nat := 118140960795 + 1076850 * 2 ^ 59
def prefixEnd_1076850 : Nat := 4983230072969 + 3 ^ 40 * 1076850 * 2
def baseEnd_1076850 : Nat := 184313880931405684374221

theorem tailTrace_1076850 : CollatzResearch.WordTrace tailWord_1076850 prefixEnd_1076850 184313880931405684374221 := by
  unfold tailWord_1076850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818986537190959045795001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26183964099175890788786669 9818986537190959045795001)
  ·
    refine ⟨7364239902893219284346251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9818986537190959045795001 7364239902893219284346251)
    ·
      refine ⟨11046359854339828926519377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7364239902893219284346251 11046359854339828926519377)
      ·
        refine ⟨8284769890754871694889533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11046359854339828926519377 8284769890754871694889533)
        ·
          refine ⟨3106788709033076885583575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8284769890754871694889533 3106788709033076885583575)
          ·
            refine ⟨4660183063549615328375363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106788709033076885583575 4660183063549615328375363)
            ·
              refine ⟨6990274595324422992563045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660183063549615328375363 6990274595324422992563045)
              ·
                refine ⟨1310676486623329311105571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6990274595324422992563045 1310676486623329311105571)
                ·
                  refine ⟨1966014729934993966658357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310676486623329311105571 1966014729934993966658357)
                  ·
                    refine ⟨184313880931405684374221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1966014729934993966658357 184313880931405684374221)
                    ·
                      rfl

theorem cell23_1076850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_1076850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076850 prefixEnd_1076850 := by exact prefixLift 1076850
  have htrace : WordTrace (prefixWord ++ tailWord_1076850) baseStart_1076850 baseEnd_1076850 := by
    simpa [prefixWord, tailWord_1076850, baseEnd_1076850] using wordTrace_append hprefix tailTrace_1076850
  have hstable : (prefixWord ++ tailWord_1076850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076850).length < 2 ^ (prefixWord ++ tailWord_1076850).sum := by decide
  have hdescent : baseEnd_1076850 < baseStart_1076850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076873 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_1076873 : Nat := 118140960795 + 1076873 * 2 ^ 59
def prefixEnd_1076873 : Nat := 4983230072969 + 3 ^ 40 * 1076873 * 2
def baseEnd_1076873 : Nat := 552953452849270463135057

theorem tailTrace_1076873 : CollatzResearch.WordTrace tailWord_1076873 prefixEnd_1076873 552953452849270463135057 := by
  unfold tailWord_1076873
  simp only [CollatzResearch.WordTrace]
  refine ⟨39276785027680511111267273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26184523351787007407511515 39276785027680511111267273)
  ·
    refine ⟨29457588770760383333450455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39276785027680511111267273 29457588770760383333450455)
    ·
      refine ⟨44186383156140575000175683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29457588770760383333450455 44186383156140575000175683)
      ·
        refine ⟨66279574734210862500263525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44186383156140575000175683 66279574734210862500263525)
        ·
          refine ⟨12427420262664536718799411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66279574734210862500263525 12427420262664536718799411)
          ·
            refine ⟨18641130393996805078199117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12427420262664536718799411 18641130393996805078199117)
            ·
              refine ⟨6990423897748801904324669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18641130393996805078199117 6990423897748801904324669)
              ·
                refine ⟨2621408961655800714121751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6990423897748801904324669 2621408961655800714121751)
                ·
                  refine ⟨3932113442483701071182627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621408961655800714121751 3932113442483701071182627)
                  ·
                    refine ⟨5898170163725551606773941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3932113442483701071182627 5898170163725551606773941)
                    ·
                      refine ⟨552953452849270463135057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5898170163725551606773941 552953452849270463135057)
                      ·
                        rfl

theorem cell23_1076873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_1076873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076873 prefixEnd_1076873 := by exact prefixLift 1076873
  have htrace : WordTrace (prefixWord ++ tailWord_1076873) baseStart_1076873 baseEnd_1076873 := by
    simpa [prefixWord, tailWord_1076873, baseEnd_1076873] using wordTrace_append hprefix tailTrace_1076873
  have hstable : (prefixWord ++ tailWord_1076873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076873).length < 2 ^ (prefixWord ++ tailWord_1076873).sum := by decide
  have hdescent : baseEnd_1076873 < baseStart_1076873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076897 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 2, 4]
def baseStart_1076897 : Nat := 118140960795 + 1076897 * 2 ^ 59
def prefixEnd_1076897 : Nat := 4983230072969 + 3 ^ 40 * 1076897 * 2
def baseEnd_1076897 : Nat := 184321925461659456411649

theorem tailTrace_1076897 : CollatzResearch.WordTrace tailWord_1076897 prefixEnd_1076897 184321925461659456411649 := by
  unfold tailWord_1076897
  simp only [CollatzResearch.WordTrace]
  refine ⟨39277660379593563210140945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26185106919729042140093963 39277660379593563210140945)
  ·
    refine ⟨29458245284695172407605709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39277660379593563210140945 29458245284695172407605709)
    ·
      refine ⟨11046841981760689652852141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29458245284695172407605709 11046841981760689652852141)
      ·
        refine ⟨4142565743160258619819553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11046841981760689652852141 4142565743160258619819553)
        ·
          refine ⟨3106924307370193964864665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4142565743160258619819553 3106924307370193964864665)
          ·
            refine ⟨2330193230527645473648499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106924307370193964864665 2330193230527645473648499)
            ·
              refine ⟨3495289845791468210472749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330193230527645473648499 3495289845791468210472749)
              ·
                refine ⟨1310733692171800578927281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3495289845791468210472749 1310733692171800578927281)
                ·
                  refine ⟨983050269128850434195461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1310733692171800578927281 983050269128850434195461)
                  ·
                    refine ⟨184321925461659456411649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 983050269128850434195461 184321925461659456411649)
                    ·
                      rfl

theorem cell23_1076897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_1076897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076897 prefixEnd_1076897 := by exact prefixLift 1076897
  have htrace : WordTrace (prefixWord ++ tailWord_1076897) baseStart_1076897 baseEnd_1076897 := by
    simpa [prefixWord, tailWord_1076897, baseEnd_1076897] using wordTrace_append hprefix tailTrace_1076897
  have hstable : (prefixWord ++ tailWord_1076897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076897).length < 2 ^ (prefixWord ++ tailWord_1076897).sum := by decide
  have hdescent : baseEnd_1076897 < baseStart_1076897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076917 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1076917 : Nat := 118140960795 + 1076917 * 2 ^ 59
def prefixEnd_1076917 : Nat := 4983230072969 + 3 ^ 40 * 1076917 * 2
def baseEnd_1076917 : Nat := 552976045998068290984855

theorem tailTrace_1076917 : CollatzResearch.WordTrace tailWord_1076917 prefixEnd_1076917 552976045998068290984855 := by
  unfold tailWord_1076917
  simp only [CollatzResearch.WordTrace]
  refine ⟨39278389839521106625869005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26185593226347404417246003 39278389839521106625869005)
  ·
    refine ⟨14729396189820414984700877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39278389839521106625869005 14729396189820414984700877)
    ·
      refine ⟨5523523571182655619262829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14729396189820414984700877 5523523571182655619262829)
      ·
        refine ⟨2071321339193495857223561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5523523571182655619262829 2071321339193495857223561)
        ·
          refine ⟨1553491004395121892917671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2071321339193495857223561 1553491004395121892917671)
          ·
            refine ⟨2330236506592682839376507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553491004395121892917671 2330236506592682839376507)
            ·
              refine ⟨3495354759889024259064761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330236506592682839376507 3495354759889024259064761)
              ·
                refine ⟨2621516069916768194298571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3495354759889024259064761 2621516069916768194298571)
                ·
                  refine ⟨3932274104875152291447857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621516069916768194298571 3932274104875152291447857)
                  ·
                    refine ⟨2949205578656364218585893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932274104875152291447857 2949205578656364218585893)
                    ·
                      refine ⟨552976045998068290984855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2949205578656364218585893 552976045998068290984855)
                      ·
                        rfl

theorem cell23_1076917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1076917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076917 prefixEnd_1076917 := by exact prefixLift 1076917
  have htrace : WordTrace (prefixWord ++ tailWord_1076917) baseStart_1076917 baseEnd_1076917 := by
    simpa [prefixWord, tailWord_1076917, baseEnd_1076917] using wordTrace_append hprefix tailTrace_1076917
  have hstable : (prefixWord ++ tailWord_1076917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076917).length < 2 ^ (prefixWord ++ tailWord_1076917).sum := by decide
  have hdescent : baseEnd_1076917 < baseStart_1076917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076920 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_1076920 : Nat := 118140960795 + 1076920 * 2 ^ 59
def prefixEnd_1076920 : Nat := 4983230072969 + 3 ^ 40 * 1076920 * 2
def baseEnd_1076920 : Nat := 552977586440031779247341

theorem tailTrace_1076920 : CollatzResearch.WordTrace tailWord_1076920 prefixEnd_1076920 552977586440031779247341 := by
  unfold tailWord_1076920
  simp only [CollatzResearch.WordTrace]
  refine ⟨19639249629255119069114107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26185666172340158758818809 19639249629255119069114107)
  ·
    refine ⟨29458874443882678603671161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19639249629255119069114107 29458874443882678603671161)
    ·
      refine ⟨22094155832912008952753371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29458874443882678603671161 22094155832912008952753371)
      ·
        refine ⟨33141233749368013429130057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22094155832912008952753371 33141233749368013429130057)
        ·
          refine ⟨24855925312026010071847543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33141233749368013429130057 24855925312026010071847543)
          ·
            refine ⟨37283887968039015107771315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24855925312026010071847543 37283887968039015107771315)
            ·
              refine ⟨55925831952058522661656973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37283887968039015107771315 55925831952058522661656973)
              ·
                refine ⟨20972186982021945998121365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55925831952058522661656973 20972186982021945998121365)
                ·
                  refine ⟨983071264782278718661939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20972186982021945998121365 983071264782278718661939)
                  ·
                    refine ⟨1474606897173418077992909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 983071264782278718661939 1474606897173418077992909)
                    ·
                      refine ⟨552977586440031779247341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474606897173418077992909 552977586440031779247341)
                      ·
                        rfl

theorem cell23_1076920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_1076920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076920 prefixEnd_1076920 := by exact prefixLift 1076920
  have htrace : WordTrace (prefixWord ++ tailWord_1076920) baseStart_1076920 baseEnd_1076920 := by
    simpa [prefixWord, tailWord_1076920, baseEnd_1076920] using wordTrace_append hprefix tailTrace_1076920
  have hstable : (prefixWord ++ tailWord_1076920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076920).length < 2 ^ (prefixWord ++ tailWord_1076920).sum := by decide
  have hdescent : baseEnd_1076920 < baseStart_1076920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076924 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_1076924 : Nat := 118140960795 + 1076924 * 2 ^ 59
def prefixEnd_1076924 : Nat := 4983230072969 + 3 ^ 40 * 1076924 * 2
def baseEnd_1076924 : Nat := 552979640362649763597323

theorem tailTrace_1076924 : CollatzResearch.WordTrace tailWord_1076924 prefixEnd_1076924 552979640362649763597323 := by
  unfold tailWord_1076924
  simp only [CollatzResearch.WordTrace]
  refine ⟨19639322575247873410686913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26185763433663831214249217 19639322575247873410686913)
  ·
    refine ⟨14729491931435905058015185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19639322575247873410686913 14729491931435905058015185)
    ·
      refine ⟨11047118948576928793511389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14729491931435905058015185 11047118948576928793511389)
      ·
        refine ⟨4142669605716348297566771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11047118948576928793511389 4142669605716348297566771)
        ·
          refine ⟨6214004408574522446350157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142669605716348297566771 6214004408574522446350157)
          ·
            refine ⟨2330251653215445917381309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6214004408574522446350157 2330251653215445917381309)
            ·
              refine ⟨873844369955792219017991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2330251653215445917381309 873844369955792219017991)
              ·
                refine ⟨1310766554933688328526987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873844369955792219017991 1310766554933688328526987)
                ·
                  refine ⟨1966149832400532492790481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310766554933688328526987 1966149832400532492790481)
                  ·
                    refine ⟨1474612374300399369592861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1966149832400532492790481 1474612374300399369592861)
                    ·
                      refine ⟨552979640362649763597323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474612374300399369592861 552979640362649763597323)
                      ·
                        rfl

theorem cell23_1076924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_1076924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076924 prefixEnd_1076924 := by exact prefixLift 1076924
  have htrace : WordTrace (prefixWord ++ tailWord_1076924) baseStart_1076924 baseEnd_1076924 := by
    simpa [prefixWord, tailWord_1076924, baseEnd_1076924] using wordTrace_append hprefix tailTrace_1076924
  have hstable : (prefixWord ++ tailWord_1076924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076924).length < 2 ^ (prefixWord ++ tailWord_1076924).sum := by decide
  have hdescent : baseEnd_1076924 < baseStart_1076924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076953 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 1, 8]
def baseStart_1076953 : Nat := 118140960795 + 1076953 * 2 ^ 59
def prefixEnd_1076953 : Nat := 4983230072969 + 3 ^ 40 * 1076953 * 2
def baseEnd_1076953 : Nat := 184331510433876716711563

theorem tailTrace_1076953 : CollatzResearch.WordTrace tailWord_1076953 prefixEnd_1076953 184331510433876716711563 := by
  unfold tailWord_1076953
  simp only [CollatzResearch.WordTrace]
  refine ⟨39279702867390684774179513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26186468578260456516119675 39279702867390684774179513)
  ·
    refine ⟨29459777150543013580634635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39279702867390684774179513 29459777150543013580634635)
    ·
      refine ⟨44189665725814520370951953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29459777150543013580634635 44189665725814520370951953)
      ·
        refine ⟨33142249294360890278213965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44189665725814520370951953 33142249294360890278213965)
        ·
          refine ⟨12428343485385333854330237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33142249294360890278213965 12428343485385333854330237)
          ·
            refine ⟨4660628807019500195373839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12428343485385333854330237 4660628807019500195373839)
            ·
              refine ⟨6990943210529250293060759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660628807019500195373839 6990943210529250293060759)
              ·
                refine ⟨10486414815793875439591139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6990943210529250293060759 10486414815793875439591139)
                ·
                  refine ⟨15729622223690813159386709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10486414815793875439591139 15729622223690813159386709)
                  ·
                    refine ⟨184331510433876716711563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15729622223690813159386709 184331510433876716711563)
                    ·
                      rfl

theorem cell23_1076953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_1076953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076953 prefixEnd_1076953 := by exact prefixLift 1076953
  have htrace : WordTrace (prefixWord ++ tailWord_1076953) baseStart_1076953 baseEnd_1076953 := by
    simpa [prefixWord, tailWord_1076953, baseEnd_1076953] using wordTrace_append hprefix tailTrace_1076953
  have hstable : (prefixWord ++ tailWord_1076953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076953).length < 2 ^ (prefixWord ++ tailWord_1076953).sum := by decide
  have hdescent : baseEnd_1076953 < baseStart_1076953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076977 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 1, 4, 2]
def baseStart_1076977 : Nat := 118140960795 + 1076977 * 2 ^ 59
def prefixEnd_1076977 : Nat := 4983230072969 + 3 ^ 40 * 1076977 * 2
def baseEnd_1076977 : Nat := 553006854837338056234579

theorem tailTrace_1076977 : CollatzResearch.WordTrace tailWord_1076977 prefixEnd_1076977 553006854837338056234579 := by
  unfold tailWord_1076977
  simp only [CollatzResearch.WordTrace]
  refine ⟨39280578219303736873053185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26187052146202491248702123 39280578219303736873053185)
  ·
    refine ⟨29460433664477802654789889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39280578219303736873053185 29460433664477802654789889)
    ·
      refine ⟨22095325248358351991092417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29460433664477802654789889 22095325248358351991092417)
      ·
        refine ⟨16571493936268763993319313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22095325248358351991092417 16571493936268763993319313)
        ·
          refine ⟨12428620452201572994989485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16571493936268763993319313 12428620452201572994989485)
          ·
            refine ⟨4660732669575589873121057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12428620452201572994989485 4660732669575589873121057)
            ·
              refine ⟨3495549502181692404840793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4660732669575589873121057 3495549502181692404840793)
              ·
                refine ⟨2621662126636269303630595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3495549502181692404840793 2621662126636269303630595)
                ·
                  refine ⟨3932493189954403955445893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621662126636269303630595 3932493189954403955445893)
                  ·
                    refine ⟨737342473116450741646105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932493189954403955445893 737342473116450741646105)
                    ·
                      refine ⟨553006854837338056234579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737342473116450741646105 553006854837338056234579)
                      ·
                        rfl

theorem cell23_1076977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_1076977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1076977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1076977 prefixEnd_1076977 := by exact prefixLift 1076977
  have htrace : WordTrace (prefixWord ++ tailWord_1076977) baseStart_1076977 baseEnd_1076977 := by
    simpa [prefixWord, tailWord_1076977, baseEnd_1076977] using wordTrace_append hprefix tailTrace_1076977
  have hstable : (prefixWord ++ tailWord_1076977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076977).length < 2 ^ (prefixWord ++ tailWord_1076977).sum := by decide
  have hdescent : baseEnd_1076977 < baseStart_1076977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077000 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 7]
def baseStart_1077000 : Nat := 118140960795 + 1077000 * 2 ^ 59
def prefixEnd_1077000 : Nat := 4983230072969 + 3 ^ 40 * 1077000 * 2
def baseEnd_1077000 : Nat := 61446518321376829582997

theorem tailTrace_1077000 : CollatzResearch.WordTrace tailWord_1077000 prefixEnd_1077000 61446518321376829582997 := by
  unfold tailWord_1077000
  simp only [CollatzResearch.WordTrace]
  refine ⟨19640708549110205900570227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26187611398813607867426969 19640708549110205900570227)
  ·
    refine ⟨29461062823665308850855341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19640708549110205900570227 29461062823665308850855341)
    ·
      refine ⟨11047898558874490819070753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29461062823665308850855341 11047898558874490819070753)
      ·
        refine ⟨8285923919155868114303065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11047898558874490819070753 8285923919155868114303065)
        ·
          refine ⟨6214442939366901085727299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8285923919155868114303065 6214442939366901085727299)
          ·
            refine ⟨9321664409050351628590949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6214442939366901085727299 9321664409050351628590949)
            ·
              refine ⟨1747812076696940930360803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9321664409050351628590949 1747812076696940930360803)
              ·
                refine ⟨2621718115045411395541205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747812076696940930360803 2621718115045411395541205)
                ·
                  refine ⟨61446518321376829582997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2621718115045411395541205 61446518321376829582997)
                  ·
                    rfl

theorem cell23_1077000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 7].length) (baseStart_1077000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077000 prefixEnd_1077000 := by exact prefixLift 1077000
  have htrace : WordTrace (prefixWord ++ tailWord_1077000) baseStart_1077000 baseEnd_1077000 := by
    simpa [prefixWord, tailWord_1077000, baseEnd_1077000] using wordTrace_append hprefix tailTrace_1077000
  have hstable : (prefixWord ++ tailWord_1077000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077000).length < 2 ^ (prefixWord ++ tailWord_1077000).sum := by decide
  have hdescent : baseEnd_1077000 < baseStart_1077000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077005 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1077005 : Nat := 118140960795 + 1077005 * 2 ^ 59
def prefixEnd_1077005 : Nat := 4983230072969 + 3 ^ 40 * 1077005 * 2
def baseEnd_1077005 : Nat := 553021232295663946684451

theorem tailTrace_1077005 : CollatzResearch.WordTrace tailWord_1077005 prefixEnd_1077005 553021232295663946684451 := by
  unfold tailWord_1077005
  simp only [CollatzResearch.WordTrace]
  refine ⟨39281599463202297655072469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26187732975468198436714979 39281599463202297655072469)
  ·
    refine ⟨920662487418803851290761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39281599463202297655072469 920662487418803851290761)
    ·
      refine ⟨690496865564102888468071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 920662487418803851290761 690496865564102888468071)
      ·
        refine ⟨1035745298346154332702107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 690496865564102888468071 1035745298346154332702107)
        ·
          refine ⟨1553617947519231499053161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1035745298346154332702107 1553617947519231499053161)
          ·
            refine ⟨1165213460639423624289871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1553617947519231499053161 1165213460639423624289871)
            ·
              refine ⟨1747820190959135436434807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165213460639423624289871 1747820190959135436434807)
              ·
                refine ⟨2621730286438703154652211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747820190959135436434807 2621730286438703154652211)
                ·
                  refine ⟨3932595429658054731978317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621730286438703154652211 3932595429658054731978317)
                  ·
                    refine ⟨1474723286121770524491869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3932595429658054731978317 1474723286121770524491869)
                    ·
                      refine ⟨553021232295663946684451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474723286121770524491869 553021232295663946684451)
                      ·
                        rfl

theorem cell23_1077005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1077005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077005 prefixEnd_1077005 := by exact prefixLift 1077005
  have htrace : WordTrace (prefixWord ++ tailWord_1077005) baseStart_1077005 baseEnd_1077005 := by
    simpa [prefixWord, tailWord_1077005, baseEnd_1077005] using wordTrace_append hprefix tailTrace_1077005
  have hstable : (prefixWord ++ tailWord_1077005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077005).length < 2 ^ (prefixWord ++ tailWord_1077005).sum := by decide
  have hdescent : baseEnd_1077005 < baseStart_1077005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077062 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1077062 : Nat := 118140960795 + 1077062 * 2 ^ 59
def prefixEnd_1077062 : Nat := 4983230072969 + 3 ^ 40 * 1077062 * 2
def baseEnd_1077062 : Nat := 553050500692970223671689

theorem tailTrace_1077062 : CollatzResearch.WordTrace tailWord_1077062 prefixEnd_1077062 553050500692970223671689 := by
  unfold tailWord_1077062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1227614950749868637184295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26189118949330530926598293 1227614950749868637184295)
  ·
    refine ⟨1841422426124802955776443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1227614950749868637184295 1841422426124802955776443)
    ·
      refine ⟨2762133639187204433664665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1841422426124802955776443 2762133639187204433664665)
      ·
        refine ⟨2071600229390403325248499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2762133639187204433664665 2071600229390403325248499)
        ·
          refine ⟨3107400344085604987872749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071600229390403325248499 3107400344085604987872749)
          ·
            refine ⟨1165275129032101870452281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3107400344085604987872749 1165275129032101870452281)
            ·
              refine ⟨873956346774076402839211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165275129032101870452281 873956346774076402839211)
              ·
                refine ⟨1310934520161114604258817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873956346774076402839211 1310934520161114604258817)
                ·
                  refine ⟨983200890120835953194113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1310934520161114604258817 983200890120835953194113)
                  ·
                    refine ⟨737400667590626964895585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 983200890120835953194113 737400667590626964895585)
                    ·
                      refine ⟨553050500692970223671689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737400667590626964895585 553050500692970223671689)
                      ·
                        rfl

theorem cell23_1077062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1077062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077062 prefixEnd_1077062 := by exact prefixLift 1077062
  have htrace : WordTrace (prefixWord ++ tailWord_1077062) baseStart_1077062 baseEnd_1077062 := by
    simpa [prefixWord, tailWord_1077062, baseEnd_1077062] using wordTrace_append hprefix tailTrace_1077062
  have hstable : (prefixWord ++ tailWord_1077062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077062).length < 2 ^ (prefixWord ++ tailWord_1077062).sum := by decide
  have hdescent : baseEnd_1077062 < baseStart_1077062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077087 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 3]
def baseStart_1077087 : Nat := 118140960795 + 1077087 * 2 ^ 59
def prefixEnd_1077087 : Nat := 4983230072969 + 3 ^ 40 * 1077087 * 2
def baseEnd_1077087 : Nat := 553063337709332625859073

theorem tailTrace_1077087 : CollatzResearch.WordTrace tailWord_1077087 prefixEnd_1077087 553063337709332625859073 := by
  unfold tailWord_1077087
  simp only [CollatzResearch.WordTrace]
  refine ⟨39284590248905225659557515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26189726832603483773038343 39284590248905225659557515)
  ·
    refine ⟨58926885373357838489336273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39284590248905225659557515 58926885373357838489336273)
    ·
      refine ⟨44195164030018378867002205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58926885373357838489336273 44195164030018378867002205)
      ·
        refine ⟨16573186511256892075125827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44195164030018378867002205 16573186511256892075125827)
        ·
          refine ⟨24859779766885338112688741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16573186511256892075125827 24859779766885338112688741)
          ·
            refine ⟨4661208706291000896129139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24859779766885338112688741 4661208706291000896129139)
            ·
              refine ⟨6991813059436501344193709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661208706291000896129139 6991813059436501344193709)
              ·
                refine ⟨2621929897288688004072641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6991813059436501344193709 2621929897288688004072641)
                ·
                  refine ⟨1966447422966516003054481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621929897288688004072641 1966447422966516003054481)
                  ·
                    refine ⟨1474835567224887002290861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1966447422966516003054481 1474835567224887002290861)
                    ·
                      refine ⟨553063337709332625859073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474835567224887002290861 553063337709332625859073)
                      ·
                        rfl

theorem cell23_1077087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_1077087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077087 prefixEnd_1077087 := by exact prefixLift 1077087
  have htrace : WordTrace (prefixWord ++ tailWord_1077087) baseStart_1077087 baseEnd_1077087 := by
    simpa [prefixWord, tailWord_1077087, baseEnd_1077087] using wordTrace_append hprefix tailTrace_1077087
  have hstable : (prefixWord ++ tailWord_1077087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077087).length < 2 ^ (prefixWord ++ tailWord_1077087).sum := by decide
  have hdescent : baseEnd_1077087 < baseStart_1077087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077120 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 5, 5]
def baseStart_1077120 : Nat := 118140960795 + 1077120 * 2 ^ 59
def prefixEnd_1077120 : Nat := 4983230072969 + 3 ^ 40 * 1077120 * 2
def baseEnd_1077120 : Nat := 184360094190310332248807

theorem tailTrace_1077120 : CollatzResearch.WordTrace tailWord_1077120 prefixEnd_1077120 184360094190310332248807 := by
  unfold tailWord_1077120
  simp only [CollatzResearch.WordTrace]
  refine ⟨19642896928892836147754407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26190529238523781530339209 19642896928892836147754407)
  ·
    refine ⟨29464345393339254221631611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19642896928892836147754407 29464345393339254221631611)
    ·
      refine ⟨44196518090008881332447417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29464345393339254221631611 44196518090008881332447417)
      ·
        refine ⟨33147388567506660999335563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44196518090008881332447417 33147388567506660999335563)
        ·
          refine ⟨49721082851259991499003345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33147388567506660999335563 49721082851259991499003345)
          ·
            refine ⟨37290812138444993624252509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49721082851259991499003345 37290812138444993624252509)
            ·
              refine ⟨13984054551916872609094691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37290812138444993624252509 13984054551916872609094691)
              ·
                refine ⟨20976081827875308913642037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13984054551916872609094691 20976081827875308913642037)
                ·
                  refine ⟨1966507671363310210653941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20976081827875308913642037 1966507671363310210653941)
                  ·
                    refine ⟨184360094190310332248807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1966507671363310210653941 184360094190310332248807)
                    ·
                      rfl

theorem cell23_1077120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_1077120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077120 prefixEnd_1077120 := by exact prefixLift 1077120
  have htrace : WordTrace (prefixWord ++ tailWord_1077120) baseStart_1077120 baseEnd_1077120 := by
    simpa [prefixWord, tailWord_1077120, baseEnd_1077120] using wordTrace_append hprefix tailTrace_1077120
  have hstable : (prefixWord ++ tailWord_1077120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077120).length < 2 ^ (prefixWord ++ tailWord_1077120).sum := by decide
  have hdescent : baseEnd_1077120 < baseStart_1077120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077157 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 8, 2]
def baseStart_1077157 : Nat := 118140960795 + 1077157 * 2 ^ 59
def prefixEnd_1077157 : Nat := 4983230072969 + 3 ^ 40 * 1077157 * 2
def baseEnd_1077157 : Nat := 553099281355147351983751

theorem tailTrace_1077157 : CollatzResearch.WordTrace tailWord_1077157 prefixEnd_1077157 553099281355147351983751 := by
  unfold tailWord_1077157
  simp only [CollatzResearch.WordTrace]
  refine ⟨39287143358651627614605725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26191428905767751743070483 39287143358651627614605725)
  ·
    refine ⟨14732678759494360355477147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39287143358651627614605725 14732678759494360355477147)
    ·
      refine ⟨22099018139241540533215721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14732678759494360355477147 22099018139241540533215721)
      ·
        refine ⟨16574263604431155399911791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22099018139241540533215721 16574263604431155399911791)
        ·
          refine ⟨24861395406646733099867687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16574263604431155399911791 24861395406646733099867687)
          ·
            refine ⟨37292093109970099649801531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24861395406646733099867687 37292093109970099649801531)
            ·
              refine ⟨55938139664955149474702297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37292093109970099649801531 55938139664955149474702297)
              ·
                refine ⟨41953604748716362106026723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55938139664955149474702297 41953604748716362106026723)
                ·
                  refine ⟨62930407123074543159040085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41953604748716362106026723 62930407123074543159040085)
                  ·
                    refine ⟨737465708473529802645001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62930407123074543159040085 737465708473529802645001)
                    ·
                      refine ⟨553099281355147351983751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737465708473529802645001 553099281355147351983751)
                      ·
                        rfl

theorem cell23_1077157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_1077157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077157 prefixEnd_1077157 := by exact prefixLift 1077157
  have htrace : WordTrace (prefixWord ++ tailWord_1077157) baseStart_1077157 baseEnd_1077157 := by
    simpa [prefixWord, tailWord_1077157, baseEnd_1077157] using wordTrace_append hprefix tailTrace_1077157
  have hstable : (prefixWord ++ tailWord_1077157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077157).length < 2 ^ (prefixWord ++ tailWord_1077157).sum := by decide
  have hdescent : baseEnd_1077157 < baseStart_1077157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077167 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 4, 4]
def baseStart_1077167 : Nat := 118140960795 + 1077167 * 2 ^ 59
def prefixEnd_1077167 : Nat := 4983230072969 + 3 ^ 40 * 1077167 * 2
def baseEnd_1077167 : Nat := 184368138720564104286235

theorem tailTrace_1077167 : CollatzResearch.WordTrace tailWord_1077167 prefixEnd_1077167 184368138720564104286235 := by
  unfold tailWord_1077167
  simp only [CollatzResearch.WordTrace]
  refine ⟨39287508088615399322469755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26191672059076932881646503 39287508088615399322469755)
  ·
    refine ⟨58931262132923098983704633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39287508088615399322469755 58931262132923098983704633)
    ·
      refine ⟨44198446599692324237778475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58931262132923098983704633 44198446599692324237778475)
      ·
        refine ⟨66297669899538486356667713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44198446599692324237778475 66297669899538486356667713)
        ·
          refine ⟨49723252424653864767500785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66297669899538486356667713 49723252424653864767500785)
          ·
            refine ⟨37292439318490398575625589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49723252424653864767500785 37292439318490398575625589)
            ·
              refine ⟨3496166186108474866464899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37292439318490398575625589 3496166186108474866464899)
              ·
                refine ⟨5244249279162712299697349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496166186108474866464899 5244249279162712299697349)
                ·
                  refine ⟨983296739843008556193253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5244249279162712299697349 983296739843008556193253)
                  ·
                    refine ⟨184368138720564104286235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 983296739843008556193253 184368138720564104286235)
                    ·
                      rfl

theorem cell23_1077167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_1077167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077167 prefixEnd_1077167 := by exact prefixLift 1077167
  have htrace : WordTrace (prefixWord ++ tailWord_1077167) baseStart_1077167 baseEnd_1077167 := by
    simpa [prefixWord, tailWord_1077167, baseEnd_1077167] using wordTrace_append hprefix tailTrace_1077167
  have hstable : (prefixWord ++ tailWord_1077167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077167).length < 2 ^ (prefixWord ++ tailWord_1077167).sum := by decide
  have hdescent : baseEnd_1077167 < baseStart_1077167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077177 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1077177 : Nat := 118140960795 + 1077177 * 2 ^ 59
def prefixEnd_1077177 : Nat := 4983230072969 + 3 ^ 40 * 1077177 * 2
def baseEnd_1077177 : Nat := 553109550968237273733659

theorem tailTrace_1077177 : CollatzResearch.WordTrace tailWord_1077177 prefixEnd_1077177 553109550968237273733659 := by
  unfold tailWord_1077177
  simp only [CollatzResearch.WordTrace]
  refine ⟨39287872818579171030333785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26191915212386114020222523 39287872818579171030333785)
  ·
    refine ⟨29465904613934378272750339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39287872818579171030333785 29465904613934378272750339)
    ·
      refine ⟨44198856920901567409125509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29465904613934378272750339 44198856920901567409125509)
      ·
        refine ⟨8287285672669043889211033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44198856920901567409125509 8287285672669043889211033)
        ·
          refine ⟨6215464254501782916908275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8287285672669043889211033 6215464254501782916908275)
          ·
            refine ⟨9323196381752674375362413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215464254501782916908275 9323196381752674375362413)
            ·
              refine ⟨3496198643157252890760905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9323196381752674375362413 3496198643157252890760905)
              ·
                refine ⟨2622148982367939668070679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3496198643157252890760905 2622148982367939668070679)
                ·
                  refine ⟨3933223473551909502106019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2622148982367939668070679 3933223473551909502106019)
                  ·
                    refine ⟨5899835210327864253159029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3933223473551909502106019 5899835210327864253159029)
                    ·
                      refine ⟨553109550968237273733659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5899835210327864253159029 553109550968237273733659)
                      ·
                        rfl

theorem cell23_1077177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1077177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077177 prefixEnd_1077177 := by exact prefixLift 1077177
  have htrace : WordTrace (prefixWord ++ tailWord_1077177) baseStart_1077177 baseEnd_1077177 := by
    simpa [prefixWord, tailWord_1077177, baseEnd_1077177] using wordTrace_append hprefix tailTrace_1077177
  have hstable : (prefixWord ++ tailWord_1077177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077177).length < 2 ^ (prefixWord ++ tailWord_1077177).sum := by decide
  have hdescent : baseEnd_1077177 < baseStart_1077177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077194 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_1077194 : Nat := 118140960795 + 1077194 * 2 ^ 59
def prefixEnd_1077194 : Nat := 4983230072969 + 3 ^ 40 * 1077194 * 2
def baseEnd_1077194 : Nat := 553118280139363707221081

theorem tailTrace_1077194 : CollatzResearch.WordTrace tailWord_1077194 prefixEnd_1077194 553118280139363707221081 := by
  unfold tailWord_1077194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822123214879395733425659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26192328573011721955801757 9822123214879395733425659)
  ·
    refine ⟨14733184822319093600138489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9822123214879395733425659 14733184822319093600138489)
    ·
      refine ⟨11049888616739320200103867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14733184822319093600138489 11049888616739320200103867)
      ·
        refine ⟨16574832925108980300155801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11049888616739320200103867 16574832925108980300155801)
        ·
          refine ⟨12431124693831735225116851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16574832925108980300155801 12431124693831735225116851)
          ·
            refine ⟨18646687040747602837675277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12431124693831735225116851 18646687040747602837675277)
            ·
              refine ⟨6992507640280351064128229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18646687040747602837675277 6992507640280351064128229)
              ·
                refine ⟨1311095182552565824524043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6992507640280351064128229 1311095182552565824524043)
                ·
                  refine ⟨1966642773828848736786065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311095182552565824524043 1966642773828848736786065)
                  ·
                    refine ⟨1474982080371636552589549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1966642773828848736786065 1474982080371636552589549)
                    ·
                      refine ⟨553118280139363707221081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474982080371636552589549 553118280139363707221081)
                      ·
                        rfl

theorem cell23_1077194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_1077194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077194 prefixEnd_1077194 := by exact prefixLift 1077194
  have htrace : WordTrace (prefixWord ++ tailWord_1077194) baseStart_1077194 baseEnd_1077194 := by
    simpa [prefixWord, tailWord_1077194, baseEnd_1077194] using wordTrace_append hprefix tailTrace_1077194
  have hstable : (prefixWord ++ tailWord_1077194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077194).length < 2 ^ (prefixWord ++ tailWord_1077194).sum := by decide
  have hdescent : baseEnd_1077194 < baseStart_1077194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077202 : List Nat := [3, 2, 2, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1077202 : Nat := 118140960795 + 1077202 * 2 ^ 59
def prefixEnd_1077202 : Nat := 4983230072969 + 3 ^ 40 * 1077202 * 2
def baseEnd_1077202 : Nat := 553122387984599675921045

theorem tailTrace_1077202 : CollatzResearch.WordTrace tailWord_1077202 prefixEnd_1077202 553122387984599675921045 := by
  unfold tailWord_1077202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822196160872150074998465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26192523095659066866662573 9822196160872150074998465)
  ·
    refine ⟨7366647120654112556248849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9822196160872150074998465 7366647120654112556248849)
    ·
      refine ⟨5524985340490584417186637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7366647120654112556248849 5524985340490584417186637)
      ·
        refine ⟨2071869502683969156444989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5524985340490584417186637 2071869502683969156444989)
        ·
          refine ⟨776951063506488433666871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2071869502683969156444989 776951063506488433666871)
          ·
            refine ⟨1165426595259732650500307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776951063506488433666871 1165426595259732650500307)
            ·
              refine ⟨1748139892889598975750461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165426595259732650500307 1748139892889598975750461)
              ·
                refine ⟨655552459833599615906423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1748139892889598975750461 655552459833599615906423)
                ·
                  refine ⟨983328689750399423859635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655552459833599615906423 983328689750399423859635)
                  ·
                    refine ⟨1474993034625599135789453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 983328689750399423859635 1474993034625599135789453)
                    ·
                      refine ⟨553122387984599675921045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474993034625599135789453 553122387984599675921045)
                      ·
                        rfl

theorem cell23_1077202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1077202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077202 prefixEnd_1077202 := by exact prefixLift 1077202
  have htrace : WordTrace (prefixWord ++ tailWord_1077202) baseStart_1077202 baseEnd_1077202 := by
    simpa [prefixWord, tailWord_1077202, baseEnd_1077202] using wordTrace_append hprefix tailTrace_1077202
  have hstable : (prefixWord ++ tailWord_1077202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077202).length < 2 ^ (prefixWord ++ tailWord_1077202).sum := by decide
  have hdescent : baseEnd_1077202 < baseStart_1077202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077207 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_1077207 : Nat := 118140960795 + 1077207 * 2 ^ 59
def prefixEnd_1077207 : Nat := 4983230072969 + 3 ^ 40 * 1077207 * 2
def baseEnd_1077207 : Nat := 553124955387872156358521

theorem tailTrace_1077207 : CollatzResearch.WordTrace tailWord_1077207 prefixEnd_1077207 553124955387872156358521 := by
  unfold tailWord_1077207
  simp only [CollatzResearch.WordTrace]
  refine ⟨39288967008470486153925875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26192644672313657435950583 39288967008470486153925875)
  ·
    refine ⟨58933450512705729230888813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39288967008470486153925875 58933450512705729230888813)
    ·
      refine ⟨22100043942264648461583305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58933450512705729230888813 22100043942264648461583305)
      ·
        refine ⟨16575032956698486346187479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22100043942264648461583305 16575032956698486346187479)
        ·
          refine ⟨24862549435047729519281219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16575032956698486346187479 24862549435047729519281219)
          ·
            refine ⟨37293824152571594278921829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24862549435047729519281219 37293824152571594278921829)
            ·
              refine ⟨6992592028607173927297843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37293824152571594278921829 6992592028607173927297843)
              ·
                refine ⟨10488888042910760890946765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992592028607173927297843 10488888042910760890946765)
                ·
                  refine ⟨3933333016091535334105037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10488888042910760890946765 3933333016091535334105037)
                  ·
                    refine ⟨1474999881034325750289389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3933333016091535334105037 1474999881034325750289389)
                    ·
                      refine ⟨553124955387872156358521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1474999881034325750289389 553124955387872156358521)
                      ·
                        rfl

theorem cell23_1077207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_1077207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077207 prefixEnd_1077207 := by exact prefixLift 1077207
  have htrace : WordTrace (prefixWord ++ tailWord_1077207) baseStart_1077207 baseEnd_1077207 := by
    simpa [prefixWord, tailWord_1077207, baseEnd_1077207] using wordTrace_append hprefix tailTrace_1077207
  have hstable : (prefixWord ++ tailWord_1077207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077207).length < 2 ^ (prefixWord ++ tailWord_1077207).sum := by decide
  have hdescent : baseEnd_1077207 < baseStart_1077207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077241 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 3]
def baseStart_1077241 : Nat := 118140960795 + 1077241 * 2 ^ 59
def prefixEnd_1077241 : Nat := 4983230072969 + 3 ^ 40 * 1077241 * 2
def baseEnd_1077241 : Nat := 553142413730125023333365

theorem tailTrace_1077241 : CollatzResearch.WordTrace tailWord_1077241 prefixEnd_1077241 553142413730125023333365 := by
  unfold tailWord_1077241
  simp only [CollatzResearch.WordTrace]
  refine ⟨39290207090347309960663577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26193471393564873307109051 39290207090347309960663577)
  ·
    refine ⟨29467655317760482470497683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39290207090347309960663577 29467655317760482470497683)
    ·
      refine ⟨44201482976640723705746525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29467655317760482470497683 44201482976640723705746525)
      ·
        refine ⟨16575556116240271389654947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44201482976640723705746525 16575556116240271389654947)
        ·
          refine ⟨24863334174360407084482421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16575556116240271389654947 24863334174360407084482421)
          ·
            refine ⟨2330937578846288164170227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24863334174360407084482421 2330937578846288164170227)
            ·
              refine ⟨3496406368269432246255341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330937578846288164170227 3496406368269432246255341)
              ·
                refine ⟨1311152388101037092345753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3496406368269432246255341 1311152388101037092345753)
                ·
                  refine ⟨983364291075777819259315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1311152388101037092345753 983364291075777819259315)
                  ·
                    refine ⟨1475046436613666728888973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 983364291075777819259315 1475046436613666728888973)
                    ·
                      refine ⟨553142413730125023333365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1475046436613666728888973 553142413730125023333365)
                      ·
                        rfl

theorem cell23_1077241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_1077241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077241 prefixEnd_1077241 := by exact prefixLift 1077241
  have htrace : WordTrace (prefixWord ++ tailWord_1077241) baseStart_1077241 baseEnd_1077241 := by
    simpa [prefixWord, tailWord_1077241, baseEnd_1077241] using wordTrace_append hprefix tailTrace_1077241
  have hstable : (prefixWord ++ tailWord_1077241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077241).length < 2 ^ (prefixWord ++ tailWord_1077241).sum := by decide
  have hdescent : baseEnd_1077241 < baseStart_1077241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077264 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 1, 4, 2]
def baseStart_1077264 : Nat := 118140960795 + 1077264 * 2 ^ 59
def prefixEnd_1077264 : Nat := 4983230072969 + 3 ^ 40 * 1077264 * 2
def baseEnd_1077264 : Nat := 553154223785178433345759

theorem tailTrace_1077264 : CollatzResearch.WordTrace tailWord_1077264 prefixEnd_1077264 553154223785178433345759 := by
  unfold tailWord_1077264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19645522984631992444375423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26194030646175989925833897 19645522984631992444375423)
  ·
    refine ⟨29468284476947988666563135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19645522984631992444375423 29468284476947988666563135)
    ·
      refine ⟨44202426715421982999844703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29468284476947988666563135 44202426715421982999844703)
      ·
        refine ⟨66303640073132974499767055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44202426715421982999844703 66303640073132974499767055)
        ·
          refine ⟨99455460109699461749650583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66303640073132974499767055 99455460109699461749650583)
          ·
            refine ⟨149183190164549192624475875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99455460109699461749650583 149183190164549192624475875)
            ·
              refine ⟨223774785246823788936713813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149183190164549192624475875 223774785246823788936713813)
              ·
                refine ⟨2622360764611216276602115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 223774785246823788936713813 2622360764611216276602115)
                ·
                  refine ⟨3933541146916824414903173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2622360764611216276602115 3933541146916824414903173)
                  ·
                    refine ⟨737538965046904577794345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933541146916824414903173 737538965046904577794345)
                    ·
                      refine ⟨553154223785178433345759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737538965046904577794345 553154223785178433345759)
                      ·
                        rfl

theorem cell23_1077264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 4, 2].length) (baseStart_1077264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077264 prefixEnd_1077264 := by exact prefixLift 1077264
  have htrace : WordTrace (prefixWord ++ tailWord_1077264) baseStart_1077264 baseEnd_1077264 := by
    simpa [prefixWord, tailWord_1077264, baseEnd_1077264] using wordTrace_append hprefix tailTrace_1077264
  have hstable : (prefixWord ++ tailWord_1077264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077264).length < 2 ^ (prefixWord ++ tailWord_1077264).sum := by decide
  have hdescent : baseEnd_1077264 < baseStart_1077264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077267 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5]
def baseStart_1077267 : Nat := 118140960795 + 1077267 * 2 ^ 59
def prefixEnd_1077267 : Nat := 4983230072969 + 3 ^ 40 * 1077267 * 2
def baseEnd_1077267 : Nat := 553155764227141921608245

theorem tailTrace_1077267 : CollatzResearch.WordTrace tailWord_1077267 prefixEnd_1077267 553155764227141921608245 := by
  unfold tailWord_1077267
  simp only [CollatzResearch.WordTrace]
  refine ⟨39291155388253116401110055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26194103592168744267406703 39291155388253116401110055)
  ·
    refine ⟨58936733082379674601665083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39291155388253116401110055 58936733082379674601665083)
    ·
      refine ⟨88405099623569511902497625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58936733082379674601665083 88405099623569511902497625)
      ·
        refine ⟨66303824717677133926873219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88405099623569511902497625 66303824717677133926873219)
        ·
          refine ⟨99455737076515700890309829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66303824717677133926873219 99455737076515700890309829)
          ·
            refine ⟨18647950701846693916933093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99455737076515700890309829 18647950701846693916933093)
            ·
              refine ⟨3496490756596255109424955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18647950701846693916933093 3496490756596255109424955)
              ·
                refine ⟨5244736134894382664137433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496490756596255109424955 5244736134894382664137433)
                ·
                  refine ⟨3933552101170786998103075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5244736134894382664137433 3933552101170786998103075)
                  ·
                    refine ⟨5900328151756180497154613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3933552101170786998103075 5900328151756180497154613)
                    ·
                      refine ⟨553155764227141921608245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5900328151756180497154613 553155764227141921608245)
                      ·
                        rfl

theorem cell23_1077267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_1077267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077267 prefixEnd_1077267 := by exact prefixLift 1077267
  have htrace : WordTrace (prefixWord ++ tailWord_1077267) baseStart_1077267 baseEnd_1077267 := by
    simpa [prefixWord, tailWord_1077267, baseEnd_1077267] using wordTrace_append hprefix tailTrace_1077267
  have hstable : (prefixWord ++ tailWord_1077267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077267).length < 2 ^ (prefixWord ++ tailWord_1077267).sum := by decide
  have hdescent : baseEnd_1077267 < baseStart_1077267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077294 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1077294 : Nat := 118140960795 + 1077294 * 2 ^ 59
def prefixEnd_1077294 : Nat := 4983230072969 + 3 ^ 40 * 1077294 * 2
def baseEnd_1077294 : Nat := 553169628204813315970621

theorem tailTrace_1077294 : CollatzResearch.WordTrace tailWord_1077294 prefixEnd_1077294 553169628204813315970621 := by
  unfold tailWord_1077294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4911517519894412501542867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26194760106103533341561957 4911517519894412501542867)
  ·
    refine ⟨7367276279841618752314301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4911517519894412501542867 7367276279841618752314301)
    ·
      refine ⟨2762728604940607032117863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7367276279841618752314301 2762728604940607032117863)
      ·
        refine ⟨4144092907410910548176795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762728604940607032117863 4144092907410910548176795)
        ·
          refine ⟨6216139361116365822265193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144092907410910548176795 6216139361116365822265193)
          ·
            refine ⟨4662104520837274366698895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6216139361116365822265193 4662104520837274366698895)
            ·
              refine ⟨6993156781255911550048343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4662104520837274366698895 6993156781255911550048343)
              ·
                refine ⟨10489735171883867325072515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6993156781255911550048343 10489735171883867325072515)
                ·
                  refine ⟨15734602757825800987608773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10489735171883867325072515 15734602757825800987608773)
                  ·
                    refine ⟨2950238017092337685176645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15734602757825800987608773 2950238017092337685176645)
                    ·
                      refine ⟨553169628204813315970621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2950238017092337685176645 553169628204813315970621)
                      ·
                        rfl

theorem cell23_1077294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1077294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077294 prefixEnd_1077294 := by exact prefixLift 1077294
  have htrace : WordTrace (prefixWord ++ tailWord_1077294) baseStart_1077294 baseEnd_1077294 := by
    simpa [prefixWord, tailWord_1077294, baseEnd_1077294] using wordTrace_append hprefix tailTrace_1077294
  have hstable : (prefixWord ++ tailWord_1077294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077294).length < 2 ^ (prefixWord ++ tailWord_1077294).sum := by decide
  have hdescent : baseEnd_1077294 < baseStart_1077294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077298 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_1077298 : Nat := 118140960795 + 1077298 * 2 ^ 59
def prefixEnd_1077298 : Nat := 4983230072969 + 3 ^ 40 * 1077298 * 2
def baseEnd_1077298 : Nat := 553171682127431300320603

theorem tailTrace_1077298 : CollatzResearch.WordTrace tailWord_1077298 prefixEnd_1077298 553171682127431300320603 := by
  unfold tailWord_1077298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9823071512785202173872137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26194857367427205796992365 9823071512785202173872137)
  ·
    refine ⟨7367303634588901630404103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9823071512785202173872137 7367303634588901630404103)
    ·
      refine ⟨11050955451883352445606155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7367303634588901630404103 11050955451883352445606155)
      ·
        refine ⟨16576433177825028668409233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11050955451883352445606155 16576433177825028668409233)
        ·
          refine ⟨12432324883368771501306925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16576433177825028668409233 12432324883368771501306925)
          ·
            refine ⟨4662121831263289312990097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12432324883368771501306925 4662121831263289312990097)
            ·
              refine ⟨3496591373447466984742573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4662121831263289312990097 3496591373447466984742573)
              ·
                refine ⟨1311221765042800119278465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3496591373447466984742573 1311221765042800119278465)
                ·
                  refine ⟨983416323782100089458849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1311221765042800119278465 983416323782100089458849)
                  ·
                    refine ⟨737562242836575067094137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 983416323782100089458849 737562242836575067094137)
                    ·
                      refine ⟨553171682127431300320603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737562242836575067094137 553171682127431300320603)
                      ·
                        rfl

theorem cell23_1077298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_1077298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077298 prefixEnd_1077298 := by exact prefixLift 1077298
  have htrace : WordTrace (prefixWord ++ tailWord_1077298) baseStart_1077298 baseEnd_1077298 := by
    simpa [prefixWord, tailWord_1077298, baseEnd_1077298] using wordTrace_append hprefix tailTrace_1077298
  have hstable : (prefixWord ++ tailWord_1077298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077298).length < 2 ^ (prefixWord ++ tailWord_1077298).sum := by decide
  have hdescent : baseEnd_1077298 < baseStart_1077298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077304 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 7]
def baseStart_1077304 : Nat := 118140960795 + 1077304 * 2 ^ 59
def prefixEnd_1077304 : Nat := 4983230072969 + 3 ^ 40 * 1077304 * 2
def baseEnd_1077304 : Nat := 61463862556817586316175

theorem tailTrace_1077304 : CollatzResearch.WordTrace tailWord_1077304 prefixEnd_1077304 61463862556817586316175 := by
  unfold tailWord_1077304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19646252444559535860103483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26195003259412714480137977 19646252444559535860103483)
  ·
    refine ⟨29469378666839303790155225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19646252444559535860103483 29469378666839303790155225)
    ·
      refine ⟨22102034000129477842616419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29469378666839303790155225 22102034000129477842616419)
      ·
        refine ⟨33153051000194216763924629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22102034000129477842616419 33153051000194216763924629)
        ·
          refine ⟨1554049265634103910808967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33153051000194216763924629 1554049265634103910808967)
          ·
            refine ⟨2331073898451155866213451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554049265634103910808967 2331073898451155866213451)
            ·
              refine ⟨3496610847676733799320177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331073898451155866213451 3496610847676733799320177)
              ·
                refine ⟨2622458135757550349490133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3496610847676733799320177 2622458135757550349490133)
                ·
                  refine ⟨61463862556817586316175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2622458135757550349490133 61463862556817586316175)
                  ·
                    rfl

theorem cell23_1077304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 7].length) (baseStart_1077304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077304 prefixEnd_1077304 := by exact prefixLift 1077304
  have htrace : WordTrace (prefixWord ++ tailWord_1077304) baseStart_1077304 baseEnd_1077304 := by
    simpa [prefixWord, tailWord_1077304, baseEnd_1077304] using wordTrace_append hprefix tailTrace_1077304
  have hstable : (prefixWord ++ tailWord_1077304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077304).length < 2 ^ (prefixWord ++ tailWord_1077304).sum := by decide
  have hdescent : baseEnd_1077304 < baseStart_1077304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077394 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 8]
def baseStart_1077394 : Nat := 118140960795 + 1077394 * 2 ^ 59
def prefixEnd_1077394 : Nat := 4983230072969 + 3 ^ 40 * 1077394 * 2
def baseEnd_1077394 : Nat := 61468997363362547191129

theorem tailTrace_1077394 : CollatzResearch.WordTrace tailWord_1077394 prefixEnd_1077394 61468997363362547191129 := by
  unfold tailWord_1077394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9823946864698254272745809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26197191639195344727322157 9823946864698254272745809)
  ·
    refine ⟨7367960148523690704559357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9823946864698254272745809 7367960148523690704559357)
    ·
      refine ⟨2762985055696384014209759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7367960148523690704559357 2762985055696384014209759)
      ·
        refine ⟨4144477583544576021314639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762985055696384014209759 4144477583544576021314639)
        ·
          refine ⟨6216716375316864031971959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144477583544576021314639 6216716375316864031971959)
          ·
            refine ⟨9325074562975296047957939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216716375316864031971959 9325074562975296047957939)
            ·
              refine ⟨13987611844462944071936909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9325074562975296047957939 13987611844462944071936909)
              ·
                refine ⟨5245354441673604026976341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13987611844462944071936909 5245354441673604026976341)
                ·
                  refine ⟨61468997363362547191129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5245354441673604026976341 61468997363362547191129)
                  ·
                    rfl

theorem cell23_1077394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_1077394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077394 prefixEnd_1077394 := by exact prefixLift 1077394
  have htrace : WordTrace (prefixWord ++ tailWord_1077394) baseStart_1077394 baseEnd_1077394 := by
    simpa [prefixWord, tailWord_1077394, baseEnd_1077394] using wordTrace_append hprefix tailTrace_1077394
  have hstable : (prefixWord ++ tailWord_1077394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077394).length < 2 ^ (prefixWord ++ tailWord_1077394).sum := by decide
  have hdescent : baseEnd_1077394 < baseStart_1077394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077498 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_1077498 : Nat := 118140960795 + 1077498 * 2 ^ 59
def prefixEnd_1077498 : Nat := 4983230072969 + 3 ^ 40 * 1077498 * 2
def baseEnd_1077498 : Nat := 553274378258330517819683

theorem tailTrace_1077498 : CollatzResearch.WordTrace tailWord_1077498 prefixEnd_1077498 553274378258330517819683 := by
  unfold tailWord_1077498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824895162604060713192287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26199720433610828568512765 9824895162604060713192287)
  ·
    refine ⟨14737342743906091069788431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9824895162604060713192287 14737342743906091069788431)
    ·
      refine ⟨22106014115859136604682647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14737342743906091069788431 22106014115859136604682647)
      ·
        refine ⟨33159021173788704907023971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22106014115859136604682647 33159021173788704907023971)
        ·
          refine ⟨49738531760683057360535957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33159021173788704907023971 49738531760683057360535957)
          ·
            refine ⟨2331493676282018313775123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49738531760683057360535957 2331493676282018313775123)
            ·
              refine ⟨3497240514423027470662685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331493676282018313775123 3497240514423027470662685)
              ·
                refine ⟨1311465192908635301498507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3497240514423027470662685 1311465192908635301498507)
                ·
                  refine ⟨1967197789362952952247761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311465192908635301498507 1967197789362952952247761)
                  ·
                    refine ⟨1475398342022214714185821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967197789362952952247761 1475398342022214714185821)
                    ·
                      refine ⟨553274378258330517819683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1475398342022214714185821 553274378258330517819683)
                      ·
                        rfl

theorem cell23_1077498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_1077498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077498 prefixEnd_1077498 := by exact prefixLift 1077498
  have htrace : WordTrace (prefixWord ++ tailWord_1077498) baseStart_1077498 baseEnd_1077498 := by
    simpa [prefixWord, tailWord_1077498, baseEnd_1077498] using wordTrace_append hprefix tailTrace_1077498
  have hstable : (prefixWord ++ tailWord_1077498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077498).length < 2 ^ (prefixWord ++ tailWord_1077498).sum := by decide
  have hdescent : baseEnd_1077498 < baseStart_1077498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077512 : List Nat := [2, 1, 3, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_1077512 : Nat := 118140960795 + 1077512 * 2 ^ 59
def prefixEnd_1077512 : Nat := 4983230072969 + 3 ^ 40 * 1077512 * 2
def baseEnd_1077512 : Nat := 553281566987493463044619

theorem tailTrace_1077512 : CollatzResearch.WordTrace tailWord_1077512 prefixEnd_1077512 553281566987493463044619 := by
  unfold tailWord_1077512
  simp only [CollatzResearch.WordTrace]
  refine ⟨19650045636182761621889395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26200060848243682162519193 19650045636182761621889395)
  ·
    refine ⟨29475068454274142432834093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19650045636182761621889395 29475068454274142432834093)
    ·
      refine ⟨11053150670352803412312785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29475068454274142432834093 11053150670352803412312785)
      ·
        refine ⟨8289863002764602559234589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11053150670352803412312785 8289863002764602559234589)
        ·
          refine ⟨3108698626036725959712971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8289863002764602559234589 3108698626036725959712971)
          ·
            refine ⟨4663047939055088939569457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108698626036725959712971 4663047939055088939569457)
            ·
              refine ⟨3497285954291316704677093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4663047939055088939569457 3497285954291316704677093)
              ·
                refine ⟨655741116429621882126955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3497285954291316704677093 655741116429621882126955)
                ·
                  refine ⟨983611674644432823190433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655741116429621882126955 983611674644432823190433)
                  ·
                    refine ⟨737708755983324617392825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 983611674644432823190433 737708755983324617392825)
                    ·
                      refine ⟨553281566987493463044619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737708755983324617392825 553281566987493463044619)
                      ·
                        rfl

theorem cell23_1077512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_1077512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077512 prefixEnd_1077512 := by exact prefixLift 1077512
  have htrace : WordTrace (prefixWord ++ tailWord_1077512) baseStart_1077512 baseEnd_1077512 := by
    simpa [prefixWord, tailWord_1077512, baseEnd_1077512] using wordTrace_append hprefix tailTrace_1077512
  have hstable : (prefixWord ++ tailWord_1077512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077512).length < 2 ^ (prefixWord ++ tailWord_1077512).sum := by decide
  have hdescent : baseEnd_1077512 < baseStart_1077512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077514 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_1077514 : Nat := 118140960795 + 1077514 * 2 ^ 59
def prefixEnd_1077514 : Nat := 4983230072969 + 3 ^ 40 * 1077514 * 2
def baseEnd_1077514 : Nat := 184427531316267485073203

theorem tailTrace_1077514 : CollatzResearch.WordTrace tailWord_1077514 prefixEnd_1077514 184427531316267485073203 := by
  unfold tailWord_1077514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825041054589569396337899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26200109478905518390234397 9825041054589569396337899)
  ·
    refine ⟨14737561581884354094506849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9825041054589569396337899 14737561581884354094506849)
    ·
      refine ⟨11053171186413265570880137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14737561581884354094506849 11053171186413265570880137)
      ·
        refine ⟨8289878389809949178160103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11053171186413265570880137 8289878389809949178160103)
        ·
          refine ⟨12434817584714923767240155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289878389809949178160103 12434817584714923767240155)
          ·
            refine ⟨18652226377072385650860233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12434817584714923767240155 18652226377072385650860233)
            ·
              refine ⟨13989169782804289238145175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18652226377072385650860233 13989169782804289238145175)
              ·
                refine ⟨20983754674206433857217763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13989169782804289238145175 20983754674206433857217763)
                ·
                  refine ⟨31475632011309650785826645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20983754674206433857217763 31475632011309650785826645)
                  ·
                    refine ⟨184427531316267485073203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31475632011309650785826645 184427531316267485073203)
                    ·
                      rfl

theorem cell23_1077514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_1077514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077514 prefixEnd_1077514 := by exact prefixLift 1077514
  have htrace : WordTrace (prefixWord ++ tailWord_1077514) baseStart_1077514 baseEnd_1077514 := by
    simpa [prefixWord, tailWord_1077514, baseEnd_1077514] using wordTrace_append hprefix tailTrace_1077514
  have hstable : (prefixWord ++ tailWord_1077514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077514).length < 2 ^ (prefixWord ++ tailWord_1077514).sum := by decide
  have hdescent : baseEnd_1077514 < baseStart_1077514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077546 : List Nat := [3, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1077546 : Nat := 118140960795 + 1077546 * 2 ^ 59
def prefixEnd_1077546 : Nat := 4983230072969 + 3 ^ 40 * 1077546 * 2
def baseEnd_1077546 : Nat := 553299025329746330019463

theorem tailTrace_1077546 : CollatzResearch.WordTrace tailWord_1077546 prefixEnd_1077546 553299025329746330019463 := by
  unfold tailWord_1077546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825332838560586762629123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26200887569494898033677661 9825332838560586762629123)
  ·
    refine ⟨14737999257840880143943685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9825332838560586762629123 14737999257840880143943685)
    ·
      refine ⟨2763374860845165026989441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14737999257840880143943685 2763374860845165026989441)
      ·
        refine ⟨2072531145633873770242081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2763374860845165026989441 2072531145633873770242081)
        ·
          refine ⟨1554398359225405327681561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2072531145633873770242081 1554398359225405327681561)
          ·
            refine ⟨1165798769419053995761171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1554398359225405327681561 1165798769419053995761171)
            ·
              refine ⟨1748698154128580993641757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165798769419053995761171 1748698154128580993641757)
              ·
                refine ⟨655761807798217872615659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1748698154128580993641757 655761807798217872615659)
                ·
                  refine ⟨983642711697326808923489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655761807798217872615659 983642711697326808923489)
                  ·
                    refine ⟨737732033772995106692617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 983642711697326808923489 737732033772995106692617)
                    ·
                      refine ⟨553299025329746330019463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737732033772995106692617 553299025329746330019463)
                      ·
                        rfl

theorem cell23_1077546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1077546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077546 prefixEnd_1077546 := by exact prefixLift 1077546
  have htrace : WordTrace (prefixWord ++ tailWord_1077546) baseStart_1077546 baseEnd_1077546 := by
    simpa [prefixWord, tailWord_1077546, baseEnd_1077546] using wordTrace_append hprefix tailTrace_1077546
  have hstable : (prefixWord ++ tailWord_1077546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077546).length < 2 ^ (prefixWord ++ tailWord_1077546).sum := by decide
  have hdescent : baseEnd_1077546 < baseStart_1077546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077589 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_1077589 : Nat := 118140960795 + 1077589 * 2 ^ 59
def prefixEnd_1077589 : Nat := 4983230072969 + 3 ^ 40 * 1077589 * 2
def baseEnd_1077589 : Nat := 553321104997889661781765

theorem tailTrace_1077589 : CollatzResearch.WordTrace tailWord_1077589 prefixEnd_1077589 553321104997889661781765 := by
  unfold tailWord_1077589
  simp only [CollatzResearch.WordTrace]
  refine ⟨39302899693086565394331821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26201933128724376929554547 39302899693086565394331821)
  ·
    refine ⟨14738587384907462022874433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39302899693086565394331821 14738587384907462022874433)
    ·
      refine ⟨11053940538680596517155825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14738587384907462022874433 11053940538680596517155825)
      ·
        refine ⟨8290455404010447387866869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11053940538680596517155825 8290455404010447387866869)
        ·
          refine ⟨777230194125979442612519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8290455404010447387866869 777230194125979442612519)
          ·
            refine ⟨1165845291188969163918779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777230194125979442612519 1165845291188969163918779)
            ·
              refine ⟨1748767936783453745878169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165845291188969163918779 1748767936783453745878169)
              ·
                refine ⟨1311575952587590309408627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1748767936783453745878169 1311575952587590309408627)
                ·
                  refine ⟨1967363928881385464112941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311575952587590309408627 1967363928881385464112941)
                  ·
                    refine ⟨737761473330519549042353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967363928881385464112941 737761473330519549042353)
                    ·
                      refine ⟨553321104997889661781765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737761473330519549042353 553321104997889661781765)
                      ·
                        rfl

theorem cell23_1077589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_1077589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077589 prefixEnd_1077589 := by exact prefixLift 1077589
  have htrace : WordTrace (prefixWord ++ tailWord_1077589) baseStart_1077589 baseEnd_1077589 := by
    simpa [prefixWord, tailWord_1077589, baseEnd_1077589] using wordTrace_append hprefix tailTrace_1077589
  have hstable : (prefixWord ++ tailWord_1077589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077589).length < 2 ^ (prefixWord ++ tailWord_1077589).sum := by decide
  have hdescent : baseEnd_1077589 < baseStart_1077589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077601 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1077601 : Nat := 118140960795 + 1077601 * 2 ^ 59
def prefixEnd_1077601 : Nat := 4983230072969 + 3 ^ 40 * 1077601 * 2
def baseEnd_1077601 : Nat := 553327266765743614831709

theorem tailTrace_1077601 : CollatzResearch.WordTrace tailWord_1077601 prefixEnd_1077601 553327266765743614831709 := by
  unfold tailWord_1077601
  simp only [CollatzResearch.WordTrace]
  refine ⟨39303337369043091443768657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26202224912695394295845771 39303337369043091443768657)
  ·
    refine ⟨29477503026782318582826493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39303337369043091443768657 29477503026782318582826493)
    ·
      refine ⟨11054063635043369468559935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29477503026782318582826493 11054063635043369468559935)
      ·
        refine ⟨16581095452565054202839903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11054063635043369468559935 16581095452565054202839903)
        ·
          refine ⟨24871643178847581304259855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16581095452565054202839903 24871643178847581304259855)
          ·
            refine ⟨37307464768271371956389783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24871643178847581304259855 37307464768271371956389783)
            ·
              refine ⟨55961197152407057934584675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37307464768271371956389783 55961197152407057934584675)
              ·
                refine ⟨83941795728610586901877013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55961197152407057934584675 83941795728610586901877013)
                ·
                  refine ⟨3934771674778621261025485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83941795728610586901877013 3934771674778621261025485)
                  ·
                    refine ⟨1475539378041982972884557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3934771674778621261025485 1475539378041982972884557)
                    ·
                      refine ⟨553327266765743614831709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1475539378041982972884557 553327266765743614831709)
                      ·
                        rfl

theorem cell23_1077601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1077601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077601 prefixEnd_1077601 := by exact prefixLift 1077601
  have htrace : WordTrace (prefixWord ++ tailWord_1077601) baseStart_1077601 baseEnd_1077601 := by
    simpa [prefixWord, tailWord_1077601, baseEnd_1077601] using wordTrace_append hprefix tailTrace_1077601
  have hstable : (prefixWord ++ tailWord_1077601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077601).length < 2 ^ (prefixWord ++ tailWord_1077601).sum := by decide
  have hdescent : baseEnd_1077601 < baseStart_1077601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077658 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1077658 : Nat := 118140960795 + 1077658 * 2 ^ 59
def prefixEnd_1077658 : Nat := 4983230072969 + 3 ^ 40 * 1077658 * 2
def baseEnd_1077658 : Nat := 553356535163049891818947

theorem tailTrace_1077658 : CollatzResearch.WordTrace tailWord_1077658 prefixEnd_1077658 553356535163049891818947 := by
  unfold tailWord_1077658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9826354082459147544648407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26203610886557726785729085 9826354082459147544648407)
  ·
    refine ⟨14739531123688721316972611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9826354082459147544648407 14739531123688721316972611)
    ·
      refine ⟨22109296685533081975458917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14739531123688721316972611 22109296685533081975458917)
      ·
        refine ⟨4145493128537452870398547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22109296685533081975458917 4145493128537452870398547)
        ·
          refine ⟨6218239692806179305597821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145493128537452870398547 6218239692806179305597821)
          ·
            refine ⟨2331839884802317239599183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6218239692806179305597821 2331839884802317239599183)
            ·
              refine ⟨3497759827203475859398775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331839884802317239599183 3497759827203475859398775)
              ·
                refine ⟨5246639740805213789098163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497759827203475859398775 5246639740805213789098163)
                ·
                  refine ⟨7869959611207820683647245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5246639740805213789098163 7869959611207820683647245)
                  ·
                    refine ⟨2951234854202932756367717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7869959611207820683647245 2951234854202932756367717)
                    ·
                      refine ⟨553356535163049891818947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2951234854202932756367717 553356535163049891818947)
                      ·
                        rfl

theorem cell23_1077658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1077658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077658 prefixEnd_1077658 := by exact prefixLift 1077658
  have htrace : WordTrace (prefixWord ++ tailWord_1077658) baseStart_1077658 baseEnd_1077658 := by
    simpa [prefixWord, tailWord_1077658, baseEnd_1077658] using wordTrace_append hprefix tailTrace_1077658
  have hstable : (prefixWord ++ tailWord_1077658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077658).length < 2 ^ (prefixWord ++ tailWord_1077658).sum := by decide
  have hdescent : baseEnd_1077658 < baseStart_1077658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077728 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 1, 5]
def baseStart_1077728 : Nat := 118140960795 + 1077728 * 2 ^ 59
def prefixEnd_1077728 : Nat := 4983230072969 + 3 ^ 40 * 1077728 * 2
def baseEnd_1077728 : Nat := 184464159602954872647875

theorem tailTrace_1077728 : CollatzResearch.WordTrace tailWord_1077728 prefixEnd_1077728 184464159602954872647875 := by
  unfold tailWord_1077728
  simp only [CollatzResearch.WordTrace]
  refine ⟨19653984719791496066820919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26205312959721994755761225 19653984719791496066820919)
  ·
    refine ⟨29480977079687244100231379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19653984719791496066820919 29480977079687244100231379)
    ·
      refine ⟨44221465619530866150347069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29480977079687244100231379 44221465619530866150347069)
      ·
        refine ⟨16583049607324074806380151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44221465619530866150347069 16583049607324074806380151)
        ·
          refine ⟨24874574410986112209570227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16583049607324074806380151 24874574410986112209570227)
          ·
            refine ⟨37311861616479168314355341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24874574410986112209570227 37311861616479168314355341)
            ·
              refine ⟨13991948106179688117883253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37311861616479168314355341 13991948106179688117883253)
              ·
                refine ⟨1311745134954345761051555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13991948106179688117883253 1311745134954345761051555)
                ·
                  refine ⟨1967617702431518641577333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311745134954345761051555 1967617702431518641577333)
                  ·
                    refine ⟨184464159602954872647875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1967617702431518641577333 184464159602954872647875)
                    ·
                      rfl

theorem cell23_1077728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_1077728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077728 prefixEnd_1077728 := by exact prefixLift 1077728
  have htrace : WordTrace (prefixWord ++ tailWord_1077728) baseStart_1077728 baseEnd_1077728 := by
    simpa [prefixWord, tailWord_1077728, baseEnd_1077728] using wordTrace_append hprefix tailTrace_1077728
  have hstable : (prefixWord ++ tailWord_1077728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077728).length < 2 ^ (prefixWord ++ tailWord_1077728).sum := by decide
  have hdescent : baseEnd_1077728 < baseStart_1077728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077742 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1077742 : Nat := 118140960795 + 1077742 * 2 ^ 59
def prefixEnd_1077742 : Nat := 4983230072969 + 3 ^ 40 * 1077742 * 2
def baseEnd_1077742 : Nat := 553399667538027563168561

theorem tailTrace_1077742 : CollatzResearch.WordTrace tailWord_1077742 prefixEnd_1077742 553399667538027563168561 := by
  unfold tailWord_1077742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913560007691534065581435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26205653374354848349767653 4913560007691534065581435)
  ·
    refine ⟨7370340011537301098372153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4913560007691534065581435 7370340011537301098372153)
    ·
      refine ⟨5527755008652975823779115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7370340011537301098372153 5527755008652975823779115)
      ·
        refine ⟨8291632512979463735668673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5527755008652975823779115 8291632512979463735668673)
        ·
          refine ⟨6218724384734597801751505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8291632512979463735668673 6218724384734597801751505)
          ·
            refine ⟨4664043288550948351313629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6218724384734597801751505 4664043288550948351313629)
            ·
              refine ⟨1749016233206605631742611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4664043288550948351313629 1749016233206605631742611)
              ·
                refine ⟨2623524349809908447613917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749016233206605631742611 2623524349809908447613917)
                ·
                  refine ⟨983821631178715667855219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2623524349809908447613917 983821631178715667855219)
                  ·
                    refine ⟨1475732446768073501782829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 983821631178715667855219 1475732446768073501782829)
                    ·
                      refine ⟨553399667538027563168561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1475732446768073501782829 553399667538027563168561)
                      ·
                        rfl

theorem cell23_1077742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1077742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077742 prefixEnd_1077742 := by exact prefixLift 1077742
  have htrace : WordTrace (prefixWord ++ tailWord_1077742) baseStart_1077742 baseEnd_1077742 := by
    simpa [prefixWord, tailWord_1077742, baseEnd_1077742] using wordTrace_append hprefix tailTrace_1077742
  have hstable : (prefixWord ++ tailWord_1077742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077742).length < 2 ^ (prefixWord ++ tailWord_1077742).sum := by decide
  have hdescent : baseEnd_1077742 < baseStart_1077742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077749 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 6]
def baseStart_1077749 : Nat := 118140960795 + 1077749 * 2 ^ 59
def prefixEnd_1077749 : Nat := 4983230072969 + 3 ^ 40 * 1077749 * 2
def baseEnd_1077749 : Nat := 61489251322512115086781

theorem tailTrace_1077749 : CollatzResearch.WordTrace tailWord_1077749 prefixEnd_1077749 61489251322512115086781 := by
  unfold tailWord_1077749
  simp only [CollatzResearch.WordTrace]
  refine ⟨39308735372506912720156301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26205823581671275146770867 39308735372506912720156301)
  ·
    refine ⟨14740775764690092270058613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39308735372506912720156301 14740775764690092270058613)
    ·
      refine ⟨1381947727939696150317995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14740775764690092270058613 1381947727939696150317995)
      ·
        refine ⟨2072921591909544225476993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381947727939696150317995 2072921591909544225476993)
        ·
          refine ⟨1554691193932158169107745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2072921591909544225476993 1554691193932158169107745)
          ·
            refine ⟨1166018395449118626830809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1554691193932158169107745 1166018395449118626830809)
            ·
              refine ⟨874513796586838970123107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166018395449118626830809 874513796586838970123107)
              ·
                refine ⟨1311770694880258455184661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874513796586838970123107 1311770694880258455184661)
                ·
                  refine ⟨61489251322512115086781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1311770694880258455184661 61489251322512115086781)
                  ·
                    rfl

theorem cell23_1077749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_1077749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077749 prefixEnd_1077749 := by exact prefixLift 1077749
  have htrace : WordTrace (prefixWord ++ tailWord_1077749) baseStart_1077749 baseEnd_1077749 := by
    simpa [prefixWord, tailWord_1077749, baseEnd_1077749] using wordTrace_append hprefix tailTrace_1077749
  have hstable : (prefixWord ++ tailWord_1077749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077749).length < 2 ^ (prefixWord ++ tailWord_1077749).sum := by decide
  have hdescent : baseEnd_1077749 < baseStart_1077749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077751 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1077751 : Nat := 118140960795 + 1077751 * 2 ^ 59
def prefixEnd_1077751 : Nat := 4983230072969 + 3 ^ 40 * 1077751 * 2
def baseEnd_1077751 : Nat := 553404288863918027956019

theorem tailTrace_1077751 : CollatzResearch.WordTrace tailWord_1077751 prefixEnd_1077751 553404288863918027956019 := by
  unfold tailWord_1077751
  simp only [CollatzResearch.WordTrace]
  refine ⟨39308808318499667061729107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26205872212333111374486071 39308808318499667061729107)
  ·
    refine ⟨58963212477749500592593661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39308808318499667061729107 58963212477749500592593661)
    ·
      refine ⟨22111204679156062722222623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58963212477749500592593661 22111204679156062722222623)
      ·
        refine ⟨33166807018734094083333935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22111204679156062722222623 33166807018734094083333935)
        ·
          refine ⟨49750210528101141125000903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33166807018734094083333935 49750210528101141125000903)
          ·
            refine ⟨74625315792151711687501355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49750210528101141125000903 74625315792151711687501355)
            ·
              refine ⟨111937973688227567531252033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74625315792151711687501355 111937973688227567531252033)
              ·
                refine ⟨83953480266170675648439025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111937973688227567531252033 83953480266170675648439025)
                ·
                  refine ⟨62965110199628006736329269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83953480266170675648439025 62965110199628006736329269)
                  ·
                    refine ⟨5902979081215125631530869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62965110199628006736329269 5902979081215125631530869)
                    ·
                      refine ⟨553404288863918027956019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5902979081215125631530869 553404288863918027956019)
                      ·
                        rfl

theorem cell23_1077751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1077751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077751 prefixEnd_1077751 := by exact prefixLift 1077751
  have htrace : WordTrace (prefixWord ++ tailWord_1077751) baseStart_1077751 baseEnd_1077751 := by
    simpa [prefixWord, tailWord_1077751, baseEnd_1077751] using wordTrace_append hprefix tailTrace_1077751
  have hstable : (prefixWord ++ tailWord_1077751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077751).length < 2 ^ (prefixWord ++ tailWord_1077751).sum := by decide
  have hdescent : baseEnd_1077751 < baseStart_1077751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077762 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1077762 : Nat := 118140960795 + 1077762 * 2 ^ 59
def prefixEnd_1077762 : Nat := 4983230072969 + 3 ^ 40 * 1077762 * 2
def baseEnd_1077762 : Nat := 184469979050372494972823

theorem tailTrace_1077762 : CollatzResearch.WordTrace tailWord_1077762 prefixEnd_1077762 184469979050372494972823 := by
  unfold tailWord_1077762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9827302380364953985094885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26206139680973210626919693 9827302380364953985094885)
  ·
    refine ⟨1842619196318428872205291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9827302380364953985094885 1842619196318428872205291)
    ·
      refine ⟨2763928794477643308307937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1842619196318428872205291 2763928794477643308307937)
      ·
        refine ⟨2072946595858232481230953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2763928794477643308307937 2072946595858232481230953)
        ·
          refine ⟨1554709946893674360923215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2072946595858232481230953 1554709946893674360923215)
          ·
            refine ⟨2332064920340511541384823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554709946893674360923215 2332064920340511541384823)
            ·
              refine ⟨3498097380510767312077235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332064920340511541384823 3498097380510767312077235)
              ·
                refine ⟨5247146070766150968115853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498097380510767312077235 5247146070766150968115853)
                ·
                  refine ⟨1967679776537306613043445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5247146070766150968115853 1967679776537306613043445)
                  ·
                    refine ⟨184469979050372494972823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1967679776537306613043445 184469979050372494972823)
                    ·
                      rfl

theorem cell23_1077762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1077762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077762 prefixEnd_1077762 := by exact prefixLift 1077762
  have htrace : WordTrace (prefixWord ++ tailWord_1077762) baseStart_1077762 baseEnd_1077762 := by
    simpa [prefixWord, tailWord_1077762, baseEnd_1077762] using wordTrace_append hprefix tailTrace_1077762
  have hstable : (prefixWord ++ tailWord_1077762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077762).length < 2 ^ (prefixWord ++ tailWord_1077762).sum := by decide
  have hdescent : baseEnd_1077762 < baseStart_1077762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077765 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_1077765 : Nat := 118140960795 + 1077765 * 2 ^ 59
def prefixEnd_1077765 : Nat := 4983230072969 + 3 ^ 40 * 1077765 * 2
def baseEnd_1077765 : Nat := 553411477593080973180955

theorem tailTrace_1077765 : CollatzResearch.WordTrace tailWord_1077765 prefixEnd_1077765 553411477593080973180955 := by
  unfold tailWord_1077765
  simp only [CollatzResearch.WordTrace]
  refine ⟨39309318940448947452738749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26206212626965964968492499 39309318940448947452738749)
  ·
    refine ⟨14740994602668355294777031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39309318940448947452738749 14740994602668355294777031)
    ·
      refine ⟨22111491904002532942165547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14740994602668355294777031 22111491904002532942165547)
      ·
        refine ⟨33167237856003799413248321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22111491904002532942165547 33167237856003799413248321)
        ·
          refine ⟨24875428392002849559936241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33167237856003799413248321 24875428392002849559936241)
          ·
            refine ⟨18656571294002137169952181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24875428392002849559936241 18656571294002137169952181)
            ·
              refine ⟨1749053558812700359683017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18656571294002137169952181 1749053558812700359683017)
              ·
                refine ⟨1311790169109525269762263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749053558812700359683017 1311790169109525269762263)
                ·
                  refine ⟨1967685253664287904643395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311790169109525269762263 1967685253664287904643395)
                  ·
                    refine ⟨2951527880496431856965093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1967685253664287904643395 2951527880496431856965093)
                    ·
                      refine ⟨553411477593080973180955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2951527880496431856965093 553411477593080973180955)
                      ·
                        rfl

theorem cell23_1077765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_1077765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077765 prefixEnd_1077765 := by exact prefixLift 1077765
  have htrace : WordTrace (prefixWord ++ tailWord_1077765) baseStart_1077765 baseEnd_1077765 := by
    simpa [prefixWord, tailWord_1077765, baseEnd_1077765] using wordTrace_append hprefix tailTrace_1077765
  have hstable : (prefixWord ++ tailWord_1077765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077765).length < 2 ^ (prefixWord ++ tailWord_1077765).sum := by decide
  have hdescent : baseEnd_1077765 < baseStart_1077765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077815 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_1077815 : Nat := 118140960795 + 1077815 * 2 ^ 59
def prefixEnd_1077815 : Nat := 4983230072969 + 3 ^ 40 * 1077815 * 2
def baseEnd_1077815 : Nat := 553437151625805777555725

theorem tailTrace_1077815 : CollatzResearch.WordTrace tailWord_1077815 prefixEnd_1077815 553437151625805777555725 := by
  unfold tailWord_1077815
  simp only [CollatzResearch.WordTrace]
  refine ⟨39311142590267805992058899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26207428393511870661372599 39311142590267805992058899)
  ·
    refine ⟨58966713885401708988088349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39311142590267805992058899 58966713885401708988088349)
    ·
      refine ⟨22112517707025640870533131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58966713885401708988088349 22112517707025640870533131)
      ·
        refine ⟨33168776560538461305799697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22112517707025640870533131 33168776560538461305799697)
        ·
          refine ⟨24876582420403845979349773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33168776560538461305799697 24876582420403845979349773)
          ·
            refine ⟨9328718407651442242256165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24876582420403845979349773 9328718407651442242256165)
            ·
              refine ⟨1749134701434645420423031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9328718407651442242256165 1749134701434645420423031)
              ·
                refine ⟨2623702052151968130634547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749134701434645420423031 2623702052151968130634547)
                ·
                  refine ⟨3935553078227952195951821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623702052151968130634547 3935553078227952195951821)
                  ·
                    refine ⟨1475832404335482073481933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3935553078227952195951821 1475832404335482073481933)
                    ·
                      refine ⟨553437151625805777555725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1475832404335482073481933 553437151625805777555725)
                      ·
                        rfl

theorem cell23_1077815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_1077815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077815 prefixEnd_1077815 := by exact prefixLift 1077815
  have htrace : WordTrace (prefixWord ++ tailWord_1077815) baseStart_1077815 baseEnd_1077815 := by
    simpa [prefixWord, tailWord_1077815, baseEnd_1077815] using wordTrace_append hprefix tailTrace_1077815
  have hstable : (prefixWord ++ tailWord_1077815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077815).length < 2 ^ (prefixWord ++ tailWord_1077815).sum := by decide
  have hdescent : baseEnd_1077815 < baseStart_1077815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077848 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 2, 6]
def baseStart_1077848 : Nat := 118140960795 + 1077848 * 2 ^ 59
def prefixEnd_1077848 : Nat := 4983230072969 + 3 ^ 40 * 1077848 * 2
def baseEnd_1077848 : Nat := 184484698829134716147691

theorem tailTrace_1077848 : CollatzResearch.WordTrace tailWord_1077848 prefixEnd_1077848 184484698829134716147691 := by
  unfold tailWord_1077848
  simp only [CollatzResearch.WordTrace]
  refine ⟨19656173099574126314005099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26208230799432168418673465 19656173099574126314005099)
  ·
    refine ⟨29484259649361189471007649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19656173099574126314005099 29484259649361189471007649)
    ·
      refine ⟨22113194737020892103255737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29484259649361189471007649 22113194737020892103255737)
      ·
        refine ⟨16584896052765669077441803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22113194737020892103255737 16584896052765669077441803)
        ·
          refine ⟨24877344079148503616162705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16584896052765669077441803 24877344079148503616162705)
          ·
            refine ⟨18658008059361377712122029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24877344079148503616162705 18658008059361377712122029)
            ·
              refine ⟨6996753022260516642045761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18658008059361377712122029 6996753022260516642045761)
              ·
                refine ⟨5247564766695387481534321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6996753022260516642045761 5247564766695387481534321)
                ·
                  refine ⟨3935673575021540611150741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247564766695387481534321 3935673575021540611150741)
                  ·
                    refine ⟨184484698829134716147691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3935673575021540611150741 184484698829134716147691)
                    ·
                      rfl

theorem cell23_1077848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_1077848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077848 prefixEnd_1077848 := by exact prefixLift 1077848
  have htrace : WordTrace (prefixWord ++ tailWord_1077848) baseStart_1077848 baseEnd_1077848 := by
    simpa [prefixWord, tailWord_1077848, baseEnd_1077848] using wordTrace_append hprefix tailTrace_1077848
  have hstable : (prefixWord ++ tailWord_1077848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077848).length < 2 ^ (prefixWord ++ tailWord_1077848).sum := by decide
  have hdescent : baseEnd_1077848 < baseStart_1077848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077855 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 3, 4, 2]
def baseStart_1077855 : Nat := 118140960795 + 1077855 * 2 ^ 59
def prefixEnd_1077855 : Nat := 4983230072969 + 3 ^ 40 * 1077855 * 2
def baseEnd_1077855 : Nat := 553457690851985621055541

theorem tailTrace_1077855 : CollatzResearch.WordTrace tailWord_1077855 prefixEnd_1077855 553457690851985621055541 := by
  unfold tailWord_1077855
  simp only [CollatzResearch.WordTrace]
  refine ⟨39312601510122892823515019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26208401006748595215676679 39312601510122892823515019)
  ·
    refine ⟨58968902265184339235272529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39312601510122892823515019 58968902265184339235272529)
    ·
      refine ⟨44226676698888254426454397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58968902265184339235272529 44226676698888254426454397)
      ·
        refine ⟨16585003762083095409920399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44226676698888254426454397 16585003762083095409920399)
        ·
          refine ⟨24877505643124643114880599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16585003762083095409920399 24877505643124643114880599)
          ·
            refine ⟨37316258464686964672320899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24877505643124643114880599 37316258464686964672320899)
            ·
              refine ⟨55974387697030447008481349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37316258464686964672320899 55974387697030447008481349)
              ·
                refine ⟨10495197693193208814090253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55974387697030447008481349 10495197693193208814090253)
                ·
                  refine ⟨3935699134947453305283845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10495197693193208814090253 3935699134947453305283845)
                  ·
                    refine ⟨737943587802647494740721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3935699134947453305283845 737943587802647494740721)
                    ·
                      refine ⟨553457690851985621055541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737943587802647494740721 553457690851985621055541)
                      ·
                        rfl

theorem cell23_1077855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_1077855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077855 prefixEnd_1077855 := by exact prefixLift 1077855
  have htrace : WordTrace (prefixWord ++ tailWord_1077855) baseStart_1077855 baseEnd_1077855 := by
    simpa [prefixWord, tailWord_1077855, baseEnd_1077855] using wordTrace_append hprefix tailTrace_1077855
  have hstable : (prefixWord ++ tailWord_1077855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077855).length < 2 ^ (prefixWord ++ tailWord_1077855).sum := by decide
  have hdescent : baseEnd_1077855 < baseStart_1077855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077915 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 6, 5, 2]
def baseStart_1077915 : Nat := 118140960795 + 1077915 * 2 ^ 59
def prefixEnd_1077915 : Nat := 4983230072969 + 3 ^ 40 * 1077915 * 2
def baseEnd_1077915 : Nat := 553488499691255386305265

theorem tailTrace_1077915 : CollatzResearch.WordTrace tailWord_1077915 prefixEnd_1077915 553488499691255386305265 := by
  unfold tailWord_1077915
  simp only [CollatzResearch.WordTrace]
  refine ⟨39314789889905523070699199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26209859926603682047132799 39314789889905523070699199)
  ·
    refine ⟨58972184834858284606048799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39314789889905523070699199 58972184834858284606048799)
    ·
      refine ⟨88458277252287426909073199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58972184834858284606048799 88458277252287426909073199)
      ·
        refine ⟨132687415878431140363609799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88458277252287426909073199 132687415878431140363609799)
        ·
          refine ⟨199031123817646710545414699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132687415878431140363609799 199031123817646710545414699)
          ·
            refine ⟨298546685726470065818122049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199031123817646710545414699 298546685726470065818122049)
            ·
              refine ⟨223910014294852549363591537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298546685726470065818122049 223910014294852549363591537)
              ·
                refine ⟨167932510721139412022693653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223910014294852549363591537 167932510721139412022693653)
                ·
                  refine ⟨7871836440053409938563765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 167932510721139412022693653 7871836440053409938563765)
                  ·
                    refine ⟨737984666255007181740353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7871836440053409938563765 737984666255007181740353)
                    ·
                      refine ⟨553488499691255386305265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 737984666255007181740353 553488499691255386305265)
                      ·
                        rfl

theorem cell23_1077915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5, 2].length) (baseStart_1077915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077915 prefixEnd_1077915 := by exact prefixLift 1077915
  have htrace : WordTrace (prefixWord ++ tailWord_1077915) baseStart_1077915 baseEnd_1077915 := by
    simpa [prefixWord, tailWord_1077915, baseEnd_1077915] using wordTrace_append hprefix tailTrace_1077915
  have hstable : (prefixWord ++ tailWord_1077915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077915).length < 2 ^ (prefixWord ++ tailWord_1077915).sum := by decide
  have hdescent : baseEnd_1077915 < baseStart_1077915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077962 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1077962 : Nat := 118140960795 + 1077962 * 2 ^ 59
def prefixEnd_1077962 : Nat := 4983230072969 + 3 ^ 40 * 1077962 * 2
def baseEnd_1077962 : Nat := 553512633282016702417549

theorem tailTrace_1077962 : CollatzResearch.WordTrace tailWord_1077962 prefixEnd_1077962 553512633282016702417549 := by
  unfold tailWord_1077962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9829126030183812524415035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26211002747156833398440093 9829126030183812524415035)
  ·
    refine ⟨14743689045275718786622553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9829126030183812524415035 14743689045275718786622553)
    ·
      refine ⟨11057766783956789089966915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14743689045275718786622553 11057766783956789089966915)
      ·
        refine ⟨16586650175935183634950373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11057766783956789089966915 16586650175935183634950373)
        ·
          refine ⟨3109996907987846931553195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16586650175935183634950373 3109996907987846931553195)
          ·
            refine ⟨4664995361981770397329793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3109996907987846931553195 4664995361981770397329793)
            ·
              refine ⟨3498746521486327797997345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4664995361981770397329793 3498746521486327797997345)
              ·
                refine ⟨2624059891114745848498009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3498746521486327797997345 2624059891114745848498009)
                ·
                  refine ⟨1968044918336059386373507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624059891114745848498009 1968044918336059386373507)
                  ·
                    refine ⟨2952067377504089079560261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1968044918336059386373507 2952067377504089079560261)
                    ·
                      refine ⟨553512633282016702417549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2952067377504089079560261 553512633282016702417549)
                      ·
                        rfl

theorem cell23_1077962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1077962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077962 prefixEnd_1077962 := by exact prefixLift 1077962
  have htrace : WordTrace (prefixWord ++ tailWord_1077962) baseStart_1077962 baseEnd_1077962 := by
    simpa [prefixWord, tailWord_1077962, baseEnd_1077962] using wordTrace_append hprefix tailTrace_1077962
  have hstable : (prefixWord ++ tailWord_1077962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077962).length < 2 ^ (prefixWord ++ tailWord_1077962).sum := by decide
  have hdescent : baseEnd_1077962 < baseStart_1077962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077968 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 12]
def baseStart_1077968 : Nat := 118140960795 + 1077968 * 2 ^ 59
def prefixEnd_1077968 : Nat := 4983230072969 + 3 ^ 40 * 1077968 * 2
def baseEnd_1077968 : Nat := 61501746018438186549169

theorem tailTrace_1077968 : CollatzResearch.WordTrace tailWord_1077968 prefixEnd_1077968 61501746018438186549169 := by
  unfold tailWord_1077968
  simp only [CollatzResearch.WordTrace]
  refine ⟨19658361479356756561189279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26211148639142342081585705 19658361479356756561189279)
  ·
    refine ⟨29487542219035134841783919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19658361479356756561189279 29487542219035134841783919)
    ·
      refine ⟨44231313328552702262675879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29487542219035134841783919 44231313328552702262675879)
      ·
        refine ⟨66346969992829053394013819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44231313328552702262675879 66346969992829053394013819)
        ·
          refine ⟨99520454989243580091020729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66346969992829053394013819 99520454989243580091020729)
          ·
            refine ⟨74640341241932685068265547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99520454989243580091020729 74640341241932685068265547)
            ·
              refine ⟨111960511862899027602398321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74640341241932685068265547 111960511862899027602398321)
              ·
                refine ⟨83970383897174270701798741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111960511862899027602398321 83970383897174270701798741)
                ·
                  refine ⟨61501746018438186549169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 83970383897174270701798741 61501746018438186549169)
                  ·
                    rfl

theorem cell23_1077968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_1077968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077968 prefixEnd_1077968 := by exact prefixLift 1077968
  have htrace : WordTrace (prefixWord ++ tailWord_1077968) baseStart_1077968 baseEnd_1077968 := by
    simpa [prefixWord, tailWord_1077968, baseEnd_1077968] using wordTrace_append hprefix tailTrace_1077968
  have hstable : (prefixWord ++ tailWord_1077968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077968).length < 2 ^ (prefixWord ++ tailWord_1077968).sum := by decide
  have hdescent : baseEnd_1077968 < baseStart_1077968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077999 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 3]
def baseStart_1077999 : Nat := 118140960795 + 1077999 * 2 ^ 59
def prefixEnd_1077999 : Nat := 4983230072969 + 3 ^ 40 * 1077999 * 2
def baseEnd_1077999 : Nat := 553531632066233057654879

theorem tailTrace_1077999 : CollatzResearch.WordTrace tailWord_1077999 prefixEnd_1077999 553531632066233057654879 := by
  unfold tailWord_1077999
  simp only [CollatzResearch.WordTrace]
  refine ⟨39317853621601205416757051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26211902414400803611171367 39317853621601205416757051)
  ·
    refine ⟨58976780432401808125135577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39317853621601205416757051 58976780432401808125135577)
    ·
      refine ⟨44232585324301356093851683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58976780432401808125135577 44232585324301356093851683)
      ·
        refine ⟨66348877986452034140777525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44232585324301356093851683 66348877986452034140777525)
        ·
          refine ⟨6220207311229878200697893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66348877986452034140777525 6220207311229878200697893)
          ·
            refine ⟨1166288870855602162630855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6220207311229878200697893 1166288870855602162630855)
            ·
              refine ⟨1749433306283403243946283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166288870855602162630855 1749433306283403243946283)
              ·
                refine ⟨2624149959425104865919425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749433306283403243946283 2624149959425104865919425)
                ·
                  refine ⟨1968112469568828649439569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624149959425104865919425 1968112469568828649439569)
                  ·
                    refine ⟨1476084352176621487079677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1968112469568828649439569 1476084352176621487079677)
                    ·
                      refine ⟨553531632066233057654879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476084352176621487079677 553531632066233057654879)
                      ·
                        rfl

theorem cell23_1077999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_1077999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1077999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1077999 prefixEnd_1077999 := by exact prefixLift 1077999
  have htrace : WordTrace (prefixWord ++ tailWord_1077999) baseStart_1077999 baseEnd_1077999 := by
    simpa [prefixWord, tailWord_1077999, baseEnd_1077999] using wordTrace_append hprefix tailTrace_1077999
  have hstable : (prefixWord ++ tailWord_1077999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077999).length < 2 ^ (prefixWord ++ tailWord_1077999).sum := by decide
  have hdescent : baseEnd_1077999 < baseStart_1077999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078006 : List Nat := [5, 1, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1078006 : Nat := 118140960795 + 1078006 * 2 ^ 59
def prefixEnd_1078006 : Nat := 4983230072969 + 3 ^ 40 * 1078006 * 2
def baseEnd_1078006 : Nat := 184511742143604843422449

theorem tailTrace_1078006 : CollatzResearch.WordTrace tailWord_1078006 prefixEnd_1078006 184511742143604843422449 := by
  unfold tailWord_1078006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457381808285990350766367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26212072621717230408174581 2457381808285990350766367)
  ·
    refine ⟨3686072712428985526149551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2457381808285990350766367 3686072712428985526149551)
    ·
      refine ⟨5529109068643478289224327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3686072712428985526149551 5529109068643478289224327)
      ·
        refine ⟨8293663602965217433836491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5529109068643478289224327 8293663602965217433836491)
        ·
          refine ⟨12440495404447826150754737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8293663602965217433836491 12440495404447826150754737)
          ·
            refine ⟨9330371553335869613066053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12440495404447826150754737 9330371553335869613066053)
            ·
              refine ⟨1749444666250475552449885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9330371553335869613066053 1749444666250475552449885)
              ·
                refine ⟨656041749843928332168707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1749444666250475552449885 656041749843928332168707)
                ·
                  refine ⟨984062624765892498253061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656041749843928332168707 984062624765892498253061)
                  ·
                    refine ⟨184511742143604843422449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 984062624765892498253061 184511742143604843422449)
                    ·
                      rfl

theorem cell23_1078006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1078006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078006 prefixEnd_1078006 := by exact prefixLift 1078006
  have htrace : WordTrace (prefixWord ++ tailWord_1078006) baseStart_1078006 baseEnd_1078006 := by
    simpa [prefixWord, tailWord_1078006, baseEnd_1078006] using wordTrace_append hprefix tailTrace_1078006
  have hstable : (prefixWord ++ tailWord_1078006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078006).length < 2 ^ (prefixWord ++ tailWord_1078006).sum := by decide
  have hdescent : baseEnd_1078006 < baseStart_1078006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078069 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_1078069 : Nat := 118140960795 + 1078069 * 2 ^ 59
def prefixEnd_1078069 : Nat := 4983230072969 + 3 ^ 40 * 1078069 * 2
def baseEnd_1078069 : Nat := 553567575712047783779557

theorem tailTrace_1078069 : CollatzResearch.WordTrace tailWord_1078069 prefixEnd_1078069 553567575712047783779557 := by
  unfold tailWord_1078069
  simp only [CollatzResearch.WordTrace]
  refine ⟨39320406731347607371805261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26213604487565071581203507 39320406731347607371805261)
  ·
    refine ⟨14745152524255352764426973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39320406731347607371805261 14745152524255352764426973)
    ·
      refine ⟨5529432196595757286660115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14745152524255352764426973 5529432196595757286660115)
      ·
        refine ⟨8294148294893635929990173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5529432196595757286660115 8294148294893635929990173)
        ·
          refine ⟨3110305610585113473746315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8294148294893635929990173 3110305610585113473746315)
          ·
            refine ⟨4665458415877670210619473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110305610585113473746315 4665458415877670210619473)
            ·
              refine ⟨3499093811908252657964605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4665458415877670210619473 3499093811908252657964605)
              ·
                refine ⟨1312160179465594746736727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3499093811908252657964605 1312160179465594746736727)
                ·
                  refine ⟨1968240269198392120105091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312160179465594746736727 1968240269198392120105091)
                  ·
                    refine ⟨2952360403797588180157637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1968240269198392120105091 2952360403797588180157637)
                    ·
                      refine ⟨553567575712047783779557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2952360403797588180157637 553567575712047783779557)
                      ·
                        rfl

theorem cell23_1078069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_1078069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078069 prefixEnd_1078069 := by exact prefixLift 1078069
  have htrace : WordTrace (prefixWord ++ tailWord_1078069) baseStart_1078069 baseEnd_1078069 := by
    simpa [prefixWord, tailWord_1078069, baseEnd_1078069] using wordTrace_append hprefix tailTrace_1078069
  have hstable : (prefixWord ++ tailWord_1078069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078069).length < 2 ^ (prefixWord ++ tailWord_1078069).sum := by decide
  have hdescent : baseEnd_1078069 < baseStart_1078069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078072 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_1078072 : Nat := 118140960795 + 1078072 * 2 ^ 59
def prefixEnd_1078072 : Nat := 4983230072969 + 3 ^ 40 * 1078072 * 2
def baseEnd_1078072 : Nat := 553569116154011272042043

theorem tailTrace_1078072 : CollatzResearch.WordTrace tailWord_1078072 prefixEnd_1078072 553569116154011272042043 := by
  unfold tailWord_1078072
  simp only [CollatzResearch.WordTrace]
  refine ⟨19660258075168369442082235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26213677433557825922776313 19660258075168369442082235)
  ·
    refine ⟨29490387112752554163123353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19660258075168369442082235 29490387112752554163123353)
    ·
      refine ⟨22117790334564415622342515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29490387112752554163123353 22117790334564415622342515)
      ·
        refine ⟨33176685501846623433513773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22117790334564415622342515 33176685501846623433513773)
        ·
          refine ⟨12441257063192483787567665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33176685501846623433513773 12441257063192483787567665)
          ·
            refine ⟨9330942797394362840675749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12441257063192483787567665 9330942797394362840675749)
            ·
              refine ⟨1749551774511443032626703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9330942797394362840675749 1749551774511443032626703)
              ·
                refine ⟨2624327661767164548940055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749551774511443032626703 2624327661767164548940055)
                ·
                  refine ⟨3936491492650746823410083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624327661767164548940055 3936491492650746823410083)
                  ·
                    refine ⟨5904737238976120235115125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3936491492650746823410083 5904737238976120235115125)
                    ·
                      refine ⟨553569116154011272042043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5904737238976120235115125 553569116154011272042043)
                      ·
                        rfl

theorem cell23_1078072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_1078072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078072 prefixEnd_1078072 := by exact prefixLift 1078072
  have htrace : WordTrace (prefixWord ++ tailWord_1078072) baseStart_1078072 baseEnd_1078072 := by
    simpa [prefixWord, tailWord_1078072, baseEnd_1078072] using wordTrace_append hprefix tailTrace_1078072
  have hstable : (prefixWord ++ tailWord_1078072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078072).length < 2 ^ (prefixWord ++ tailWord_1078072).sum := by decide
  have hdescent : baseEnd_1078072 < baseStart_1078072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078092 : List Nat := [2, 2, 1, 3, 3, 2, 2, 8]
def baseStart_1078092 : Nat := 118140960795 + 1078092 * 2 ^ 59
def prefixEnd_1078092 : Nat := 4983230072969 + 3 ^ 40 * 1078092 * 2
def baseEnd_1078092 : Nat := 20502940213596340510813

theorem tailTrace_1078092 : CollatzResearch.WordTrace tailWord_1078092 prefixEnd_1078092 20502940213596340510813 := by
  unfold tailWord_1078092
  simp only [CollatzResearch.WordTrace]
  refine ⟨19660622805132141149946265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26214163740176188199928353 19660622805132141149946265)
  ·
    refine ⟨14745467103849105862459699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19660622805132141149946265 14745467103849105862459699)
    ·
      refine ⟨22118200655773658793689549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14745467103849105862459699 22118200655773658793689549)
      ·
        refine ⟨8294325245915122047633581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22118200655773658793689549 8294325245915122047633581)
        ·
          refine ⟨3110371967218170767862593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8294325245915122047633581 3110371967218170767862593)
          ·
            refine ⟨2332778975413628075896945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3110371967218170767862593 2332778975413628075896945)
            ·
              refine ⟨1749584231560221056922709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2332778975413628075896945 1749584231560221056922709)
              ·
                refine ⟨20502940213596340510813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1749584231560221056922709 20502940213596340510813)
                ·
                  rfl

theorem cell23_1078092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 8].length) (baseStart_1078092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078092 prefixEnd_1078092 := by exact prefixLift 1078092
  have htrace : WordTrace (prefixWord ++ tailWord_1078092) baseStart_1078092 baseEnd_1078092 := by
    simpa [prefixWord, tailWord_1078092, baseEnd_1078092] using wordTrace_append hprefix tailTrace_1078092
  have hstable : (prefixWord ++ tailWord_1078092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078092).length < 2 ^ (prefixWord ++ tailWord_1078092).sum := by decide
  have hdescent : baseEnd_1078092 < baseStart_1078092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078106 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_1078106 : Nat := 118140960795 + 1078106 * 2 ^ 59
def prefixEnd_1078106 : Nat := 4983230072969 + 3 ^ 40 * 1078106 * 2
def baseEnd_1078106 : Nat := 553586574496264139016887

theorem tailTrace_1078106 : CollatzResearch.WordTrace tailWord_1078106 prefixEnd_1078106 553586574496264139016887 := by
  unfold tailWord_1078106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9830439058053390672725543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26214504154809041793934781 9830439058053390672725543)
  ·
    refine ⟨14745658587080086009088315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9830439058053390672725543 14745658587080086009088315)
    ·
      refine ⟨22118487880620129013632473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14745658587080086009088315 22118487880620129013632473)
      ·
        refine ⟨16588865910465096760224355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22118487880620129013632473 16588865910465096760224355)
        ·
          refine ⟨24883298865697645140336533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16588865910465096760224355 24883298865697645140336533)
          ·
            refine ⟨1166404634329577115953275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24883298865697645140336533 1166404634329577115953275)
            ·
              refine ⟨1749606951494365673929913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166404634329577115953275 1749606951494365673929913)
              ·
                refine ⟨1312205213620774255447435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749606951494365673929913 1312205213620774255447435)
                ·
                  refine ⟨1968307820431161383171153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312205213620774255447435 1968307820431161383171153)
                  ·
                    refine ⟨1476230865323371037378365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1968307820431161383171153 1476230865323371037378365)
                    ·
                      refine ⟨553586574496264139016887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476230865323371037378365 553586574496264139016887)
                      ·
                        rfl

theorem cell23_1078106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_1078106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078106 prefixEnd_1078106 := by exact prefixLift 1078106
  have htrace : WordTrace (prefixWord ++ tailWord_1078106) baseStart_1078106 baseEnd_1078106 := by
    simpa [prefixWord, tailWord_1078106, baseEnd_1078106] using wordTrace_append hprefix tailTrace_1078106
  have hstable : (prefixWord ++ tailWord_1078106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078106).length < 2 ^ (prefixWord ++ tailWord_1078106).sum := by decide
  have hdescent : baseEnd_1078106 < baseStart_1078106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078119 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1078119 : Nat := 118140960795 + 1078119 * 2 ^ 59
def prefixEnd_1078119 : Nat := 4983230072969 + 3 ^ 40 * 1078119 * 2
def baseEnd_1078119 : Nat := 553593249744772588154327

theorem tailTrace_1078119 : CollatzResearch.WordTrace tailWord_1078119 prefixEnd_1078119 553593249744772588154327 := by
  unfold tailWord_1078119
  simp only [CollatzResearch.WordTrace]
  refine ⟨39322230381166465911125411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26214820254110977274083607 39322230381166465911125411)
  ·
    refine ⟨58983345571749698866688117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39322230381166465911125411 58983345571749698866688117)
    ·
      refine ⟨5529688647351534268752011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58983345571749698866688117 5529688647351534268752011)
      ·
        refine ⟨8294532971027301403128017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5529688647351534268752011 8294532971027301403128017)
        ·
          refine ⟨6220899728270476052346013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8294532971027301403128017 6220899728270476052346013)
          ·
            refine ⟨2332837398101428519629755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6220899728270476052346013 2332837398101428519629755)
            ·
              refine ⟨3499256097152142779444633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332837398101428519629755 3499256097152142779444633)
              ·
                refine ⟨2624442072864107084583475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3499256097152142779444633 2624442072864107084583475)
                ·
                  refine ⟨3936663109296160626875213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624442072864107084583475 3936663109296160626875213)
                  ·
                    refine ⟨1476248665986060235078205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3936663109296160626875213 1476248665986060235078205)
                    ·
                      refine ⟨553593249744772588154327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476248665986060235078205 553593249744772588154327)
                      ·
                        rfl

theorem cell23_1078119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1078119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078119 prefixEnd_1078119 := by exact prefixLift 1078119
  have htrace : WordTrace (prefixWord ++ tailWord_1078119) baseStart_1078119 baseEnd_1078119 := by
    simpa [prefixWord, tailWord_1078119, baseEnd_1078119] using wordTrace_append hprefix tailTrace_1078119
  have hstable : (prefixWord ++ tailWord_1078119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078119).length < 2 ^ (prefixWord ++ tailWord_1078119).sum := by decide
  have hdescent : baseEnd_1078119 < baseStart_1078119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078135 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 3, 8]
def baseStart_1078135 : Nat := 118140960795 + 1078135 * 2 ^ 59
def prefixEnd_1078135 : Nat := 4983230072969 + 3 ^ 40 * 1078135 * 2
def baseEnd_1078135 : Nat := 184533821811748175184751

theorem tailTrace_1078135 : CollatzResearch.WordTrace tailWord_1078135 prefixEnd_1078135 184533821811748175184751 := by
  unfold tailWord_1078135
  simp only [CollatzResearch.WordTrace]
  refine ⟨39322813949108500643707859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26215209299405667095805239 39322813949108500643707859)
  ·
    refine ⟨58984220923662750965561789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39322813949108500643707859 58984220923662750965561789)
    ·
      refine ⟨22119082846373531612085671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58984220923662750965561789 22119082846373531612085671)
      ·
        refine ⟨33178624269560297418128507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22119082846373531612085671 33178624269560297418128507)
        ·
          refine ⟨49767936404340446127192761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33178624269560297418128507 49767936404340446127192761)
          ·
            refine ⟨37325952303255334595394571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49767936404340446127192761 37325952303255334595394571)
            ·
              refine ⟨55988928454883001893091857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37325952303255334595394571 55988928454883001893091857)
              ·
                refine ⟨41991696341162251419818893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55988928454883001893091857 41991696341162251419818893)
                ·
                  refine ⟨15746886127935844282432085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41991696341162251419818893 15746886127935844282432085)
                  ·
                    refine ⟨184533821811748175184751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15746886127935844282432085 184533821811748175184751)
                    ·
                      rfl

theorem cell23_1078135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_1078135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078135 prefixEnd_1078135 := by exact prefixLift 1078135
  have htrace : WordTrace (prefixWord ++ tailWord_1078135) baseStart_1078135 baseEnd_1078135 := by
    simpa [prefixWord, tailWord_1078135, baseEnd_1078135] using wordTrace_append hprefix tailTrace_1078135
  have hstable : (prefixWord ++ tailWord_1078135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078135).length < 2 ^ (prefixWord ++ tailWord_1078135).sum := by decide
  have hdescent : baseEnd_1078135 < baseStart_1078135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078152 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1078152 : Nat := 118140960795 + 1078152 * 2 ^ 59
def prefixEnd_1078152 : Nat := 4983230072969 + 3 ^ 40 * 1078152 * 2
def baseEnd_1078152 : Nat := 184536731535456986347225

theorem tailTrace_1078152 : CollatzResearch.WordTrace tailWord_1078152 prefixEnd_1078152 184536731535456986347225 := by
  unfold tailWord_1078152
  simp only [CollatzResearch.WordTrace]
  refine ⟨19661716995023456273538355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26215622660031275031384473 19661716995023456273538355)
  ·
    refine ⟨29492575492535184410307533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19661716995023456273538355 29492575492535184410307533)
    ·
      refine ⟨11059715809700694153865325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29492575492535184410307533 11059715809700694153865325)
      ·
        refine ⟨4147393428637760307699497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11059715809700694153865325 4147393428637760307699497)
        ·
          refine ⟨3110545071478320230774623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4147393428637760307699497 3110545071478320230774623)
          ·
            refine ⟨4665817607217480346161935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110545071478320230774623 4665817607217480346161935)
            ·
              refine ⟨6998726410826220519242903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4665817607217480346161935 6998726410826220519242903)
              ·
                refine ⟨10498089616239330778864355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6998726410826220519242903 10498089616239330778864355)
                ·
                  refine ⟨15747134424358996168296533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10498089616239330778864355 15747134424358996168296533)
                  ·
                    refine ⟨184536731535456986347225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15747134424358996168296533 184536731535456986347225)
                    ·
                      rfl

theorem cell23_1078152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1078152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078152 prefixEnd_1078152 := by exact prefixLift 1078152
  have htrace : WordTrace (prefixWord ++ tailWord_1078152) baseStart_1078152 baseEnd_1078152 := by
    simpa [prefixWord, tailWord_1078152, baseEnd_1078152] using wordTrace_append hprefix tailTrace_1078152
  have hstable : (prefixWord ++ tailWord_1078152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078152).length < 2 ^ (prefixWord ++ tailWord_1078152).sum := by decide
  have hdescent : baseEnd_1078152 < baseStart_1078152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078193 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 4, 2, 2]
def baseStart_1078193 : Nat := 118140960795 + 1078193 * 2 ^ 59
def prefixEnd_1078193 : Nat := 4983230072969 + 3 ^ 40 * 1078193 * 2
def baseEnd_1078193 : Nat := 553631247313205298628987

theorem tailTrace_1078193 : CollatzResearch.WordTrace tailWord_1078193 prefixEnd_1078193 553631247313205298628987 := by
  unfold tailWord_1078193
  simp only [CollatzResearch.WordTrace]
  refine ⟨39324929382898376549319233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26216619588598917699546155 39324929382898376549319233)
  ·
    refine ⟨29493697037173782411989425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39324929382898376549319233 29493697037173782411989425)
    ·
      refine ⟨22120272777880336808992069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29493697037173782411989425 22120272777880336808992069)
      ·
        refine ⟨4147551145852563151686013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22120272777880336808992069 4147551145852563151686013)
        ·
          refine ⟨1555331679694711181882255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4147551145852563151686013 1555331679694711181882255)
          ·
            refine ⟨2332997519542066772823383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555331679694711181882255 2332997519542066772823383)
            ·
              refine ⟨3499496279313100159235075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332997519542066772823383 3499496279313100159235075)
              ·
                refine ⟨5249244418969650238852613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3499496279313100159235075 5249244418969650238852613)
                ·
                  refine ⟨984233328556809419784865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5249244418969650238852613 984233328556809419784865)
                  ·
                    refine ⟨738174996417607064838649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 984233328556809419784865 738174996417607064838649)
                    ·
                      refine ⟨553631247313205298628987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738174996417607064838649 553631247313205298628987)
                      ·
                        rfl

theorem cell23_1078193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_1078193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078193 prefixEnd_1078193 := by exact prefixLift 1078193
  have htrace : WordTrace (prefixWord ++ tailWord_1078193) baseStart_1078193 baseEnd_1078193 := by
    simpa [prefixWord, tailWord_1078193, baseEnd_1078193] using wordTrace_append hprefix tailTrace_1078193
  have hstable : (prefixWord ++ tailWord_1078193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078193).length < 2 ^ (prefixWord ++ tailWord_1078193).sum := by decide
  have hdescent : baseEnd_1078193 < baseStart_1078193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078199 : List Nat := [1, 1, 3, 1, 3, 1, 4, 4, 5]
def baseStart_1078199 : Nat := 118140960795 + 1078199 * 2 ^ 59
def prefixEnd_1078199 : Nat := 4983230072969 + 3 ^ 40 * 1078199 * 2
def baseEnd_1078199 : Nat := 61514925355236919461551

theorem tailTrace_1078199 : CollatzResearch.WordTrace tailWord_1078199 prefixEnd_1078199 61514925355236919461551 := by
  unfold tailWord_1078199
  simp only [CollatzResearch.WordTrace]
  refine ⟨39325148220876639574037651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26216765480584426382691767 39325148220876639574037651)
  ·
    refine ⟨58987722331314959361056477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39325148220876639574037651 58987722331314959361056477)
    ·
      refine ⟨22120395874243109760396179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58987722331314959361056477 22120395874243109760396179)
      ·
        refine ⟨33180593811364664640594269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22120395874243109760396179 33180593811364664640594269)
        ·
          refine ⟨12442722679261749240222851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33180593811364664640594269 12442722679261749240222851)
          ·
            refine ⟨18664084018892623860334277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12442722679261749240222851 18664084018892623860334277)
            ·
              refine ⟨3499515753542366973812677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18664084018892623860334277 3499515753542366973812677)
              ·
                refine ⟨656159203789193807589877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3499515753542366973812677 656159203789193807589877)
                ·
                  refine ⟨61514925355236919461551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 656159203789193807589877 61514925355236919461551)
                  ·
                    rfl

theorem cell23_1078199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 5].length) (baseStart_1078199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078199 prefixEnd_1078199 := by exact prefixLift 1078199
  have htrace : WordTrace (prefixWord ++ tailWord_1078199) baseStart_1078199 baseEnd_1078199 := by
    simpa [prefixWord, tailWord_1078199, baseEnd_1078199] using wordTrace_append hprefix tailTrace_1078199
  have hstable : (prefixWord ++ tailWord_1078199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078199).length < 2 ^ (prefixWord ++ tailWord_1078199).sum := by decide
  have hdescent : baseEnd_1078199 < baseStart_1078199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078261 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1078261 : Nat := 118140960795 + 1078261 * 2 ^ 59
def prefixEnd_1078261 : Nat := 4983230072969 + 3 ^ 40 * 1078261 * 2
def baseEnd_1078261 : Nat := 553666163997711032578675

theorem tailTrace_1078261 : CollatzResearch.WordTrace tailWord_1078261 prefixEnd_1078261 553666163997711032578675 := by
  unfold tailWord_1078261
  simp only [CollatzResearch.WordTrace]
  refine ⟨39327409546652024162794637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26218273031101349441863091 39327409546652024162794637)
  ·
    refine ⟨14747778579994509061047989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39327409546652024162794637 14747778579994509061047989)
    ·
      refine ⟨1382604241874485224473249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14747778579994509061047989 1382604241874485224473249)
      ·
        refine ⟨1036953181405863918354937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1382604241874485224473249 1036953181405863918354937)
        ·
          refine ⟨777714886054397938766203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1036953181405863918354937 777714886054397938766203)
          ·
            refine ⟨1166572329081596908149305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777714886054397938766203 1166572329081596908149305)
            ·
              refine ⟨874929246811197681111979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166572329081596908149305 874929246811197681111979)
              ·
                refine ⟨1312393870216796521667969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874929246811197681111979 1312393870216796521667969)
                ·
                  refine ⟨984295402662597391250977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312393870216796521667969 984295402662597391250977)
                  ·
                    refine ⟨738221551996948043438233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 984295402662597391250977 738221551996948043438233)
                    ·
                      refine ⟨553666163997711032578675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738221551996948043438233 553666163997711032578675)
                      ·
                        rfl

theorem cell23_1078261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1078261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078261 prefixEnd_1078261 := by exact prefixLift 1078261
  have htrace : WordTrace (prefixWord ++ tailWord_1078261) baseStart_1078261 baseEnd_1078261 := by
    simpa [prefixWord, tailWord_1078261, baseEnd_1078261] using wordTrace_append hprefix tailTrace_1078261
  have hstable : (prefixWord ++ tailWord_1078261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078261).length < 2 ^ (prefixWord ++ tailWord_1078261).sum := by decide
  have hdescent : baseEnd_1078261 < baseStart_1078261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078269 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_1078269 : Nat := 118140960795 + 1078269 * 2 ^ 59
def prefixEnd_1078269 : Nat := 4983230072969 + 3 ^ 40 * 1078269 * 2
def baseEnd_1078269 : Nat := 553670271842947001278637

theorem tailTrace_1078269 : CollatzResearch.WordTrace tailWord_1078269 prefixEnd_1078269 553670271842947001278637 := by
  unfold tailWord_1078269
  simp only [CollatzResearch.WordTrace]
  refine ⟨39327701330623041529085861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26218467553748694352723907 39327701330623041529085861)
  ·
    refine ⟨7373943999491820286703599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39327701330623041529085861 7373943999491820286703599)
    ·
      refine ⟨11060915999237730430055399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7373943999491820286703599 11060915999237730430055399)
      ·
        refine ⟨16591373998856595645083099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11060915999237730430055399 16591373998856595645083099)
        ·
          refine ⟨24887060998284893467624649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16591373998856595645083099 24887060998284893467624649)
          ·
            refine ⟨18665295748713670100718487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24887060998284893467624649 18665295748713670100718487)
            ·
              refine ⟨27997943623070505151077731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18665295748713670100718487 27997943623070505151077731)
              ·
                refine ⟨41996915434605757726616597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27997943623070505151077731 41996915434605757726616597)
                ·
                  refine ⟨1968605410997144893435153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41996915434605757726616597 1968605410997144893435153)
                  ·
                    refine ⟨1476454058247858670076365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1968605410997144893435153 1476454058247858670076365)
                    ·
                      refine ⟨553670271842947001278637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476454058247858670076365 553670271842947001278637)
                      ·
                        rfl

theorem cell23_1078269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_1078269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078269 prefixEnd_1078269 := by exact prefixLift 1078269
  have htrace : WordTrace (prefixWord ++ tailWord_1078269) baseStart_1078269 baseEnd_1078269 := by
    simpa [prefixWord, tailWord_1078269, baseEnd_1078269] using wordTrace_append hprefix tailTrace_1078269
  have hstable : (prefixWord ++ tailWord_1078269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078269).length < 2 ^ (prefixWord ++ tailWord_1078269).sum := by decide
  have hdescent : baseEnd_1078269 < baseStart_1078269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078286 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1078286 : Nat := 118140960795 + 1078286 * 2 ^ 59
def prefixEnd_1078286 : Nat := 4983230072969 + 3 ^ 40 * 1078286 * 2
def baseEnd_1078286 : Nat := 553679001014073434766059

theorem tailTrace_1078286 : CollatzResearch.WordTrace tailWord_1078286 prefixEnd_1078286 553679001014073434766059 := by
  unfold tailWord_1078286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916040171445181679056839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26218880914374302288303141 4916040171445181679056839)
  ·
    refine ⟨7374060257167772518585259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4916040171445181679056839 7374060257167772518585259)
    ·
      refine ⟨11061090385751658777877889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7374060257167772518585259 11061090385751658777877889)
      ·
        refine ⟨8295817789313744083408417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11061090385751658777877889 8295817789313744083408417)
        ·
          refine ⟨6221863341985308062556313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8295817789313744083408417 6221863341985308062556313)
          ·
            refine ⟨4666397506488981046917235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6221863341985308062556313 4666397506488981046917235)
            ·
              refine ⟨6999596259733471570375853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666397506488981046917235 6999596259733471570375853)
              ·
                refine ⟨2624848597400051838890945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6999596259733471570375853 2624848597400051838890945)
                ·
                  refine ⟨1968636448050038879168209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624848597400051838890945 1968636448050038879168209)
                  ·
                    refine ⟨1476477336037529159376157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1968636448050038879168209 1476477336037529159376157)
                    ·
                      refine ⟨553679001014073434766059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476477336037529159376157 553679001014073434766059)
                      ·
                        rfl

theorem cell23_1078286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1078286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078286 prefixEnd_1078286 := by exact prefixLift 1078286
  have htrace : WordTrace (prefixWord ++ tailWord_1078286) baseStart_1078286 baseEnd_1078286 := by
    simpa [prefixWord, tailWord_1078286, baseEnd_1078286] using wordTrace_append hprefix tailTrace_1078286
  have hstable : (prefixWord ++ tailWord_1078286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078286).length < 2 ^ (prefixWord ++ tailWord_1078286).sum := by decide
  have hdescent : baseEnd_1078286 < baseStart_1078286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078306 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1078306 : Nat := 118140960795 + 1078306 * 2 ^ 59
def prefixEnd_1078306 : Nat := 4983230072969 + 3 ^ 40 * 1078306 * 2
def baseEnd_1078306 : Nat := 61521030069684817390663

theorem tailTrace_1078306 : CollatzResearch.WordTrace tailWord_1078306 prefixEnd_1078306 61521030069684817390663 := by
  unfold tailWord_1078306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9832262707872249212045693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26219367220992664565455181 9832262707872249212045693)
  ·
    refine ⟨3687098515452093454517135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9832262707872249212045693 3687098515452093454517135)
    ·
      refine ⟨5530647773178140181775703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3687098515452093454517135 5530647773178140181775703)
      ·
        refine ⟨8295971659767210272663555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5530647773178140181775703 8295971659767210272663555)
        ·
          refine ⟨12443957489650815408995333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8295971659767210272663555 12443957489650815408995333)
          ·
            refine ⟨2333242029309527889186625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12443957489650815408995333 2333242029309527889186625)
            ·
              refine ⟨1749931521982145916889969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333242029309527889186625 1749931521982145916889969)
              ·
                refine ⟨1312448641486609437667477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749931521982145916889969 1312448641486609437667477)
                ·
                  refine ⟨61521030069684817390663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1312448641486609437667477 61521030069684817390663)
                  ·
                    rfl

theorem cell23_1078306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1078306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078306 prefixEnd_1078306 := by exact prefixLift 1078306
  have htrace : WordTrace (prefixWord ++ tailWord_1078306) baseStart_1078306 baseEnd_1078306 := by
    simpa [prefixWord, tailWord_1078306, baseEnd_1078306] using wordTrace_append hprefix tailTrace_1078306
  have hstable : (prefixWord ++ tailWord_1078306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078306).length < 2 ^ (prefixWord ++ tailWord_1078306).sum := by decide
  have hdescent : baseEnd_1078306 < baseStart_1078306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078316 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_1078316 : Nat := 118140960795 + 1078316 * 2 ^ 59
def prefixEnd_1078316 : Nat := 4983230072969 + 3 ^ 40 * 1078316 * 2
def baseEnd_1078316 : Nat := 553694405433708317390921

theorem tailTrace_1078316 : CollatzResearch.WordTrace tailWord_1078316 prefixEnd_1078316 553694405433708317390921 := by
  unfold tailWord_1078316
  simp only [CollatzResearch.WordTrace]
  refine ⟨19664707780726384278023401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26219610374301845704031201 19664707780726384278023401)
  ·
    refine ⟨14748530835544788208517551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19664707780726384278023401 14748530835544788208517551)
    ·
      refine ⟨22122796253317182312776327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14748530835544788208517551 22122796253317182312776327)
      ·
        refine ⟨33184194379975773469164491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22122796253317182312776327 33184194379975773469164491)
        ·
          refine ⟨49776291569963660203746737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33184194379975773469164491 49776291569963660203746737)
          ·
            refine ⟨37332218677472745152810053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49776291569963660203746737 37332218677472745152810053)
            ·
              refine ⟨6999791002026139716151885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37332218677472745152810053 6999791002026139716151885)
              ·
                refine ⟨2624921625759802393556957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6999791002026139716151885 2624921625759802393556957)
                ·
                  refine ⟨984345609659925897583859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2624921625759802393556957 984345609659925897583859)
                  ·
                    refine ⟨1476518414489888846375789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984345609659925897583859 1476518414489888846375789)
                    ·
                      refine ⟨553694405433708317390921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476518414489888846375789 553694405433708317390921)
                      ·
                        rfl

theorem cell23_1078316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_1078316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078316 prefixEnd_1078316 := by exact prefixLift 1078316
  have htrace : WordTrace (prefixWord ++ tailWord_1078316) baseStart_1078316 baseEnd_1078316 := by
    simpa [prefixWord, tailWord_1078316, baseEnd_1078316] using wordTrace_append hprefix tailTrace_1078316
  have hstable : (prefixWord ++ tailWord_1078316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078316).length < 2 ^ (prefixWord ++ tailWord_1078316).sum := by decide
  have hdescent : baseEnd_1078316 < baseStart_1078316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
