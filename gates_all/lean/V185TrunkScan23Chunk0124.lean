import V185TrunkScan23Chunk0123

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_734067 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5]
def baseStart_734067 : Nat := 118140960795 + 734067 * 2 ^ 59
def prefixEnd_734067 : Nat := 4983230072969 + 3 ^ 40 * 734067 * 2
def baseEnd_734067 : Nat := 376929203604084693186593

theorem tailTrace_734067 : CollatzResearch.WordTrace tailWord_734067 prefixEnd_734067 376929203604084693186593 := by
  unfold tailWord_734067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26773623031608102507600455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17849082021072068338400303 26773623031608102507600455)
  ·
    refine ⟨40160434547412153761400683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26773623031608102507600455 40160434547412153761400683)
    ·
      refine ⟨60240651821118230642101025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40160434547412153761400683 60240651821118230642101025)
      ·
        refine ⟨45180488865838672981575769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60240651821118230642101025 45180488865838672981575769)
        ·
          refine ⟨33885366649379004736181827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45180488865838672981575769 33885366649379004736181827)
          ·
            refine ⟨50828049974068507104272741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33885366649379004736181827 50828049974068507104272741)
            ·
              refine ⟨9530259370137845082051139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50828049974068507104272741 9530259370137845082051139)
              ·
                refine ⟨14295389055206767623076709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9530259370137845082051139 14295389055206767623076709)
                ·
                  refine ⟨2680385447851268929326883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14295389055206767623076709 2680385447851268929326883)
                  ·
                    refine ⟨4020578171776903393990325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2680385447851268929326883 4020578171776903393990325)
                    ·
                      refine ⟨376929203604084693186593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4020578171776903393990325 376929203604084693186593)
                      ·
                        rfl

theorem cell23_734067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_734067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734067 prefixEnd_734067 := by exact prefixLift 734067
  have htrace : WordTrace (prefixWord ++ tailWord_734067) baseStart_734067 baseEnd_734067 := by
    simpa [prefixWord, tailWord_734067, baseEnd_734067] using wordTrace_append hprefix tailTrace_734067
  have hstable : (prefixWord ++ tailWord_734067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734067).length < 2 ^ (prefixWord ++ tailWord_734067).sum := by decide
  have hdescent : baseEnd_734067 < baseStart_734067 := by decide
  rcases family_descends (prefixWord ++ tailWord_734067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734085 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 1, 3, 2]
def baseStart_734085 : Nat := 118140960795 + 734085 * 2 ^ 59
def prefixEnd_734085 : Nat := 4983230072969 + 3 ^ 40 * 734085 * 2
def baseEnd_734085 : Nat := 376938446255865622761511

theorem tailTrace_734085 : CollatzResearch.WordTrace tailWord_734085 prefixEnd_734085 376938446255865622761511 := by
  unfold tailWord_734085
  simp only [CollatzResearch.WordTrace]
  refine ⟨26774279545542891581755709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17849519697028594387837139 26774279545542891581755709)
  ·
    refine ⟨10040354829578584343158391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26774279545542891581755709 10040354829578584343158391)
    ·
      refine ⟨15060532244367876514737587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10040354829578584343158391 15060532244367876514737587)
      ·
        refine ⟨22590798366551814772106381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15060532244367876514737587 22590798366551814772106381)
        ·
          refine ⟨8471549387456930539539893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22590798366551814772106381 8471549387456930539539893)
          ·
            refine ⟨794207755074087238081865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8471549387456930539539893 794207755074087238081865)
            ·
              refine ⟨595655816305565428561399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794207755074087238081865 595655816305565428561399)
              ·
                refine ⟨893483724458348142842099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595655816305565428561399 893483724458348142842099)
                ·
                  refine ⟨1340225586687522214263149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893483724458348142842099 1340225586687522214263149)
                  ·
                    refine ⟨502584595007820830348681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340225586687522214263149 502584595007820830348681)
                    ·
                      refine ⟨376938446255865622761511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502584595007820830348681 376938446255865622761511)
                      ·
                        rfl

theorem cell23_734085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_734085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734085 prefixEnd_734085 := by exact prefixLift 734085
  have htrace : WordTrace (prefixWord ++ tailWord_734085) baseStart_734085 baseEnd_734085 := by
    simpa [prefixWord, tailWord_734085, baseEnd_734085] using wordTrace_append hprefix tailTrace_734085
  have hstable : (prefixWord ++ tailWord_734085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734085).length < 2 ^ (prefixWord ++ tailWord_734085).sum := by decide
  have hdescent : baseEnd_734085 < baseStart_734085 := by decide
  rcases family_descends (prefixWord ++ tailWord_734085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734127 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_734127 : Nat := 118140960795 + 734127 * 2 ^ 59
def prefixEnd_734127 : Nat := 4983230072969 + 3 ^ 40 * 734127 * 2
def baseEnd_734127 : Nat := 376960012443354458436317

theorem tailTrace_734127 : CollatzResearch.WordTrace tailWord_734127 prefixEnd_734127 376960012443354458436317 := by
  unfold tailWord_734127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26775811411390732754784635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17850540940927155169856423 26775811411390732754784635)
  ·
    refine ⟨40163717117086099132176953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26775811411390732754784635 40163717117086099132176953)
    ·
      refine ⟨30122787837814574349132715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40163717117086099132176953 30122787837814574349132715)
      ·
        refine ⟨45184181756721861523699073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30122787837814574349132715 45184181756721861523699073)
        ·
          refine ⟨33888136317541396142774305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45184181756721861523699073 33888136317541396142774305)
          ·
            refine ⟨25416102238156047107080729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33888136317541396142774305 25416102238156047107080729)
            ·
              refine ⟨19062076678617035330310547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25416102238156047107080729 19062076678617035330310547)
              ·
                refine ⟨28593115017925552995465821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19062076678617035330310547 28593115017925552995465821)
                ·
                  refine ⟨10722418131722082373299683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28593115017925552995465821 10722418131722082373299683)
                  ·
                    refine ⟨16083627197583123559949525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10722418131722082373299683 16083627197583123559949525)
                    ·
                      refine ⟨376960012443354458436317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16083627197583123559949525 376960012443354458436317)
                      ·
                        rfl

theorem cell23_734127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_734127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734127 prefixEnd_734127 := by exact prefixLift 734127
  have htrace : WordTrace (prefixWord ++ tailWord_734127) baseStart_734127 baseEnd_734127 := by
    simpa [prefixWord, tailWord_734127, baseEnd_734127] using wordTrace_append hprefix tailTrace_734127
  have hstable : (prefixWord ++ tailWord_734127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734127).length < 2 ^ (prefixWord ++ tailWord_734127).sum := by decide
  have hdescent : baseEnd_734127 < baseStart_734127 := by decide
  rcases family_descends (prefixWord ++ tailWord_734127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734147 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 10]
def baseStart_734147 : Nat := 118140960795 + 734147 * 2 ^ 59
def prefixEnd_734147 : Nat := 4983230072969 + 3 ^ 40 * 734147 * 2
def baseEnd_734147 : Nat := 125656760685481460062075

theorem tailTrace_734147 : CollatzResearch.WordTrace tailWord_734147 prefixEnd_734147 125656760685481460062075 := by
  unfold tailWord_734147
  simp only [CollatzResearch.WordTrace]
  refine ⟨26776540871318276170512695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17851027247545517447008463 26776540871318276170512695)
  ·
    refine ⟨40164811306977414255769043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26776540871318276170512695 40164811306977414255769043)
    ·
      refine ⟨60247216960466121383653565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40164811306977414255769043 60247216960466121383653565)
      ·
        refine ⟨22592706360174795518870087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60247216960466121383653565 22592706360174795518870087)
        ·
          refine ⟨33889059540262193278305131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22592706360174795518870087 33889059540262193278305131)
          ·
            refine ⟨50833589310393289917457697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33889059540262193278305131 50833589310393289917457697)
            ·
              refine ⟨38125191982794967438093273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50833589310393289917457697 38125191982794967438093273)
              ·
                refine ⟨28593893987096225578569955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38125191982794967438093273 28593893987096225578569955)
                ·
                  refine ⟨42890840980644338367854933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28593893987096225578569955 42890840980644338367854933)
                  ·
                    refine ⟨125656760685481460062075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 42890840980644338367854933 125656760685481460062075)
                    ·
                      rfl

theorem cell23_734147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 10].length) (baseStart_734147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734147 prefixEnd_734147 := by exact prefixLift 734147
  have htrace : WordTrace (prefixWord ++ tailWord_734147) baseStart_734147 baseEnd_734147 := by
    simpa [prefixWord, tailWord_734147, baseEnd_734147] using wordTrace_append hprefix tailTrace_734147
  have hstable : (prefixWord ++ tailWord_734147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734147).length < 2 ^ (prefixWord ++ tailWord_734147).sum := by decide
  have hdescent : baseEnd_734147 < baseStart_734147 := by decide
  rcases family_descends (prefixWord ++ tailWord_734147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734184 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_734184 : Nat := 118140960795 + 734184 * 2 ^ 59
def prefixEnd_734184 : Nat := 4983230072969 + 3 ^ 40 * 734184 * 2
def baseEnd_734184 : Nat := 376989280840660735423555

theorem tailTrace_734184 : CollatzResearch.WordTrace tailWord_734184 prefixEnd_734184 376989280840660735423555 := by
  unfold tailWord_734184
  simp only [CollatzResearch.WordTrace]
  refine ⟨13388945186092115744804803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17851926914789487659739737 13388945186092115744804803)
  ·
    refine ⟨20083417779138173617207205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13388945186092115744804803 20083417779138173617207205)
    ·
      refine ⟨3765640833588407553226351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20083417779138173617207205 3765640833588407553226351)
      ·
        refine ⟨5648461250382611329839527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765640833588407553226351 5648461250382611329839527)
        ·
          refine ⟨8472691875573916994759291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648461250382611329839527 8472691875573916994759291)
          ·
            refine ⟨12709037813360875492138937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8472691875573916994759291 12709037813360875492138937)
            ·
              refine ⟨9531778360020656619104203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12709037813360875492138937 9531778360020656619104203)
              ·
                refine ⟨14297667540030984928656305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9531778360020656619104203 14297667540030984928656305)
                ·
                  refine ⟨10723250655023238696492229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14297667540030984928656305 10723250655023238696492229)
                  ·
                    refine ⟨2010609497816857255592293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10723250655023238696492229 2010609497816857255592293)
                    ·
                      refine ⟨376989280840660735423555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2010609497816857255592293 376989280840660735423555)
                      ·
                        rfl

theorem cell23_734184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_734184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734184 prefixEnd_734184 := by exact prefixLift 734184
  have htrace : WordTrace (prefixWord ++ tailWord_734184) baseStart_734184 baseEnd_734184 := by
    simpa [prefixWord, tailWord_734184, baseEnd_734184] using wordTrace_append hprefix tailTrace_734184
  have hstable : (prefixWord ++ tailWord_734184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734184).length < 2 ^ (prefixWord ++ tailWord_734184).sum := by decide
  have hdescent : baseEnd_734184 < baseStart_734184 := by decide
  rcases family_descends (prefixWord ++ tailWord_734184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734191 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 3]
def baseStart_734191 : Nat := 118140960795 + 734191 * 2 ^ 59
def prefixEnd_734191 : Nat := 4983230072969 + 3 ^ 40 * 734191 * 2
def baseEnd_734191 : Nat := 376992875205242208036023

theorem tailTrace_734191 : CollatzResearch.WordTrace tailWord_734191 prefixEnd_734191 376992875205242208036023 := by
  unfold tailWord_734191
  simp only [CollatzResearch.WordTrace]
  refine ⟨26778145683158871685114427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17852097122105914456742951 26778145683158871685114427)
  ·
    refine ⟨40167218524738307527671641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26778145683158871685114427 40167218524738307527671641)
    ·
      refine ⟨30125413893553730645753731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40167218524738307527671641 30125413893553730645753731)
      ·
        refine ⟨45188120840330595968630597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30125413893553730645753731 45188120840330595968630597)
        ·
          refine ⟨8472772657561986744118237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45188120840330595968630597 8472772657561986744118237)
          ·
            refine ⟨3177289746585745029044339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8472772657561986744118237 3177289746585745029044339)
            ·
              refine ⟨4765934619878617543566509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177289746585745029044339 4765934619878617543566509)
              ·
                refine ⟨1787225482454481578837441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4765934619878617543566509 1787225482454481578837441)
                ·
                  refine ⟨1340419111840861184128081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787225482454481578837441 1340419111840861184128081)
                  ·
                    refine ⟨1005314333880645888096061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340419111840861184128081 1005314333880645888096061)
                    ·
                      refine ⟨376992875205242208036023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005314333880645888096061 376992875205242208036023)
                      ·
                        rfl

theorem cell23_734191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_734191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734191 prefixEnd_734191 := by exact prefixLift 734191
  have htrace : WordTrace (prefixWord ++ tailWord_734191) baseStart_734191 baseEnd_734191 := by
    simpa [prefixWord, tailWord_734191, baseEnd_734191] using wordTrace_append hprefix tailTrace_734191
  have hstable : (prefixWord ++ tailWord_734191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734191).length < 2 ^ (prefixWord ++ tailWord_734191).sum := by decide
  have hdescent : baseEnd_734191 < baseStart_734191 := by decide
  rcases family_descends (prefixWord ++ tailWord_734191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734234 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_734234 : Nat := 118140960795 + 734234 * 2 ^ 59
def prefixEnd_734234 : Nat := 4983230072969 + 3 ^ 40 * 734234 * 2
def baseEnd_734234 : Nat := 377014954873385539798325

theorem tailTrace_734234 : CollatzResearch.WordTrace tailWord_734234 prefixEnd_734234 377014954873385539798325 := by
  unfold tailWord_734234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6694928505500772507232439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17853142681335393352619837 6694928505500772507232439)
  ·
    refine ⟨10042392758251158760848659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6694928505500772507232439 10042392758251158760848659)
    ·
      refine ⟨15063589137376738141272989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10042392758251158760848659 15063589137376738141272989)
      ·
        refine ⟨5648845926516276802977371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15063589137376738141272989 5648845926516276802977371)
        ·
          refine ⟨8473268889774415204466057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648845926516276802977371 8473268889774415204466057)
          ·
            refine ⟨6354951667330811403349543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8473268889774415204466057 6354951667330811403349543)
            ·
              refine ⟨9532427500996217105024315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354951667330811403349543 9532427500996217105024315)
              ·
                refine ⟨14298641251494325657536473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9532427500996217105024315 14298641251494325657536473)
                ·
                  refine ⟨10723980938620744243152355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14298641251494325657536473 10723980938620744243152355)
                  ·
                    refine ⟨16085971407931116364728533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10723980938620744243152355 16085971407931116364728533)
                    ·
                      refine ⟨377014954873385539798325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16085971407931116364728533 377014954873385539798325)
                      ·
                        rfl

theorem cell23_734234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_734234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734234 prefixEnd_734234 := by exact prefixLift 734234
  have htrace : WordTrace (prefixWord ++ tailWord_734234) baseStart_734234 baseEnd_734234 := by
    simpa [prefixWord, tailWord_734234, baseEnd_734234] using wordTrace_append hprefix tailTrace_734234
  have hstable : (prefixWord ++ tailWord_734234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734234).length < 2 ^ (prefixWord ++ tailWord_734234).sum := by decide
  have hdescent : baseEnd_734234 < baseStart_734234 := by decide
  rcases family_descends (prefixWord ++ tailWord_734234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734241 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 3, 5]
def baseStart_734241 : Nat := 118140960795 + 734241 * 2 ^ 59
def prefixEnd_734241 : Nat := 4983230072969 + 3 ^ 40 * 734241 * 2
def baseEnd_734241 : Nat := 125672849745989004136931

theorem tailTrace_734241 : CollatzResearch.WordTrace tailWord_734241 prefixEnd_734241 125672849745989004136931 := by
  unfold tailWord_734241
  simp only [CollatzResearch.WordTrace]
  refine ⟨26779969332977730224434577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17853312888651820149623051 26779969332977730224434577)
  ·
    refine ⟨20084976999733297668325933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26779969332977730224434577 20084976999733297668325933)
    ·
      refine ⟨7531866374899986625622225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20084976999733297668325933 7531866374899986625622225)
      ·
        refine ⟨5648899781174989969216669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7531866374899986625622225 5648899781174989969216669)
        ·
          refine ⟨2118337417940621238456251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5648899781174989969216669 2118337417940621238456251)
          ·
            refine ⟨3177506126910931857684377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118337417940621238456251 3177506126910931857684377)
            ·
              refine ⟨2383129595183198893263283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177506126910931857684377 2383129595183198893263283)
              ·
                refine ⟨3574694392774798339894925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383129595183198893263283 3574694392774798339894925)
                ·
                  refine ⟨1340510397290549377460597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3574694392774798339894925 1340510397290549377460597)
                  ·
                    refine ⟨125672849745989004136931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1340510397290549377460597 125672849745989004136931)
                    ·
                      rfl

theorem cell23_734241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_734241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734241 prefixEnd_734241 := by exact prefixLift 734241
  have htrace : WordTrace (prefixWord ++ tailWord_734241) baseStart_734241 baseEnd_734241 := by
    simpa [prefixWord, tailWord_734241, baseEnd_734241] using wordTrace_append hprefix tailTrace_734241
  have hstable : (prefixWord ++ tailWord_734241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734241).length < 2 ^ (prefixWord ++ tailWord_734241).sum := by decide
  have hdescent : baseEnd_734241 < baseStart_734241 := by decide
  rcases family_descends (prefixWord ++ tailWord_734241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734281 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 3]
def baseStart_734281 : Nat := 118140960795 + 734281 * 2 ^ 59
def prefixEnd_734281 : Nat := 4983230072969 + 3 ^ 40 * 734281 * 2
def baseEnd_734281 : Nat := 377039088464146855910609

theorem tailTrace_734281 : CollatzResearch.WordTrace tailWord_734281 prefixEnd_734281 377039088464146855910609 := by
  unfold tailWord_734281
  simp only [CollatzResearch.WordTrace]
  refine ⟨26781428252832817055890697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17854285501888544703927131 26781428252832817055890697)
  ·
    refine ⟨20086071189624612791918023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26781428252832817055890697 20086071189624612791918023)
    ·
      refine ⟨30129106784436919187877035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20086071189624612791918023 30129106784436919187877035)
      ·
        refine ⟨45193660176655378781815553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30129106784436919187877035 45193660176655378781815553)
        ·
          refine ⟨33895245132491534086361665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45193660176655378781815553 33895245132491534086361665)
          ·
            refine ⟨25421433849368650564771249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33895245132491534086361665 25421433849368650564771249)
            ·
              refine ⟨19066075387026487923578437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25421433849368650564771249 19066075387026487923578437)
              ·
                refine ⟨3574889135067466485670957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19066075387026487923578437 3574889135067466485670957)
                ·
                  refine ⟨1340583425650299932126609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3574889135067466485670957 1340583425650299932126609)
                  ·
                    refine ⟨1005437569237724949094957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340583425650299932126609 1005437569237724949094957)
                    ·
                      refine ⟨377039088464146855910609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005437569237724949094957 377039088464146855910609)
                      ·
                        rfl

theorem cell23_734281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_734281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734281 prefixEnd_734281 := by exact prefixLift 734281
  have htrace : WordTrace (prefixWord ++ tailWord_734281) baseStart_734281 baseEnd_734281 := by
    simpa [prefixWord, tailWord_734281, baseEnd_734281] using wordTrace_append hprefix tailTrace_734281
  have hstable : (prefixWord ++ tailWord_734281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734281).length < 2 ^ (prefixWord ++ tailWord_734281).sum := by decide
  have hdescent : baseEnd_734281 < baseStart_734281 := by decide
  rcases family_descends (prefixWord ++ tailWord_734281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734284 : List Nat := [2, 2, 1, 3, 1, 1, 1, 12]
def baseStart_734284 : Nat := 118140960795 + 734284 * 2 ^ 59
def prefixEnd_734284 : Nat := 4983230072969 + 3 ^ 40 * 734284 * 2
def baseEnd_734284 : Nat := 13964467737263346080485

theorem tailTrace_734284 : CollatzResearch.WordTrace tailWord_734284 prefixEnd_734284 13964467737263346080485 := by
  unfold tailWord_734284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390768835910974284124953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17854358447881299045499937 13390768835910974284124953)
  ·
    refine ⟨10043076626933230713093715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13390768835910974284124953 10043076626933230713093715)
    ·
      refine ⟨15064614940399846069640573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10043076626933230713093715 15064614940399846069640573)
      ·
        refine ⟨5649230602649942276115215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15064614940399846069640573 5649230602649942276115215)
        ·
          refine ⟨8473845903974913414172823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649230602649942276115215 8473845903974913414172823)
          ·
            refine ⟨12710768855962370121259235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8473845903974913414172823 12710768855962370121259235)
            ·
              refine ⟨19066153283943555181888853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12710768855962370121259235 19066153283943555181888853)
              ·
                refine ⟨13964467737263346080485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 19066153283943555181888853 13964467737263346080485)
                ·
                  rfl

theorem cell23_734284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 12].length) (baseStart_734284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734284 prefixEnd_734284 := by exact prefixLift 734284
  have htrace : WordTrace (prefixWord ++ tailWord_734284) baseStart_734284 baseEnd_734284 := by
    simpa [prefixWord, tailWord_734284, baseEnd_734284] using wordTrace_append hprefix tailTrace_734284
  have hstable : (prefixWord ++ tailWord_734284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734284).length < 2 ^ (prefixWord ++ tailWord_734284).sum := by decide
  have hdescent : baseEnd_734284 < baseStart_734284 := by decide
  rcases family_descends (prefixWord ++ tailWord_734284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734328 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_734328 : Nat := 118140960795 + 734328 * 2 ^ 59
def prefixEnd_734328 : Nat := 4983230072969 + 3 ^ 40 * 734328 * 2
def baseEnd_734328 : Nat := 377063222054908172022893

theorem tailTrace_734328 : CollatzResearch.WordTrace tailWord_734328 prefixEnd_734328 377063222054908172022893 := by
  unfold tailWord_734328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391571241831272041425819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17855428322441696055234425 13391571241831272041425819)
  ·
    refine ⟨20087356862746908062138729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13391571241831272041425819 20087356862746908062138729)
    ·
      refine ⟨15065517647060181046604047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20087356862746908062138729 15065517647060181046604047)
      ·
        refine ⟨22598276470590271569906071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15065517647060181046604047 22598276470590271569906071)
        ·
          refine ⟨33897414705885407354859107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22598276470590271569906071 33897414705885407354859107)
          ·
            refine ⟨50846122058828111032288661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33897414705885407354859107 50846122058828111032288661)
            ·
              refine ⟨2383411971507567704638531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50846122058828111032288661 2383411971507567704638531)
              ·
                refine ⟨3575117957261351556957797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383411971507567704638531 3575117957261351556957797)
                ·
                  refine ⟨670334616986503416929587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3575117957261351556957797 670334616986503416929587)
                  ·
                    refine ⟨1005501925479755125394381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 670334616986503416929587 1005501925479755125394381)
                    ·
                      refine ⟨377063222054908172022893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005501925479755125394381 377063222054908172022893)
                      ·
                        rfl

theorem cell23_734328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_734328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734328 prefixEnd_734328 := by exact prefixLift 734328
  have htrace : WordTrace (prefixWord ++ tailWord_734328) baseStart_734328 baseEnd_734328 := by
    simpa [prefixWord, tailWord_734328, baseEnd_734328] using wordTrace_append hprefix tailTrace_734328
  have hstable : (prefixWord ++ tailWord_734328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734328).length < 2 ^ (prefixWord ++ tailWord_734328).sum := by decide
  have hdescent : baseEnd_734328 < baseStart_734328 := by decide
  rcases family_descends (prefixWord ++ tailWord_734328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734329 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 3, 2, 2]
def baseStart_734329 : Nat := 118140960795 + 734329 * 2 ^ 59
def prefixEnd_734329 : Nat := 4983230072969 + 3 ^ 40 * 734329 * 2
def baseEnd_734329 : Nat := 377063735535562668110389

theorem tailTrace_734329 : CollatzResearch.WordTrace tailWord_734329 prefixEnd_734329 377063735535562668110389 := by
  unfold tailWord_734329
  simp only [CollatzResearch.WordTrace]
  refine ⟨26783178956658921253638041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17855452637772614169092027 26783178956658921253638041)
  ·
    refine ⟨20087384217494190940228531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26783178956658921253638041 20087384217494190940228531)
    ·
      refine ⟨30131076326241286410342797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20087384217494190940228531 30131076326241286410342797)
      ·
        refine ⟨11299153622340482403878549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30131076326241286410342797 11299153622340482403878549)
        ·
          refine ⟨529647826047210112681807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11299153622340482403878549 529647826047210112681807)
          ·
            refine ⟨794471739070815169022711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529647826047210112681807 794471739070815169022711)
            ·
              refine ⟨1191707608606222753534067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794471739070815169022711 1191707608606222753534067)
              ·
                refine ⟨1787561412909334130301101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191707608606222753534067 1787561412909334130301101)
                ·
                  refine ⟨670335529841000298862913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1787561412909334130301101 670335529841000298862913)
                  ·
                    refine ⟨502751647380750224147185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 670335529841000298862913 502751647380750224147185)
                    ·
                      refine ⟨377063735535562668110389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502751647380750224147185 377063735535562668110389)
                      ·
                        rfl

theorem cell23_734329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_734329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734329 prefixEnd_734329 := by exact prefixLift 734329
  have htrace : WordTrace (prefixWord ++ tailWord_734329) baseStart_734329 baseEnd_734329 := by
    simpa [prefixWord, tailWord_734329, baseEnd_734329] using wordTrace_append hprefix tailTrace_734329
  have hstable : (prefixWord ++ tailWord_734329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734329).length < 2 ^ (prefixWord ++ tailWord_734329).sum := by decide
  have hdescent : baseEnd_734329 < baseStart_734329 := by decide
  rcases family_descends (prefixWord ++ tailWord_734329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734345 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 3]
def baseStart_734345 : Nat := 118140960795 + 734345 * 2 ^ 59
def prefixEnd_734345 : Nat := 4983230072969 + 3 ^ 40 * 734345 * 2
def baseEnd_734345 : Nat := 377071951226034605510315

theorem tailTrace_734345 : CollatzResearch.WordTrace tailWord_734345 prefixEnd_734345 377071951226034605510315 := by
  unfold tailWord_734345
  simp only [CollatzResearch.WordTrace]
  refine ⟨26783762524600955986220489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17855841683067303990813659 26783762524600955986220489)
  ·
    refine ⟨20087821893450716989665367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26783762524600955986220489 20087821893450716989665367)
    ·
      refine ⟨30131732840176075484498051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20087821893450716989665367 30131732840176075484498051)
      ·
        refine ⟨45197599260264113226747077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30131732840176075484498051 45197599260264113226747077)
        ·
          refine ⟨8474549861299521230015077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45197599260264113226747077 8474549861299521230015077)
          ·
            refine ⟨1588978098993660230627827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8474549861299521230015077 1588978098993660230627827)
            ·
              refine ⟨2383467148490490345941741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588978098993660230627827 2383467148490490345941741)
              ·
                refine ⟨893800180683933879728153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2383467148490490345941741 893800180683933879728153)
                ·
                  refine ⟨670350135512950409796115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893800180683933879728153 670350135512950409796115)
                  ·
                    refine ⟨1005525203269425614694173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 670350135512950409796115 1005525203269425614694173)
                    ·
                      refine ⟨377071951226034605510315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005525203269425614694173 377071951226034605510315)
                      ·
                        rfl

theorem cell23_734345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 3].length) (baseStart_734345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734345 prefixEnd_734345 := by exact prefixLift 734345
  have htrace : WordTrace (prefixWord ++ tailWord_734345) baseStart_734345 baseEnd_734345 := by
    simpa [prefixWord, tailWord_734345, baseEnd_734345] using wordTrace_append hprefix tailTrace_734345
  have hstable : (prefixWord ++ tailWord_734345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734345).length < 2 ^ (prefixWord ++ tailWord_734345).sum := by decide
  have hdescent : baseEnd_734345 < baseStart_734345 := by decide
  rcases family_descends (prefixWord ++ tailWord_734345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734355 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 1, 3, 2]
def baseStart_734355 : Nat := 118140960795 + 734355 * 2 ^ 59
def prefixEnd_734355 : Nat := 4983230072969 + 3 ^ 40 * 734355 * 2
def baseEnd_734355 : Nat := 377077086032579566385269

theorem tailTrace_734355 : CollatzResearch.WordTrace tailWord_734355 prefixEnd_734355 377077086032579566385269 := by
  unfold tailWord_734355
  simp only [CollatzResearch.WordTrace]
  refine ⟨26784127254564727694084519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17856084836376485129389679 26784127254564727694084519)
  ·
    refine ⟨40176190881847091541126779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26784127254564727694084519 40176190881847091541126779)
    ·
      refine ⟨60264286322770637311690169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40176190881847091541126779 60264286322770637311690169)
      ·
        refine ⟨45198214742077977983767627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60264286322770637311690169 45198214742077977983767627)
        ·
          refine ⟨67797322113116966975651441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45198214742077977983767627 67797322113116966975651441)
          ·
            refine ⟨50847991584837725231738581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67797322113116966975651441 50847991584837725231738581)
            ·
              refine ⟨1191749802769634185118873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 50847991584837725231738581 1191749802769634185118873)
              ·
                refine ⟨893812352077225638839155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191749802769634185118873 893812352077225638839155)
                ·
                  refine ⟨1340718528115838458258733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893812352077225638839155 1340718528115838458258733)
                  ·
                    refine ⟨502769448043439421847025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340718528115838458258733 502769448043439421847025)
                    ·
                      refine ⟨377077086032579566385269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502769448043439421847025 377077086032579566385269)
                      ·
                        rfl

theorem cell23_734355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 3, 2].length) (baseStart_734355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734355 prefixEnd_734355 := by exact prefixLift 734355
  have htrace : WordTrace (prefixWord ++ tailWord_734355) baseStart_734355 baseEnd_734355 := by
    simpa [prefixWord, tailWord_734355, baseEnd_734355] using wordTrace_append hprefix tailTrace_734355
  have hstable : (prefixWord ++ tailWord_734355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734355).length < 2 ^ (prefixWord ++ tailWord_734355).sum := by decide
  have hdescent : baseEnd_734355 < baseStart_734355 := by decide
  rcases family_descends (prefixWord ++ tailWord_734355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734371 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 3]
def baseStart_734371 : Nat := 118140960795 + 734371 * 2 ^ 59
def prefixEnd_734371 : Nat := 4983230072969 + 3 ^ 40 * 734371 * 2
def baseEnd_734371 : Nat := 377085301723051503785195

theorem tailTrace_734371 : CollatzResearch.WordTrace tailWord_734371 prefixEnd_734371 377085301723051503785195 := by
  unfold tailWord_734371
  simp only [CollatzResearch.WordTrace]
  refine ⟨26784710822506762426666967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17856473881671174951111311 26784710822506762426666967)
  ·
    refine ⟨40177066233760143640000451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26784710822506762426666967 40177066233760143640000451)
    ·
      refine ⟨60265599350640215460000677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40177066233760143640000451 60265599350640215460000677)
      ·
        refine ⟨11299799878245040398750127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60265599350640215460000677 11299799878245040398750127)
        ·
          refine ⟨16949699817367560598125191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11299799878245040398750127 16949699817367560598125191)
          ·
            refine ⟨25424549726051340897187787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16949699817367560598125191 25424549726051340897187787)
            ·
              refine ⟨38136824589077011345781681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25424549726051340897187787 38136824589077011345781681)
              ·
                refine ⟨28602618441807758509336261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38136824589077011345781681 28602618441807758509336261)
                ·
                  refine ⟨5362990957838954720500549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28602618441807758509336261 5362990957838954720500549)
                  ·
                    refine ⟨1005560804594804010093853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362990957838954720500549 1005560804594804010093853)
                    ·
                      refine ⟨377085301723051503785195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005560804594804010093853 377085301723051503785195)
                      ·
                        rfl

theorem cell23_734371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_734371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734371 prefixEnd_734371 := by exact prefixLift 734371
  have htrace : WordTrace (prefixWord ++ tailWord_734371) baseStart_734371 baseEnd_734371 := by
    simpa [prefixWord, tailWord_734371, baseEnd_734371] using wordTrace_append hprefix tailTrace_734371
  have hstable : (prefixWord ++ tailWord_734371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734371).length < 2 ^ (prefixWord ++ tailWord_734371).sum := by decide
  have hdescent : baseEnd_734371 < baseStart_734371 := by decide
  rcases family_descends (prefixWord ++ tailWord_734371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734391 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 7]
def baseStart_734391 : Nat := 118140960795 + 734391 * 2 ^ 59
def prefixEnd_734391 : Nat := 4983230072969 + 3 ^ 40 * 734391 * 2
def baseEnd_734391 : Nat := 41899507926237936170567

theorem tailTrace_734391 : CollatzResearch.WordTrace tailWord_734391 prefixEnd_734391 41899507926237936170567 := by
  unfold tailWord_734391
  simp only [CollatzResearch.WordTrace]
  refine ⟨26785440282434305842395027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17856960188289537228263351 26785440282434305842395027)
  ·
    refine ⟨40178160423651458763592541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26785440282434305842395027 40178160423651458763592541)
    ·
      refine ⟨15066810158869297036347203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40178160423651458763592541 15066810158869297036347203)
      ·
        refine ⟨22600215238303945554520805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15066810158869297036347203 22600215238303945554520805)
        ·
          refine ⟨4237540357181989791472651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22600215238303945554520805 4237540357181989791472651)
          ·
            refine ⟨6356310535772984687208977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237540357181989791472651 6356310535772984687208977)
            ·
              refine ⟨4767232901829738515406733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6356310535772984687208977 4767232901829738515406733)
              ·
                refine ⟨1787712338186151943277525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4767232901829738515406733 1787712338186151943277525)
                ·
                  refine ⟨41899507926237936170567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1787712338186151943277525 41899507926237936170567)
                  ·
                    rfl

theorem cell23_734391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 7].length) (baseStart_734391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734391 prefixEnd_734391 := by exact prefixLift 734391
  have htrace : WordTrace (prefixWord ++ tailWord_734391) baseStart_734391 baseEnd_734391 := by
    simpa [prefixWord, tailWord_734391, baseEnd_734391] using wordTrace_append hprefix tailTrace_734391
  have hstable : (prefixWord ++ tailWord_734391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734391).length < 2 ^ (prefixWord ++ tailWord_734391).sum := by decide
  have hdescent : baseEnd_734391 < baseStart_734391 := by decide
  rcases family_descends (prefixWord ++ tailWord_734391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734398 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_734398 : Nat := 118140960795 + 734398 * 2 ^ 59
def prefixEnd_734398 : Nat := 4983230072969 + 3 ^ 40 * 734398 * 2
def baseEnd_734398 : Nat := 377099165700722898147571

theorem tailTrace_734398 : CollatzResearch.WordTrace tailWord_734398 prefixEnd_734398 377099165700722898147571 := by
  unfold tailWord_734398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348211949176118254737481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17857130395605964025266565 3348211949176118254737481)
  ·
    refine ⟨2511158961882088691053111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3348211949176118254737481 2511158961882088691053111)
    ·
      refine ⟨3766738442823133036579667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2511158961882088691053111 3766738442823133036579667)
      ·
        refine ⟨5650107664234699554869501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766738442823133036579667 5650107664234699554869501)
        ·
          refine ⟨2118790374088012333076063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5650107664234699554869501 2118790374088012333076063)
          ·
            refine ⟨3178185561132018499614095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118790374088012333076063 3178185561132018499614095)
            ·
              refine ⟨4767278341698027749421143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178185561132018499614095 4767278341698027749421143)
              ·
                refine ⟨7150917512547041624131715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767278341698027749421143 7150917512547041624131715)
                ·
                  refine ⟨10726376268820562436197573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150917512547041624131715 10726376268820562436197573)
                  ·
                    refine ⟨2011195550403855456787045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10726376268820562436197573 2011195550403855456787045)
                    ·
                      refine ⟨377099165700722898147571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2011195550403855456787045 377099165700722898147571)
                      ·
                        rfl

theorem cell23_734398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_734398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734398 prefixEnd_734398 := by exact prefixLift 734398
  have htrace : WordTrace (prefixWord ++ tailWord_734398) baseStart_734398 baseEnd_734398 := by
    simpa [prefixWord, tailWord_734398, baseEnd_734398] using wordTrace_append hprefix tailTrace_734398
  have hstable : (prefixWord ++ tailWord_734398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734398).length < 2 ^ (prefixWord ++ tailWord_734398).sum := by decide
  have hdescent : baseEnd_734398 < baseStart_734398 := by decide
  rcases family_descends (prefixWord ++ tailWord_734398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734418 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_734418 : Nat := 118140960795 + 734418 * 2 ^ 59
def prefixEnd_734418 : Nat := 4983230072969 + 3 ^ 40 * 734418 * 2
def baseEnd_734418 : Nat := 377109435313812819897479

theorem tailTrace_734418 : CollatzResearch.WordTrace tailWord_734418 prefixEnd_734418 377109435313812819897479 := by
  unfold tailWord_734418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6696606263334122363406977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17857616702224326302418605 6696606263334122363406977)
  ·
    refine ⟨5022454697500591772555233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6696606263334122363406977 5022454697500591772555233)
    ·
      refine ⟨3766841023125443829416425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5022454697500591772555233 3766841023125443829416425)
      ·
        refine ⟨2825130767344082872062319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3766841023125443829416425 2825130767344082872062319)
        ·
          refine ⟨4237696151016124308093479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825130767344082872062319 4237696151016124308093479)
          ·
            refine ⟨6356544226524186462140219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237696151016124308093479 6356544226524186462140219)
            ·
              refine ⟨9534816339786279693210329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6356544226524186462140219 9534816339786279693210329)
              ·
                refine ⟨7151112254839709769907747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9534816339786279693210329 7151112254839709769907747)
                ·
                  refine ⟨10726668382259564654861621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7151112254839709769907747 10726668382259564654861621)
                  ·
                    refine ⟨1005625160836834186393277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10726668382259564654861621 1005625160836834186393277)
                    ·
                      refine ⟨377109435313812819897479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005625160836834186393277 377109435313812819897479)
                      ·
                        rfl

theorem cell23_734418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_734418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734418 prefixEnd_734418 := by exact prefixLift 734418
  have htrace : WordTrace (prefixWord ++ tailWord_734418) baseStart_734418 baseEnd_734418 := by
    simpa [prefixWord, tailWord_734418, baseEnd_734418] using wordTrace_append hprefix tailTrace_734418
  have hstable : (prefixWord ++ tailWord_734418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734418).length < 2 ^ (prefixWord ++ tailWord_734418).sum := by decide
  have hdescent : baseEnd_734418 < baseStart_734418 := by decide
  rcases family_descends (prefixWord ++ tailWord_734418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734431 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_734431 : Nat := 118140960795 + 734431 * 2 ^ 59
def prefixEnd_734431 : Nat := 4983230072969 + 3 ^ 40 * 734431 * 2
def baseEnd_734431 : Nat := 377116110562321269034919

theorem tailTrace_734431 : CollatzResearch.WordTrace tailWord_734431 prefixEnd_734431 377116110562321269034919 := by
  unfold tailWord_734431
  simp only [CollatzResearch.WordTrace]
  refine ⟨26786899202289392673851147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17857932801526261782567431 26786899202289392673851147)
  ·
    refine ⟨40180348803434089010776721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26786899202289392673851147 40180348803434089010776721)
    ·
      refine ⟨30135261602575566758082541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40180348803434089010776721 30135261602575566758082541)
      ·
        refine ⟨11300723100965837534280953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30135261602575566758082541 11300723100965837534280953)
        ·
          refine ⟨8475542325724378150710715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11300723100965837534280953 8475542325724378150710715)
          ·
            refine ⟨12713313488586567226066073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8475542325724378150710715 12713313488586567226066073)
            ·
              refine ⟨9534985116439925419549555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12713313488586567226066073 9534985116439925419549555)
              ·
                refine ⟨14302477674659888129324333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534985116439925419549555 14302477674659888129324333)
                ·
                  refine ⟨5363429127997458048496625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14302477674659888129324333 5363429127997458048496625)
                  ·
                    refine ⟨4022571845998093536372469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363429127997458048496625 4022571845998093536372469)
                    ·
                      refine ⟨377116110562321269034919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4022571845998093536372469 377116110562321269034919)
                      ·
                        rfl

theorem cell23_734431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_734431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734431 prefixEnd_734431 := by exact prefixLift 734431
  have htrace : WordTrace (prefixWord ++ tailWord_734431) baseStart_734431 baseEnd_734431 := by
    simpa [prefixWord, tailWord_734431, baseEnd_734431] using wordTrace_append hprefix tailTrace_734431
  have hstable : (prefixWord ++ tailWord_734431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734431).length < 2 ^ (prefixWord ++ tailWord_734431).sum := by decide
  have hdescent : baseEnd_734431 < baseStart_734431 := by decide
  rcases family_descends (prefixWord ++ tailWord_734431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734441 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_734441 : Nat := 118140960795 + 734441 * 2 ^ 59
def prefixEnd_734441 : Nat := 4983230072969 + 3 ^ 40 * 734441 * 2
def baseEnd_734441 : Nat := 377121245368866229909873

theorem tailTrace_734441 : CollatzResearch.WordTrace tailWord_734441 prefixEnd_734441 377121245368866229909873 := by
  unfold tailWord_734441
  simp only [CollatzResearch.WordTrace]
  refine ⟨26787263932253164381715177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17858175954835442921143451 26787263932253164381715177)
  ·
    refine ⟨20090447949189873286286383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26787263932253164381715177 20090447949189873286286383)
    ·
      refine ⟨30135671923784809929429575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20090447949189873286286383 30135671923784809929429575)
      ·
        refine ⟨45203507885677214894144363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30135671923784809929429575 45203507885677214894144363)
        ·
          refine ⟨67805261828515822341216545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45203507885677214894144363 67805261828515822341216545)
          ·
            refine ⟨50853946371386866755912409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67805261828515822341216545 50853946371386866755912409)
            ·
              refine ⟨38140459778540150066934307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50853946371386866755912409 38140459778540150066934307)
              ·
                refine ⟨57210689667810225100401461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38140459778540150066934307 57210689667810225100401461)
                ·
                  refine ⟨5363502156357208603162637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57210689667810225100401461 5363502156357208603162637)
                  ·
                    refine ⟨2011313308633953226185989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5363502156357208603162637 2011313308633953226185989)
                    ·
                      refine ⟨377121245368866229909873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2011313308633953226185989 377121245368866229909873)
                      ·
                        rfl

theorem cell23_734441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_734441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734441 prefixEnd_734441 := by exact prefixLift 734441
  have htrace : WordTrace (prefixWord ++ tailWord_734441) baseStart_734441 baseEnd_734441 := by
    simpa [prefixWord, tailWord_734441, baseEnd_734441] using wordTrace_append hprefix tailTrace_734441
  have hstable : (prefixWord ++ tailWord_734441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734441).length < 2 ^ (prefixWord ++ tailWord_734441).sum := by decide
  have hdescent : baseEnd_734441 < baseStart_734441 := by decide
  rcases family_descends (prefixWord ++ tailWord_734441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734481 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 10]
def baseStart_734481 : Nat := 118140960795 + 734481 * 2 ^ 59
def prefixEnd_734481 : Nat := 4983230072969 + 3 ^ 40 * 734481 * 2
def baseEnd_734481 : Nat := 41904642732782897045521

theorem tailTrace_734481 : CollatzResearch.WordTrace tailWord_734481 prefixEnd_734481 41904642732782897045521 := by
  unfold tailWord_734481
  simp only [CollatzResearch.WordTrace]
  refine ⟨26788722852108251213171297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17859148568072167475447531 26788722852108251213171297)
  ·
    refine ⟨20091542139081188409878473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26788722852108251213171297 20091542139081188409878473)
    ·
      refine ⟨15068656604310891307408855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20091542139081188409878473 15068656604310891307408855)
      ·
        refine ⟨22602984906466336961113283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068656604310891307408855 22602984906466336961113283)
        ·
          refine ⟨33904477359699505441669925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22602984906466336961113283 33904477359699505441669925)
          ·
            refine ⟨6357089504943657270313111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33904477359699505441669925 6357089504943657270313111)
            ·
              refine ⟨9535634257415485905469667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6357089504943657270313111 9535634257415485905469667)
              ·
                refine ⟨14303451386123228858204501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9535634257415485905469667 14303451386123228858204501)
                ·
                  refine ⟨41904642732782897045521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14303451386123228858204501 41904642732782897045521)
                  ·
                    rfl

theorem cell23_734481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 10].length) (baseStart_734481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734481 prefixEnd_734481 := by exact prefixLift 734481
  have htrace : WordTrace (prefixWord ++ tailWord_734481) baseStart_734481 baseEnd_734481 := by
    simpa [prefixWord, tailWord_734481, baseEnd_734481] using wordTrace_append hprefix tailTrace_734481
  have hstable : (prefixWord ++ tailWord_734481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734481).length < 2 ^ (prefixWord ++ tailWord_734481).sum := by decide
  have hdescent : baseEnd_734481 < baseStart_734481 := by decide
  rcases family_descends (prefixWord ++ tailWord_734481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734511 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 9]
def baseStart_734511 : Nat := 118140960795 + 734511 * 2 ^ 59
def prefixEnd_734511 : Nat := 4983230072969 + 3 ^ 40 * 734511 * 2
def baseEnd_734511 : Nat := 125719063004893652011517

theorem tailTrace_734511 : CollatzResearch.WordTrace tailWord_734511 prefixEnd_734511 125719063004893652011517 := by
  unfold tailWord_734511
  simp only [CollatzResearch.WordTrace]
  refine ⟨26789817041999566336763387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17859878027999710891175591 26789817041999566336763387)
  ·
    refine ⟨40184725562999349505145081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26789817041999566336763387 40184725562999349505145081)
    ·
      refine ⟨30138544172249512128858811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40184725562999349505145081 30138544172249512128858811)
      ·
        refine ⟨45207816258374268193288217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30138544172249512128858811 45207816258374268193288217)
        ·
          refine ⟨33905862193780701144966163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45207816258374268193288217 33905862193780701144966163)
          ·
            refine ⟨50858793290671051717449245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33905862193780701144966163 50858793290671051717449245)
            ·
              refine ⟨19072047484001644394043467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50858793290671051717449245 19072047484001644394043467)
              ·
                refine ⟨28608071226002466591065201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19072047484001644394043467 28608071226002466591065201)
                ·
                  refine ⟨21456053419501849943298901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28608071226002466591065201 21456053419501849943298901)
                  ·
                    refine ⟨125719063004893652011517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 21456053419501849943298901 125719063004893652011517)
                    ·
                      rfl

theorem cell23_734511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_734511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734511 prefixEnd_734511 := by exact prefixLift 734511
  have htrace : WordTrace (prefixWord ++ tailWord_734511) baseStart_734511 baseEnd_734511 := by
    simpa [prefixWord, tailWord_734511, baseEnd_734511] using wordTrace_append hprefix tailTrace_734511
  have hstable : (prefixWord ++ tailWord_734511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734511).length < 2 ^ (prefixWord ++ tailWord_734511).sum := by decide
  have hdescent : baseEnd_734511 < baseStart_734511 := by decide
  rcases family_descends (prefixWord ++ tailWord_734511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734515 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 6]
def baseStart_734515 : Nat := 118140960795 + 734515 * 2 ^ 59
def prefixEnd_734515 : Nat := 4983230072969 + 3 ^ 40 * 734515 * 2
def baseEnd_734515 : Nat := 41906582548588771153837

theorem tailTrace_734515 : CollatzResearch.WordTrace tailWord_734515 prefixEnd_734515 41906582548588771153837 := by
  unfold tailWord_734515
  simp only [CollatzResearch.WordTrace]
  refine ⟨26789962933985075019908999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17859975289323383346605999 26789962933985075019908999)
  ·
    refine ⟨40184944400977612529863499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26789962933985075019908999 40184944400977612529863499)
    ·
      refine ⟨60277416601466418794795249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40184944400977612529863499 60277416601466418794795249)
      ·
        refine ⟨45208062451099814096096437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60277416601466418794795249 45208062451099814096096437)
        ·
          refine ⟨4238255854790607571509041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45208062451099814096096437 4238255854790607571509041)
          ·
            refine ⟨3178691891092955678631781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238255854790607571509041 3178691891092955678631781)
            ·
              refine ⟨596004729579929189743459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3178691891092955678631781 596004729579929189743459)
              ·
                refine ⟨894007094369893784615189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596004729579929189743459 894007094369893784615189)
                ·
                  refine ⟨41906582548588771153837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 894007094369893784615189 41906582548588771153837)
                  ·
                    rfl

theorem cell23_734515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 6].length) (baseStart_734515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734515 prefixEnd_734515 := by exact prefixLift 734515
  have htrace : WordTrace (prefixWord ++ tailWord_734515) baseStart_734515 baseEnd_734515 := by
    simpa [prefixWord, tailWord_734515, baseEnd_734515] using wordTrace_append hprefix tailTrace_734515
  have hstable : (prefixWord ++ tailWord_734515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734515).length < 2 ^ (prefixWord ++ tailWord_734515).sum := by decide
  have hdescent : baseEnd_734515 < baseStart_734515 := by decide
  rcases family_descends (prefixWord ++ tailWord_734515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734528 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 3, 5]
def baseStart_734528 : Nat := 118140960795 + 734528 * 2 ^ 59
def prefixEnd_734528 : Nat := 4983230072969 + 3 ^ 40 * 734528 * 2
def baseEnd_734528 : Nat := 125721972728602463173991

theorem tailTrace_734528 : CollatzResearch.WordTrace tailWord_734528 prefixEnd_734528 125721972728602463173991 := by
  unfold tailWord_734528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13395218541468989120066119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17860291388625318826754825 13395218541468989120066119)
  ·
    refine ⟨20092827812203483680099179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13395218541468989120066119 20092827812203483680099179)
    ·
      refine ⟨30139241718305225520148769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20092827812203483680099179 30139241718305225520148769)
      ·
        refine ⟨22604431288728919140111577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30139241718305225520148769 22604431288728919140111577)
        ·
          refine ⟨16953323466546689355083683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22604431288728919140111577 16953323466546689355083683)
          ·
            refine ⟨25429985199820034032625525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16953323466546689355083683 25429985199820034032625525)
            ·
              refine ⟨2384061112483128190558643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25429985199820034032625525 2384061112483128190558643)
              ·
                refine ⟨3576091668724692285837965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384061112483128190558643 3576091668724692285837965)
                ·
                  refine ⟨1341034375771759607189237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3576091668724692285837965 1341034375771759607189237)
                  ·
                    refine ⟨125721972728602463173991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1341034375771759607189237 125721972728602463173991)
                    ·
                      rfl

theorem cell23_734528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_734528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734528 prefixEnd_734528 := by exact prefixLift 734528
  have htrace : WordTrace (prefixWord ++ tailWord_734528) baseStart_734528 baseEnd_734528 := by
    simpa [prefixWord, tailWord_734528, baseEnd_734528] using wordTrace_append hprefix tailTrace_734528
  have hstable : (prefixWord ++ tailWord_734528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734528).length < 2 ^ (prefixWord ++ tailWord_734528).sum := by decide
  have hdescent : baseEnd_734528 < baseStart_734528 := by decide
  rcases family_descends (prefixWord ++ tailWord_734528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734575 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 2, 4]
def baseStart_734575 : Nat := 118140960795 + 734575 * 2 ^ 59
def prefixEnd_734575 : Nat := 4983230072969 + 3 ^ 40 * 734575 * 2
def baseEnd_734575 : Nat := 125730017258856235211419

theorem tailTrace_734575 : CollatzResearch.WordTrace tailWord_734575 prefixEnd_734575 125730017258856235211419 := by
  unfold tailWord_734575
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792151313767705267093179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17861434209178470178062119 26792151313767705267093179)
  ·
    refine ⟨40188226970651557900639769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26792151313767705267093179 40188226970651557900639769)
    ·
      refine ⟨30141170227988668425479827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40188226970651557900639769 30141170227988668425479827)
      ·
        refine ⟨45211755341983002638219741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30141170227988668425479827 45211755341983002638219741)
        ·
          refine ⟨16954408253243625989332403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45211755341983002638219741 16954408253243625989332403)
          ·
            refine ⟨25431612379865438983998605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16954408253243625989332403 25431612379865438983998605)
            ·
              refine ⟨9536854642449539618999477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25431612379865438983998605 9536854642449539618999477)
              ·
                refine ⟨894080122729644339281201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9536854642449539618999477 894080122729644339281201)
                ·
                  refine ⟨670560092047233254460901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894080122729644339281201 670560092047233254460901)
                  ·
                    refine ⟨125730017258856235211419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670560092047233254460901 125730017258856235211419)
                    ·
                      rfl

theorem cell23_734575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_734575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734575 prefixEnd_734575 := by exact prefixLift 734575
  have htrace : WordTrace (prefixWord ++ tailWord_734575) baseStart_734575 baseEnd_734575 := by
    simpa [prefixWord, tailWord_734575, baseEnd_734575] using wordTrace_append hprefix tailTrace_734575
  have hstable : (prefixWord ++ tailWord_734575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734575).length < 2 ^ (prefixWord ++ tailWord_734575).sum := by decide
  have hdescent : baseEnd_734575 < baseStart_734575 := by decide
  rcases family_descends (prefixWord ++ tailWord_734575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734585 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 3]
def baseStart_734585 : Nat := 118140960795 + 734585 * 2 ^ 59
def prefixEnd_734585 : Nat := 4983230072969 + 3 ^ 40 * 734585 * 2
def baseEnd_734585 : Nat := 377195186583113666509211

theorem tailTrace_734585 : CollatzResearch.WordTrace tailWord_734585 prefixEnd_734585 377195186583113666509211 := by
  unfold tailWord_734585
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792516043731476974957209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17861677362487651316638139 26792516043731476974957209)
  ·
    refine ⟨20094387032798607731217907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26792516043731476974957209 20094387032798607731217907)
    ·
      refine ⟨30141580549197911596826861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20094387032798607731217907 30141580549197911596826861)
      ·
        refine ⟨11303092705949216848810073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30141580549197911596826861 11303092705949216848810073)
        ·
          refine ⟨8477319529461912636607555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11303092705949216848810073 8477319529461912636607555)
          ·
            refine ⟨12715979294192868954911333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8477319529461912636607555 12715979294192868954911333)
            ·
              refine ⟨2384246117661162929045875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12715979294192868954911333 2384246117661162929045875)
              ·
                refine ⟨3576369176491744393568813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384246117661162929045875 3576369176491744393568813)
                ·
                  refine ⟨1341138441184404147588305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3576369176491744393568813 1341138441184404147588305)
                  ·
                    refine ⟨1005853830888303110691229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1341138441184404147588305 1005853830888303110691229)
                    ·
                      refine ⟨377195186583113666509211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005853830888303110691229 377195186583113666509211)
                      ·
                        rfl

theorem cell23_734585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_734585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734585 prefixEnd_734585 := by exact prefixLift 734585
  have htrace : WordTrace (prefixWord ++ tailWord_734585) baseStart_734585 baseEnd_734585 := by
    simpa [prefixWord, tailWord_734585, baseEnd_734585] using wordTrace_append hprefix tailTrace_734585
  have hstable : (prefixWord ++ tailWord_734585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734585).length < 2 ^ (prefixWord ++ tailWord_734585).sum := by decide
  have hdescent : baseEnd_734585 < baseStart_734585 := by decide
  rcases family_descends (prefixWord ++ tailWord_734585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734595 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4]
def baseStart_734595 : Nat := 118140960795 + 734595 * 2 ^ 59
def prefixEnd_734595 : Nat := 4983230072969 + 3 ^ 40 * 734595 * 2
def baseEnd_734595 : Nat := 377200321389658627384165

theorem tailTrace_734595 : CollatzResearch.WordTrace tailWord_734595 prefixEnd_734595 377200321389658627384165 := by
  unfold tailWord_734595
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792880773695248682821239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17861920515796832455214159 26792880773695248682821239)
  ·
    refine ⟨40189321160542873024231859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26792880773695248682821239 40189321160542873024231859)
    ·
      refine ⟨60283981740814309536347789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40189321160542873024231859 60283981740814309536347789)
      ·
        refine ⟨22606493152805366076130421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60283981740814309536347789 22606493152805366076130421)
        ·
          refine ⟨2119358733075503069637227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22606493152805366076130421 2119358733075503069637227)
          ·
            refine ⟨3179038099613254604455841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119358733075503069637227 3179038099613254604455841)
            ·
              refine ⟨2384278574709940953341881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179038099613254604455841 2384278574709940953341881)
              ·
                refine ⟨1788208931032455715006411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384278574709940953341881 1788208931032455715006411)
                ·
                  refine ⟨2682313396548683572509617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788208931032455715006411 2682313396548683572509617)
                  ·
                    refine ⟨2011735047411512679382213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682313396548683572509617 2011735047411512679382213)
                    ·
                      refine ⟨377200321389658627384165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2011735047411512679382213 377200321389658627384165)
                      ·
                        rfl

theorem cell23_734595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_734595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734595 prefixEnd_734595 := by exact prefixLift 734595
  have htrace : WordTrace (prefixWord ++ tailWord_734595) baseStart_734595 baseEnd_734595 := by
    simpa [prefixWord, tailWord_734595, baseEnd_734595] using wordTrace_append hprefix tailTrace_734595
  have hstable : (prefixWord ++ tailWord_734595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734595).length < 2 ^ (prefixWord ++ tailWord_734595).sum := by decide
  have hdescent : baseEnd_734595 < baseStart_734595 := by decide
  rcases family_descends (prefixWord ++ tailWord_734595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734599 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_734599 : Nat := 118140960795 + 734599 * 2 ^ 59
def prefixEnd_734599 : Nat := 4983230072969 + 3 ^ 40 * 734599 * 2
def baseEnd_734599 : Nat := 377202375312276611734147

theorem tailTrace_734599 : CollatzResearch.WordTrace tailWord_734599 prefixEnd_734599 377202375312276611734147 := by
  unfold tailWord_734599
  simp only [CollatzResearch.WordTrace]
  refine ⟨26793026665680757365966851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17862017777120504910644567 26793026665680757365966851)
  ·
    refine ⟨40189539998521136048950277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26793026665680757365966851 40189539998521136048950277)
    ·
      refine ⟨7535538749722713009178177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40189539998521136048950277 7535538749722713009178177)
      ·
        refine ⟨5651654062292034756883633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7535538749722713009178177 5651654062292034756883633)
        ·
          refine ⟨4238740546719026067662725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5651654062292034756883633 4238740546719026067662725)
          ·
            refine ⟨794763852509817387686761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4238740546719026067662725 794763852509817387686761)
            ·
              refine ⟨596072889382363040765071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794763852509817387686761 596072889382363040765071)
              ·
                refine ⟨894109334073544561147607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596072889382363040765071 894109334073544561147607)
                ·
                  refine ⟨1341164001110316841721411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894109334073544561147607 1341164001110316841721411)
                  ·
                    refine ⟨2011746001665475262582117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1341164001110316841721411 2011746001665475262582117)
                    ·
                      refine ⟨377202375312276611734147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2011746001665475262582117 377202375312276611734147)
                      ·
                        rfl

theorem cell23_734599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_734599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734599 prefixEnd_734599 := by exact prefixLift 734599
  have htrace : WordTrace (prefixWord ++ tailWord_734599) baseStart_734599 baseEnd_734599 := by
    simpa [prefixWord, tailWord_734599, baseEnd_734599] using wordTrace_append hprefix tailTrace_734599
  have hstable : (prefixWord ++ tailWord_734599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734599).length < 2 ^ (prefixWord ++ tailWord_734599).sum := by decide
  have hdescent : baseEnd_734599 < baseStart_734599 := by decide
  rcases family_descends (prefixWord ++ tailWord_734599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734616 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 3, 2, 2]
def baseStart_734616 : Nat := 118140960795 + 734616 * 2 ^ 59
def prefixEnd_734616 : Nat := 4983230072969 + 3 ^ 40 * 734616 * 2
def baseEnd_734616 : Nat := 377211104483403045221569

theorem tailTrace_734616 : CollatzResearch.WordTrace tailWord_734616 prefixEnd_734616 377211104483403045221569 := by
  unfold tailWord_734616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13396823353309584634667851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17862431137746112846223801 13396823353309584634667851)
  ·
    refine ⟨20095235029964376952001777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13396823353309584634667851 20095235029964376952001777)
    ·
      refine ⟨15071426272473282714001333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20095235029964376952001777 15071426272473282714001333)
      ·
        refine ⟨1412946213044370254437625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15071426272473282714001333 1412946213044370254437625)
        ·
          refine ⟨1059709659783277690828219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1412946213044370254437625 1059709659783277690828219)
          ·
            refine ⟨1589564489674916536242329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059709659783277690828219 1589564489674916536242329)
            ·
              refine ⟨1192173367256187402181747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589564489674916536242329 1192173367256187402181747)
              ·
                refine ⟨1788260050884281103272621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192173367256187402181747 1788260050884281103272621)
                ·
                  refine ⟨670597519081605413727233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1788260050884281103272621 670597519081605413727233)
                  ·
                    refine ⟨502948139311204060295425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 670597519081605413727233 502948139311204060295425)
                    ·
                      refine ⟨377211104483403045221569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502948139311204060295425 377211104483403045221569)
                      ·
                        rfl

theorem cell23_734616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_734616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734616 prefixEnd_734616 := by exact prefixLift 734616
  have htrace : WordTrace (prefixWord ++ tailWord_734616) baseStart_734616 baseEnd_734616 := by
    simpa [prefixWord, tailWord_734616, baseEnd_734616] using wordTrace_append hprefix tailTrace_734616
  have hstable : (prefixWord ++ tailWord_734616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734616).length < 2 ^ (prefixWord ++ tailWord_734616).sum := by decide
  have hdescent : baseEnd_734616 < baseStart_734616 := by decide
  rcases family_descends (prefixWord ++ tailWord_734616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734645 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_734645 : Nat := 118140960795 + 734645 * 2 ^ 59
def prefixEnd_734645 : Nat := 4983230072969 + 3 ^ 40 * 734645 * 2
def baseEnd_734645 : Nat := 377225995422383431758935

theorem tailTrace_734645 : CollatzResearch.WordTrace tailWord_734645 prefixEnd_734645 377225995422383431758935 := by
  unfold tailWord_734645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26794704423514107222141389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17863136282342738148094259 26794704423514107222141389)
  ·
    refine ⟨10048014158817790208303021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26794704423514107222141389 10048014158817790208303021)
    ·
      refine ⟨3768005309556671328113633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10048014158817790208303021 3768005309556671328113633)
      ·
        refine ⟨2826003982167503496085225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3768005309556671328113633 2826003982167503496085225)
        ·
          refine ⟨2119502986625627622063919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826003982167503496085225 2119502986625627622063919)
          ·
            refine ⟨3179254479938441433095879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119502986625627622063919 3179254479938441433095879)
            ·
              refine ⟨4768881719907662149643819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179254479938441433095879 4768881719907662149643819)
              ·
                refine ⟨7153322579861493224465729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768881719907662149643819 7153322579861493224465729)
                ·
                  refine ⟨5364991934896119918349297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7153322579861493224465729 5364991934896119918349297)
                  ·
                    refine ⟨4023743951172089938761973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5364991934896119918349297 4023743951172089938761973)
                    ·
                      refine ⟨377225995422383431758935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4023743951172089938761973 377225995422383431758935)
                      ·
                        rfl

theorem cell23_734645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_734645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734645 prefixEnd_734645 := by exact prefixLift 734645
  have htrace : WordTrace (prefixWord ++ tailWord_734645) baseStart_734645 baseEnd_734645 := by
    simpa [prefixWord, tailWord_734645, baseEnd_734645] using wordTrace_append hprefix tailTrace_734645
  have hstable : (prefixWord ++ tailWord_734645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734645).length < 2 ^ (prefixWord ++ tailWord_734645).sum := by decide
  have hdescent : baseEnd_734645 < baseStart_734645 := by decide
  rcases family_descends (prefixWord ++ tailWord_734645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734648 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 1, 8]
def baseStart_734648 : Nat := 118140960795 + 734648 * 2 ^ 59
def prefixEnd_734648 : Nat := 4983230072969 + 3 ^ 40 * 734648 * 2
def baseEnd_734648 : Nat := 125742511954782306673807

theorem tailTrace_734648 : CollatzResearch.WordTrace tailWord_734648 prefixEnd_734648 125742511954782306673807 := by
  unfold tailWord_734648
  simp only [CollatzResearch.WordTrace]
  refine ⟨13397406921251619367250299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17863209228335492489667065 13397406921251619367250299)
  ·
    refine ⟨20096110381877429050875449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13397406921251619367250299 20096110381877429050875449)
    ·
      refine ⟨15072082786408071788156587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20096110381877429050875449 15072082786408071788156587)
      ·
        refine ⟨22608124179612107682234881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15072082786408071788156587 22608124179612107682234881)
        ·
          refine ⟨16956093134709080761676161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22608124179612107682234881 16956093134709080761676161)
          ·
            refine ⟨12717069851031810571257121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16956093134709080761676161 12717069851031810571257121)
            ·
              refine ⟨9537802388273857928442841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12717069851031810571257121 9537802388273857928442841)
              ·
                refine ⟨7153351791205393446332131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9537802388273857928442841 7153351791205393446332131)
                ·
                  refine ⟨10730027686808090169498197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7153351791205393446332131 10730027686808090169498197)
                  ·
                    refine ⟨125742511954782306673807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10730027686808090169498197 125742511954782306673807)
                    ·
                      rfl

theorem cell23_734648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_734648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734648 prefixEnd_734648 := by exact prefixLift 734648
  have htrace : WordTrace (prefixWord ++ tailWord_734648) baseStart_734648 baseEnd_734648 := by
    simpa [prefixWord, tailWord_734648, baseEnd_734648] using wordTrace_append hprefix tailTrace_734648
  have hstable : (prefixWord ++ tailWord_734648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734648).length < 2 ^ (prefixWord ++ tailWord_734648).sum := by decide
  have hdescent : baseEnd_734648 < baseStart_734648 := by decide
  rcases family_descends (prefixWord ++ tailWord_734648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734762 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_734762 : Nat := 118140960795 + 734762 * 2 ^ 59
def prefixEnd_734762 : Nat := 4983230072969 + 3 ^ 40 * 734762 * 2
def baseEnd_734762 : Nat := 377286072658959473995897

theorem tailTrace_734762 : CollatzResearch.WordTrace tailWord_734762 prefixEnd_734762 377286072658959473995897 := by
  unfold tailWord_734762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699742941022559051037635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17865981176060157469433693 6699742941022559051037635)
  ·
    refine ⟨10049614411533838576556453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6699742941022559051037635 10049614411533838576556453)
    ·
      refine ⟨1884302702162594733104335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10049614411533838576556453 1884302702162594733104335)
      ·
        refine ⟨2826454053243892099656503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884302702162594733104335 2826454053243892099656503)
        ·
          refine ⟨4239681079865838149484755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826454053243892099656503 4239681079865838149484755)
          ·
            refine ⟨6359521619798757224227133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239681079865838149484755 6359521619798757224227133)
            ·
              refine ⟨2384820607424533959085175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6359521619798757224227133 2384820607424533959085175)
              ·
                refine ⟨3577230911136800938627763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384820607424533959085175 3577230911136800938627763)
                ·
                  refine ⟨5365846366705201407941645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577230911136800938627763 5365846366705201407941645)
                  ·
                    refine ⟨2012192387514450527978117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5365846366705201407941645 2012192387514450527978117)
                    ·
                      refine ⟨377286072658959473995897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2012192387514450527978117 377286072658959473995897)
                      ·
                        rfl

theorem cell23_734762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_734762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734762 prefixEnd_734762 := by exact prefixLift 734762
  have htrace : WordTrace (prefixWord ++ tailWord_734762) baseStart_734762 baseEnd_734762 := by
    simpa [prefixWord, tailWord_734762, baseEnd_734762] using wordTrace_append hprefix tailTrace_734762
  have hstable : (prefixWord ++ tailWord_734762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734762).length < 2 ^ (prefixWord ++ tailWord_734762).sum := by decide
  have hdescent : baseEnd_734762 < baseStart_734762 := by decide
  rcases family_descends (prefixWord ++ tailWord_734762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734775 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_734775 : Nat := 118140960795 + 734775 * 2 ^ 59
def prefixEnd_734775 : Nat := 4983230072969 + 3 ^ 40 * 734775 * 2
def baseEnd_734775 : Nat := 377292747907467923133337

theorem tailTrace_734775 : CollatzResearch.WordTrace tailWord_734775 prefixEnd_734775 377292747907467923133337 := by
  unfold tailWord_734775
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799445913043139424373779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17866297275362092949582519 26799445913043139424373779)
  ·
    refine ⟨40199168869564709136560669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26799445913043139424373779 40199168869564709136560669)
    ·
      refine ⟨15074688326086765926210251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40199168869564709136560669 15074688326086765926210251)
      ·
        refine ⟨22612032489130148889315377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15074688326086765926210251 22612032489130148889315377)
        ·
          refine ⟨16959024366847611666986533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22612032489130148889315377 16959024366847611666986533)
          ·
            refine ⟨3179817068783927187559975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16959024366847611666986533 3179817068783927187559975)
            ·
              refine ⟨4769725603175890781339963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179817068783927187559975 4769725603175890781339963)
              ·
                refine ⟨7154588404763836172009945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769725603175890781339963 7154588404763836172009945)
                ·
                  refine ⟨5365941303572877129007459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7154588404763836172009945 5365941303572877129007459)
                  ·
                    refine ⟨8048911955359315693511189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365941303572877129007459 8048911955359315693511189)
                    ·
                      refine ⟨377292747907467923133337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8048911955359315693511189 377292747907467923133337)
                      ·
                        rfl

theorem cell23_734775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_734775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734775 prefixEnd_734775 := by exact prefixLift 734775
  have htrace : WordTrace (prefixWord ++ tailWord_734775) baseStart_734775 baseEnd_734775 := by
    simpa [prefixWord, tailWord_734775, baseEnd_734775] using wordTrace_append hprefix tailTrace_734775
  have hstable : (prefixWord ++ tailWord_734775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734775).length < 2 ^ (prefixWord ++ tailWord_734775).sum := by decide
  have hdescent : baseEnd_734775 < baseStart_734775 := by decide
  rcases family_descends (prefixWord ++ tailWord_734775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734789 : List Nat := [1, 3, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_734789 : Nat := 118140960795 + 734789 * 2 ^ 59
def prefixEnd_734789 : Nat := 4983230072969 + 3 ^ 40 * 734789 * 2
def baseEnd_734789 : Nat := 125766645545543622786091

theorem tailTrace_734789 : CollatzResearch.WordTrace tailWord_734789 prefixEnd_734789 125766645545543622786091 := by
  unfold tailWord_734789
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799956534992419815383421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17866637689994946543588947 26799956534992419815383421)
  ·
    refine ⟨10049983700622157430768783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26799956534992419815383421 10049983700622157430768783)
    ·
      refine ⟨15074975550933236146153175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10049983700622157430768783 15074975550933236146153175)
      ·
        refine ⟨22612463326399854219229763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15074975550933236146153175 22612463326399854219229763)
        ·
          refine ⟨33918694989599781328844645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22612463326399854219229763 33918694989599781328844645)
          ·
            refine ⟨6359755310549958999158371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33918694989599781328844645 6359755310549958999158371)
            ·
              refine ⟨9539632965824938498737557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359755310549958999158371 9539632965824938498737557)
              ·
                refine ⟨447170295273043992128323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9539632965824938498737557 447170295273043992128323)
                ·
                  refine ⟨670755442909565988192485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447170295273043992128323 670755442909565988192485)
                  ·
                    refine ⟨125766645545543622786091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670755442909565988192485 125766645545543622786091)
                    ·
                      rfl

theorem cell23_734789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_734789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734789 prefixEnd_734789 := by exact prefixLift 734789
  have htrace : WordTrace (prefixWord ++ tailWord_734789) baseStart_734789 baseEnd_734789 := by
    simpa [prefixWord, tailWord_734789, baseEnd_734789] using wordTrace_append hprefix tailTrace_734789
  have hstable : (prefixWord ++ tailWord_734789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734789).length < 2 ^ (prefixWord ++ tailWord_734789).sum := by decide
  have hdescent : baseEnd_734789 < baseStart_734789 := by decide
  rcases family_descends (prefixWord ++ tailWord_734789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734805 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_734805 : Nat := 118140960795 + 734805 * 2 ^ 59
def prefixEnd_734805 : Nat := 4983230072969 + 3 ^ 40 * 734805 * 2
def baseEnd_734805 : Nat := 377308152327102805758199

theorem tailTrace_734805 : CollatzResearch.WordTrace tailWord_734805 prefixEnd_734805 377308152327102805758199 := by
  unfold tailWord_734805
  simp only [CollatzResearch.WordTrace]
  refine ⟨26800540102934454547965869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17867026735289636365310579 26800540102934454547965869)
  ·
    refine ⟨10050202538600420455487201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26800540102934454547965869 10050202538600420455487201)
    ·
      refine ⟨7537651903950315341615401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10050202538600420455487201 7537651903950315341615401)
      ·
        refine ⟨5653238927962736506211551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7537651903950315341615401 5653238927962736506211551)
        ·
          refine ⟨8479858391944104759317327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5653238927962736506211551 8479858391944104759317327)
          ·
            refine ⟨12719787587916157138975991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8479858391944104759317327 12719787587916157138975991)
            ·
              refine ⟨19079681381874235708463987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12719787587916157138975991 19079681381874235708463987)
              ·
                refine ⟨28619522072811353562695981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19079681381874235708463987 28619522072811353562695981)
                ·
                  refine ⟨10732320777304257586010993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28619522072811353562695981 10732320777304257586010993)
                  ·
                    refine ⟨8049240582978193189508245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10732320777304257586010993 8049240582978193189508245)
                    ·
                      refine ⟨377308152327102805758199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8049240582978193189508245 377308152327102805758199)
                      ·
                        rfl

theorem cell23_734805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_734805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734805 prefixEnd_734805 := by exact prefixLift 734805
  have htrace : WordTrace (prefixWord ++ tailWord_734805) baseStart_734805 baseEnd_734805 := by
    simpa [prefixWord, tailWord_734805, baseEnd_734805] using wordTrace_append hprefix tailTrace_734805
  have hstable : (prefixWord ++ tailWord_734805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734805).length < 2 ^ (prefixWord ++ tailWord_734805).sum := by decide
  have hdescent : baseEnd_734805 < baseStart_734805 := by decide
  rcases family_descends (prefixWord ++ tailWord_734805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734835 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4]
def baseStart_734835 : Nat := 118140960795 + 734835 * 2 ^ 59
def prefixEnd_734835 : Nat := 4983230072969 + 3 ^ 40 * 734835 * 2
def baseEnd_734835 : Nat := 377323556746737688383061

theorem tailTrace_734835 : CollatzResearch.WordTrace tailWord_734835 prefixEnd_734835 377323556746737688383061 := by
  unfold tailWord_734835
  simp only [CollatzResearch.WordTrace]
  refine ⟨26801634292825769671557959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17867756195217179781038639 26801634292825769671557959)
  ·
    refine ⟨40202451439238654507336939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26801634292825769671557959 40202451439238654507336939)
    ·
      refine ⟨60303677158857981761005409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40202451439238654507336939 60303677158857981761005409)
      ·
        refine ⟨45227757869143486320754057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60303677158857981761005409 45227757869143486320754057)
        ·
          refine ⟨33920818401857614740565543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45227757869143486320754057 33920818401857614740565543)
          ·
            refine ⟨50881227602786422110848315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33920818401857614740565543 50881227602786422110848315)
            ·
              refine ⟨76321841404179633166272473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50881227602786422110848315 76321841404179633166272473)
              ·
                refine ⟨57241381053134724874704355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76321841404179633166272473 57241381053134724874704355)
                ·
                  refine ⟨85862071579702087312056533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57241381053134724874704355 85862071579702087312056533)
                  ·
                    refine ⟨2012392302649267671376325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 85862071579702087312056533 2012392302649267671376325)
                    ·
                      refine ⟨377323556746737688383061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2012392302649267671376325 377323556746737688383061)
                      ·
                        rfl

theorem cell23_734835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_734835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734835 prefixEnd_734835 := by exact prefixLift 734835
  have htrace : WordTrace (prefixWord ++ tailWord_734835) baseStart_734835 baseEnd_734835 := by
    simpa [prefixWord, tailWord_734835, baseEnd_734835] using wordTrace_append hprefix tailTrace_734835
  have hstable : (prefixWord ++ tailWord_734835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734835).length < 2 ^ (prefixWord ++ tailWord_734835).sum := by decide
  have hdescent : baseEnd_734835 < baseStart_734835 := by decide
  rcases family_descends (prefixWord ++ tailWord_734835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734919 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_734919 : Nat := 118140960795 + 734919 * 2 ^ 59
def prefixEnd_734919 : Nat := 4983230072969 + 3 ^ 40 * 734919 * 2
def baseEnd_734919 : Nat := 377366689121715359732675

theorem tailTrace_734919 : CollatzResearch.WordTrace tailWord_734919 prefixEnd_734919 377366689121715359732675 := by
  unfold tailWord_734919
  simp only [CollatzResearch.WordTrace]
  refine ⟨26804698024521452017615811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17869798683014301345077207 26804698024521452017615811)
  ·
    refine ⟨40207047036782178026423717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26804698024521452017615811 40207047036782178026423717)
    ·
      refine ⟨7538821319396658379954447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40207047036782178026423717 7538821319396658379954447)
      ·
        refine ⟨11308231979094987569931671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7538821319396658379954447 11308231979094987569931671)
        ·
          refine ⟨16962347968642481354897507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11308231979094987569931671 16962347968642481354897507)
          ·
            refine ⟨25443521952963722032346261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16962347968642481354897507 25443521952963722032346261)
            ·
              refine ⟨1192665091545174470266231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25443521952963722032346261 1192665091545174470266231)
              ·
                refine ⟨1788997637317761705399347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192665091545174470266231 1788997637317761705399347)
                ·
                  refine ⟨2683496455976642558099021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788997637317761705399347 2683496455976642558099021)
                  ·
                    refine ⟨1006311170991240959287133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683496455976642558099021 1006311170991240959287133)
                    ·
                      refine ⟨377366689121715359732675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1006311170991240959287133 377366689121715359732675)
                      ·
                        rfl

theorem cell23_734919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_734919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734919 prefixEnd_734919 := by exact prefixLift 734919
  have htrace : WordTrace (prefixWord ++ tailWord_734919) baseStart_734919 baseEnd_734919 := by
    simpa [prefixWord, tailWord_734919, baseEnd_734919] using wordTrace_append hprefix tailTrace_734919
  have hstable : (prefixWord ++ tailWord_734919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734919).length < 2 ^ (prefixWord ++ tailWord_734919).sum := by decide
  have hdescent : baseEnd_734919 < baseStart_734919 := by decide
  rcases family_descends (prefixWord ++ tailWord_734919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735016 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 7]
def baseStart_735016 : Nat := 118140960795 + 735016 * 2 ^ 59
def prefixEnd_735016 : Nat := 4983230072969 + 3 ^ 40 * 735016 * 2
def baseEnd_735016 : Nat := 41935166305022386691081

theorem tailTrace_735016 : CollatzResearch.WordTrace tailWord_735016 prefixEnd_735016 41935166305022386691081 := by
  unfold tailWord_735016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13404117952585018791948451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17872157270113358389264601 13404117952585018791948451)
  ·
    refine ⟨20106176928877528187922677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13404117952585018791948451 20106176928877528187922677)
    ·
      refine ⟨1884954087082268267617751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20106176928877528187922677 1884954087082268267617751)
      ·
        refine ⟨2827431130623402401426627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884954087082268267617751 2827431130623402401426627)
        ·
          refine ⟨4241146695935103602139941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827431130623402401426627 4241146695935103602139941)
          ·
            refine ⟨795215005487831925401239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4241146695935103602139941 795215005487831925401239)
            ·
              refine ⟨1192822508231747888101859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795215005487831925401239 1192822508231747888101859)
              ·
                refine ⟨1789233762347621832152789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192822508231747888101859 1789233762347621832152789)
                ·
                  refine ⟨41935166305022386691081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1789233762347621832152789 41935166305022386691081)
                  ·
                    rfl

theorem cell23_735016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 7].length) (baseStart_735016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735016 prefixEnd_735016 := by exact prefixLift 735016
  have htrace : WordTrace (prefixWord ++ tailWord_735016) baseStart_735016 baseEnd_735016 := by
    simpa [prefixWord, tailWord_735016, baseEnd_735016] using wordTrace_append hprefix tailTrace_735016
  have hstable : (prefixWord ++ tailWord_735016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735016).length < 2 ^ (prefixWord ++ tailWord_735016).sum := by decide
  have hdescent : baseEnd_735016 < baseStart_735016 := by decide
  rcases family_descends (prefixWord ++ tailWord_735016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735027 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 2, 2, 2]
def baseStart_735027 : Nat := 118140960795 + 735027 * 2 ^ 59
def prefixEnd_735027 : Nat := 4983230072969 + 3 ^ 40 * 735027 * 2
def baseEnd_735027 : Nat := 377422145032400937182179

theorem tailTrace_735027 : CollatzResearch.WordTrace tailWord_735027 prefixEnd_735027 377422145032400937182179 := by
  unfold tailWord_735027
  simp only [CollatzResearch.WordTrace]
  refine ⟨26808637108130186462547335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17872424738753457641698223 26808637108130186462547335)
  ·
    refine ⟨40212955662195279693821003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26808637108130186462547335 40212955662195279693821003)
    ·
      refine ⟨60319433493292919540731505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40212955662195279693821003 60319433493292919540731505)
      ·
        refine ⟨45239575119969689655548629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60319433493292919540731505 45239575119969689655548629)
        ·
          refine ⟨1060302541874289601301921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45239575119969689655548629 1060302541874289601301921)
          ·
            refine ⟨795226906405717200976441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060302541874289601301921 795226906405717200976441)
            ·
              refine ⟨596420179804287900732331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795226906405717200976441 596420179804287900732331)
              ·
                refine ⟨894630269706431851098497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596420179804287900732331 894630269706431851098497)
                ·
                  refine ⟨670972702279823888323873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894630269706431851098497 670972702279823888323873)
                  ·
                    refine ⟨503229526709867916242905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 670972702279823888323873 503229526709867916242905)
                    ·
                      refine ⟨377422145032400937182179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503229526709867916242905 377422145032400937182179)
                      ·
                        rfl

theorem cell23_735027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 2, 2].length) (baseStart_735027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735027 prefixEnd_735027 := by exact prefixLift 735027
  have htrace : WordTrace (prefixWord ++ tailWord_735027) baseStart_735027 baseEnd_735027 := by
    simpa [prefixWord, tailWord_735027, baseEnd_735027] using wordTrace_append hprefix tailTrace_735027
  have hstable : (prefixWord ++ tailWord_735027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735027).length < 2 ^ (prefixWord ++ tailWord_735027).sum := by decide
  have hdescent : baseEnd_735027 < baseStart_735027 := by decide
  rcases family_descends (prefixWord ++ tailWord_735027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735066 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2]
def baseStart_735066 : Nat := 118140960795 + 735066 * 2 ^ 59
def prefixEnd_735066 : Nat := 4983230072969 + 3 ^ 40 * 735066 * 2
def baseEnd_735066 : Nat := 377442170777926284594499

theorem tailTrace_735066 : CollatzResearch.WordTrace tailWord_735066 prefixEnd_735066 377442170777926284594499 := by
  unfold tailWord_735066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6702514888747224030804263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17873373036659264082144701 6702514888747224030804263)
  ·
    refine ⟨10053772333120836046206395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6702514888747224030804263 10053772333120836046206395)
    ·
      refine ⟨15080658499681254069309593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10053772333120836046206395 15080658499681254069309593)
      ·
        refine ⟨11310493874760940551982195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15080658499681254069309593 11310493874760940551982195)
        ·
          refine ⟨16965740812141410827973293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310493874760940551982195 16965740812141410827973293)
          ·
            refine ⟨6362152804553029060489985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16965740812141410827973293 6362152804553029060489985)
            ·
              refine ⟨4771614603414771795367489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6362152804553029060489985 4771614603414771795367489)
              ·
                refine ⟨3578710952561078846525617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4771614603414771795367489 3578710952561078846525617)
                ·
                  refine ⟨2684033214420809134894213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578710952561078846525617 2684033214420809134894213)
                  ·
                    refine ⟨503256227703901712792665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684033214420809134894213 503256227703901712792665)
                    ·
                      refine ⟨377442170777926284594499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503256227703901712792665 377442170777926284594499)
                      ·
                        rfl

theorem cell23_735066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_735066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735066 prefixEnd_735066 := by exact prefixLift 735066
  have htrace : WordTrace (prefixWord ++ tailWord_735066) baseStart_735066 baseEnd_735066 := by
    simpa [prefixWord, tailWord_735066, baseEnd_735066] using wordTrace_append hprefix tailTrace_735066
  have hstable : (prefixWord ++ tailWord_735066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735066).length < 2 ^ (prefixWord ++ tailWord_735066).sum := by decide
  have hdescent : baseEnd_735066 < baseStart_735066 := by decide
  rcases family_descends (prefixWord ++ tailWord_735066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735089 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 6]
def baseStart_735089 : Nat := 118140960795 + 735089 * 2 ^ 59
def prefixEnd_735089 : Nat := 4983230072969 + 3 ^ 40 * 735089 * 2
def baseEnd_735089 : Nat := 41939331203664410511877

theorem tailTrace_735089 : CollatzResearch.WordTrace tailWord_735089 prefixEnd_735089 41939331203664410511877 := by
  unfold tailWord_735089
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810898433905571051304321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17873932289270380700869547 26810898433905571051304321)
  ·
    refine ⟨20108173825429178288478241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26810898433905571051304321 20108173825429178288478241)
    ·
      refine ⟨15081130369071883716358681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20108173825429178288478241 15081130369071883716358681)
      ·
        refine ⟨11310847776803912787269011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15081130369071883716358681 11310847776803912787269011)
        ·
          refine ⟨16966271665205869180903517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310847776803912787269011 16966271665205869180903517)
          ·
            refine ⟨6362351874452200942838819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16966271665205869180903517 6362351874452200942838819)
            ·
              refine ⟨9543527811678301414258229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362351874452200942838819 9543527811678301414258229)
              ·
                refine ⟨894705732344840757586709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9543527811678301414258229 894705732344840757586709)
                ·
                  refine ⟨41939331203664410511877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 894705732344840757586709 41939331203664410511877)
                  ·
                    rfl

theorem cell23_735089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 6].length) (baseStart_735089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735089 prefixEnd_735089 := by exact prefixLift 735089
  have htrace : WordTrace (prefixWord ++ tailWord_735089) baseStart_735089 baseEnd_735089 := by
    simpa [prefixWord, tailWord_735089, baseEnd_735089] using wordTrace_append hprefix tailTrace_735089
  have hstable : (prefixWord ++ tailWord_735089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735089).length < 2 ^ (prefixWord ++ tailWord_735089).sum := by decide
  have hdescent : baseEnd_735089 < baseStart_735089 := by decide
  rcases family_descends (prefixWord ++ tailWord_735089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735116 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_735116 : Nat := 118140960795 + 735116 * 2 ^ 59
def prefixEnd_735116 : Nat := 4983230072969 + 3 ^ 40 * 735116 * 2
def baseEnd_735116 : Nat := 377467844810651088969269

theorem tailTrace_735116 : CollatzResearch.WordTrace tailWord_735116 prefixEnd_735116 377467844810651088969269 := by
  unfold tailWord_735116
  simp only [CollatzResearch.WordTrace]
  refine ⟨13405941602403877331268601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17874588803205169775024801 13405941602403877331268601)
  ·
    refine ⟨10054456201802907998451451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13405941602403877331268601 10054456201802907998451451)
    ·
      refine ⟨15081684302704361997677177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054456201802907998451451 15081684302704361997677177)
      ·
        refine ⟨11311263227028271498257883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15081684302704361997677177 11311263227028271498257883)
        ·
          refine ⟨16966894840542407247386825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11311263227028271498257883 16966894840542407247386825)
          ·
            refine ⟨12725171130406805435540119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16966894840542407247386825 12725171130406805435540119)
            ·
              refine ⟨19087756695610208153310179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12725171130406805435540119 19087756695610208153310179)
              ·
                refine ⟨28631635043415312229965269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19087756695610208153310179 28631635043415312229965269)
                ·
                  refine ⟨671053946330046380389811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 28631635043415312229965269 671053946330046380389811)
                  ·
                    refine ⟨1006580919495069570584717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671053946330046380389811 1006580919495069570584717)
                    ·
                      refine ⟨377467844810651088969269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1006580919495069570584717 377467844810651088969269)
                      ·
                        rfl

theorem cell23_735116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_735116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735116 prefixEnd_735116 := by exact prefixLift 735116
  have htrace : WordTrace (prefixWord ++ tailWord_735116) baseStart_735116 baseEnd_735116 := by
    simpa [prefixWord, tailWord_735116, baseEnd_735116] using wordTrace_append hprefix tailTrace_735116
  have hstable : (prefixWord ++ tailWord_735116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735116).length < 2 ^ (prefixWord ++ tailWord_735116).sum := by decide
  have hdescent : baseEnd_735116 < baseStart_735116 := by decide
  rcases family_descends (prefixWord ++ tailWord_735116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735133 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_735133 : Nat := 118140960795 + 735133 * 2 ^ 59
def prefixEnd_735133 : Nat := 4983230072969 + 3 ^ 40 * 735133 * 2
def baseEnd_735133 : Nat := 377476573981777522456691

theorem tailTrace_735133 : CollatzResearch.WordTrace tailWord_735133 prefixEnd_735133 377476573981777522456691 := by
  unfold tailWord_735133
  simp only [CollatzResearch.WordTrace]
  refine ⟨26812503245746166565906053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17875002163830777710604035 26812503245746166565906053)
  ·
    refine ⟨5027344358577406231107385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26812503245746166565906053 5027344358577406231107385)
    ·
      refine ⟨3770508268933054673330539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5027344358577406231107385 3770508268933054673330539)
      ·
        refine ⟨5655762403399582009995809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770508268933054673330539 5655762403399582009995809)
        ·
          refine ⟨4241821802549686507496857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5655762403399582009995809 4241821802549686507496857)
          ·
            refine ⟨3181366351912264880622643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4241821802549686507496857 3181366351912264880622643)
            ·
              refine ⟨4772049527868397320933965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181366351912264880622643 4772049527868397320933965)
              ·
                refine ⟨1789518572950648995350237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4772049527868397320933965 1789518572950648995350237)
                ·
                  refine ⟨671069464856493373256339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1789518572950648995350237 671069464856493373256339)
                  ·
                    refine ⟨1006604197284740059884509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671069464856493373256339 1006604197284740059884509)
                    ·
                      refine ⟨377476573981777522456691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1006604197284740059884509 377476573981777522456691)
                      ·
                        rfl

theorem cell23_735133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_735133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735133 prefixEnd_735133 := by exact prefixLift 735133
  have htrace : WordTrace (prefixWord ++ tailWord_735133) baseStart_735133 baseEnd_735133 := by
    simpa [prefixWord, tailWord_735133, baseEnd_735133] using wordTrace_append hprefix tailTrace_735133
  have hstable : (prefixWord ++ tailWord_735133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735133).length < 2 ^ (prefixWord ++ tailWord_735133).sum := by decide
  have hdescent : baseEnd_735133 < baseStart_735133 := by decide
  rcases family_descends (prefixWord ++ tailWord_735133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735143 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_735143 : Nat := 118140960795 + 735143 * 2 ^ 59
def prefixEnd_735143 : Nat := 4983230072969 + 3 ^ 40 * 735143 * 2
def baseEnd_735143 : Nat := 377481708788322483331645

theorem tailTrace_735143 : CollatzResearch.WordTrace tailWord_735143 prefixEnd_735143 377481708788322483331645 := by
  unfold tailWord_735143
  simp only [CollatzResearch.WordTrace]
  refine ⟨26812867975709938273770083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17875245317139958849180055 26812867975709938273770083)
  ·
    refine ⟨40219301963564907410655125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26812867975709938273770083 40219301963564907410655125)
    ·
      refine ⟨1885279779542105034874459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40219301963564907410655125 1885279779542105034874459)
      ·
        refine ⟨2827919669313157552311689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885279779542105034874459 2827919669313157552311689)
        ·
          refine ⟨2120939751984868164233767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827919669313157552311689 2120939751984868164233767)
          ·
            refine ⟨3181409627977302246350651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120939751984868164233767 3181409627977302246350651)
            ·
              refine ⟨4772114441965953369525977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181409627977302246350651 4772114441965953369525977)
              ·
                refine ⟨3579085831474465027144483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4772114441965953369525977 3579085831474465027144483)
                ·
                  refine ⟨5368628747211697540716725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579085831474465027144483 5368628747211697540716725)
                  ·
                    refine ⟨503308945051096644442193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5368628747211697540716725 503308945051096644442193)
                    ·
                      refine ⟨377481708788322483331645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503308945051096644442193 377481708788322483331645)
                      ·
                        rfl

theorem cell23_735143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_735143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735143 prefixEnd_735143 := by exact prefixLift 735143
  have htrace : WordTrace (prefixWord ++ tailWord_735143) baseStart_735143 baseEnd_735143 := by
    simpa [prefixWord, tailWord_735143, baseEnd_735143] using wordTrace_append hprefix tailTrace_735143
  have hstable : (prefixWord ++ tailWord_735143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735143).length < 2 ^ (prefixWord ++ tailWord_735143).sum := by decide
  have hdescent : baseEnd_735143 < baseStart_735143 := by decide
  rcases family_descends (prefixWord ++ tailWord_735143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735153 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 1, 5]
def baseStart_735153 : Nat := 118140960795 + 735153 * 2 ^ 59
def prefixEnd_735153 : Nat := 4983230072969 + 3 ^ 40 * 735153 * 2
def baseEnd_735153 : Nat := 125828947864955814735533

theorem tailTrace_735153 : CollatzResearch.WordTrace tailWord_735153 prefixEnd_735153 125828947864955814735533 := by
  unfold tailWord_735153
  simp only [CollatzResearch.WordTrace]
  refine ⟨26813232705673709981634113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17875488470449139987756075 26813232705673709981634113)
  ·
    refine ⟨20109924529255282486225585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26813232705673709981634113 20109924529255282486225585)
    ·
      refine ⟨15082443396941461864669189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20109924529255282486225585 15082443396941461864669189)
      ·
        refine ⟨2827958136926524099625473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15082443396941461864669189 2827958136926524099625473)
        ·
          refine ⟨2120968602694893074719105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827958136926524099625473 2120968602694893074719105)
          ·
            refine ⟨1590726452021169806039329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2120968602694893074719105 1590726452021169806039329)
            ·
              refine ⟨1193044839015877354529497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590726452021169806039329 1193044839015877354529497)
              ·
                refine ⟨894783629261908015897123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193044839015877354529497 894783629261908015897123)
                ·
                  refine ⟨1342175443892862023845685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894783629261908015897123 1342175443892862023845685)
                  ·
                    refine ⟨125828947864955814735533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1342175443892862023845685 125828947864955814735533)
                    ·
                      rfl

theorem cell23_735153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_735153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735153 prefixEnd_735153 := by exact prefixLift 735153
  have htrace : WordTrace (prefixWord ++ tailWord_735153) baseStart_735153 baseEnd_735153 := by
    simpa [prefixWord, tailWord_735153, baseEnd_735153] using wordTrace_append hprefix tailTrace_735153
  have hstable : (prefixWord ++ tailWord_735153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735153).length < 2 ^ (prefixWord ++ tailWord_735153).sum := by decide
  have hdescent : baseEnd_735153 < baseStart_735153 := by decide
  rcases family_descends (prefixWord ++ tailWord_735153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735159 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_735159 : Nat := 118140960795 + 735159 * 2 ^ 59
def prefixEnd_735159 : Nat := 4983230072969 + 3 ^ 40 * 735159 * 2
def baseEnd_735159 : Nat := 377489924478794420731571

theorem tailTrace_735159 : CollatzResearch.WordTrace tailWord_735159 prefixEnd_735159 377489924478794420731571 := by
  unfold tailWord_735159
  simp only [CollatzResearch.WordTrace]
  refine ⟨26813451543651973006352531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17875634362434648670901687 26813451543651973006352531)
  ·
    refine ⟨40220177315477959509528797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26813451543651973006352531 40220177315477959509528797)
    ·
      refine ⟨15082566493304234816073299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40220177315477959509528797 15082566493304234816073299)
      ·
        refine ⟨22623849739956352224109949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15082566493304234816073299 22623849739956352224109949)
        ·
          refine ⟨8483943652483632084041231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22623849739956352224109949 8483943652483632084041231)
          ·
            refine ⟨12725915478725448126061847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483943652483632084041231 12725915478725448126061847)
            ·
              refine ⟨19088873218088172189092771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12725915478725448126061847 19088873218088172189092771)
              ·
                refine ⟨28633309827132258283639157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19088873218088172189092771 28633309827132258283639157)
                ·
                  refine ⟨2684372796293649214091171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28633309827132258283639157 2684372796293649214091171)
                  ·
                    refine ⟨4026559194440473821136757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2684372796293649214091171 4026559194440473821136757)
                    ·
                      refine ⟨377489924478794420731571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4026559194440473821136757 377489924478794420731571)
                      ·
                        rfl

theorem cell23_735159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_735159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735159 prefixEnd_735159 := by exact prefixLift 735159
  have htrace : WordTrace (prefixWord ++ tailWord_735159) baseStart_735159 baseEnd_735159 := by
    simpa [prefixWord, tailWord_735159, baseEnd_735159] using wordTrace_append hprefix tailTrace_735159
  have hstable : (prefixWord ++ tailWord_735159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735159).length < 2 ^ (prefixWord ++ tailWord_735159).sum := by decide
  have hdescent : baseEnd_735159 < baseStart_735159 := by decide
  rcases family_descends (prefixWord ++ tailWord_735159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735176 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_735176 : Nat := 118140960795 + 735176 * 2 ^ 59
def prefixEnd_735176 : Nat := 4983230072969 + 3 ^ 40 * 735176 * 2
def baseEnd_735176 : Nat := 377498653649920854218993

theorem tailTrace_735176 : CollatzResearch.WordTrace tailWord_735176 prefixEnd_735176 377498653649920854218993 := by
  unfold tailWord_735176
  simp only [CollatzResearch.WordTrace]
  refine ⟨13407035792295192454860691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17876047723060256606480921 13407035792295192454860691)
  ·
    refine ⟨20110553688442788682291037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13407035792295192454860691 20110553688442788682291037)
    ·
      refine ⟨7541457633166045755859139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20110553688442788682291037 7541457633166045755859139)
      ·
        refine ⟨11312186449749068633788709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7541457633166045755859139 11312186449749068633788709)
        ·
          refine ⟨2121034959327950368835383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11312186449749068633788709 2121034959327950368835383)
          ·
            refine ⟨3181552438991925553253075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121034959327950368835383 3181552438991925553253075)
            ·
              refine ⟨4772328658487888329879613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181552438991925553253075 4772328658487888329879613)
              ·
                refine ⟨1789623246932958123704855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4772328658487888329879613 1789623246932958123704855)
                ·
                  refine ⟨2684434870399437185557283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789623246932958123704855 2684434870399437185557283)
                  ·
                    refine ⟨4026652305599155778335925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2684434870399437185557283 4026652305599155778335925)
                    ·
                      refine ⟨377498653649920854218993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4026652305599155778335925 377498653649920854218993)
                      ·
                        rfl

theorem cell23_735176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_735176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735176 prefixEnd_735176 := by exact prefixLift 735176
  have htrace : WordTrace (prefixWord ++ tailWord_735176) baseStart_735176 baseEnd_735176 := by
    simpa [prefixWord, tailWord_735176, baseEnd_735176] using wordTrace_append hprefix tailTrace_735176
  have hstable : (prefixWord ++ tailWord_735176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735176).length < 2 ^ (prefixWord ++ tailWord_735176).sum := by decide
  have hdescent : baseEnd_735176 < baseStart_735176 := by decide
  rcases family_descends (prefixWord ++ tailWord_735176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735207 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_735207 : Nat := 118140960795 + 735207 * 2 ^ 59
def prefixEnd_735207 : Nat := 4983230072969 + 3 ^ 40 * 735207 * 2
def baseEnd_735207 : Nat := 377514571550210232931351

theorem tailTrace_735207 : CollatzResearch.WordTrace tailWord_735207 prefixEnd_735207 377514571550210232931351 := by
  unfold tailWord_735207
  simp only [CollatzResearch.WordTrace]
  refine ⟨26815202247478077204099875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17876801498318718136066583 26815202247478077204099875)
  ·
    refine ⟨40222803371217115806149813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26815202247478077204099875 40222803371217115806149813)
    ·
      refine ⟨3770887816051604606826545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40222803371217115806149813 3770887816051604606826545)
      ·
        refine ⟨2828165862038703455119909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3770887816051604606826545 2828165862038703455119909)
        ·
          refine ⟨530281099132256897834983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2828165862038703455119909 530281099132256897834983)
          ·
            refine ⟨795421648698385346752475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530281099132256897834983 795421648698385346752475)
            ·
              refine ⟨1193132473047578020128713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795421648698385346752475 1193132473047578020128713)
              ·
                refine ⟨894849354785683515096535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193132473047578020128713 894849354785683515096535)
                ·
                  refine ⟨1342274032178525272644803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894849354785683515096535 1342274032178525272644803)
                  ·
                    refine ⟨2013411048267787908967205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1342274032178525272644803 2013411048267787908967205)
                    ·
                      refine ⟨377514571550210232931351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2013411048267787908967205 377514571550210232931351)
                      ·
                        rfl

theorem cell23_735207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_735207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735207 prefixEnd_735207 := by exact prefixLift 735207
  have htrace : WordTrace (prefixWord ++ tailWord_735207) baseStart_735207 baseEnd_735207 := by
    simpa [prefixWord, tailWord_735207, baseEnd_735207] using wordTrace_append hprefix tailTrace_735207
  have hstable : (prefixWord ++ tailWord_735207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735207).length < 2 ^ (prefixWord ++ tailWord_735207).sum := by decide
  have hdescent : baseEnd_735207 < baseStart_735207 := by decide
  rcases family_descends (prefixWord ++ tailWord_735207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735219 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5]
def baseStart_735219 : Nat := 118140960795 + 735219 * 2 ^ 59
def prefixEnd_735219 : Nat := 4983230072969 + 3 ^ 40 * 735219 * 2
def baseEnd_735219 : Nat := 377520733318064185981295

theorem tailTrace_735219 : CollatzResearch.WordTrace tailWord_735219 prefixEnd_735219 377520733318064185981295 := by
  unfold tailWord_735219
  simp only [CollatzResearch.WordTrace]
  refine ⟨26815639923434603253536711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17877093282289735502357807 26815639923434603253536711)
  ·
    refine ⟨40223459885151904880305067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26815639923434603253536711 40223459885151904880305067)
    ·
      refine ⟨60335189827727857320457601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40223459885151904880305067 60335189827727857320457601)
      ·
        refine ⟨45251392370795892990343201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60335189827727857320457601 45251392370795892990343201)
        ·
          refine ⟨33938544278096919742757401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45251392370795892990343201 33938544278096919742757401)
          ·
            refine ⟨25453908208572689807068051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33938544278096919742757401 25453908208572689807068051)
            ·
              refine ⟨38180862312859034710602077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25453908208572689807068051 38180862312859034710602077)
              ·
                refine ⟨14317823367322138016475779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38180862312859034710602077 14317823367322138016475779)
                ·
                  refine ⟨21476735050983207024713669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14317823367322138016475779 21476735050983207024713669)
                  ·
                    refine ⟨4026887822059351317133813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21476735050983207024713669 4026887822059351317133813)
                    ·
                      refine ⟨377520733318064185981295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4026887822059351317133813 377520733318064185981295)
                      ·
                        rfl

theorem cell23_735219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_735219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735219 prefixEnd_735219 := by exact prefixLift 735219
  have htrace : WordTrace (prefixWord ++ tailWord_735219) baseStart_735219 baseEnd_735219 := by
    simpa [prefixWord, tailWord_735219, baseEnd_735219] using wordTrace_append hprefix tailTrace_735219
  have hstable : (prefixWord ++ tailWord_735219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735219).length < 2 ^ (prefixWord ++ tailWord_735219).sum := by decide
  have hdescent : baseEnd_735219 < baseStart_735219 := by decide
  rcases family_descends (prefixWord ++ tailWord_735219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735240 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_735240 : Nat := 118140960795 + 735240 * 2 ^ 59
def prefixEnd_735240 : Nat := 4983230072969 + 3 ^ 40 * 735240 * 2
def baseEnd_735240 : Nat := 377531516411808603818699

theorem tailTrace_735240 : CollatzResearch.WordTrace tailWord_735240 prefixEnd_735240 377531516411808603818699 := by
  unfold tailWord_735240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13408202928179261920025587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17877603904239015893367449 13408202928179261920025587)
  ·
    refine ⟨20112304392268892880038381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13408202928179261920025587 20112304392268892880038381)
    ·
      refine ⟨7542114147100834830014393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20112304392268892880038381 7542114147100834830014393)
      ·
        refine ⟨5656585610325626122510795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7542114147100834830014393 5656585610325626122510795)
        ·
          refine ⟨8484878415488439183766193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656585610325626122510795 8484878415488439183766193)
          ·
            refine ⟨6363658811616329387824645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8484878415488439183766193 6363658811616329387824645)
            ·
              refine ⟨1193186027178061760217121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6363658811616329387824645 1193186027178061760217121)
              ·
                refine ⟨894889520383546320162841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193186027178061760217121 894889520383546320162841)
                ·
                  refine ⟨671167140287659740122131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894889520383546320162841 671167140287659740122131)
                  ·
                    refine ⟨1006750710431489610183197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671167140287659740122131 1006750710431489610183197)
                    ·
                      refine ⟨377531516411808603818699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1006750710431489610183197 377531516411808603818699)
                      ·
                        rfl

theorem cell23_735240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_735240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735240 prefixEnd_735240 := by exact prefixLift 735240
  have htrace : WordTrace (prefixWord ++ tailWord_735240) baseStart_735240 baseEnd_735240 := by
    simpa [prefixWord, tailWord_735240, baseEnd_735240] using wordTrace_append hprefix tailTrace_735240
  have hstable : (prefixWord ++ tailWord_735240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735240).length < 2 ^ (prefixWord ++ tailWord_735240).sum := by decide
  have hdescent : baseEnd_735240 < baseStart_735240 := by decide
  rcases family_descends (prefixWord ++ tailWord_735240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735246 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_735246 : Nat := 118140960795 + 735246 * 2 ^ 59
def prefixEnd_735246 : Nat := 4983230072969 + 3 ^ 40 * 735246 * 2
def baseEnd_735246 : Nat := 377534597295735580343671

theorem tailTrace_735246 : CollatzResearch.WordTrace tailWord_735246 prefixEnd_735246 377534597295735580343671 := by
  unfold tailWord_735246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352078086792098358096199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17877749796224524576513061 3352078086792098358096199)
  ·
    refine ⟨5028117130188147537144299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352078086792098358096199 5028117130188147537144299)
    ·
      refine ⟨7542175695282221305716449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028117130188147537144299 7542175695282221305716449)
      ·
        refine ⟨5656631771461665979287337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7542175695282221305716449 5656631771461665979287337)
        ·
          refine ⟨4242473828596249484465503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656631771461665979287337 4242473828596249484465503)
          ·
            refine ⟨6363710742894374226698255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242473828596249484465503 6363710742894374226698255)
            ·
              refine ⟨9545566114341561340047383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363710742894374226698255 9545566114341561340047383)
              ·
                refine ⟨14318349171512342010071075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9545566114341561340047383 14318349171512342010071075)
                ·
                  refine ⟨21477523757268513015106613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14318349171512342010071075 21477523757268513015106613)
                  ·
                    refine ⟨2013517852243923095166245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21477523757268513015106613 2013517852243923095166245)
                    ·
                      refine ⟨377534597295735580343671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2013517852243923095166245 377534597295735580343671)
                      ·
                        rfl

theorem cell23_735246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_735246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735246 prefixEnd_735246 := by exact prefixLift 735246
  have htrace : WordTrace (prefixWord ++ tailWord_735246) baseStart_735246 baseEnd_735246 := by
    simpa [prefixWord, tailWord_735246, baseEnd_735246] using wordTrace_append hprefix tailTrace_735246
  have hstable : (prefixWord ++ tailWord_735246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735246).length < 2 ^ (prefixWord ++ tailWord_735246).sum := by decide
  have hdescent : baseEnd_735246 < baseStart_735246 := by decide
  rcases family_descends (prefixWord ++ tailWord_735246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735256 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 2, 6]
def baseStart_735256 : Nat := 118140960795 + 735256 * 2 ^ 59
def prefixEnd_735256 : Nat := 4983230072969 + 3 ^ 40 * 735256 * 2
def baseEnd_735256 : Nat := 125846577367426847072875

theorem tailTrace_735256 : CollatzResearch.WordTrace tailWord_735256 prefixEnd_735256 125846577367426847072875 := by
  unfold tailWord_735256
  simp only [CollatzResearch.WordTrace]
  refine ⟨13408494712150279286316811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17877992949533705715089081 13408494712150279286316811)
  ·
    refine ⟨20112742068225418929475217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13408494712150279286316811 20112742068225418929475217)
    ·
      refine ⟨15084556551169064197106413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20112742068225418929475217 15084556551169064197106413)
      ·
        refine ⟨5656708706688399073914905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15084556551169064197106413 5656708706688399073914905)
        ·
          refine ⟨4242531530016299305436179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656708706688399073914905 4242531530016299305436179)
          ·
            refine ⟨6363797295024448958154269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242531530016299305436179 6363797295024448958154269)
            ·
              refine ⟨2386423985634168359307851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6363797295024448958154269 2386423985634168359307851)
              ·
                refine ⟨3579635978451252538961777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386423985634168359307851 3579635978451252538961777)
                ·
                  refine ⟨2684726983838439404221333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3579635978451252538961777 2684726983838439404221333)
                  ·
                    refine ⟨125846577367426847072875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2684726983838439404221333 125846577367426847072875)
                    ·
                      rfl

theorem cell23_735256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_735256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735256 prefixEnd_735256 := by exact prefixLift 735256
  have htrace : WordTrace (prefixWord ++ tailWord_735256) baseStart_735256 baseEnd_735256 := by
    simpa [prefixWord, tailWord_735256, baseEnd_735256] using wordTrace_append hprefix tailTrace_735256
  have hstable : (prefixWord ++ tailWord_735256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735256).length < 2 ^ (prefixWord ++ tailWord_735256).sum := by decide
  have hdescent : baseEnd_735256 < baseStart_735256 := by decide
  rcases family_descends (prefixWord ++ tailWord_735256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735284 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_735284 : Nat := 118140960795 + 735284 * 2 ^ 59
def prefixEnd_735284 : Nat := 4983230072969 + 3 ^ 40 * 735284 * 2
def baseEnd_735284 : Nat := 377554109560606431668497

theorem tailTrace_735284 : CollatzResearch.WordTrace tailWord_735284 prefixEnd_735284 377554109560606431668497 := by
  unfold tailWord_735284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13409005334099559677326453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17878673778799412903101937 13409005334099559677326453)
  ·
    refine ⟨1257094250071833719749355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13409005334099559677326453 1257094250071833719749355)
    ·
      refine ⟨1885641375107750579624033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1257094250071833719749355 1885641375107750579624033)
      ·
        refine ⟨1414231031330812934718025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1885641375107750579624033 1414231031330812934718025)
        ·
          refine ⟨1060673273498109701038519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414231031330812934718025 1060673273498109701038519)
          ·
            refine ⟨1591009910247164551557779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060673273498109701038519 1591009910247164551557779)
            ·
              refine ⟨2386514865370746827336669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591009910247164551557779 2386514865370746827336669)
              ·
                refine ⟨894943074514030060251251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2386514865370746827336669 894943074514030060251251)
                ·
                  refine ⟨1342414611771045090376877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894943074514030060251251 1342414611771045090376877)
                  ·
                    refine ⟨503405479414141908891329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342414611771045090376877 503405479414141908891329)
                    ·
                      refine ⟨377554109560606431668497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503405479414141908891329 377554109560606431668497)
                      ·
                        rfl

theorem cell23_735284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_735284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735284 prefixEnd_735284 := by exact prefixLift 735284
  have htrace : WordTrace (prefixWord ++ tailWord_735284) baseStart_735284 baseEnd_735284 := by
    simpa [prefixWord, tailWord_735284, baseEnd_735284] using wordTrace_append hprefix tailTrace_735284
  have hstable : (prefixWord ++ tailWord_735284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735284).length < 2 ^ (prefixWord ++ tailWord_735284).sum := by decide
  have hdescent : baseEnd_735284 < baseStart_735284 := by decide
  rcases family_descends (prefixWord ++ tailWord_735284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735297 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_735297 : Nat := 118140960795 + 735297 * 2 ^ 59
def prefixEnd_735297 : Nat := 4983230072969 + 3 ^ 40 * 735297 * 2
def baseEnd_735297 : Nat := 377560784809114880805937

theorem tailTrace_735297 : CollatzResearch.WordTrace tailWord_735297 prefixEnd_735297 377560784809114880805937 := by
  unfold tailWord_735297
  simp only [CollatzResearch.WordTrace]
  refine ⟨26818484817152022574876145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17878989878101348383250763 26818484817152022574876145)
  ·
    refine ⟨20113863612864016931157109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26818484817152022574876145 20113863612864016931157109)
    ·
      refine ⟨1885674713706001587295979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20113863612864016931157109 1885674713706001587295979)
      ·
        refine ⟨2828512070559002380943969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885674713706001587295979 2828512070559002380943969)
        ·
          refine ⟨2121384052919251785707977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828512070559002380943969 2121384052919251785707977)
          ·
            refine ⟨1591038039689438839280983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2121384052919251785707977 1591038039689438839280983)
            ·
              refine ⟨2386557059534158258921475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591038039689438839280983 2386557059534158258921475)
              ·
                refine ⟨3579835589301237388382213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386557059534158258921475 3579835589301237388382213)
                ·
                  refine ⟨671219172993982010321665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3579835589301237388382213 671219172993982010321665)
                  ·
                    refine ⟨503414379745486507741249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 671219172993982010321665 503414379745486507741249)
                    ·
                      refine ⟨377560784809114880805937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503414379745486507741249 377560784809114880805937)
                      ·
                        rfl

theorem cell23_735297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_735297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735297 prefixEnd_735297 := by exact prefixLift 735297
  have htrace : WordTrace (prefixWord ++ tailWord_735297) baseStart_735297 baseEnd_735297 := by
    simpa [prefixWord, tailWord_735297, baseEnd_735297] using wordTrace_append hprefix tailTrace_735297
  have hstable : (prefixWord ++ tailWord_735297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735297).length < 2 ^ (prefixWord ++ tailWord_735297).sum := by decide
  have hdescent : baseEnd_735297 < baseStart_735297 := by decide
  rcases family_descends (prefixWord ++ tailWord_735297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735303 : List Nat := [1, 1, 4, 1, 3, 1, 1, 6, 5]
def baseStart_735303 : Nat := 118140960795 + 735303 * 2 ^ 59
def prefixEnd_735303 : Nat := 4983230072969 + 3 ^ 40 * 735303 * 2
def baseEnd_735303 : Nat := 41951540632560206370101

theorem tailTrace_735303 : CollatzResearch.WordTrace tailWord_735303 prefixEnd_735303 41951540632560206370101 := by
  unfold tailWord_735303
  simp only [CollatzResearch.WordTrace]
  refine ⟨26818703655130285599594563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17879135770086857066396375 26818703655130285599594563)
  ·
    refine ⟨40228055482695428399391845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26818703655130285599594563 40228055482695428399391845)
    ·
      refine ⟨7542760403005392824885971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40228055482695428399391845 7542760403005392824885971)
      ·
        refine ⟨11314140604508089237328957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542760403005392824885971 11314140604508089237328957)
        ·
          refine ⟨4242802726690533463998359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11314140604508089237328957 4242802726690533463998359)
          ·
            refine ⟨6364204090035800195997539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242802726690533463998359 6364204090035800195997539)
            ·
              refine ⟨9546306135053700293996309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364204090035800195997539 9546306135053700293996309)
              ·
                refine ⟨447483100080642201281077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9546306135053700293996309 447483100080642201281077)
                ·
                  refine ⟨41951540632560206370101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 447483100080642201281077 41951540632560206370101)
                  ·
                    rfl

theorem cell23_735303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 5].length) (baseStart_735303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735303 prefixEnd_735303 := by exact prefixLift 735303
  have htrace : WordTrace (prefixWord ++ tailWord_735303) baseStart_735303 baseEnd_735303 := by
    simpa [prefixWord, tailWord_735303, baseEnd_735303] using wordTrace_append hprefix tailTrace_735303
  have hstable : (prefixWord ++ tailWord_735303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735303).length < 2 ^ (prefixWord ++ tailWord_735303).sum := by decide
  have hdescent : baseEnd_735303 < baseStart_735303 := by decide
  rcases family_descends (prefixWord ++ tailWord_735303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735314 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_735314 : Nat := 118140960795 + 735314 * 2 ^ 59
def prefixEnd_735314 : Nat := 4983230072969 + 3 ^ 40 * 735314 * 2
def baseEnd_735314 : Nat := 377569513980241314293359

theorem tailTrace_735314 : CollatzResearch.WordTrace tailWord_735314 prefixEnd_735314 377569513980241314293359 := by
  unfold tailWord_735314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704776214522608619561249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17879403238726956318829997 6704776214522608619561249)
  ·
    refine ⟨5028582160891956464670937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6704776214522608619561249 5028582160891956464670937)
    ·
      refine ⟨3771436620668967348503203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5028582160891956464670937 3771436620668967348503203)
      ·
        refine ⟨5657154931003451022754805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771436620668967348503203 5657154931003451022754805)
        ·
          refine ⟨530358274781573533383263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5657154931003451022754805 530358274781573533383263)
          ·
            refine ⟨795537412172360300074895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530358274781573533383263 795537412172360300074895)
            ·
              refine ⟨1193306118258540450112343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795537412172360300074895 1193306118258540450112343)
              ·
                refine ⟨1789959177387810675168515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193306118258540450112343 1789959177387810675168515)
                ·
                  refine ⟨2684938766081716012752773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789959177387810675168515 2684938766081716012752773)
                  ·
                    refine ⟨503426018640321752391145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684938766081716012752773 503426018640321752391145)
                    ·
                      refine ⟨377569513980241314293359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503426018640321752391145 377569513980241314293359)
                      ·
                        rfl

theorem cell23_735314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_735314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735314 prefixEnd_735314 := by exact prefixLift 735314
  have htrace : WordTrace (prefixWord ++ tailWord_735314) baseStart_735314 baseEnd_735314 := by
    simpa [prefixWord, tailWord_735314, baseEnd_735314] using wordTrace_append hprefix tailTrace_735314
  have hstable : (prefixWord ++ tailWord_735314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735314).length < 2 ^ (prefixWord ++ tailWord_735314).sum := by decide
  have hdescent : baseEnd_735314 < baseStart_735314 := by decide
  rcases family_descends (prefixWord ++ tailWord_735314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735350 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_735350 : Nat := 118140960795 + 735350 * 2 ^ 59
def prefixEnd_735350 : Nat := 4983230072969 + 3 ^ 40 * 735350 * 2
def baseEnd_735350 : Nat := 125862666427934391147731

theorem tailTrace_735350 : CollatzResearch.WordTrace tailWord_735350 prefixEnd_735350 125862666427934391147731 := by
  unfold tailWord_735350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676276117872500789159719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17880278590640008417703669 1676276117872500789159719)
  ·
    refine ⟨2514414176808751183739579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676276117872500789159719 2514414176808751183739579)
    ·
      refine ⟨3771621265213126775609369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2514414176808751183739579 3771621265213126775609369)
      ·
        refine ⟨2828715948909845081707027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3771621265213126775609369 2828715948909845081707027)
        ·
          refine ⟨4243073923364767622560541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828715948909845081707027 4243073923364767622560541)
          ·
            refine ⟨1591152721261787858460203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4243073923364767622560541 1591152721261787858460203)
            ·
              refine ⟨2386729081892681787690305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591152721261787858460203 2386729081892681787690305)
              ·
                refine ⟨1790046811419511340767729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386729081892681787690305 1790046811419511340767729)
                ·
                  refine ⟨1342535108564633505575797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1790046811419511340767729 1342535108564633505575797)
                  ·
                    refine ⟨125862666427934391147731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1342535108564633505575797 125862666427934391147731)
                    ·
                      rfl

theorem cell23_735350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_735350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735350 prefixEnd_735350 := by exact prefixLift 735350
  have htrace : WordTrace (prefixWord ++ tailWord_735350) baseStart_735350 baseEnd_735350 := by
    simpa [prefixWord, tailWord_735350, baseEnd_735350] using wordTrace_append hprefix tailTrace_735350
  have hstable : (prefixWord ++ tailWord_735350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735350).length < 2 ^ (prefixWord ++ tailWord_735350).sum := by decide
  have hdescent : baseEnd_735350 < baseStart_735350 := by decide
  rcases family_descends (prefixWord ++ tailWord_735350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735353 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_735353 : Nat := 118140960795 + 735353 * 2 ^ 59
def prefixEnd_735353 : Nat := 4983230072969 + 3 ^ 40 * 735353 * 2
def baseEnd_735353 : Nat := 377589539725766661705679

theorem tailTrace_735353 : CollatzResearch.WordTrace tailWord_735353 prefixEnd_735353 377589539725766661705679 := by
  unfold tailWord_735353
  simp only [CollatzResearch.WordTrace]
  refine ⟨26820527304949144138914713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17880351536632762759276475 26820527304949144138914713)
  ·
    refine ⟨20115395478711858104186035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26820527304949144138914713 20115395478711858104186035)
    ·
      refine ⟨30173093218067787156279053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20115395478711858104186035 30173093218067787156279053)
      ·
        refine ⟨11314909956775420183604645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30173093218067787156279053 11314909956775420183604645)
        ·
          refine ⟨2121545616895391284425871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11314909956775420183604645 2121545616895391284425871)
          ·
            refine ⟨3182318425343086926638807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121545616895391284425871 3182318425343086926638807)
            ·
              refine ⟨4773477638014630389958211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182318425343086926638807 4773477638014630389958211)
              ·
                refine ⟨7160216457021945584937317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773477638014630389958211 7160216457021945584937317)
                ·
                  refine ⟨1342540585691614797175747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7160216457021945584937317 1342540585691614797175747)
                  ·
                    refine ⟨2013810878537422195763621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1342540585691614797175747 2013810878537422195763621)
                    ·
                      refine ⟨377589539725766661705679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2013810878537422195763621 377589539725766661705679)
                      ·
                        rfl

theorem cell23_735353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_735353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735353 prefixEnd_735353 := by exact prefixLift 735353
  have htrace : WordTrace (prefixWord ++ tailWord_735353) baseStart_735353 baseEnd_735353 := by
    simpa [prefixWord, tailWord_735353, baseEnd_735353] using wordTrace_append hprefix tailTrace_735353
  have hstable : (prefixWord ++ tailWord_735353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735353).length < 2 ^ (prefixWord ++ tailWord_735353).sum := by decide
  have hdescent : baseEnd_735353 < baseStart_735353 := by decide
  rcases family_descends (prefixWord ++ tailWord_735353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735473 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_735473 : Nat := 118140960795 + 735473 * 2 ^ 59
def prefixEnd_735473 : Nat := 4983230072969 + 3 ^ 40 * 735473 * 2
def baseEnd_735473 : Nat := 377651157404306192205127

theorem tailTrace_735473 : CollatzResearch.WordTrace tailWord_735473 prefixEnd_735473 377651157404306192205127 := by
  unfold tailWord_735473
  simp only [CollatzResearch.WordTrace]
  refine ⟨26824904064514404633283073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17883269376342936422188715 26824904064514404633283073)
  ·
    refine ⟨20118678048385803474962305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26824904064514404633283073 20118678048385803474962305)
    ·
      refine ⟨15089008536289352606221729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20118678048385803474962305 15089008536289352606221729)
      ·
        refine ⟨11316756402217014454666297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15089008536289352606221729 11316756402217014454666297)
        ·
          refine ⟨8487567301662760840999723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11316756402217014454666297 8487567301662760840999723)
          ·
            refine ⟨12731350952494141261499585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487567301662760840999723 12731350952494141261499585)
            ·
              refine ⟨9548513214370605946124689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12731350952494141261499585 9548513214370605946124689)
              ·
                refine ⟨7161384910777954459593517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9548513214370605946124689 7161384910777954459593517)
                ·
                  refine ⟨2685519341541732922347569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7161384910777954459593517 2685519341541732922347569)
                  ·
                    refine ⟨2014139506156299691760677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2685519341541732922347569 2014139506156299691760677)
                    ·
                      refine ⟨377651157404306192205127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2014139506156299691760677 377651157404306192205127)
                      ·
                        rfl

theorem cell23_735473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_735473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735473 prefixEnd_735473 := by exact prefixLift 735473
  have htrace : WordTrace (prefixWord ++ tailWord_735473) baseStart_735473 baseEnd_735473 := by
    simpa [prefixWord, tailWord_735473, baseEnd_735473] using wordTrace_append hprefix tailTrace_735473
  have hstable : (prefixWord ++ tailWord_735473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735473).length < 2 ^ (prefixWord ++ tailWord_735473).sum := by decide
  have hdescent : baseEnd_735473 < baseStart_735473 := by decide
  rcases family_descends (prefixWord ++ tailWord_735473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735487 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 2, 4]
def baseStart_735487 : Nat := 118140960795 + 735487 * 2 ^ 59
def prefixEnd_735487 : Nat := 4983230072969 + 3 ^ 40 * 735487 * 2
def baseEnd_735487 : Nat := 125886115377823045810021

theorem tailTrace_735487 : CollatzResearch.WordTrace tailWord_735487 prefixEnd_735487 125886115377823045810021 := by
  unfold tailWord_735487
  simp only [CollatzResearch.WordTrace]
  refine ⟨26825414686463685024292715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17883609790975790016195143 26825414686463685024292715)
  ·
    refine ⟨40238122029695527536439073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26825414686463685024292715 40238122029695527536439073)
    ·
      refine ⟨30178591522271645652329305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40238122029695527536439073 30178591522271645652329305)
      ·
        refine ⟨22633943641703734239246979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30178591522271645652329305 22633943641703734239246979)
        ·
          refine ⟨33950915462555601358870469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22633943641703734239246979 33950915462555601358870469)
          ·
            refine ⟨6365796649229175254788213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33950915462555601358870469 6365796649229175254788213)
            ·
              refine ⟨596793435865235180136395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6365796649229175254788213 596793435865235180136395)
              ·
                refine ⟨895190153797852770204593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596793435865235180136395 895190153797852770204593)
                ·
                  refine ⟨671392615348389577653445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 895190153797852770204593 671392615348389577653445)
                  ·
                    refine ⟨125886115377823045810021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 671392615348389577653445 125886115377823045810021)
                    ·
                      rfl

theorem cell23_735487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 4].length) (baseStart_735487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735487 prefixEnd_735487 := by exact prefixLift 735487
  have htrace : WordTrace (prefixWord ++ tailWord_735487) baseStart_735487 baseEnd_735487 := by
    simpa [prefixWord, tailWord_735487, baseEnd_735487] using wordTrace_append hprefix tailTrace_735487
  have hstable : (prefixWord ++ tailWord_735487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735487).length < 2 ^ (prefixWord ++ tailWord_735487).sum := by decide
  have hdescent : baseEnd_735487 < baseStart_735487 := by decide
  rcases family_descends (prefixWord ++ tailWord_735487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735497 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 3]
def baseStart_735497 : Nat := 118140960795 + 735497 * 2 ^ 59
def prefixEnd_735497 : Nat := 4983230072969 + 3 ^ 40 * 735497 * 2
def baseEnd_735497 : Nat := 377663480940014098305017

theorem tailTrace_735497 : CollatzResearch.WordTrace tailWord_735497 prefixEnd_735497 377663480940014098305017 := by
  unfold tailWord_735497
  simp only [CollatzResearch.WordTrace]
  refine ⟨26825779416427456732156745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17883852944284971154771163 26825779416427456732156745)
  ·
    refine ⟨20119334562320592549117559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26825779416427456732156745 20119334562320592549117559)
    ·
      refine ⟨30179001843480888823676339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20119334562320592549117559 30179001843480888823676339)
      ·
        refine ⟨45268502765221333235514509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30179001843480888823676339 45268502765221333235514509)
        ·
          refine ⟨16975688536957999963317941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45268502765221333235514509 16975688536957999963317941)
          ·
            refine ⟨1591470800339812496561057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16975688536957999963317941 1591470800339812496561057)
            ·
              refine ⟨1193603100254859372420793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591470800339812496561057 1193603100254859372420793)
              ·
                refine ⟨895202325191144529315595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193603100254859372420793 895202325191144529315595)
                ·
                  refine ⟨1342803487786716793973393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895202325191144529315595 1342803487786716793973393)
                  ·
                    refine ⟨1007102615840037595480045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1342803487786716793973393 1007102615840037595480045)
                    ·
                      refine ⟨377663480940014098305017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007102615840037595480045 377663480940014098305017)
                      ·
                        rfl

theorem cell23_735497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_735497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735497 prefixEnd_735497 := by exact prefixLift 735497
  have htrace : WordTrace (prefixWord ++ tailWord_735497) baseStart_735497 baseEnd_735497 := by
    simpa [prefixWord, tailWord_735497, baseEnd_735497] using wordTrace_append hprefix tailTrace_735497
  have hstable : (prefixWord ++ tailWord_735497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735497).length < 2 ^ (prefixWord ++ tailWord_735497).sum := by decide
  have hdescent : baseEnd_735497 < baseStart_735497 := by decide
  rcases family_descends (prefixWord ++ tailWord_735497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735511 : List Nat := [1, 1, 3, 4, 1, 2, 3, 3, 1, 2, 2]
def baseStart_735511 : Nat := 118140960795 + 735511 * 2 ^ 59
def prefixEnd_735511 : Nat := 4983230072969 + 3 ^ 40 * 735511 * 2
def baseEnd_735511 : Nat := 377670669669177043529953

theorem tailTrace_735511 : CollatzResearch.WordTrace tailWord_735511 prefixEnd_735511 377670669669177043529953 := by
  unfold tailWord_735511
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826290038376737123166387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17884193358917824748777591 26826290038376737123166387)
  ·
    refine ⟨40239435057565105684749581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26826290038376737123166387 40239435057565105684749581)
    ·
      refine ⟨15089788146586914631781093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40239435057565105684749581 15089788146586914631781093)
      ·
        refine ⟨2829335277485046493458955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15089788146586914631781093 2829335277485046493458955)
        ·
          refine ⟨4244002916227569740188433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829335277485046493458955 4244002916227569740188433)
          ·
            refine ⟨3183002187170677305141325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4244002916227569740188433 3183002187170677305141325)
            ·
              refine ⟨1193625820189003989427997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3183002187170677305141325 1193625820189003989427997)
              ·
                refine ⟨447609682570876496035499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193625820189003989427997 447609682570876496035499)
                ·
                  refine ⟨671414523856314744053249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447609682570876496035499 671414523856314744053249)
                  ·
                    refine ⟨503560892892236058039937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 671414523856314744053249 503560892892236058039937)
                    ·
                      refine ⟨377670669669177043529953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503560892892236058039937 377670669669177043529953)
                      ·
                        rfl

theorem cell23_735511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_735511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735511 prefixEnd_735511 := by exact prefixLift 735511
  have htrace : WordTrace (prefixWord ++ tailWord_735511) baseStart_735511 baseEnd_735511 := by
    simpa [prefixWord, tailWord_735511, baseEnd_735511] using wordTrace_append hprefix tailTrace_735511
  have hstable : (prefixWord ++ tailWord_735511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735511).length < 2 ^ (prefixWord ++ tailWord_735511).sum := by decide
  have hdescent : baseEnd_735511 < baseStart_735511 := by decide
  rcases family_descends (prefixWord ++ tailWord_735511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735517 : List Nat := [1, 4, 2, 3, 3, 1, 9]
def baseStart_735517 : Nat := 118140960795 + 735517 * 2 ^ 59
def prefixEnd_735517 : Nat := 4983230072969 + 3 ^ 40 * 735517 * 2
def baseEnd_735517 : Nat := 4662638895717333580925

theorem tailTrace_735517 : CollatzResearch.WordTrace tailWord_735517 prefixEnd_735517 4662638895717333580925 := by
  unfold tailWord_735517
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826508876355000147884805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17884339250903333431923203 26826508876355000147884805)
  ·
    refine ⟨5029970414316562527728401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26826508876355000147884805 5029970414316562527728401)
    ·
      refine ⟨3772477810737421895796301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5029970414316562527728401 3772477810737421895796301)
      ·
        refine ⟨1414679179026533210923613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3772477810737421895796301 1414679179026533210923613)
        ·
          refine ⟨530504692134949954096355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1414679179026533210923613 530504692134949954096355)
          ·
            refine ⟨795757038202424931144533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530504692134949954096355 795757038202424931144533)
            ·
              refine ⟨4662638895717333580925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 795757038202424931144533 4662638895717333580925)
              ·
                rfl

theorem cell23_735517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 9].length) (baseStart_735517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735517 prefixEnd_735517 := by exact prefixLift 735517
  have htrace : WordTrace (prefixWord ++ tailWord_735517) baseStart_735517 baseEnd_735517 := by
    simpa [prefixWord, tailWord_735517, baseEnd_735517] using wordTrace_append hprefix tailTrace_735517
  have hstable : (prefixWord ++ tailWord_735517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735517).length < 2 ^ (prefixWord ++ tailWord_735517).sum := by decide
  have hdescent : baseEnd_735517 < baseStart_735517 := by decide
  rcases family_descends (prefixWord ++ tailWord_735517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735523 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5]
def baseStart_735523 : Nat := 118140960795 + 735523 * 2 ^ 59
def prefixEnd_735523 : Nat := 4983230072969 + 3 ^ 40 * 735523 * 2
def baseEnd_735523 : Nat := 377676831437030996579897

theorem tailTrace_735523 : CollatzResearch.WordTrace tailWord_735523 prefixEnd_735523 377676831437030996579897 := by
  unfold tailWord_735523
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826727714333263172603223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17884485142888842115068815 26826727714333263172603223)
  ·
    refine ⟨40240091571499894758904835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26826727714333263172603223 40240091571499894758904835)
    ·
      refine ⟨60360137357249842138357253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40240091571499894758904835 60360137357249842138357253)
      ·
        refine ⟨11317525754484345400941985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60360137357249842138357253 11317525754484345400941985)
        ·
          refine ⟨8488144315863259050706489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11317525754484345400941985 8488144315863259050706489)
          ·
            refine ⟨6366108236897444288029867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8488144315863259050706489 6366108236897444288029867)
            ·
              refine ⟨9549162355346166432044801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6366108236897444288029867 9549162355346166432044801)
              ·
                refine ⟨7161871766509624824033601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9549162355346166432044801 7161871766509624824033601)
                ·
                  refine ⟨5371403824882218618025201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7161871766509624824033601 5371403824882218618025201)
                  ·
                    refine ⟨4028552868661663963518901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5371403824882218618025201 4028552868661663963518901)
                    ·
                      refine ⟨377676831437030996579897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4028552868661663963518901 377676831437030996579897)
                      ·
                        rfl

theorem cell23_735523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_735523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735523 prefixEnd_735523 := by exact prefixLift 735523
  have htrace : WordTrace (prefixWord ++ tailWord_735523) baseStart_735523 baseEnd_735523 := by
    simpa [prefixWord, tailWord_735523, baseEnd_735523] using wordTrace_append hprefix tailTrace_735523
  have hstable : (prefixWord ++ tailWord_735523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735523).length < 2 ^ (prefixWord ++ tailWord_735523).sum := by decide
  have hdescent : baseEnd_735523 < baseStart_735523 := by decide
  rcases family_descends (prefixWord ++ tailWord_735523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735528 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_735528 : Nat := 118140960795 + 735528 * 2 ^ 59
def prefixEnd_735528 : Nat := 4983230072969 + 3 ^ 40 * 735528 * 2
def baseEnd_735528 : Nat := 377679398840303477017375

theorem tailTrace_735528 : CollatzResearch.WordTrace tailWord_735528 prefixEnd_735528 377679398840303477017375 := by
  unfold tailWord_735528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13413455039657574513267619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17884606719543432684356825 13413455039657574513267619)
  ·
    refine ⟨20120182559486361769901429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13413455039657574513267619 20120182559486361769901429)
    ·
      refine ⟨1886267114951846415928259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20120182559486361769901429 1886267114951846415928259)
      ·
        refine ⟨2829400672427769623892389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886267114951846415928259 2829400672427769623892389)
        ·
          refine ⟨530512626080206804479823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2829400672427769623892389 530512626080206804479823)
          ·
            refine ⟨795768939120310206719735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530512626080206804479823 795768939120310206719735)
            ·
              refine ⟨1193653408680465310079603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795768939120310206719735 1193653408680465310079603)
              ·
                refine ⟨1790480113020697965119405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193653408680465310079603 1790480113020697965119405)
                ·
                  refine ⟨671430042382761736919777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1790480113020697965119405 671430042382761736919777)
                  ·
                    refine ⟨503572531787071302689833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 671430042382761736919777 503572531787071302689833)
                    ·
                      refine ⟨377679398840303477017375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503572531787071302689833 377679398840303477017375)
                      ·
                        rfl

theorem cell23_735528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_735528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735528 prefixEnd_735528 := by exact prefixLift 735528
  have htrace : WordTrace (prefixWord ++ tailWord_735528) baseStart_735528 baseEnd_735528 := by
    simpa [prefixWord, tailWord_735528, baseEnd_735528] using wordTrace_append hprefix tailTrace_735528
  have hstable : (prefixWord ++ tailWord_735528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735528).length < 2 ^ (prefixWord ++ tailWord_735528).sum := by decide
  have hdescent : baseEnd_735528 < baseStart_735528 := by decide
  rcases family_descends (prefixWord ++ tailWord_735528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735543 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 2, 6]
def baseStart_735543 : Nat := 118140960795 + 735543 * 2 ^ 59
def prefixEnd_735543 : Nat := 4983230072969 + 3 ^ 40 * 735543 * 2
def baseEnd_735543 : Nat := 125895700350040306109935

theorem tailTrace_735543 : CollatzResearch.WordTrace tailWord_735543 prefixEnd_735543 125895700350040306109935 := by
  unfold tailWord_735543
  simp only [CollatzResearch.WordTrace]
  refine ⟨26827457174260806588331283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17884971449507204392220855 26827457174260806588331283)
  ·
    refine ⟨40241185761391209882496925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26827457174260806588331283 40241185761391209882496925)
    ·
      refine ⟨15090444660521703705936347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40241185761391209882496925 15090444660521703705936347)
      ·
        refine ⟨22635666990782555558904521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15090444660521703705936347 22635666990782555558904521)
        ·
          refine ⟨16976750243086916669178391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22635666990782555558904521 16976750243086916669178391)
          ·
            refine ⟨25465125364630375003767587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16976750243086916669178391 25465125364630375003767587)
            ·
              refine ⟨38197688046945562505651381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25465125364630375003767587 38197688046945562505651381)
              ·
                refine ⟨3581033254401146484904817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38197688046945562505651381 3581033254401146484904817)
                ·
                  refine ⟨2685774940800859863678613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581033254401146484904817 2685774940800859863678613)
                  ·
                    refine ⟨125895700350040306109935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2685774940800859863678613 125895700350040306109935)
                    ·
                      rfl

theorem cell23_735543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_735543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735543 prefixEnd_735543 := by exact prefixLift 735543
  have htrace : WordTrace (prefixWord ++ tailWord_735543) baseStart_735543 baseEnd_735543 := by
    simpa [prefixWord, tailWord_735543, baseEnd_735543] using wordTrace_append hprefix tailTrace_735543
  have hstable : (prefixWord ++ tailWord_735543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735543).length < 2 ^ (prefixWord ++ tailWord_735543).sum := by decide
  have hdescent : baseEnd_735543 < baseStart_735543 := by decide
  rcases family_descends (prefixWord ++ tailWord_735543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735544 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 2, 1, 3]
def baseStart_735544 : Nat := 118140960795 + 735544 * 2 ^ 59
def prefixEnd_735544 : Nat := 4983230072969 + 3 ^ 40 * 735544 * 2
def baseEnd_735544 : Nat := 377687614530775414417301

theorem tailTrace_735544 : CollatzResearch.WordTrace tailWord_735544 prefixEnd_735544 377687614530775414417301 := by
  unfold tailWord_735544
  simp only [CollatzResearch.WordTrace]
  refine ⟨13413746823628591879558843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17884995764838122506078457 13413746823628591879558843)
  ·
    refine ⟨20120620235442887819338265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13413746823628591879558843 20120620235442887819338265)
    ·
      refine ⟨15090465176582165864503699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20120620235442887819338265 15090465176582165864503699)
      ·
        refine ⟨22635697764873248796755549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15090465176582165864503699 22635697764873248796755549)
        ·
          refine ⟨8488386661827468298783331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22635697764873248796755549 8488386661827468298783331)
          ·
            refine ⟨12732579992741202448174997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488386661827468298783331 12732579992741202448174997)
            ·
              refine ⟨596839687159743864758203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12732579992741202448174997 596839687159743864758203)
              ·
                refine ⟨895259530739615797137305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596839687159743864758203 895259530739615797137305)
                ·
                  refine ⟨671444648054711847852979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 895259530739615797137305 671444648054711847852979)
                  ·
                    refine ⟨1007166972082067771779469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671444648054711847852979 1007166972082067771779469)
                    ·
                      refine ⟨377687614530775414417301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007166972082067771779469 377687614530775414417301)
                      ·
                        rfl

theorem cell23_735544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_735544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735544 prefixEnd_735544 := by exact prefixLift 735544
  have htrace : WordTrace (prefixWord ++ tailWord_735544) baseStart_735544 baseEnd_735544 := by
    simpa [prefixWord, tailWord_735544, baseEnd_735544] using wordTrace_append hprefix tailTrace_735544
  have hstable : (prefixWord ++ tailWord_735544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735544).length < 2 ^ (prefixWord ++ tailWord_735544).sum := by decide
  have hdescent : baseEnd_735544 < baseStart_735544 := by decide
  rcases family_descends (prefixWord ++ tailWord_735544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735563 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4]
def baseStart_735563 : Nat := 118140960795 + 735563 * 2 ^ 59
def prefixEnd_735563 : Nat := 4983230072969 + 3 ^ 40 * 735563 * 2
def baseEnd_735563 : Nat := 377697370663210840079713

theorem tailTrace_735563 : CollatzResearch.WordTrace tailWord_735563 prefixEnd_735563 377697370663210840079713 := by
  unfold tailWord_735563
  simp only [CollatzResearch.WordTrace]
  refine ⟨26828186634188350004059343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17885457756125566669372895 26828186634188350004059343)
  ·
    refine ⟨40242279951282525006089015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26828186634188350004059343 40242279951282525006089015)
    ·
      refine ⟨60363419926923787509133523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40242279951282525006089015 60363419926923787509133523)
      ·
        refine ⟨90545129890385681263700285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60363419926923787509133523 90545129890385681263700285)
        ·
          refine ⟨33954423708894630473887607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90545129890385681263700285 33954423708894630473887607)
          ·
            refine ⟨50931635563341945710831411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33954423708894630473887607 50931635563341945710831411)
            ·
              refine ⟨76397453345012918566247117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50931635563341945710831411 76397453345012918566247117)
              ·
                refine ⟨28649045004379844462342669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76397453345012918566247117 28649045004379844462342669)
                ·
                  refine ⟨10743391876642441673378501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28649045004379844462342669 10743391876642441673378501)
                  ·
                    refine ⟨2014385976870457813758469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10743391876642441673378501 2014385976870457813758469)
                    ·
                      refine ⟨377697370663210840079713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2014385976870457813758469 377697370663210840079713)
                      ·
                        rfl

theorem cell23_735563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_735563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735563 prefixEnd_735563 := by exact prefixLift 735563
  have htrace : WordTrace (prefixWord ++ tailWord_735563) baseStart_735563 baseEnd_735563 := by
    simpa [prefixWord, tailWord_735563, baseEnd_735563] using wordTrace_append hprefix tailTrace_735563
  have hstable : (prefixWord ++ tailWord_735563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735563).length < 2 ^ (prefixWord ++ tailWord_735563).sum := by decide
  have hdescent : baseEnd_735563 < baseStart_735563 := by decide
  rcases family_descends (prefixWord ++ tailWord_735563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735567 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 4, 2, 2]
def baseStart_735567 : Nat := 118140960795 + 735567 * 2 ^ 59
def prefixEnd_735567 : Nat := 4983230072969 + 3 ^ 40 * 735567 * 2
def baseEnd_735567 : Nat := 377699424585828824429695

theorem tailTrace_735567 : CollatzResearch.WordTrace tailWord_735567 prefixEnd_735567 377699424585828824429695 := by
  unfold tailWord_735567
  simp only [CollatzResearch.WordTrace]
  refine ⟨26828332526173858687204955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17885555017449239124803303 26828332526173858687204955)
  ·
    refine ⟨40242498789260788030807433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26828332526173858687204955 40242498789260788030807433)
    ·
      refine ⟨30181874091945591023105575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40242498789260788030807433 30181874091945591023105575)
      ·
        refine ⟨45272811137918386534658363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30181874091945591023105575 45272811137918386534658363)
        ·
          refine ⟨67909216706877579801987545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45272811137918386534658363 67909216706877579801987545)
          ·
            refine ⟨50931912530158184851490659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67909216706877579801987545 50931912530158184851490659)
            ·
              refine ⟨76397868795237277277235989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50931912530158184851490659 76397868795237277277235989)
              ·
                refine ⟨3581150099776747372370437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76397868795237277277235989 3581150099776747372370437)
                ·
                  refine ⟨671465643708140132319457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3581150099776747372370437 671465643708140132319457)
                  ·
                    refine ⟨503599232781105099239593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 671465643708140132319457 503599232781105099239593)
                    ·
                      refine ⟨377699424585828824429695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503599232781105099239593 377699424585828824429695)
                      ·
                        rfl

theorem cell23_735567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 2, 2].length) (baseStart_735567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735567 prefixEnd_735567 := by exact prefixLift 735567
  have htrace : WordTrace (prefixWord ++ tailWord_735567) baseStart_735567 baseEnd_735567 := by
    simpa [prefixWord, tailWord_735567, baseEnd_735567] using wordTrace_append hprefix tailTrace_735567
  have hstable : (prefixWord ++ tailWord_735567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735567).length < 2 ^ (prefixWord ++ tailWord_735567).sum := by decide
  have hdescent : baseEnd_735567 < baseStart_735567 := by decide
  rcases family_descends (prefixWord ++ tailWord_735567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735570 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_735570 : Nat := 118140960795 + 735570 * 2 ^ 59
def prefixEnd_735570 : Nat := 4983230072969 + 3 ^ 40 * 735570 * 2
def baseEnd_735570 : Nat := 377700965027792312692181

theorem tailTrace_735570 : CollatzResearch.WordTrace tailWord_735570 prefixEnd_735570 377700965027792312692181 := by
  unfold tailWord_735570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6707110486290747549891041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17885627963441993466376109 6707110486290747549891041)
  ·
    refine ⟨5030332864718060662418281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6707110486290747549891041 5030332864718060662418281)
    ·
      refine ⟨3772749648538545496813711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5030332864718060662418281 3772749648538545496813711)
      ·
        refine ⟨5659124472807818245220567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772749648538545496813711 5659124472807818245220567)
        ·
          refine ⟨8488686709211727367830851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659124472807818245220567 8488686709211727367830851)
          ·
            refine ⟨12733030063817591051746277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488686709211727367830851 12733030063817591051746277)
            ·
              refine ⟨2387443136965798322202427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12733030063817591051746277 2387443136965798322202427)
              ·
                refine ⟨3581164705448697483303641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387443136965798322202427 3581164705448697483303641)
                ·
                  refine ⟨2685873529086523112477731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581164705448697483303641 2685873529086523112477731)
                  ·
                    refine ⟨4028810293629784668716597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2685873529086523112477731 4028810293629784668716597)
                    ·
                      refine ⟨377700965027792312692181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4028810293629784668716597 377700965027792312692181)
                      ·
                        rfl

theorem cell23_735570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_735570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735570 prefixEnd_735570 := by exact prefixLift 735570
  have htrace : WordTrace (prefixWord ++ tailWord_735570) baseStart_735570 baseEnd_735570 := by
    simpa [prefixWord, tailWord_735570, baseEnd_735570] using wordTrace_append hprefix tailTrace_735570
  have hstable : (prefixWord ++ tailWord_735570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735570).length < 2 ^ (prefixWord ++ tailWord_735570).sum := by decide
  have hdescent : baseEnd_735570 < baseStart_735570 := by decide
  rcases family_descends (prefixWord ++ tailWord_735570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735583 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_735583 : Nat := 118140960795 + 735583 * 2 ^ 59
def prefixEnd_735583 : Nat := 4983230072969 + 3 ^ 40 * 735583 * 2
def baseEnd_735583 : Nat := 377707640276300761829621

theorem tailTrace_735583 : CollatzResearch.WordTrace tailWord_735583 prefixEnd_735583 377707640276300761829621 := by
  unfold tailWord_735583
  simp only [CollatzResearch.WordTrace]
  refine ⟨26828916094115893419787403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17885944062743928946524935 26828916094115893419787403)
  ·
    refine ⟨40243374141173840129681105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26828916094115893419787403 40243374141173840129681105)
    ·
      refine ⟨30182530605880380097260829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40243374141173840129681105 30182530605880380097260829)
      ·
        refine ⟨11318448977205142536472811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30182530605880380097260829 11318448977205142536472811)
        ·
          refine ⟨16977673465807713804709217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11318448977205142536472811 16977673465807713804709217)
          ·
            refine ⟨12733255099355785353531913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16977673465807713804709217 12733255099355785353531913)
            ·
              refine ⟨9549941324516839015148935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12733255099355785353531913 9549941324516839015148935)
              ·
                refine ⟨14324911986775258522723403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9549941324516839015148935 14324911986775258522723403)
                ·
                  refine ⟨21487367980162887784085105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14324911986775258522723403 21487367980162887784085105)
                  ·
                    refine ⟨16115525985122165838063829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21487367980162887784085105 16115525985122165838063829)
                    ·
                      refine ⟨377707640276300761829621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16115525985122165838063829 377707640276300761829621)
                      ·
                        rfl

theorem cell23_735583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_735583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735583 prefixEnd_735583 := by exact prefixLift 735583
  have htrace : WordTrace (prefixWord ++ tailWord_735583) baseStart_735583 baseEnd_735583 := by
    simpa [prefixWord, tailWord_735583, baseEnd_735583] using wordTrace_append hprefix tailTrace_735583
  have hstable : (prefixWord ++ tailWord_735583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735583).length < 2 ^ (prefixWord ++ tailWord_735583).sum := by decide
  have hdescent : baseEnd_735583 < baseStart_735583 := by decide
  rcases family_descends (prefixWord ++ tailWord_735583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735600 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3]
def baseStart_735600 : Nat := 118140960795 + 735600 * 2 ^ 59
def prefixEnd_735600 : Nat := 4983230072969 + 3 ^ 40 * 735600 * 2
def baseEnd_735600 : Nat := 377716369447427195317043

theorem tailTrace_735600 : CollatzResearch.WordTrace tailWord_735600 prefixEnd_735600 377716369447427195317043 := by
  unfold tailWord_735600
  simp only [CollatzResearch.WordTrace]
  refine ⟨13414768067527152661578127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17886357423369536882104169 13414768067527152661578127)
  ·
    refine ⟨20122152101290728992367191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13414768067527152661578127 20122152101290728992367191)
    ·
      refine ⟨30183228151936093488550787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20122152101290728992367191 30183228151936093488550787)
      ·
        refine ⟨45274842227904140232826181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30183228151936093488550787 45274842227904140232826181)
        ·
          refine ⟨8489032917732026293654909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45274842227904140232826181 8489032917732026293654909)
          ·
            refine ⟨3183387344149509860120591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8489032917732026293654909 3183387344149509860120591)
            ·
              refine ⟨4775081016224264790180887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183387344149509860120591 4775081016224264790180887)
              ·
                refine ⟨7162621524336397185271331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775081016224264790180887 7162621524336397185271331)
                ·
                  refine ⟨10743932286504595777906997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7162621524336397185271331 10743932286504595777906997)
                  ·
                    refine ⟨1007243651859805854178781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10743932286504595777906997 1007243651859805854178781)
                    ·
                      refine ⟨377716369447427195317043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007243651859805854178781 377716369447427195317043)
                      ·
                        rfl

theorem cell23_735600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_735600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735600 prefixEnd_735600 := by exact prefixLift 735600
  have htrace : WordTrace (prefixWord ++ tailWord_735600) baseStart_735600 baseEnd_735600 := by
    simpa [prefixWord, tailWord_735600, baseEnd_735600] using wordTrace_append hprefix tailTrace_735600
  have hstable : (prefixWord ++ tailWord_735600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735600).length < 2 ^ (prefixWord ++ tailWord_735600).sum := by decide
  have hdescent : baseEnd_735600 < baseStart_735600 := by decide
  rcases family_descends (prefixWord ++ tailWord_735600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735603 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 3, 7]
def baseStart_735603 : Nat := 118140960795 + 735603 * 2 ^ 59
def prefixEnd_735603 : Nat := 4983230072969 + 3 ^ 40 * 735603 * 2
def baseEnd_735603 : Nat := 125905969963130227859843

theorem tailTrace_735603 : CollatzResearch.WordTrace tailWord_735603 prefixEnd_735603 125905969963130227859843 := by
  unfold tailWord_735603
  simp only [CollatzResearch.WordTrace]
  refine ⟨26829645554043436835515463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17886430369362291223676975 26829645554043436835515463)
  ·
    refine ⟨40244468331065155253273195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26829645554043436835515463 40244468331065155253273195)
    ·
      refine ⟨60366702496597732879909793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40244468331065155253273195 60366702496597732879909793)
      ·
        refine ⟨45275026872448299659932345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60366702496597732879909793 45275026872448299659932345)
        ·
          refine ⟨33956270154336224744949259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45275026872448299659932345 33956270154336224744949259)
          ·
            refine ⟨50934405231504337117423889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33956270154336224744949259 50934405231504337117423889)
            ·
              refine ⟨38200803923628252838067917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50934405231504337117423889 38200803923628252838067917)
              ·
                refine ⟨14325301471360594814275469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38200803923628252838067917 14325301471360594814275469)
                ·
                  refine ⟨5371988051760223055353301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14325301471360594814275469 5371988051760223055353301)
                  ·
                    refine ⟨125905969963130227859843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5371988051760223055353301 125905969963130227859843)
                    ·
                      rfl

theorem cell23_735603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 7].length) (baseStart_735603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735603 prefixEnd_735603 := by exact prefixLift 735603
  have htrace : WordTrace (prefixWord ++ tailWord_735603) baseStart_735603 baseEnd_735603 := by
    simpa [prefixWord, tailWord_735603, baseEnd_735603] using wordTrace_append hprefix tailTrace_735603
  have hstable : (prefixWord ++ tailWord_735603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735603).length < 2 ^ (prefixWord ++ tailWord_735603).sum := by decide
  have hdescent : baseEnd_735603 < baseStart_735603 := by decide
  rcases family_descends (prefixWord ++ tailWord_735603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735620 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_735620 : Nat := 118140960795 + 735620 * 2 ^ 59
def prefixEnd_735620 : Nat := 4983230072969 + 3 ^ 40 * 735620 * 2
def baseEnd_735620 : Nat := 125908879686839039022317

theorem tailTrace_735620 : CollatzResearch.WordTrace tailWord_735620 prefixEnd_735620 125908879686839039022317 := by
  unfold tailWord_735620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415132797490924369442157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17886843729987899159256209 13415132797490924369442157)
  ·
    refine ⟨5030674799059096638540809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13415132797490924369442157 5030674799059096638540809)
    ·
      refine ⟨3773006099294322478905607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5030674799059096638540809 3773006099294322478905607)
      ·
        refine ⟨5659509148941483718358411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773006099294322478905607 5659509148941483718358411)
        ·
          refine ⟨8489263723412225577537617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659509148941483718358411 8489263723412225577537617)
          ·
            refine ⟨6366947792559169183153213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8489263723412225577537617 6366947792559169183153213)
            ·
              refine ⟨2387605422209688443682455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6366947792559169183153213 2387605422209688443682455)
              ·
                refine ⟨3581408133314532665523683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387605422209688443682455 3581408133314532665523683)
                ·
                  refine ⟨5372112199971798998285525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581408133314532665523683 5372112199971798998285525)
                  ·
                    refine ⟨125908879686839039022317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5372112199971798998285525 125908879686839039022317)
                    ·
                      rfl

theorem cell23_735620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_735620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735620 prefixEnd_735620 := by exact prefixLift 735620
  have htrace : WordTrace (prefixWord ++ tailWord_735620) baseStart_735620 baseEnd_735620 := by
    simpa [prefixWord, tailWord_735620, baseEnd_735620] using wordTrace_append hprefix tailTrace_735620
  have hstable : (prefixWord ++ tailWord_735620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735620).length < 2 ^ (prefixWord ++ tailWord_735620).sum := by decide
  have hdescent : baseEnd_735620 < baseStart_735620 := by decide
  rcases family_descends (prefixWord ++ tailWord_735620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735677 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_735677 : Nat := 118140960795 + 735677 * 2 ^ 59
def prefixEnd_735677 : Nat := 4983230072969 + 3 ^ 40 * 735677 * 2
def baseEnd_735677 : Nat := 377755907457823394054189

theorem tailTrace_735677 : CollatzResearch.WordTrace tailWord_735677 prefixEnd_735677 377755907457823394054189 := by
  unfold tailWord_735677
  simp only [CollatzResearch.WordTrace]
  refine ⟨26832344555775347473709285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17888229703850231649139523 26832344555775347473709285)
  ·
    refine ⟨5031064604207877651320491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26832344555775347473709285 5031064604207877651320491)
    ·
      refine ⟨7546596906311816476980737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5031064604207877651320491 7546596906311816476980737)
      ·
        refine ⟨5659947679733862357735553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7546596906311816476980737 5659947679733862357735553)
        ·
          refine ⟨4244960759800396768301665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5659947679733862357735553 4244960759800396768301665)
          ·
            refine ⟨3183720569850297576226249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4244960759800396768301665 3183720569850297576226249)
            ·
              refine ⟨2387790427387723182169687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3183720569850297576226249 2387790427387723182169687)
              ·
                refine ⟨3581685641081584773254531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387790427387723182169687 3581685641081584773254531)
                ·
                  refine ⟨5372528461622377159881797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581685641081584773254531 5372528461622377159881797)
                  ·
                    refine ⟨1007349086554195717477837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5372528461622377159881797 1007349086554195717477837)
                    ·
                      refine ⟨377755907457823394054189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007349086554195717477837 377755907457823394054189)
                      ·
                        rfl

theorem cell23_735677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_735677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735677 prefixEnd_735677 := by exact prefixLift 735677
  have htrace : WordTrace (prefixWord ++ tailWord_735677) baseStart_735677 baseEnd_735677 := by
    simpa [prefixWord, tailWord_735677, baseEnd_735677] using wordTrace_append hprefix tailTrace_735677
  have hstable : (prefixWord ++ tailWord_735677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735677).length < 2 ^ (prefixWord ++ tailWord_735677).sum := by decide
  have hdescent : baseEnd_735677 < baseStart_735677 := by decide
  rcases family_descends (prefixWord ++ tailWord_735677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735741 : List Nat := [1, 4, 1, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_735741 : Nat := 118140960795 + 735741 * 2 ^ 59
def prefixEnd_735741 : Nat := 4983230072969 + 3 ^ 40 * 735741 * 2
def baseEnd_735741 : Nat := 377788770219711143653895

theorem tailTrace_735741 : CollatzResearch.WordTrace tailWord_735741 prefixEnd_735741 377788770219711143653895 := by
  unfold tailWord_735741
  simp only [CollatzResearch.WordTrace]
  refine ⟨26834678827543486404039077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17889785885028990936026051 26834678827543486404039077)
  ·
    refine ⟨5031502280164403700757327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26834678827543486404039077 5031502280164403700757327)
    ·
      refine ⟨7547253420246605551135991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5031502280164403700757327 7547253420246605551135991)
      ·
        refine ⟨11320880130369908326703987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7547253420246605551135991 11320880130369908326703987)
        ·
          refine ⟨16981320195554862490055981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11320880130369908326703987 16981320195554862490055981)
          ·
            refine ⟨6367995073333073433770993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16981320195554862490055981 6367995073333073433770993)
            ·
              refine ⟨4775996304999805075328245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6367995073333073433770993 4775996304999805075328245)
              ·
                refine ⟨447749653593731725812023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4775996304999805075328245 447749653593731725812023)
                ·
                  refine ⟨671624480390597588718035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447749653593731725812023 671624480390597588718035)
                  ·
                    refine ⟨1007436720585896383077053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671624480390597588718035 1007436720585896383077053)
                    ·
                      refine ⟨377788770219711143653895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007436720585896383077053 377788770219711143653895)
                      ·
                        rfl

theorem cell23_735741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_735741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735741 prefixEnd_735741 := by exact prefixLift 735741
  have htrace : WordTrace (prefixWord ++ tailWord_735741) baseStart_735741 baseEnd_735741 := by
    simpa [prefixWord, tailWord_735741, baseEnd_735741] using wordTrace_append hprefix tailTrace_735741
  have hstable : (prefixWord ++ tailWord_735741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735741).length < 2 ^ (prefixWord ++ tailWord_735741).sum := by decide
  have hdescent : baseEnd_735741 < baseStart_735741 := by decide
  rcases family_descends (prefixWord ++ tailWord_735741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735758 : List Nat := [4, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_735758 : Nat := 118140960795 + 735758 * 2 ^ 59
def prefixEnd_735758 : Nat := 4983230072969 + 3 ^ 40 * 735758 * 2
def baseEnd_735758 : Nat := 377797499390837577141317

theorem tailTrace_735758 : CollatzResearch.WordTrace tailWord_735758 prefixEnd_735758 377797499390837577141317 := by
  unfold tailWord_735758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354412358560237288425991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17890199245654598871605285 3354412358560237288425991)
  ·
    refine ⟨5031618537840355932638987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3354412358560237288425991 5031618537840355932638987)
    ·
      refine ⟨7547427806760533898958481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5031618537840355932638987 7547427806760533898958481)
      ·
        refine ⟨5660570855070400424218861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7547427806760533898958481 5660570855070400424218861)
        ·
          refine ⟨2122714070651400159082073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5660570855070400424218861 2122714070651400159082073)
          ·
            refine ⟨1592035552988550119311555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122714070651400159082073 1592035552988550119311555)
            ·
              refine ⟨2388053329482825178967333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592035552988550119311555 2388053329482825178967333)
              ·
                refine ⟨447759999278029721056375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2388053329482825178967333 447759999278029721056375)
                ·
                  refine ⟨671639998917044581584563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447759999278029721056375 671639998917044581584563)
                  ·
                    refine ⟨1007459998375566872376845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671639998917044581584563 1007459998375566872376845)
                    ·
                      refine ⟨377797499390837577141317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007459998375566872376845 377797499390837577141317)
                      ·
                        rfl

theorem cell23_735758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_735758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735758 prefixEnd_735758 := by exact prefixLift 735758
  have htrace : WordTrace (prefixWord ++ tailWord_735758) baseStart_735758 baseEnd_735758 := by
    simpa [prefixWord, tailWord_735758, baseEnd_735758] using wordTrace_append hprefix tailTrace_735758
  have hstable : (prefixWord ++ tailWord_735758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735758).length < 2 ^ (prefixWord ++ tailWord_735758).sum := by decide
  have hdescent : baseEnd_735758 < baseStart_735758 := by decide
  rcases family_descends (prefixWord ++ tailWord_735758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735798 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_735798 : Nat := 118140960795 + 735798 * 2 ^ 59
def prefixEnd_735798 : Nat := 4983230072969 + 3 ^ 40 * 735798 * 2
def baseEnd_735798 : Nat := 377818038617017420641133

theorem tailTrace_735798 : CollatzResearch.WordTrace tailWord_735798 prefixEnd_735798 377818038617017420641133 := by
  unfold tailWord_735798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677297361771061571179003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17891171858891323425909365 1677297361771061571179003)
  ·
    refine ⟨2515946042656592356768505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1677297361771061571179003 2515946042656592356768505)
    ·
      refine ⟨1886959531992444267576379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2515946042656592356768505 1886959531992444267576379)
      ·
        refine ⟨2830439297988666401364569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886959531992444267576379 2830439297988666401364569)
        ·
          refine ⟨2122829473491499801023427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2830439297988666401364569 2122829473491499801023427)
          ·
            refine ⟨3184244210237249701535141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122829473491499801023427 3184244210237249701535141)
            ·
              refine ⟨597045789419484319037839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3184244210237249701535141 597045789419484319037839)
              ·
                refine ⟨895568684129226478556759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597045789419484319037839 895568684129226478556759)
                ·
                  refine ⟨1343353026193839717835139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895568684129226478556759 1343353026193839717835139)
                  ·
                    refine ⟨2015029539290759576752709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1343353026193839717835139 2015029539290759576752709)
                    ·
                      refine ⟨377818038617017420641133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2015029539290759576752709 377818038617017420641133)
                      ·
                        rfl

theorem cell23_735798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_735798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735798 prefixEnd_735798 := by exact prefixLift 735798
  have htrace : WordTrace (prefixWord ++ tailWord_735798) baseStart_735798 baseEnd_735798 := by
    simpa [prefixWord, tailWord_735798, baseEnd_735798] using wordTrace_append hprefix tailTrace_735798
  have hstable : (prefixWord ++ tailWord_735798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735798).length < 2 ^ (prefixWord ++ tailWord_735798).sum := by decide
  have hdescent : baseEnd_735798 < baseStart_735798 := by decide
  rcases family_descends (prefixWord ++ tailWord_735798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735824 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 3, 3, 2]
def baseStart_735824 : Nat := 118140960795 + 735824 * 2 ^ 59
def prefixEnd_735824 : Nat := 4983230072969 + 3 ^ 40 * 735824 * 2
def baseEnd_735824 : Nat := 377831389114034318916013

theorem tailTrace_735824 : CollatzResearch.WordTrace tailWord_735824 prefixEnd_735824 377831389114034318916013 := by
  unfold tailWord_735824
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418853043121395789655263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17891804057495194386207017 13418853043121395789655263)
  ·
    refine ⟨20128279564682093684482895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13418853043121395789655263 20128279564682093684482895)
    ·
      refine ⟨30192419347023140526724343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20128279564682093684482895 30192419347023140526724343)
      ·
        refine ⟨45288629020534710790086515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30192419347023140526724343 45288629020534710790086515)
        ·
          refine ⟨67932943530802066185129773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45288629020534710790086515 67932943530802066185129773)
          ·
            refine ⟨25474853824050774819423665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67932943530802066185129773 25474853824050774819423665)
            ·
              refine ⟨19106140368038081114567749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25474853824050774819423665 19106140368038081114567749)
              ·
                refine ⟨3582401319007140208981453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19106140368038081114567749 3582401319007140208981453)
                ·
                  refine ⟨1343400494627677578368045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3582401319007140208981453 1343400494627677578368045)
                  ·
                    refine ⟨503775185485379091888017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343400494627677578368045 503775185485379091888017)
                    ·
                      refine ⟨377831389114034318916013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503775185485379091888017 377831389114034318916013)
                      ·
                        rfl

theorem cell23_735824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 3, 2].length) (baseStart_735824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735824 prefixEnd_735824 := by exact prefixLift 735824
  have htrace : WordTrace (prefixWord ++ tailWord_735824) baseStart_735824 baseEnd_735824 := by
    simpa [prefixWord, tailWord_735824, baseEnd_735824] using wordTrace_append hprefix tailTrace_735824
  have hstable : (prefixWord ++ tailWord_735824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735824).length < 2 ^ (prefixWord ++ tailWord_735824).sum := by decide
  have hdescent : baseEnd_735824 < baseStart_735824 := by decide
  rcases family_descends (prefixWord ++ tailWord_735824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735838 : List Nat := [4, 4, 1, 2, 1, 1, 1, 9]
def baseStart_735838 : Nat := 118140960795 + 735838 * 2 ^ 59
def prefixEnd_735838 : Nat := 4983230072969 + 3 ^ 40 * 735838 * 2
def baseEnd_735838 : Nat := 13994021401599898671887

theorem tailTrace_735838 : CollatzResearch.WordTrace tailWord_735838 prefixEnd_735838 13994021401599898671887 := by
  unfold tailWord_735838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354777088524008996290021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17892144472128047980213445 3354777088524008996290021)
  ·
    refine ⟨629020704098251686804379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3354777088524008996290021 629020704098251686804379)
    ·
      refine ⟨943531056147377530206569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 629020704098251686804379 943531056147377530206569)
      ·
        refine ⟨707648292110533147654927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 943531056147377530206569 707648292110533147654927)
        ·
          refine ⟨1061472438165799721482391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707648292110533147654927 1061472438165799721482391)
          ·
            refine ⟨1592208657248699582223587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061472438165799721482391 1592208657248699582223587)
            ·
              refine ⟨2388312985873049373335381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592208657248699582223587 2388312985873049373335381)
              ·
                refine ⟨13994021401599898671887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2388312985873049373335381 13994021401599898671887)
                ·
                  rfl

theorem cell23_735838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_735838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735838 prefixEnd_735838 := by exact prefixLift 735838
  have htrace : WordTrace (prefixWord ++ tailWord_735838) baseStart_735838 baseEnd_735838 := by
    simpa [prefixWord, tailWord_735838, baseEnd_735838] using wordTrace_append hprefix tailTrace_735838
  have hstable : (prefixWord ++ tailWord_735838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735838).length < 2 ^ (prefixWord ++ tailWord_735838).sum := by decide
  have hdescent : baseEnd_735838 < baseStart_735838 := by decide
  rcases family_descends (prefixWord ++ tailWord_735838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735841 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_735841 : Nat := 118140960795 + 735841 * 2 ^ 59
def prefixEnd_735841 : Nat := 4983230072969 + 3 ^ 40 * 735841 * 2
def baseEnd_735841 : Nat := 377840118285160752403435

theorem tailTrace_735841 : CollatzResearch.WordTrace tailWord_735841 prefixEnd_735841 377840118285160752403435 := by
  unfold tailWord_735841
  simp only [CollatzResearch.WordTrace]
  refine ⟨26838326127181203482679377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17892217418120802321786251 26838326127181203482679377)
  ·
    refine ⟨20128744595385902612009533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26838326127181203482679377 20128744595385902612009533)
    ·
      refine ⟨7548279223269713479503575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20128744595385902612009533 7548279223269713479503575)
      ·
        refine ⟨11322418834904570219255363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7548279223269713479503575 11322418834904570219255363)
        ·
          refine ⟨16983628252356855328883045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11322418834904570219255363 16983628252356855328883045)
          ·
            refine ⟨3184430297316910374165571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16983628252356855328883045 3184430297316910374165571)
            ·
              refine ⟨4776645445975365561248357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184430297316910374165571 4776645445975365561248357)
              ·
                refine ⟨895621021120381042734067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4776645445975365561248357 895621021120381042734067)
                ·
                  refine ⟨1343431531680571564101101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895621021120381042734067 1343431531680571564101101)
                  ·
                    refine ⟨503786824380214336537913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343431531680571564101101 503786824380214336537913)
                    ·
                      refine ⟨377840118285160752403435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503786824380214336537913 377840118285160752403435)
                      ·
                        rfl

theorem cell23_735841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_735841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735841 prefixEnd_735841 := by exact prefixLift 735841
  have htrace : WordTrace (prefixWord ++ tailWord_735841) baseStart_735841 baseEnd_735841 := by
    simpa [prefixWord, tailWord_735841, baseEnd_735841] using wordTrace_append hprefix tailTrace_735841
  have hstable : (prefixWord ++ tailWord_735841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735841).length < 2 ^ (prefixWord ++ tailWord_735841).sum := by decide
  have hdescent : baseEnd_735841 < baseStart_735841 := by decide
  rcases family_descends (prefixWord ++ tailWord_735841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735857 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_735857 : Nat := 118140960795 + 735857 * 2 ^ 59
def prefixEnd_735857 : Nat := 4983230072969 + 3 ^ 40 * 735857 * 2
def baseEnd_735857 : Nat := 377848333975632689803361

theorem tailTrace_735857 : CollatzResearch.WordTrace tailWord_735857 prefixEnd_735857 377848333975632689803361 := by
  unfold tailWord_735857
  simp only [CollatzResearch.WordTrace]
  refine ⟨26838909695123238215261825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17892606463415492143507883 26838909695123238215261825)
  ·
    refine ⟨20129182271342428661446369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26838909695123238215261825 20129182271342428661446369)
    ·
      refine ⟨15096886703506821496084777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20129182271342428661446369 15096886703506821496084777)
      ·
        refine ⟨11322665027630116122063583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15096886703506821496084777 11322665027630116122063583)
        ·
          refine ⟨16983997541445174183095375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11322665027630116122063583 16983997541445174183095375)
          ·
            refine ⟨25475996312167761274643063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16983997541445174183095375 25475996312167761274643063)
            ·
              refine ⟨38213994468251641911964595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25475996312167761274643063 38213994468251641911964595)
              ·
                refine ⟨57320991702377462867946893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38213994468251641911964595 57320991702377462867946893)
                ·
                  refine ⟨21495371888391548575480085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57320991702377462867946893 21495371888391548575480085)
                  ·
                    refine ⟨1007595557268353839475629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21495371888391548575480085 1007595557268353839475629)
                    ·
                      refine ⟨377848333975632689803361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007595557268353839475629 377848333975632689803361)
                      ·
                        rfl

theorem cell23_735857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_735857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735857 prefixEnd_735857 := by exact prefixLift 735857
  have htrace : WordTrace (prefixWord ++ tailWord_735857) baseStart_735857 baseEnd_735857 := by
    simpa [prefixWord, tailWord_735857, baseEnd_735857] using wordTrace_append hprefix tailTrace_735857
  have hstable : (prefixWord ++ tailWord_735857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735857).length < 2 ^ (prefixWord ++ tailWord_735857).sum := by decide
  have hdescent : baseEnd_735857 < baseStart_735857 := by decide
  rcases family_descends (prefixWord ++ tailWord_735857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735867 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4]
def baseStart_735867 : Nat := 118140960795 + 735867 * 2 ^ 59
def prefixEnd_735867 : Nat := 4983230072969 + 3 ^ 40 * 735867 * 2
def baseEnd_735867 : Nat := 377853468782177650678315

theorem tailTrace_735867 : CollatzResearch.WordTrace tailWord_735867 prefixEnd_735867 377853468782177650678315 := by
  unfold tailWord_735867
  simp only [CollatzResearch.WordTrace]
  refine ⟨26839274425087009923125855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17892849616724673282083903 26839274425087009923125855)
  ·
    refine ⟨40258911637630514884688783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26839274425087009923125855 40258911637630514884688783)
    ·
      refine ⟨60388367456445772327033175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40258911637630514884688783 60388367456445772327033175)
      ·
        refine ⟨90582551184668658490549763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60388367456445772327033175 90582551184668658490549763)
        ·
          refine ⟨135873826777002987735824645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90582551184668658490549763 135873826777002987735824645)
          ·
            refine ⟨25476342520688060200467121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135873826777002987735824645 25476342520688060200467121)
            ·
              refine ⟨19107256890516045150350341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25476342520688060200467121 19107256890516045150350341)
              ·
                refine ⟨3582610666971758465690689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19107256890516045150350341 3582610666971758465690689)
                ·
                  refine ⟨2686958000228818849268017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3582610666971758465690689 2686958000228818849268017)
                  ·
                    refine ⟨2015218500171614136951013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2686958000228818849268017 2015218500171614136951013)
                    ·
                      refine ⟨377853468782177650678315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2015218500171614136951013 377853468782177650678315)
                      ·
                        rfl

theorem cell23_735867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_735867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735867 prefixEnd_735867 := by exact prefixLift 735867
  have htrace : WordTrace (prefixWord ++ tailWord_735867) baseStart_735867 baseEnd_735867 := by
    simpa [prefixWord, tailWord_735867, baseEnd_735867] using wordTrace_append hprefix tailTrace_735867
  have hstable : (prefixWord ++ tailWord_735867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735867).length < 2 ^ (prefixWord ++ tailWord_735867).sum := by decide
  have hdescent : baseEnd_735867 < baseStart_735867 := by decide
  rcases family_descends (prefixWord ++ tailWord_735867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735882 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_735882 : Nat := 118140960795 + 735882 * 2 ^ 59
def prefixEnd_735882 : Nat := 4983230072969 + 3 ^ 40 * 735882 * 2
def baseEnd_735882 : Nat := 377861170991995091990747

theorem tailTrace_735882 : CollatzResearch.WordTrace tailWord_735882 prefixEnd_735882 377861170991995091990747 := by
  unfold tailWord_735882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709955380008166871230475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17893214346688444989947933 6709955380008166871230475)
  ·
    refine ⟨10064933070012250306845713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6709955380008166871230475 10064933070012250306845713)
    ·
      refine ⟨7548699802509187730134285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10064933070012250306845713 7548699802509187730134285)
      ·
        refine ⟨2830762425940945398800357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7548699802509187730134285 2830762425940945398800357)
        ·
          refine ⟨530767954863927262275067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2830762425940945398800357 530767954863927262275067)
          ·
            refine ⟨796151932295890893412601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530767954863927262275067 796151932295890893412601)
            ·
              refine ⟨597113949221918170059451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796151932295890893412601 597113949221918170059451)
              ·
                refine ⟨895670923832877255089177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597113949221918170059451 895670923832877255089177)
                ·
                  refine ⟨671753192874657941316883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 895670923832877255089177 671753192874657941316883)
                  ·
                    refine ⟨1007629789311986911975325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671753192874657941316883 1007629789311986911975325)
                    ·
                      refine ⟨377861170991995091990747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007629789311986911975325 377861170991995091990747)
                      ·
                        rfl

theorem cell23_735882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_735882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735882 prefixEnd_735882 := by exact prefixLift 735882
  have htrace : WordTrace (prefixWord ++ tailWord_735882) baseStart_735882 baseEnd_735882 := by
    simpa [prefixWord, tailWord_735882, baseEnd_735882] using wordTrace_append hprefix tailTrace_735882
  have hstable : (prefixWord ++ tailWord_735882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735882).length < 2 ^ (prefixWord ++ tailWord_735882).sum := by decide
  have hdescent : baseEnd_735882 < baseStart_735882 := by decide
  rcases family_descends (prefixWord ++ tailWord_735882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735934 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_735934 : Nat := 118140960795 + 735934 * 2 ^ 59
def prefixEnd_735934 : Nat := 4983230072969 + 3 ^ 40 * 735934 * 2
def baseEnd_735934 : Nat := 377887871986028888540507

theorem tailTrace_735934 : CollatzResearch.WordTrace tailWord_735934 prefixEnd_735934 377887871986028888540507 := by
  unfold tailWord_735934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355214764480535045726857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17894478743896186910543237 3355214764480535045726857)
  ·
    refine ⟨2516411073360401284295143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3355214764480535045726857 2516411073360401284295143)
    ·
      refine ⟨3774616610040601926442715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2516411073360401284295143 3774616610040601926442715)
      ·
        refine ⟨5661924915060902889664073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774616610040601926442715 5661924915060902889664073)
        ·
          refine ⟨4246443686295677167248055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5661924915060902889664073 4246443686295677167248055)
          ·
            refine ⟨6369665529443515750872083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246443686295677167248055 6369665529443515750872083)
            ·
              refine ⟨9554498294165273626308125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6369665529443515750872083 9554498294165273626308125)
              ·
                refine ⟨3582936860311977609865547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9554498294165273626308125 3582936860311977609865547)
                ·
                  refine ⟨5374405290467966414798321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582936860311977609865547 5374405290467966414798321)
                  ·
                    refine ⟨4030803967850974811098741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5374405290467966414798321 4030803967850974811098741)
                    ·
                      refine ⟨377887871986028888540507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4030803967850974811098741 377887871986028888540507)
                      ·
                        rfl

theorem cell23_735934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_735934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735934 prefixEnd_735934 := by exact prefixLift 735934
  have htrace : WordTrace (prefixWord ++ tailWord_735934) baseStart_735934 baseEnd_735934 := by
    simpa [prefixWord, tailWord_735934, baseEnd_735934] using wordTrace_append hprefix tailTrace_735934
  have hstable : (prefixWord ++ tailWord_735934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735934).length < 2 ^ (prefixWord ++ tailWord_735934).sum := by decide
  have hdescent : baseEnd_735934 < baseStart_735934 := by decide
  rcases family_descends (prefixWord ++ tailWord_735934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735981 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_735981 : Nat := 118140960795 + 735981 * 2 ^ 59
def prefixEnd_735981 : Nat := 4983230072969 + 3 ^ 40 * 735981 * 2
def baseEnd_735981 : Nat := 377912005576790204652791

theorem tailTrace_735981 : CollatzResearch.WordTrace tailWord_735981 prefixEnd_735981 377912005576790204652791 := by
  unfold tailWord_735981
  simp only [CollatzResearch.WordTrace]
  refine ⟨26843432346674007392775797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17895621564449338261850531 26843432346674007392775797)
  ·
    refine ⟨2516571782500688193072731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26843432346674007392775797 2516571782500688193072731)
    ·
      refine ⟨3774857673751032289609097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2516571782500688193072731 3774857673751032289609097)
      ·
        refine ⟨2831143255313274217206823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3774857673751032289609097 2831143255313274217206823)
        ·
          refine ⟨4246714882969911325810235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831143255313274217206823 4246714882969911325810235)
          ·
            refine ⟨6370072324454866988715353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246714882969911325810235 6370072324454866988715353)
            ·
              refine ⟨4777554243341150241536515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6370072324454866988715353 4777554243341150241536515)
              ·
                refine ⟨7166331365011725362304773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777554243341150241536515 7166331365011725362304773)
                ·
                  refine ⟨1343687130939698505432145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7166331365011725362304773 1343687130939698505432145)
                  ·
                    refine ⟨1007765348204773879074109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343687130939698505432145 1007765348204773879074109)
                    ·
                      refine ⟨377912005576790204652791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007765348204773879074109 377912005576790204652791)
                      ·
                        rfl

theorem cell23_735981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_735981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_735981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_735981 prefixEnd_735981 := by exact prefixLift 735981
  have htrace : WordTrace (prefixWord ++ tailWord_735981) baseStart_735981 baseEnd_735981 := by
    simpa [prefixWord, tailWord_735981, baseEnd_735981] using wordTrace_append hprefix tailTrace_735981
  have hstable : (prefixWord ++ tailWord_735981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735981).length < 2 ^ (prefixWord ++ tailWord_735981).sum := by decide
  have hdescent : baseEnd_735981 < baseStart_735981 := by decide
  rcases family_descends (prefixWord ++ tailWord_735981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736004 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_736004 : Nat := 118140960795 + 736004 * 2 ^ 59
def prefixEnd_736004 : Nat := 4983230072969 + 3 ^ 40 * 736004 * 2
def baseEnd_736004 : Nat := 377923815631843614665185

theorem tailTrace_736004 : CollatzResearch.WordTrace tailWord_736004 prefixEnd_736004 377923815631843614665185 := by
  unfold tailWord_736004
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422135612795341160431533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17896180817060454880575377 13422135612795341160431533)
  ·
    refine ⟨5033300854798252935161825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13422135612795341160431533 5033300854798252935161825)
    ·
      refine ⟨3774975641098689701371369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5033300854798252935161825 3774975641098689701371369)
      ·
        refine ⟨2831231730824017276028527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3774975641098689701371369 2831231730824017276028527)
        ·
          refine ⟨4246847596236025914042791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831231730824017276028527 4246847596236025914042791)
          ·
            refine ⟨6370271394354038871064187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246847596236025914042791 6370271394354038871064187)
            ·
              refine ⟨9555407091531058306596281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370271394354038871064187 9555407091531058306596281)
              ·
                refine ⟨7166555318648293729947211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9555407091531058306596281 7166555318648293729947211)
                ·
                  refine ⟨10749832977972440594920817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7166555318648293729947211 10749832977972440594920817)
                  ·
                    refine ⟨8062374733479330446190613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10749832977972440594920817 8062374733479330446190613)
                    ·
                      refine ⟨377923815631843614665185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8062374733479330446190613 377923815631843614665185)
                      ·
                        rfl

theorem cell23_736004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_736004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736004 prefixEnd_736004 := by exact prefixLift 736004
  have htrace : WordTrace (prefixWord ++ tailWord_736004) baseStart_736004 baseEnd_736004 := by
    simpa [prefixWord, tailWord_736004, baseEnd_736004] using wordTrace_append hprefix tailTrace_736004
  have hstable : (prefixWord ++ tailWord_736004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736004).length < 2 ^ (prefixWord ++ tailWord_736004).sum := by decide
  have hdescent : baseEnd_736004 < baseStart_736004 := by decide
  rcases family_descends (prefixWord ++ tailWord_736004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736021 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_736021 : Nat := 118140960795 + 736021 * 2 ^ 59
def prefixEnd_736021 : Nat := 4983230072969 + 3 ^ 40 * 736021 * 2
def baseEnd_736021 : Nat := 377932544802970048152607

theorem tailTrace_736021 : CollatzResearch.WordTrace tailWord_736021 prefixEnd_736021 377932544802970048152607 := by
  unfold tailWord_736021
  simp only [CollatzResearch.WordTrace]
  refine ⟨26844891266529094224231917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17896594177686062816154611 26844891266529094224231917)
  ·
    refine ⟨10066834224948410334086969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26844891266529094224231917 10066834224948410334086969)
    ·
      refine ⟨7550125668711307750565227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10066834224948410334086969 7550125668711307750565227)
      ·
        refine ⟨11325188503066961625847841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550125668711307750565227 11325188503066961625847841)
        ·
          refine ⟨8493891377300221219385881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11325188503066961625847841 8493891377300221219385881)
          ·
            refine ⟨6370418532975165914539411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8493891377300221219385881 6370418532975165914539411)
            ·
              refine ⟨9555627799462748871809117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370418532975165914539411 9555627799462748871809117)
              ·
                refine ⟨3583360424798530826928419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9555627799462748871809117 3583360424798530826928419)
                ·
                  refine ⟨5375040637197796240392629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583360424798530826928419 5375040637197796240392629)
                  ·
                    refine ⟨503910059737293397536809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5375040637197796240392629 503910059737293397536809)
                    ·
                      refine ⟨377932544802970048152607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 503910059737293397536809 377932544802970048152607)
                      ·
                        rfl

theorem cell23_736021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_736021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736021 prefixEnd_736021 := by exact prefixLift 736021
  have htrace : WordTrace (prefixWord ++ tailWord_736021) baseStart_736021 baseEnd_736021 := by
    simpa [prefixWord, tailWord_736021, baseEnd_736021] using wordTrace_append hprefix tailTrace_736021
  have hstable : (prefixWord ++ tailWord_736021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736021).length < 2 ^ (prefixWord ++ tailWord_736021).sum := by decide
  have hdescent : baseEnd_736021 < baseStart_736021 := by decide
  rcases family_descends (prefixWord ++ tailWord_736021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736031 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 1, 5]
def baseStart_736031 : Nat := 118140960795 + 736031 * 2 ^ 59
def prefixEnd_736031 : Nat := 4983230072969 + 3 ^ 40 * 736031 * 2
def baseEnd_736031 : Nat := 125979226536505003009187

theorem tailTrace_736031 : CollatzResearch.WordTrace tailWord_736031 prefixEnd_736031 125979226536505003009187 := by
  unfold tailWord_736031
  simp only [CollatzResearch.WordTrace]
  refine ⟨26845255996492865932095947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17896837330995243954730631 26845255996492865932095947)
  ·
    refine ⟨40267883994739298898143921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26845255996492865932095947 40267883994739298898143921)
    ·
      refine ⟨30200912996054474173607941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40267883994739298898143921 30200912996054474173607941)
      ·
        refine ⟨5662671186760213907551489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30200912996054474173607941 5662671186760213907551489)
        ·
          refine ⟨4247003390070160430663617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5662671186760213907551489 4247003390070160430663617)
          ·
            refine ⟨3185252542552620322997713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4247003390070160430663617 3185252542552620322997713)
            ·
              refine ⟨2388939406914465242248285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185252542552620322997713 2388939406914465242248285)
              ·
                refine ⟨895852277592924465843107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2388939406914465242248285 895852277592924465843107)
                ·
                  refine ⟨1343778416389386698764661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895852277592924465843107 1343778416389386698764661)
                  ·
                    refine ⟨125979226536505003009187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1343778416389386698764661 125979226536505003009187)
                    ·
                      rfl

theorem cell23_736031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_736031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736031 prefixEnd_736031 := by exact prefixLift 736031
  have htrace : WordTrace (prefixWord ++ tailWord_736031) baseStart_736031 baseEnd_736031 := by
    simpa [prefixWord, tailWord_736031, baseEnd_736031] using wordTrace_append hprefix tailTrace_736031
  have hstable : (prefixWord ++ tailWord_736031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736031).length < 2 ^ (prefixWord ++ tailWord_736031).sum := by decide
  have hdescent : baseEnd_736031 < baseStart_736031 := by decide
  rcases family_descends (prefixWord ++ tailWord_736031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736052 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 6]
def baseStart_736052 : Nat := 118140960795 + 736052 * 2 ^ 59
def prefixEnd_736052 : Nat := 4983230072969 + 3 ^ 40 * 736052 * 2
def baseEnd_736052 : Nat := 41994273633695491873885

theorem tailTrace_736052 : CollatzResearch.WordTrace tailWord_736052 prefixEnd_736052 41994273633695491873885 := by
  unfold tailWord_736052
  simp only [CollatzResearch.WordTrace]
  refine ⟨13423010964708393259305205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17897347952944524345740273 13423010964708393259305205)
  ·
    refine ⟨1258407277941411868059863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13423010964708393259305205 1258407277941411868059863)
    ·
      refine ⟨1887610916912117802089795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258407277941411868059863 1887610916912117802089795)
      ·
        refine ⟨2831416375368176703134693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887610916912117802089795 2831416375368176703134693)
        ·
          refine ⟨530890570381533131837755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2831416375368176703134693 530890570381533131837755)
          ·
            refine ⟨796335855572299697756633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530890570381533131837755 796335855572299697756633)
            ·
              refine ⟨597251891679224773317475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796335855572299697756633 597251891679224773317475)
              ·
                refine ⟨895877837518837159976213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597251891679224773317475 895877837518837159976213)
                ·
                  refine ⟨41994273633695491873885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 895877837518837159976213 41994273633695491873885)
                  ·
                    rfl

theorem cell23_736052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_736052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736052 prefixEnd_736052 := by exact prefixLift 736052
  have htrace : WordTrace (prefixWord ++ tailWord_736052) baseStart_736052 baseEnd_736052 := by
    simpa [prefixWord, tailWord_736052, baseEnd_736052] using wordTrace_append hprefix tailTrace_736052
  have hstable : (prefixWord ++ tailWord_736052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736052).length < 2 ^ (prefixWord ++ tailWord_736052).sum := by decide
  have hdescent : baseEnd_736052 < baseStart_736052 := by decide
  rcases family_descends (prefixWord ++ tailWord_736052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736064 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_736064 : Nat := 118140960795 + 736064 * 2 ^ 59
def prefixEnd_736064 : Nat := 4983230072969 + 3 ^ 40 * 736064 * 2
def baseEnd_736064 : Nat := 377954624471113379914909

theorem tailTrace_736064 : CollatzResearch.WordTrace tailWord_736064 prefixEnd_736064 377954624471113379914909 := by
  unfold tailWord_736064
  simp only [CollatzResearch.WordTrace]
  refine ⟨13423229802686656284023623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17897639736915541712031497 13423229802686656284023623)
  ·
    refine ⟨20134844704029984426035435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13423229802686656284023623 20134844704029984426035435)
    ·
      refine ⟨30202267056044976639053153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20134844704029984426035435 30202267056044976639053153)
      ·
        refine ⟨22651700292033732479289865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30202267056044976639053153 22651700292033732479289865)
        ·
          refine ⟨16988775219025299359467399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22651700292033732479289865 16988775219025299359467399)
          ·
            refine ⟨25483162828537949039201099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16988775219025299359467399 25483162828537949039201099)
            ·
              refine ⟨38224744242806923558801649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25483162828537949039201099 38224744242806923558801649)
              ·
                refine ⟨28668558182105192669101237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38224744242806923558801649 28668558182105192669101237)
                ·
                  refine ⟨2687677329572361812728241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28668558182105192669101237 2687677329572361812728241)
                  ·
                    refine ⟨2015757997179271359546181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2687677329572361812728241 2015757997179271359546181)
                    ·
                      refine ⟨377954624471113379914909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2015757997179271359546181 377954624471113379914909)
                      ·
                        rfl

theorem cell23_736064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_736064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736064 prefixEnd_736064 := by exact prefixLift 736064
  have htrace : WordTrace (prefixWord ++ tailWord_736064) baseStart_736064 baseEnd_736064 := by
    simpa [prefixWord, tailWord_736064, baseEnd_736064] using wordTrace_append hprefix tailTrace_736064
  have hstable : (prefixWord ++ tailWord_736064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736064).length < 2 ^ (prefixWord ++ tailWord_736064).sum := by decide
  have hdescent : baseEnd_736064 < baseStart_736064 := by decide
  rcases family_descends (prefixWord ++ tailWord_736064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736181 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 7]
def baseStart_736181 : Nat := 118140960795 + 736181 * 2 ^ 59
def prefixEnd_736181 : Nat := 4983230072969 + 3 ^ 40 * 736181 * 2
def baseEnd_736181 : Nat := 42001633523076602461319

theorem tailTrace_736181 : CollatzResearch.WordTrace tailWord_736181 prefixEnd_736181 42001633523076602461319 := by
  unfold tailWord_736181
  simp only [CollatzResearch.WordTrace]
  refine ⟨26850726945949441550056397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17900484630632961033370931 26850726945949441550056397)
  ·
    refine ⟨10069022604731040581271149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26850726945949441550056397 10069022604731040581271149)
    ·
      refine ⟨3775883476774140217976681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10069022604731040581271149 3775883476774140217976681)
      ·
        refine ⟨2831912607580605163482511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3775883476774140217976681 2831912607580605163482511)
        ·
          refine ⟨4247868911370907745223767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831912607580605163482511 4247868911370907745223767)
          ·
            refine ⟨6371803367056361617835651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4247868911370907745223767 6371803367056361617835651)
            ·
              refine ⟨9557705050584542426753477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6371803367056361617835651 9557705050584542426753477)
              ·
                refine ⟨1792069696984601705016277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9557705050584542426753477 1792069696984601705016277)
                ·
                  refine ⟨42001633523076602461319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1792069696984601705016277 42001633523076602461319)
                  ·
                    rfl

theorem cell23_736181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_736181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736181 prefixEnd_736181 := by exact prefixLift 736181
  have htrace : WordTrace (prefixWord ++ tailWord_736181) baseStart_736181 baseEnd_736181 := by
    simpa [prefixWord, tailWord_736181, baseEnd_736181] using wordTrace_append hprefix tailTrace_736181
  have hstable : (prefixWord ++ tailWord_736181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736181).length < 2 ^ (prefixWord ++ tailWord_736181).sum := by decide
  have hdescent : baseEnd_736181 < baseStart_736181 := by decide
  rcases family_descends (prefixWord ++ tailWord_736181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736191 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 3]
def baseStart_736191 : Nat := 118140960795 + 736191 * 2 ^ 59
def prefixEnd_736191 : Nat := 4983230072969 + 3 ^ 40 * 736191 * 2
def baseEnd_736191 : Nat := 378019836514234383026825

theorem tailTrace_736191 : CollatzResearch.WordTrace tailWord_736191 prefixEnd_736191 378019836514234383026825 := by
  unfold tailWord_736191
  simp only [CollatzResearch.WordTrace]
  refine ⟨26851091675913213257920427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17900727783942142171946951 26851091675913213257920427)
  ·
    refine ⟨40276637513869819886880641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26851091675913213257920427 40276637513869819886880641)
    ·
      refine ⟨30207478135402364915160481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40276637513869819886880641 30207478135402364915160481)
      ·
        refine ⟨22655608601551773686370361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30207478135402364915160481 22655608601551773686370361)
        ·
          refine ⟨16991706451163830264777771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22655608601551773686370361 16991706451163830264777771)
          ·
            refine ⟨25487559676745745397166657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16991706451163830264777771 25487559676745745397166657)
            ·
              refine ⟨19115669757559309047874993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25487559676745745397166657 19115669757559309047874993)
              ·
                refine ⟨14336752318169481785906245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19115669757559309047874993 14336752318169481785906245)
                ·
                  refine ⟨2688141059656777834857421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14336752318169481785906245 2688141059656777834857421)
                  ·
                    refine ⟨1008052897371291688071533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688141059656777834857421 1008052897371291688071533)
                    ·
                      refine ⟨378019836514234383026825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1008052897371291688071533 378019836514234383026825)
                      ·
                        rfl

theorem cell23_736191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_736191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736191 prefixEnd_736191 := by exact prefixLift 736191
  have htrace : WordTrace (prefixWord ++ tailWord_736191) baseStart_736191 baseEnd_736191 := by
    simpa [prefixWord, tailWord_736191, baseEnd_736191] using wordTrace_append hprefix tailTrace_736191
  have hstable : (prefixWord ++ tailWord_736191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736191).length < 2 ^ (prefixWord ++ tailWord_736191).sum := by decide
  have hdescent : baseEnd_736191 < baseStart_736191 := by decide
  rcases family_descends (prefixWord ++ tailWord_736191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736226 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_736226 : Nat := 118140960795 + 736226 * 2 ^ 59
def prefixEnd_736226 : Nat := 4983230072969 + 3 ^ 40 * 736226 * 2
def baseEnd_736226 : Nat := 378037808337141746089165

theorem tailTrace_736226 : CollatzResearch.WordTrace tailWord_736226 prefixEnd_736226 378037808337141746089165 := by
  unfold tailWord_736226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713092057696603558861133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17901578820524276156963021 6713092057696603558861133)
  ·
    refine ⟨2517409521636226334572925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6713092057696603558861133 2517409521636226334572925)
    ·
      refine ⟨944028570613584875464847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2517409521636226334572925 944028570613584875464847)
      ·
        refine ⟨1416042855920377313197271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944028570613584875464847 1416042855920377313197271)
        ·
          refine ⟨2124064283880565969795907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416042855920377313197271 2124064283880565969795907)
          ·
            refine ⟨3186096425820848954693861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124064283880565969795907 3186096425820848954693861)
            ·
              refine ⟨597393079841409179005099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3186096425820848954693861 597393079841409179005099)
              ·
                refine ⟨896089619762113768507649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597393079841409179005099 896089619762113768507649)
                ·
                  refine ⟨672067214821585326380737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896089619762113768507649 672067214821585326380737)
                  ·
                    refine ⟨504050411116188994785553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 672067214821585326380737 504050411116188994785553)
                    ·
                      refine ⟨378037808337141746089165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504050411116188994785553 378037808337141746089165)
                      ·
                        rfl

theorem cell23_736226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_736226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736226 prefixEnd_736226 := by exact prefixLift 736226
  have htrace : WordTrace (prefixWord ++ tailWord_736226) baseStart_736226 baseEnd_736226 := by
    simpa [prefixWord, tailWord_736226, baseEnd_736226] using wordTrace_append hprefix tailTrace_736226
  have hstable : (prefixWord ++ tailWord_736226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736226).length < 2 ^ (prefixWord ++ tailWord_736226).sum := by decide
  have hdescent : baseEnd_736226 < baseStart_736226 := by decide
  rcases family_descends (prefixWord ++ tailWord_736226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736248 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 4, 4, 2]
def baseStart_736248 : Nat := 118140960795 + 736248 * 2 ^ 59
def prefixEnd_736248 : Nat := 4983230072969 + 3 ^ 40 * 736248 * 2
def baseEnd_736248 : Nat := 378049104911540660014063

theorem tailTrace_736248 : CollatzResearch.WordTrace tailWord_736248 prefixEnd_736248 378049104911540660014063 := by
  unfold tailWord_736248
  simp only [CollatzResearch.WordTrace]
  refine ⟨13426585318353355996372699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17902113757804474661830265 13426585318353355996372699)
  ·
    refine ⟨20139877977530033994559049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13426585318353355996372699 20139877977530033994559049)
    ·
      refine ⟨15104908483147525495919287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20139877977530033994559049 15104908483147525495919287)
      ·
        refine ⟨22657362724721288243878931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15104908483147525495919287 22657362724721288243878931)
        ·
          refine ⟨33986044087081932365818397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22657362724721288243878931 33986044087081932365818397)
          ·
            refine ⟨12744766532655724637181899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33986044087081932365818397 12744766532655724637181899)
            ·
              refine ⟨19117149798983586955772849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744766532655724637181899 19117149798983586955772849)
              ·
                refine ⟨14337862349237690216829637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19117149798983586955772849 14337862349237690216829637)
                ·
                  refine ⟨2688349190482066915655557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14337862349237690216829637 2688349190482066915655557)
                  ·
                    refine ⟨504065473215387546685417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688349190482066915655557 504065473215387546685417)
                    ·
                      refine ⟨378049104911540660014063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504065473215387546685417 378049104911540660014063)
                      ·
                        rfl

theorem cell23_736248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_736248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736248 prefixEnd_736248 := by exact prefixLift 736248
  have htrace : WordTrace (prefixWord ++ tailWord_736248) baseStart_736248 baseEnd_736248 := by
    simpa [prefixWord, tailWord_736248, baseEnd_736248] using wordTrace_append hprefix tailTrace_736248
  have hstable : (prefixWord ++ tailWord_736248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736248).length < 2 ^ (prefixWord ++ tailWord_736248).sum := by decide
  have hdescent : baseEnd_736248 < baseStart_736248 := by decide
  rcases family_descends (prefixWord ++ tailWord_736248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736261 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_736261 : Nat := 118140960795 + 736261 * 2 ^ 59
def prefixEnd_736261 : Nat := 4983230072969 + 3 ^ 40 * 736261 * 2
def baseEnd_736261 : Nat := 378055780160049109151503

theorem tailTrace_736261 : CollatzResearch.WordTrace tailWord_736261 prefixEnd_736261 378055780160049109151503 := by
  unfold tailWord_736261
  simp only [CollatzResearch.WordTrace]
  refine ⟨26853644785659615212968637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17902429857106410141979091 26853644785659615212968637)
  ·
    refine ⟨10070116794622355704863239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26853644785659615212968637 10070116794622355704863239)
    ·
      refine ⟨15105175191933533557294859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10070116794622355704863239 15105175191933533557294859)
      ·
        refine ⟨22657762787900300335942289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15105175191933533557294859 22657762787900300335942289)
        ·
          refine ⟨16993322090925225251956717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22657762787900300335942289 16993322090925225251956717)
          ·
            refine ⟨6372495784096959469483769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16993322090925225251956717 6372495784096959469483769)
            ·
              refine ⟨4779371838072719602112827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6372495784096959469483769 4779371838072719602112827)
              ·
                refine ⟨7169057757109079403169241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779371838072719602112827 7169057757109079403169241)
                ·
                  refine ⟨5376793317831809552376931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7169057757109079403169241 5376793317831809552376931)
                  ·
                    refine ⟨8065189976747714328565397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5376793317831809552376931 8065189976747714328565397)
                    ·
                      refine ⟨378055780160049109151503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8065189976747714328565397 378055780160049109151503)
                      ·
                        rfl

theorem cell23_736261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_736261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736261 prefixEnd_736261 := by exact prefixLift 736261
  have htrace : WordTrace (prefixWord ++ tailWord_736261) baseStart_736261 baseEnd_736261 := by
    simpa [prefixWord, tailWord_736261, baseEnd_736261] using wordTrace_append hprefix tailTrace_736261
  have hstable : (prefixWord ++ tailWord_736261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736261).length < 2 ^ (prefixWord ++ tailWord_736261).sum := by decide
  have hdescent : baseEnd_736261 < baseStart_736261 := by decide
  rcases family_descends (prefixWord ++ tailWord_736261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736311 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_736311 : Nat := 118140960795 + 736311 * 2 ^ 59
def prefixEnd_736311 : Nat := 4983230072969 + 3 ^ 40 * 736311 * 2
def baseEnd_736311 : Nat := 378081454192773913526273

theorem tailTrace_736311 : CollatzResearch.WordTrace tailWord_736311 prefixEnd_736311 378081454192773913526273 := by
  unfold tailWord_736311
  simp only [CollatzResearch.WordTrace]
  refine ⟨26855468435478473752288787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17903645623652315834859191 26855468435478473752288787)
  ·
    refine ⟨40283202653217710628433181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26855468435478473752288787 40283202653217710628433181)
    ·
      refine ⟨15106200994956641485662443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40283202653217710628433181 15106200994956641485662443)
      ·
        refine ⟨22659301492434962228493665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15106200994956641485662443 22659301492434962228493665)
        ·
          refine ⟨16994476119326221671370249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22659301492434962228493665 16994476119326221671370249)
          ·
            refine ⟨12745857089494666253527687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16994476119326221671370249 12745857089494666253527687)
            ·
              refine ⟨19118785634241999380291531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12745857089494666253527687 19118785634241999380291531)
              ·
                refine ⟨28678178451362999070437297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19118785634241999380291531 28678178451362999070437297)
                ·
                  refine ⟨21508633838522249302827973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28678178451362999070437297 21508633838522249302827973)
                  ·
                    refine ⟨4032868844722921744280245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21508633838522249302827973 4032868844722921744280245)
                    ·
                      refine ⟨378081454192773913526273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4032868844722921744280245 378081454192773913526273)
                      ·
                        rfl

theorem cell23_736311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_736311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736311 prefixEnd_736311 := by exact prefixLift 736311
  have htrace : WordTrace (prefixWord ++ tailWord_736311) baseStart_736311 baseEnd_736311 := by
    simpa [prefixWord, tailWord_736311, baseEnd_736311] using wordTrace_append hprefix tailTrace_736311
  have hstable : (prefixWord ++ tailWord_736311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736311).length < 2 ^ (prefixWord ++ tailWord_736311).sum := by decide
  have hdescent : baseEnd_736311 < baseStart_736311 := by decide
  rcases family_descends (prefixWord ++ tailWord_736311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736325 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 2, 3, 2]
def baseStart_736325 : Nat := 118140960795 + 736325 * 2 ^ 59
def prefixEnd_736325 : Nat := 4983230072969 + 3 ^ 40 * 736325 * 2
def baseEnd_736325 : Nat := 378088642921936858751209

theorem tailTrace_736325 : CollatzResearch.WordTrace tailWord_736325 prefixEnd_736325 378088642921936858751209 := by
  unfold tailWord_736325
  simp only [CollatzResearch.WordTrace]
  refine ⟨26855979057427754143298429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17903986038285169428865619 26855979057427754143298429)
  ·
    refine ⟨10070992146535407803736911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26855979057427754143298429 10070992146535407803736911)
    ·
      refine ⟨15106488219803111705605367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10070992146535407803736911 15106488219803111705605367)
      ·
        refine ⟨22659732329704667558408051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15106488219803111705605367 22659732329704667558408051)
        ·
          refine ⟨33989598494557001337612077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22659732329704667558408051 33989598494557001337612077)
          ·
            refine ⟨12746099435458875501604529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33989598494557001337612077 12746099435458875501604529)
            ·
              refine ⟨9559574576594156626203397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12746099435458875501604529 9559574576594156626203397)
              ·
                refine ⟨1792420233111404367413137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9559574576594156626203397 1792420233111404367413137)
                ·
                  refine ⟨1344315174833553275559853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1792420233111404367413137 1344315174833553275559853)
                  ·
                    refine ⟨504118190562582478334945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1344315174833553275559853 504118190562582478334945)
                    ·
                      refine ⟨378088642921936858751209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504118190562582478334945 378088642921936858751209)
                      ·
                        rfl

theorem cell23_736325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_736325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736325 prefixEnd_736325 := by exact prefixLift 736325
  have htrace : WordTrace (prefixWord ++ tailWord_736325) baseStart_736325 baseEnd_736325 := by
    simpa [prefixWord, tailWord_736325, baseEnd_736325] using wordTrace_append hprefix tailTrace_736325
  have hstable : (prefixWord ++ tailWord_736325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736325).length < 2 ^ (prefixWord ++ tailWord_736325).sum := by decide
  have hdescent : baseEnd_736325 < baseStart_736325 := by decide
  rcases family_descends (prefixWord ++ tailWord_736325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736365 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_736365 : Nat := 118140960795 + 736365 * 2 ^ 59
def prefixEnd_736365 : Nat := 4983230072969 + 3 ^ 40 * 736365 * 2
def baseEnd_736365 : Nat := 126036394049372234083675

theorem tailTrace_736365 : CollatzResearch.WordTrace tailWord_736365 prefixEnd_736365 126036394049372234083675 := by
  unfold tailWord_736365
  simp only [CollatzResearch.WordTrace]
  refine ⟨26857437977282840974754549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17904958651521893983169699 26857437977282840974754549)
  ·
    refine ⟨2517884810370266341383239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26857437977282840974754549 2517884810370266341383239)
    ·
      refine ⟨3776827215555399512074859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517884810370266341383239 3776827215555399512074859)
      ·
        refine ⟨5665240823333099268112289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776827215555399512074859 5665240823333099268112289)
        ·
          refine ⟨4248930617499824451084217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5665240823333099268112289 4248930617499824451084217)
          ·
            refine ⟨3186697963124868338313163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4248930617499824451084217 3186697963124868338313163)
            ·
              refine ⟨4780046944687302507469745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186697963124868338313163 4780046944687302507469745)
              ·
                refine ⟨3585035208515476880602309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780046944687302507469745 3585035208515476880602309)
                ·
                  refine ⟨672194101596651915112933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3585035208515476880602309 672194101596651915112933)
                  ·
                    refine ⟨126036394049372234083675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 672194101596651915112933 126036394049372234083675)
                    ·
                      rfl

theorem cell23_736365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_736365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736365 prefixEnd_736365 := by exact prefixLift 736365
  have htrace : WordTrace (prefixWord ++ tailWord_736365) baseStart_736365 baseEnd_736365 := by
    simpa [prefixWord, tailWord_736365, baseEnd_736365] using wordTrace_append hprefix tailTrace_736365
  have hstable : (prefixWord ++ tailWord_736365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736365).length < 2 ^ (prefixWord ++ tailWord_736365).sum := by decide
  have hdescent : baseEnd_736365 < baseStart_736365 := by decide
  rcases family_descends (prefixWord ++ tailWord_736365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736366 : List Nat := [4, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_736366 : Nat := 118140960795 + 736366 * 2 ^ 59
def prefixEnd_736366 : Nat := 4983230072969 + 3 ^ 40 * 736366 * 2
def baseEnd_736366 : Nat := 378109695628771198338521

theorem tailTrace_736366 : CollatzResearch.WordTrace tailWord_736366 prefixEnd_736366 378109695628771198338521 := by
  unfold tailWord_736366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357184306284902268192619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17904982966852812097027301 3357184306284902268192619)
  ·
    refine ⟨5035776459427353402288929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357184306284902268192619 5035776459427353402288929)
    ·
      refine ⟨3776832344570515051716697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5035776459427353402288929 3776832344570515051716697)
      ·
        refine ⟨2832624258427886288787523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3776832344570515051716697 2832624258427886288787523)
        ·
          refine ⟨4248936387641829433181285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832624258427886288787523 4248936387641829433181285)
          ·
            refine ⟨796675572682843018721491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4248936387641829433181285 796675572682843018721491)
            ·
              refine ⟨1195013359024264528082237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796675572682843018721491 1195013359024264528082237)
              ·
                refine ⟨448130009634099198030839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1195013359024264528082237 448130009634099198030839)
                ·
                  refine ⟨672195014451148797046259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448130009634099198030839 672195014451148797046259)
                  ·
                    refine ⟨1008292521676723195569389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 672195014451148797046259 1008292521676723195569389)
                    ·
                      refine ⟨378109695628771198338521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1008292521676723195569389 378109695628771198338521)
                      ·
                        rfl

theorem cell23_736366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_736366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736366 prefixEnd_736366 := by exact prefixLift 736366
  have htrace : WordTrace (prefixWord ++ tailWord_736366) baseStart_736366 baseEnd_736366 := by
    simpa [prefixWord, tailWord_736366, baseEnd_736366] using wordTrace_append hprefix tailTrace_736366
  have hstable : (prefixWord ++ tailWord_736366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736366).length < 2 ^ (prefixWord ++ tailWord_736366).sum := by decide
  have hdescent : baseEnd_736366 < baseStart_736366 := by decide
  rcases family_descends (prefixWord ++ tailWord_736366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736368 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_736368 : Nat := 118140960795 + 736368 * 2 ^ 59
def prefixEnd_736368 : Nat := 4983230072969 + 3 ^ 40 * 736368 * 2
def baseEnd_736368 : Nat := 378110722590080190513511

theorem tailTrace_736368 : CollatzResearch.WordTrace tailWord_736368 prefixEnd_736368 378110722590080190513511 := by
  unfold tailWord_736368
  simp only [CollatzResearch.WordTrace]
  refine ⟨13428773698135986243556879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17905031597514648324742505 13428773698135986243556879)
  ·
    refine ⟨20143160547203979365335319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13428773698135986243556879 20143160547203979365335319)
    ·
      refine ⟨30214740820805969048002979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20143160547203979365335319 30214740820805969048002979)
      ·
        refine ⟨45322111231208953572004469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30214740820805969048002979 45322111231208953572004469)
        ·
          refine ⟨4248947927925839397375419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45322111231208953572004469 4248947927925839397375419)
          ·
            refine ⟨6373421891888759096063129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248947927925839397375419 6373421891888759096063129)
            ·
              refine ⟨4780066418916569322047347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6373421891888759096063129 4780066418916569322047347)
              ·
                refine ⟨7170099628374853983071021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780066418916569322047347 7170099628374853983071021)
                ·
                  refine ⟨2688787360640570243651633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7170099628374853983071021 2688787360640570243651633)
                  ·
                    refine ⟨2016590520480427682738725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2688787360640570243651633 2016590520480427682738725)
                    ·
                      refine ⟨378110722590080190513511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2016590520480427682738725 378110722590080190513511)
                      ·
                        rfl

theorem cell23_736368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_736368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736368 prefixEnd_736368 := by exact prefixLift 736368
  have htrace : WordTrace (prefixWord ++ tailWord_736368) baseStart_736368 baseEnd_736368 := by
    simpa [prefixWord, tailWord_736368, baseEnd_736368] using wordTrace_append hprefix tailTrace_736368
  have hstable : (prefixWord ++ tailWord_736368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736368).length < 2 ^ (prefixWord ++ tailWord_736368).sum := by decide
  have hdescent : baseEnd_736368 < baseStart_736368 := by decide
  rcases family_descends (prefixWord ++ tailWord_736368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736375 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_736375 : Nat := 118140960795 + 736375 * 2 ^ 59
def prefixEnd_736375 : Nat := 4983230072969 + 3 ^ 40 * 736375 * 2
def baseEnd_736375 : Nat := 378114316954661663125979

theorem tailTrace_736375 : CollatzResearch.WordTrace tailWord_736375 prefixEnd_736375 378114316954661663125979 := by
  unfold tailWord_736375
  simp only [CollatzResearch.WordTrace]
  refine ⟨26857802707246612682618579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17905201804831075121745719 26857802707246612682618579)
  ·
    refine ⟨40286704060869919023927869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26857802707246612682618579 40286704060869919023927869)
    ·
      refine ⟨15107514022826219633972951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40286704060869919023927869 15107514022826219633972951)
      ·
        refine ⟨22661271034239329450959427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15107514022826219633972951 22661271034239329450959427)
        ·
          refine ⟨33991906551358994176439141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22661271034239329450959427 33991906551358994176439141)
          ·
            refine ⟨6373482478379811408082339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33991906551358994176439141 6373482478379811408082339)
            ·
              refine ⟨9560223717569717112123509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373482478379811408082339 9560223717569717112123509)
              ·
                refine ⟨896270973522160979261579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9560223717569717112123509 896270973522160979261579)
                ·
                  refine ⟨1344406460283241468892369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896270973522160979261579 1344406460283241468892369)
                  ·
                    refine ⟨1008304845212431101669277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1344406460283241468892369 1008304845212431101669277)
                    ·
                      refine ⟨378114316954661663125979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1008304845212431101669277 378114316954661663125979)
                      ·
                        rfl

theorem cell23_736375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_736375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736375 prefixEnd_736375 := by exact prefixLift 736375
  have htrace : WordTrace (prefixWord ++ tailWord_736375) baseStart_736375 baseEnd_736375 := by
    simpa [prefixWord, tailWord_736375, baseEnd_736375] using wordTrace_append hprefix tailTrace_736375
  have hstable : (prefixWord ++ tailWord_736375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736375).length < 2 ^ (prefixWord ++ tailWord_736375).sum := by decide
  have hdescent : baseEnd_736375 < baseStart_736375 := by decide
  rcases family_descends (prefixWord ++ tailWord_736375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736405 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_736405 : Nat := 118140960795 + 736405 * 2 ^ 59
def prefixEnd_736405 : Nat := 4983230072969 + 3 ^ 40 * 736405 * 2
def baseEnd_736405 : Nat := 378129721374296545750841

theorem tailTrace_736405 : CollatzResearch.WordTrace tailWord_736405 prefixEnd_736405 378129721374296545750841 := by
  unfold tailWord_736405
  simp only [CollatzResearch.WordTrace]
  refine ⟨26858896897137927806210669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17905931264758618537473779 26858896897137927806210669)
  ·
    refine ⟨10072086336426722927329001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26858896897137927806210669 10072086336426722927329001)
    ·
      refine ⟨7554064752320042195496751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10072086336426722927329001 7554064752320042195496751)
      ·
        refine ⟨11331097128480063293245127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7554064752320042195496751 11331097128480063293245127)
        ·
          refine ⟨16996645692720094939867691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11331097128480063293245127 16996645692720094939867691)
          ·
            refine ⟨25494968539080142409801537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16996645692720094939867691 25494968539080142409801537)
            ·
              refine ⟨19121226404310106807351153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25494968539080142409801537 19121226404310106807351153)
              ·
                refine ⟨14340919803232580105513365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19121226404310106807351153 14340919803232580105513365)
                ·
                  refine ⟨672230615776527192445939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14340919803232580105513365 672230615776527192445939)
                  ·
                    refine ⟨1008345923664790788668909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 672230615776527192445939 1008345923664790788668909)
                    ·
                      refine ⟨378129721374296545750841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1008345923664790788668909 378129721374296545750841)
                      ·
                        rfl

theorem cell23_736405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_736405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736405 prefixEnd_736405 := by exact prefixLift 736405
  have htrace : WordTrace (prefixWord ++ tailWord_736405) baseStart_736405 baseEnd_736405 := by
    simpa [prefixWord, tailWord_736405, baseEnd_736405] using wordTrace_append hprefix tailTrace_736405
  have hstable : (prefixWord ++ tailWord_736405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736405).length < 2 ^ (prefixWord ++ tailWord_736405).sum := by decide
  have hdescent : baseEnd_736405 < baseStart_736405 := by decide
  rcases family_descends (prefixWord ++ tailWord_736405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736426 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_736426 : Nat := 118140960795 + 736426 * 2 ^ 59
def prefixEnd_736426 : Nat := 4983230072969 + 3 ^ 40 * 736426 * 2
def baseEnd_736426 : Nat := 378140504468040963588245

theorem tailTrace_736426 : CollatzResearch.WordTrace tailWord_736426 prefixEnd_736426 378140504468040963588245 := by
  unfold tailWord_736426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714915707515462098181283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17906441886707898928483421 6714915707515462098181283)
  ·
    refine ⟨10072373561273193147271925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6714915707515462098181283 10072373561273193147271925)
    ·
      refine ⟨944285021369361857556743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10072373561273193147271925 944285021369361857556743)
      ·
        refine ⟨1416427532054042786335115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944285021369361857556743 1416427532054042786335115)
        ·
          refine ⟨2124641298081064179502673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416427532054042786335115 2124641298081064179502673)
          ·
            refine ⟨1593480973560798134627005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124641298081064179502673 1593480973560798134627005)
            ·
              refine ⟨597555365085299300485127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593480973560798134627005 597555365085299300485127)
              ·
                refine ⟨896333047627948950727691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597555365085299300485127 896333047627948950727691)
                ·
                  refine ⟨1344499571441923426091537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896333047627948950727691 1344499571441923426091537)
                  ·
                    refine ⟨1008374678581442569568653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1344499571441923426091537 1008374678581442569568653)
                    ·
                      refine ⟨378140504468040963588245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1008374678581442569568653 378140504468040963588245)
                      ·
                        rfl

theorem cell23_736426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_736426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736426 prefixEnd_736426 := by exact prefixLift 736426
  have htrace : WordTrace (prefixWord ++ tailWord_736426) baseStart_736426 baseEnd_736426 := by
    simpa [prefixWord, tailWord_736426, baseEnd_736426] using wordTrace_append hprefix tailTrace_736426
  have hstable : (prefixWord ++ tailWord_736426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736426).length < 2 ^ (prefixWord ++ tailWord_736426).sum := by decide
  have hdescent : baseEnd_736426 < baseStart_736426 := by decide
  rcases family_descends (prefixWord ++ tailWord_736426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736449 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_736449 : Nat := 118140960795 + 736449 * 2 ^ 59
def prefixEnd_736449 : Nat := 4983230072969 + 3 ^ 40 * 736449 * 2
def baseEnd_736449 : Nat := 378152314523094373600639

theorem tailTrace_736449 : CollatzResearch.WordTrace tailWord_736449 prefixEnd_736449 378152314523094373600639 := by
  unfold tailWord_736449
  simp only [CollatzResearch.WordTrace]
  refine ⟨26860501708978523320812401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17907001139319015547208267 26860501708978523320812401)
  ·
    refine ⟨20145376281733892490609301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26860501708978523320812401 20145376281733892490609301)
    ·
      refine ⟨944314513206276210497311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20145376281733892490609301 944314513206276210497311)
      ·
        refine ⟨1416471769809414315745967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944314513206276210497311 1416471769809414315745967)
        ·
          refine ⟨2124707654714121473618951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416471769809414315745967 2124707654714121473618951)
          ·
            refine ⟨3187061482071182210428427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124707654714121473618951 3187061482071182210428427)
            ·
              refine ⟨4780592223106773315642641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187061482071182210428427 4780592223106773315642641)
              ·
                refine ⟨3585444167330079986731981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780592223106773315642641 3585444167330079986731981)
                ·
                  refine ⟨1344541562748779995024493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3585444167330079986731981 1344541562748779995024493)
                  ·
                    refine ⟨504203086030792498134185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1344541562748779995024493 504203086030792498134185)
                    ·
                      refine ⟨378152314523094373600639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504203086030792498134185 378152314523094373600639)
                      ·
                        rfl

theorem cell23_736449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_736449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736449 prefixEnd_736449 := by exact prefixLift 736449
  have htrace : WordTrace (prefixWord ++ tailWord_736449) baseStart_736449 baseEnd_736449 := by
    simpa [prefixWord, tailWord_736449, baseEnd_736449] using wordTrace_append hprefix tailTrace_736449
  have hstable : (prefixWord ++ tailWord_736449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736449).length < 2 ^ (prefixWord ++ tailWord_736449).sum := by decide
  have hdescent : baseEnd_736449 < baseStart_736449 := by decide
  rcases family_descends (prefixWord ++ tailWord_736449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736535 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_736535 : Nat := 118140960795 + 736535 * 2 ^ 59
def prefixEnd_736535 : Nat := 4983230072969 + 3 ^ 40 * 736535 * 2
def baseEnd_736535 : Nat := 378196473859381037125243

theorem tailTrace_736535 : CollatzResearch.WordTrace tailWord_736535 prefixEnd_736535 378196473859381037125243 := by
  unfold tailWord_736535
  simp only [CollatzResearch.WordTrace]
  refine ⟨26863638386666960008443059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17909092257777973338962039 26863638386666960008443059)
  ·
    refine ⟨40295457580000440012664589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26863638386666960008443059 40295457580000440012664589)
    ·
      refine ⟨15110796592500165004749221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40295457580000440012664589 15110796592500165004749221)
      ·
        refine ⟨2833274361093780938390479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15110796592500165004749221 2833274361093780938390479)
        ·
          refine ⟨4249911541640671407585719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833274361093780938390479 4249911541640671407585719)
          ·
            refine ⟨6374867312461007111378579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249911541640671407585719 6374867312461007111378579)
            ·
              refine ⟨9562300968691510667067869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6374867312461007111378579 9562300968691510667067869)
              ·
                refine ⟨3585862863259316500150451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9562300968691510667067869 3585862863259316500150451)
                ·
                  refine ⟨5378794294888974750225677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585862863259316500150451 5378794294888974750225677)
                  ·
                    refine ⟨2017047860583365531334629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5378794294888974750225677 2017047860583365531334629)
                    ·
                      refine ⟨378196473859381037125243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2017047860583365531334629 378196473859381037125243)
                      ·
                        rfl

theorem cell23_736535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_736535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736535 prefixEnd_736535 := by exact prefixLift 736535
  have htrace : WordTrace (prefixWord ++ tailWord_736535) baseStart_736535 baseEnd_736535 := by
    simpa [prefixWord, tailWord_736535, baseEnd_736535] using wordTrace_append hprefix tailTrace_736535
  have hstable : (prefixWord ++ tailWord_736535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736535).length < 2 ^ (prefixWord ++ tailWord_736535).sum := by decide
  have hdescent : baseEnd_736535 < baseStart_736535 := by decide
  rcases family_descends (prefixWord ++ tailWord_736535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736552 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_736552 : Nat := 118140960795 + 736552 * 2 ^ 59
def prefixEnd_736552 : Nat := 4983230072969 + 3 ^ 40 * 736552 * 2
def baseEnd_736552 : Nat := 378205203030507470612665

theorem tailTrace_736552 : CollatzResearch.WordTrace tailWord_736552 prefixEnd_736552 378205203030507470612665 := by
  unfold tailWord_736552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432129213802685955905955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17909505618403581274541273 13432129213802685955905955)
  ·
    refine ⟨20148193820704028933858933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13432129213802685955905955 20148193820704028933858933)
    ·
      refine ⟨1888893170691002712549275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20148193820704028933858933 1888893170691002712549275)
      ·
        refine ⟨2833339756036504068823913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888893170691002712549275 2833339756036504068823913)
        ·
          refine ⟨2125004817027378051617935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2833339756036504068823913 2125004817027378051617935)
          ·
            refine ⟨3187507225541067077426903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125004817027378051617935 3187507225541067077426903)
            ·
              refine ⟨4781260838311600616140355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187507225541067077426903 4781260838311600616140355)
              ·
                refine ⟨7171891257467400924210533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781260838311600616140355 7171891257467400924210533)
                ·
                  refine ⟨1344729610775137673289475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7171891257467400924210533 1344729610775137673289475)
                  ·
                    refine ⟨2017094416162706509934213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1344729610775137673289475 2017094416162706509934213)
                    ·
                      refine ⟨378205203030507470612665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2017094416162706509934213 378205203030507470612665)
                      ·
                        rfl

theorem cell23_736552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_736552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736552 prefixEnd_736552 := by exact prefixLift 736552
  have htrace : WordTrace (prefixWord ++ tailWord_736552) baseStart_736552 baseEnd_736552 := by
    simpa [prefixWord, tailWord_736552, baseEnd_736552] using wordTrace_append hprefix tailTrace_736552
  have hstable : (prefixWord ++ tailWord_736552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736552).length < 2 ^ (prefixWord ++ tailWord_736552).sum := by decide
  have hdescent : baseEnd_736552 < baseStart_736552 := by decide
  rcases family_descends (prefixWord ++ tailWord_736552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736585 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 3]
def baseStart_736585 : Nat := 118140960795 + 736585 * 2 ^ 59
def prefixEnd_736585 : Nat := 4983230072969 + 3 ^ 40 * 736585 * 2
def baseEnd_736585 : Nat := 378222147892105841500013

theorem tailTrace_736585 : CollatzResearch.WordTrace tailWord_736585 prefixEnd_736585 378222147892105841500013 := by
  unfold tailWord_736585
  simp only [CollatzResearch.WordTrace]
  refine ⟨26865462036485818547763209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17910308024323879031842139 26865462036485818547763209)
  ·
    refine ⟨20149096527364363910822407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26865462036485818547763209 20149096527364363910822407)
    ·
      refine ⟨30223644791046545866233611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20149096527364363910822407 30223644791046545866233611)
      ·
        refine ⟨45335467186569818799350417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30223644791046545866233611 45335467186569818799350417)
        ·
          refine ⟨34001600389927364099512813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45335467186569818799350417 34001600389927364099512813)
          ·
            refine ⟨12750600146222761537317305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34001600389927364099512813 12750600146222761537317305)
            ·
              refine ⟨9562950109667071152987979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12750600146222761537317305 9562950109667071152987979)
              ·
                refine ⟨14344425164500606729481969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9562950109667071152987979 14344425164500606729481969)
                ·
                  refine ⟨10758318873375455047111477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14344425164500606729481969 10758318873375455047111477)
                  ·
                    refine ⟨1008592394378948910666701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10758318873375455047111477 1008592394378948910666701)
                    ·
                      refine ⟨378222147892105841500013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1008592394378948910666701 378222147892105841500013)
                      ·
                        rfl

theorem cell23_736585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_736585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736585 prefixEnd_736585 := by exact prefixLift 736585
  have htrace : WordTrace (prefixWord ++ tailWord_736585) baseStart_736585 baseEnd_736585 := by
    simpa [prefixWord, tailWord_736585, baseEnd_736585] using wordTrace_append hprefix tailTrace_736585
  have hstable : (prefixWord ++ tailWord_736585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736585).length < 2 ^ (prefixWord ++ tailWord_736585).sum := by decide
  have hdescent : baseEnd_736585 < baseStart_736585 := by decide
  rcases family_descends (prefixWord ++ tailWord_736585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736652 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_736652 : Nat := 118140960795 + 736652 * 2 ^ 59
def prefixEnd_736652 : Nat := 4983230072969 + 3 ^ 40 * 736652 * 2
def baseEnd_736652 : Nat := 126085517031985693120735

theorem tailTrace_736652 : CollatzResearch.WordTrace tailWord_736652 prefixEnd_736652 126085517031985693120735 := by
  unfold tailWord_736652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13433952863621544495226105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17911937151495392660301473 13433952863621544495226105)
  ·
    refine ⟨10075464647716158371419579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13433952863621544495226105 10075464647716158371419579)
    ·
      refine ⟨15113196971574237557129369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10075464647716158371419579 15113196971574237557129369)
      ·
        refine ⟨11334897728680678167847027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15113196971574237557129369 11334897728680678167847027)
        ·
          refine ⟨17002346593021017251770541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11334897728680678167847027 17002346593021017251770541)
          ·
            refine ⟨6375879972382881469413953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17002346593021017251770541 6375879972382881469413953)
            ·
              refine ⟨4781909979287161102060465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6375879972382881469413953 4781909979287161102060465)
              ·
                refine ⟨3586432484465370826545349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781909979287161102060465 3586432484465370826545349)
                ·
                  refine ⟨672456090837257029977253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3586432484465370826545349 672456090837257029977253)
                  ·
                    refine ⟨126085517031985693120735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 672456090837257029977253 126085517031985693120735)
                    ·
                      rfl

theorem cell23_736652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_736652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736652 prefixEnd_736652 := by exact prefixLift 736652
  have htrace : WordTrace (prefixWord ++ tailWord_736652) baseStart_736652 baseEnd_736652 := by
    simpa [prefixWord, tailWord_736652, baseEnd_736652] using wordTrace_append hprefix tailTrace_736652
  have hstable : (prefixWord ++ tailWord_736652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736652).length < 2 ^ (prefixWord ++ tailWord_736652).sum := by decide
  have hdescent : baseEnd_736652 < baseStart_736652 := by decide
  rcases family_descends (prefixWord ++ tailWord_736652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736665 : List Nat := [1, 2, 1, 2, 1, 6, 10]
def baseStart_736665 : Nat := 118140960795 + 736665 * 2 ^ 59
def prefixEnd_736665 : Nat := 4983230072969 + 3 ^ 40 * 736665 * 2
def baseEnd_736665 : Nat := 4669916374623031216045

theorem tailTrace_736665 : CollatzResearch.WordTrace tailWord_736665 prefixEnd_736665 4669916374623031216045 := by
  unfold tailWord_736665
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868379876195992210675449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17912253250797328140450299 26868379876195992210675449)
  ·
    refine ⟨20151284907146994158006587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26868379876195992210675449 20151284907146994158006587)
    ·
      refine ⟨30226927360720491237009881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20151284907146994158006587 30226927360720491237009881)
      ·
        refine ⟨22670195520540368427757411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30226927360720491237009881 22670195520540368427757411)
        ·
          refine ⟨34005293280810552641636117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22670195520540368427757411 34005293280810552641636117)
          ·
            refine ⟨1593998122537994655076693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34005293280810552641636117 1593998122537994655076693)
            ·
              refine ⟨4669916374623031216045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1593998122537994655076693 4669916374623031216045)
              ·
                rfl

theorem cell23_736665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 10].length) (baseStart_736665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736665 prefixEnd_736665 := by exact prefixLift 736665
  have htrace : WordTrace (prefixWord ++ tailWord_736665) baseStart_736665 baseEnd_736665 := by
    simpa [prefixWord, tailWord_736665, baseEnd_736665] using wordTrace_append hprefix tailTrace_736665
  have hstable : (prefixWord ++ tailWord_736665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736665).length < 2 ^ (prefixWord ++ tailWord_736665).sum := by decide
  have hdescent : baseEnd_736665 < baseStart_736665 := by decide
  rcases family_descends (prefixWord ++ tailWord_736665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736669 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_736669 : Nat := 118140960795 + 736669 * 2 ^ 59
def prefixEnd_736669 : Nat := 4983230072969 + 3 ^ 40 * 736669 * 2
def baseEnd_736669 : Nat := 126088426755694504283209

theorem tailTrace_736669 : CollatzResearch.WordTrace tailWord_736669 prefixEnd_736669 126088426755694504283209 := by
  unfold tailWord_736669
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868525768181500893821061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17912350512121000595880707 26868525768181500893821061)
  ·
    refine ⟨5037848581534031417591449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26868525768181500893821061 5037848581534031417591449)
    ·
      refine ⟨3778386436150523563193587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5037848581534031417591449 3778386436150523563193587)
      ·
        refine ⟨5667579654225785344790381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778386436150523563193587 5667579654225785344790381)
        ·
          refine ⟨2125342370334669504296393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5667579654225785344790381 2125342370334669504296393)
          ·
            refine ⟨1594006777751002128222295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2125342370334669504296393 1594006777751002128222295)
            ·
              refine ⟨2391010166626503192333443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594006777751002128222295 2391010166626503192333443)
              ·
                refine ⟨3586515249939754788500165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391010166626503192333443 3586515249939754788500165)
                ·
                  refine ⟨672471609363704022843781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3586515249939754788500165 672471609363704022843781)
                  ·
                    refine ⟨126088426755694504283209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 672471609363704022843781 126088426755694504283209)
                    ·
                      rfl

theorem cell23_736669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_736669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736669 prefixEnd_736669 := by exact prefixLift 736669
  have htrace : WordTrace (prefixWord ++ tailWord_736669) baseStart_736669 baseEnd_736669 := by
    simpa [prefixWord, tailWord_736669, baseEnd_736669] using wordTrace_append hprefix tailTrace_736669
  have hstable : (prefixWord ++ tailWord_736669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736669).length < 2 ^ (prefixWord ++ tailWord_736669).sum := by decide
  have hdescent : baseEnd_736669 < baseStart_736669 := by decide
  rcases family_descends (prefixWord ++ tailWord_736669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736743 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_736743 : Nat := 118140960795 + 736743 * 2 ^ 59
def prefixEnd_736743 : Nat := 4983230072969 + 3 ^ 40 * 736743 * 2
def baseEnd_736743 : Nat := 378303277835516223324287

theorem tailTrace_736743 : CollatzResearch.WordTrace tailWord_736743 prefixEnd_736743 378303277835516223324287 := by
  unfold tailWord_736743
  simp only [CollatzResearch.WordTrace]
  refine ⟨26871224769913411532014883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17914149846608941021343255 26871224769913411532014883)
  ·
    refine ⟨40306837154870117298022325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26871224769913411532014883 40306837154870117298022325)
    ·
      refine ⟨3778765983269073496689593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40306837154870117298022325 3778765983269073496689593)
      ·
        refine ⟨2834074487451805122517195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3778765983269073496689593 2834074487451805122517195)
        ·
          refine ⟨4251111731177707683775793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834074487451805122517195 4251111731177707683775793)
          ·
            refine ⟨3188333798383280762831845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4251111731177707683775793 3188333798383280762831845)
            ·
              refine ⟨597812587196865143030971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3188333798383280762831845 597812587196865143030971)
              ·
                refine ⟨896718880795297714546457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597812587196865143030971 896718880795297714546457)
                ·
                  refine ⟨672539160596473285909843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896718880795297714546457 672539160596473285909843)
                  ·
                    refine ⟨1008808740894709928864765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 672539160596473285909843 1008808740894709928864765)
                    ·
                      refine ⟨378303277835516223324287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1008808740894709928864765 378303277835516223324287)
                      ·
                        rfl

theorem cell23_736743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_736743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736743 prefixEnd_736743 := by exact prefixLift 736743
  have htrace : WordTrace (prefixWord ++ tailWord_736743) baseStart_736743 baseEnd_736743 := by
    simpa [prefixWord, tailWord_736743, baseEnd_736743] using wordTrace_append hprefix tailTrace_736743
  have hstable : (prefixWord ++ tailWord_736743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736743).length < 2 ^ (prefixWord ++ tailWord_736743).sum := by decide
  have hdescent : baseEnd_736743 < baseStart_736743 := by decide
  rcases family_descends (prefixWord ++ tailWord_736743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736752 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_736752 : Nat := 118140960795 + 736752 * 2 ^ 59
def prefixEnd_736752 : Nat := 4983230072969 + 3 ^ 40 * 736752 * 2
def baseEnd_736752 : Nat := 378307899161406688111745

theorem tailTrace_736752 : CollatzResearch.WordTrace tailWord_736752 prefixEnd_736752 378307899161406688111745 := by
  unfold tailWord_736752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13435776513440403034546255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17914368684587204046061673 13435776513440403034546255)
  ·
    refine ⟨20153664770160604551819383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13435776513440403034546255 20153664770160604551819383)
    ·
      refine ⟨30230497155240906827729075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20153664770160604551819383 30230497155240906827729075)
      ·
        refine ⟨45345745732861360241593613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30230497155240906827729075 45345745732861360241593613)
        ·
          refine ⟨17004654649823010090597605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45345745732861360241593613 17004654649823010090597605)
          ·
            refine ⟨3188372746841814391987051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17004654649823010090597605 3188372746841814391987051)
            ·
              refine ⟨4782559120262721587980577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188372746841814391987051 4782559120262721587980577)
              ·
                refine ⟨3586919340197041190985433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4782559120262721587980577 3586919340197041190985433)
                ·
                  refine ⟨2690189505147780893239075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3586919340197041190985433 2690189505147780893239075)
                  ·
                    refine ⟨4035284257721671339858613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2690189505147780893239075 4035284257721671339858613)
                    ·
                      refine ⟨378307899161406688111745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4035284257721671339858613 378307899161406688111745)
                      ·
                        rfl

theorem cell23_736752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_736752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736752 prefixEnd_736752 := by exact prefixLift 736752
  have htrace : WordTrace (prefixWord ++ tailWord_736752) baseStart_736752 baseEnd_736752 := by
    simpa [prefixWord, tailWord_736752, baseEnd_736752] using wordTrace_append hprefix tailTrace_736752
  have hstable : (prefixWord ++ tailWord_736752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736752).length < 2 ^ (prefixWord ++ tailWord_736752).sum := by decide
  have hdescent : baseEnd_736752 < baseStart_736752 := by decide
  rcases family_descends (prefixWord ++ tailWord_736752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736753 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 1, 3, 2]
def baseStart_736753 : Nat := 118140960795 + 736753 * 2 ^ 59
def prefixEnd_736753 : Nat := 4983230072969 + 3 ^ 40 * 736753 * 2
def baseEnd_736753 : Nat := 378308412642061184199241

theorem tailTrace_736753 : CollatzResearch.WordTrace tailWord_736753 prefixEnd_736753 378308412642061184199241 := by
  unfold tailWord_736753
  simp only [CollatzResearch.WordTrace]
  refine ⟨26871589499877183239878913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17914392999918122159919275 26871589499877183239878913)
  ·
    refine ⟨20153692124907887429909185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26871589499877183239878913 20153692124907887429909185)
    ·
      refine ⟨15115269093680915572431889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20153692124907887429909185 15115269093680915572431889)
      ·
        refine ⟨11336451820260686679323917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15115269093680915572431889 11336451820260686679323917)
        ·
          refine ⟨4251169432597757504746469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11336451820260686679323917 4251169432597757504746469)
          ·
            refine ⟨797094268612079532139963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4251169432597757504746469 797094268612079532139963)
            ·
              refine ⟨1195641402918119298209945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797094268612079532139963 1195641402918119298209945)
              ·
                refine ⟨896731052188589473657459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195641402918119298209945 896731052188589473657459)
                ·
                  refine ⟨1345096578282884210486189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896731052188589473657459 1345096578282884210486189)
                  ·
                    refine ⟨504411216856081578932321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1345096578282884210486189 504411216856081578932321)
                    ·
                      refine ⟨378308412642061184199241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504411216856081578932321 378308412642061184199241)
                      ·
                        rfl

theorem cell23_736753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_736753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736753 prefixEnd_736753 := by exact prefixLift 736753
  have htrace : WordTrace (prefixWord ++ tailWord_736753) baseStart_736753 baseEnd_736753 := by
    simpa [prefixWord, tailWord_736753, baseEnd_736753] using wordTrace_append hprefix tailTrace_736753
  have hstable : (prefixWord ++ tailWord_736753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736753).length < 2 ^ (prefixWord ++ tailWord_736753).sum := by decide
  have hdescent : baseEnd_736753 < baseStart_736753 := by decide
  rcases family_descends (prefixWord ++ tailWord_736753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736819 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 2, 5]
def baseStart_736819 : Nat := 118140960795 + 736819 * 2 ^ 59
def prefixEnd_736819 : Nat := 4983230072969 + 3 ^ 40 * 736819 * 2
def baseEnd_736819 : Nat := 126114100788419308657979

theorem tailTrace_736819 : CollatzResearch.WordTrace tailWord_736819 prefixEnd_736819 126114100788419308657979 := by
  unfold tailWord_736819
  simp only [CollatzResearch.WordTrace]
  refine ⟨26873996717638076511781511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17915997811758717674521007 26873996717638076511781511)
  ·
    refine ⟨40310995076457114767672267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26873996717638076511781511 40310995076457114767672267)
    ·
      refine ⟨60466492614685672151508401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40310995076457114767672267 60466492614685672151508401)
      ·
        refine ⟨45349869461014254113631301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60466492614685672151508401 45349869461014254113631301)
        ·
          refine ⟨8503100523940172646305869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45349869461014254113631301 8503100523940172646305869)
          ·
            refine ⟨3188662696477564742364701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8503100523940172646305869 3188662696477564742364701)
            ·
              refine ⟨1195748511179086778386763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3188662696477564742364701 1195748511179086778386763)
              ·
                refine ⟨1793622766768630167580145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195748511179086778386763 1793622766768630167580145)
                ·
                  refine ⟨1345217075076472625685109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1793622766768630167580145 1345217075076472625685109)
                  ·
                    refine ⟨126114100788419308657979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1345217075076472625685109 126114100788419308657979)
                    ·
                      rfl

theorem cell23_736819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 5].length) (baseStart_736819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736819 prefixEnd_736819 := by exact prefixLift 736819
  have htrace : WordTrace (prefixWord ++ tailWord_736819) baseStart_736819 baseEnd_736819 := by
    simpa [prefixWord, tailWord_736819, baseEnd_736819] using wordTrace_append hprefix tailTrace_736819
  have hstable : (prefixWord ++ tailWord_736819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736819).length < 2 ^ (prefixWord ++ tailWord_736819).sum := by decide
  have hdescent : baseEnd_736819 < baseStart_736819 := by decide
  rcases family_descends (prefixWord ++ tailWord_736819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736900 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_736900 : Nat := 118140960795 + 736900 * 2 ^ 59
def prefixEnd_736900 : Nat := 4983230072969 + 3 ^ 40 * 736900 * 2
def baseEnd_736900 : Nat := 126127964766090703020355

theorem tailTrace_736900 : CollatzResearch.WordTrace tailWord_736900 prefixEnd_736900 126127964766090703020355 := by
  unfold tailWord_736900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438475515172313672740077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17917967353563084896986769 13438475515172313672740077)
  ·
    refine ⟨5039428318189617627277529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13438475515172313672740077 5039428318189617627277529)
    ·
      refine ⟨3779571238642213220458147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5039428318189617627277529 3779571238642213220458147)
      ·
        refine ⟨5669356857963319830687221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779571238642213220458147 5669356857963319830687221)
        ·
          refine ⟨531502205434061234126927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5669356857963319830687221 531502205434061234126927)
          ·
            refine ⟨797253308151091851190391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531502205434061234126927 797253308151091851190391)
            ·
              refine ⟨1195879962226637776785587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797253308151091851190391 1195879962226637776785587)
              ·
                refine ⟨1793819943339956665178381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195879962226637776785587 1793819943339956665178381)
                ·
                  refine ⟨672682478752483749441893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1793819943339956665178381 672682478752483749441893)
                  ·
                    refine ⟨126127964766090703020355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 672682478752483749441893 126127964766090703020355)
                    ·
                      rfl

theorem cell23_736900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_736900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736900 prefixEnd_736900 := by exact prefixLift 736900
  have htrace : WordTrace (prefixWord ++ tailWord_736900) baseStart_736900 baseEnd_736900 := by
    simpa [prefixWord, tailWord_736900, baseEnd_736900] using wordTrace_append hprefix tailTrace_736900
  have hstable : (prefixWord ++ tailWord_736900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736900).length < 2 ^ (prefixWord ++ tailWord_736900).sum := by decide
  have hdescent : baseEnd_736900 < baseStart_736900 := by decide
  rcases family_descends (prefixWord ++ tailWord_736900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736946 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_736946 : Nat := 118140960795 + 736946 * 2 ^ 59
def prefixEnd_736946 : Nat := 4983230072969 + 3 ^ 40 * 736946 * 2
def baseEnd_736946 : Nat := 378407514408378929085853

theorem tailTrace_736946 : CollatzResearch.WordTrace tailWord_736946 prefixEnd_736946 378407514408378929085853 := by
  unfold tailWord_736946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719657197044494300413673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17919085858785318134436461 6719657197044494300413673)
  ·
    refine ⟨5039742897783370725310255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6719657197044494300413673 5039742897783370725310255)
    ·
      refine ⟨7559614346675056087965383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5039742897783370725310255 7559614346675056087965383)
      ·
        refine ⟨11339421520012584131948075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7559614346675056087965383 11339421520012584131948075)
        ·
          refine ⟨17009132280018876197922113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11339421520012584131948075 17009132280018876197922113)
          ·
            refine ⟨12756849210014157148441585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17009132280018876197922113 12756849210014157148441585)
            ·
              refine ⟨9567636907510617861331189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12756849210014157148441585 9567636907510617861331189)
              ·
                refine ⟨896965960079120424499799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9567636907510617861331189 896965960079120424499799)
                ·
                  refine ⟨1345448940118680636749699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896965960079120424499799 1345448940118680636749699)
                  ·
                    refine ⟨2018173410178020955124549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1345448940118680636749699 2018173410178020955124549)
                    ·
                      refine ⟨378407514408378929085853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2018173410178020955124549 378407514408378929085853)
                      ·
                        rfl

theorem cell23_736946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_736946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736946 prefixEnd_736946 := by exact prefixLift 736946
  have htrace : WordTrace (prefixWord ++ tailWord_736946) baseStart_736946 baseEnd_736946 := by
    simpa [prefixWord, tailWord_736946, baseEnd_736946] using wordTrace_append hprefix tailTrace_736946
  have hstable : (prefixWord ++ tailWord_736946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736946).length < 2 ^ (prefixWord ++ tailWord_736946).sum := by decide
  have hdescent : baseEnd_736946 < baseStart_736946 := by decide
  rcases family_descends (prefixWord ++ tailWord_736946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736959 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_736959 : Nat := 118140960795 + 736959 * 2 ^ 59
def prefixEnd_736959 : Nat := 4983230072969 + 3 ^ 40 * 736959 * 2
def baseEnd_736959 : Nat := 378414189656887378223293

theorem tailTrace_736959 : CollatzResearch.WordTrace tailWord_736959 prefixEnd_736959 378414189656887378223293 := by
  unfold tailWord_736959
  simp only [CollatzResearch.WordTrace]
  refine ⟨26879102937130880421877931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17919401958087253614585287 26879102937130880421877931)
  ·
    refine ⟨40318654405696320632816897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26879102937130880421877931 40318654405696320632816897)
    ·
      refine ⟨30238990804272240474612673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40318654405696320632816897 30238990804272240474612673)
      ·
        refine ⟨22679243103204180355959505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30238990804272240474612673 22679243103204180355959505)
        ·
          refine ⟨17009432327403135266969629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22679243103204180355959505 17009432327403135266969629)
          ·
            refine ⟨6378537122776175725113611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17009432327403135266969629 6378537122776175725113611)
            ·
              refine ⟨9567805684164263587670417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378537122776175725113611 9567805684164263587670417)
              ·
                refine ⟨7175854263123197690752813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9567805684164263587670417 7175854263123197690752813)
                ·
                  refine ⟨2690945348671199134032305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7175854263123197690752813 2690945348671199134032305)
                  ·
                    refine ⟨2018209011503399350524229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2690945348671199134032305 2018209011503399350524229)
                    ·
                      refine ⟨378414189656887378223293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2018209011503399350524229 378414189656887378223293)
                      ·
                        rfl

theorem cell23_736959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_736959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736959 prefixEnd_736959 := by exact prefixLift 736959
  have htrace : WordTrace (prefixWord ++ tailWord_736959) baseStart_736959 baseEnd_736959 := by
    simpa [prefixWord, tailWord_736959, baseEnd_736959] using wordTrace_append hprefix tailTrace_736959
  have hstable : (prefixWord ++ tailWord_736959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736959).length < 2 ^ (prefixWord ++ tailWord_736959).sum := by decide
  have hdescent : baseEnd_736959 < baseStart_736959 := by decide
  rcases family_descends (prefixWord ++ tailWord_736959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736973 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_736973 : Nat := 118140960795 + 736973 * 2 ^ 59
def prefixEnd_736973 : Nat := 4983230072969 + 3 ^ 40 * 736973 * 2
def baseEnd_736973 : Nat := 126140459462016774482743

theorem tailTrace_736973 : CollatzResearch.WordTrace tailWord_736973 prefixEnd_736973 126140459462016774482743 := by
  unfold tailWord_736973
  simp only [CollatzResearch.WordTrace]
  refine ⟨26879613559080160812887573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17919742372720107208591715 26879613559080160812887573)
  ·
    refine ⟨1259981885581882538104105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26879613559080160812887573 1259981885581882538104105)
    ·
      refine ⟨944986414186411903578079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1259981885581882538104105 944986414186411903578079)
      ·
        refine ⟨1417479621279617855367119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944986414186411903578079 1417479621279617855367119)
        ·
          refine ⟨2126219431919426783050679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417479621279617855367119 2126219431919426783050679)
          ·
            refine ⟨3189329147879140174576019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126219431919426783050679 3189329147879140174576019)
            ·
              refine ⟨4783993721818710261864029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189329147879140174576019 4783993721818710261864029)
              ·
                refine ⟨1793997645682016348199011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4783993721818710261864029 1793997645682016348199011)
                ·
                  refine ⟨2690996468523024522298517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793997645682016348199011 2690996468523024522298517)
                  ·
                    refine ⟨126140459462016774482743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2690996468523024522298517 126140459462016774482743)
                    ·
                      rfl

theorem cell23_736973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_736973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736973 prefixEnd_736973 := by exact prefixLift 736973
  have htrace : WordTrace (prefixWord ++ tailWord_736973) baseStart_736973 baseEnd_736973 := by
    simpa [prefixWord, tailWord_736973, baseEnd_736973] using wordTrace_append hprefix tailTrace_736973
  have hstable : (prefixWord ++ tailWord_736973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736973).length < 2 ^ (prefixWord ++ tailWord_736973).sum := by decide
  have hdescent : baseEnd_736973 < baseStart_736973 := by decide
  rcases family_descends (prefixWord ++ tailWord_736973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736980 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_736980 : Nat := 118140960795 + 736980 * 2 ^ 59
def prefixEnd_736980 : Nat := 4983230072969 + 3 ^ 40 * 736980 * 2
def baseEnd_736980 : Nat := 378424972750631796060697

theorem tailTrace_736980 : CollatzResearch.WordTrace tailWord_736980 prefixEnd_736980 378424972750631796060697 := by
  unfold tailWord_736980
  simp only [CollatzResearch.WordTrace]
  refine ⟨13439934435027400504196197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17919912580036534005594929 13439934435027400504196197)
  ·
    refine ⟨2519987706567637594536787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13439934435027400504196197 2519987706567637594536787)
    ·
      refine ⟨3779981559851456391805181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519987706567637594536787 3779981559851456391805181)
      ·
        refine ⟨1417493084944296146926943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3779981559851456391805181 1417493084944296146926943)
        ·
          refine ⟨2126239627416444220390415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417493084944296146926943 2126239627416444220390415)
          ·
            refine ⟨3189359441124666330585623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126239627416444220390415 3189359441124666330585623)
            ·
              refine ⟨4784039161686999495878435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189359441124666330585623 4784039161686999495878435)
              ·
                refine ⟨7176058742530499243817653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784039161686999495878435 7176058742530499243817653)
                ·
                  refine ⟨672755507112234304107905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7176058742530499243817653 672755507112234304107905)
                  ·
                    refine ⟨504566630334175728080929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 672755507112234304107905 504566630334175728080929)
                    ·
                      refine ⟨378424972750631796060697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504566630334175728080929 378424972750631796060697)
                      ·
                        rfl

theorem cell23_736980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_736980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736980 prefixEnd_736980 := by exact prefixLift 736980
  have htrace : WordTrace (prefixWord ++ tailWord_736980) baseStart_736980 baseEnd_736980 := by
    simpa [prefixWord, tailWord_736980, baseEnd_736980] using wordTrace_append hprefix tailTrace_736980
  have hstable : (prefixWord ++ tailWord_736980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736980).length < 2 ^ (prefixWord ++ tailWord_736980).sum := by decide
  have hdescent : baseEnd_736980 < baseStart_736980 := by decide
  rcases family_descends (prefixWord ++ tailWord_736980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736986 : List Nat := [3, 1, 1, 2, 2, 4, 3, 7]
def baseStart_736986 : Nat := 118140960795 + 736986 * 2 ^ 59
def prefixEnd_736986 : Nat := 4983230072969 + 3 ^ 40 * 736986 * 2
def baseEnd_736986 : Nat := 14015853838316991577247

theorem tailTrace_736986 : CollatzResearch.WordTrace tailWord_736986 prefixEnd_736986 14015853838316991577247 := by
  unfold tailWord_736986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720021927008266008277703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17920058472022042688740541 6720021927008266008277703)
  ·
    refine ⟨10080032890512399012416555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6720021927008266008277703 10080032890512399012416555)
    ·
      refine ⟨15120049335768598518624833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10080032890512399012416555 15120049335768598518624833)
      ·
        refine ⟨11340037001826448888968625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15120049335768598518624833 11340037001826448888968625)
        ·
          refine ⟨8505027751369836666726469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11340037001826448888968625 8505027751369836666726469)
          ·
            refine ⟨1594692703381844375011213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8505027751369836666726469 1594692703381844375011213)
            ·
              refine ⟨598009763768191640629205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1594692703381844375011213 598009763768191640629205)
              ·
                refine ⟨14015853838316991577247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 598009763768191640629205 14015853838316991577247)
                ·
                  rfl

theorem cell23_736986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_736986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736986 prefixEnd_736986 := by exact prefixLift 736986
  have htrace : WordTrace (prefixWord ++ tailWord_736986) baseStart_736986 baseEnd_736986 := by
    simpa [prefixWord, tailWord_736986, baseEnd_736986] using wordTrace_append hprefix tailTrace_736986
  have hstable : (prefixWord ++ tailWord_736986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736986).length < 2 ^ (prefixWord ++ tailWord_736986).sum := by decide
  have hdescent : baseEnd_736986 < baseStart_736986 := by decide
  rcases family_descends (prefixWord ++ tailWord_736986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736996 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_736996 : Nat := 118140960795 + 736996 * 2 ^ 59
def prefixEnd_736996 : Nat := 4983230072969 + 3 ^ 40 * 736996 * 2
def baseEnd_736996 : Nat := 378433188441103733460623

theorem tailTrace_736996 : CollatzResearch.WordTrace tailWord_736996 prefixEnd_736996 378433188441103733460623 := by
  unfold tailWord_736996
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440226218998417870487421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17920301625331223827316561 13440226218998417870487421)
  ·
    refine ⟨5040084832124406701432783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13440226218998417870487421 5040084832124406701432783)
    ·
      refine ⟨7560127248186610052149175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040084832124406701432783 7560127248186610052149175)
      ·
        refine ⟨11340190872279915078223763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7560127248186610052149175 11340190872279915078223763)
        ·
          refine ⟨17010286308419872617335645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11340190872279915078223763 17010286308419872617335645)
          ·
            refine ⟨6378857365657452231500867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17010286308419872617335645 6378857365657452231500867)
            ·
              refine ⟨9568286048486178347251301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378857365657452231500867 9568286048486178347251301)
              ·
                refine ⟨1794053634091158440109619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9568286048486178347251301 1794053634091158440109619)
                ·
                  refine ⟨2691080451136737660164429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794053634091158440109619 2691080451136737660164429)
                  ·
                    refine ⟨1009155169176276622561661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691080451136737660164429 1009155169176276622561661)
                    ·
                      refine ⟨378433188441103733460623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009155169176276622561661 378433188441103733460623)
                      ·
                        rfl

theorem cell23_736996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_736996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736996 prefixEnd_736996 := by exact prefixLift 736996
  have htrace : WordTrace (prefixWord ++ tailWord_736996) baseStart_736996 baseEnd_736996 := by
    simpa [prefixWord, tailWord_736996, baseEnd_736996] using wordTrace_append hprefix tailTrace_736996
  have hstable : (prefixWord ++ tailWord_736996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736996).length < 2 ^ (prefixWord ++ tailWord_736996).sum := by decide
  have hdescent : baseEnd_736996 < baseStart_736996 := by decide
  rcases family_descends (prefixWord ++ tailWord_736996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736997 : List Nat := [1, 3, 1, 4, 1, 1, 4, 3, 1, 2, 2]
def baseStart_736997 : Nat := 118140960795 + 736997 * 2 ^ 59
def prefixEnd_736997 : Nat := 4983230072969 + 3 ^ 40 * 736997 * 2
def baseEnd_736997 : Nat := 378433701921758229548119

theorem tailTrace_736997 : CollatzResearch.WordTrace tailWord_736997 prefixEnd_736997 378433701921758229548119 := by
  unfold tailWord_736997
  simp only [CollatzResearch.WordTrace]
  refine ⟨26880488910993212911761245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17920325940662141941174163 26880488910993212911761245)
  ·
    refine ⟨10080183341622454841910467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26880488910993212911761245 10080183341622454841910467)
    ·
      refine ⟨15120275012433682262865701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10080183341622454841910467 15120275012433682262865701)
      ·
        refine ⟨2835051564831315424287319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15120275012433682262865701 2835051564831315424287319)
        ·
          refine ⟨4252577347246973136430979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835051564831315424287319 4252577347246973136430979)
          ·
            refine ⟨6378866020870459704646469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252577347246973136430979 6378866020870459704646469)
            ·
              refine ⟨1196037378913211194621213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6378866020870459704646469 1196037378913211194621213)
              ·
                refine ⟨448514017092454197982955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196037378913211194621213 448514017092454197982955)
                ·
                  refine ⟨672771025638681296974433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448514017092454197982955 672771025638681296974433)
                  ·
                    refine ⟨504578269229010972730825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 672771025638681296974433 504578269229010972730825)
                    ·
                      refine ⟨378433701921758229548119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504578269229010972730825 378433701921758229548119)
                      ·
                        rfl

theorem cell23_736997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_736997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736997 prefixEnd_736997 := by exact prefixLift 736997
  have htrace : WordTrace (prefixWord ++ tailWord_736997) baseStart_736997 baseEnd_736997 := by
    simpa [prefixWord, tailWord_736997, baseEnd_736997] using wordTrace_append hprefix tailTrace_736997
  have hstable : (prefixWord ++ tailWord_736997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736997).length < 2 ^ (prefixWord ++ tailWord_736997).sum := by decide
  have hdescent : baseEnd_736997 < baseStart_736997 := by decide
  rcases family_descends (prefixWord ++ tailWord_736997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737000 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_737000 : Nat := 118140960795 + 737000 * 2 ^ 59
def prefixEnd_737000 : Nat := 4983230072969 + 3 ^ 40 * 737000 * 2
def baseEnd_737000 : Nat := 378435242363721717810605

theorem tailTrace_737000 : CollatzResearch.WordTrace tailWord_737000 prefixEnd_737000 378435242363721717810605 := by
  unfold tailWord_737000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440299164991172212060227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17920398886654896282746969 13440299164991172212060227)
  ·
    refine ⟨20160448747486758318090341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13440299164991172212060227 20160448747486758318090341)
    ·
      refine ⟨3780084140153767184641939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20160448747486758318090341 3780084140153767184641939)
      ·
        refine ⟨5670126210230650776962909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780084140153767184641939 5670126210230650776962909)
        ·
          refine ⟨2126297328836494041361091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5670126210230650776962909 2126297328836494041361091)
          ·
            refine ⟨3189445993254741062041637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126297328836494041361091 3189445993254741062041637)
            ·
              refine ⟨598021123735263949132807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3189445993254741062041637 598021123735263949132807)
              ·
                refine ⟨897031685602895923699211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598021123735263949132807 897031685602895923699211)
                ·
                  refine ⟨1345547528404343885548817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897031685602895923699211 1345547528404343885548817)
                  ·
                    refine ⟨1009160646303257914161613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345547528404343885548817 1009160646303257914161613)
                    ·
                      refine ⟨378435242363721717810605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009160646303257914161613 378435242363721717810605)
                      ·
                        rfl

theorem cell23_737000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_737000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737000 prefixEnd_737000 := by exact prefixLift 737000
  have htrace : WordTrace (prefixWord ++ tailWord_737000) baseStart_737000 baseEnd_737000 := by
    simpa [prefixWord, tailWord_737000, baseEnd_737000] using wordTrace_append hprefix tailTrace_737000
  have hstable : (prefixWord ++ tailWord_737000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737000).length < 2 ^ (prefixWord ++ tailWord_737000).sum := by decide
  have hdescent : baseEnd_737000 < baseStart_737000 := by decide
  rcases family_descends (prefixWord ++ tailWord_737000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737019 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4]
def baseStart_737019 : Nat := 118140960795 + 737019 * 2 ^ 59
def prefixEnd_737019 : Nat := 4983230072969 + 3 ^ 40 * 737019 * 2
def baseEnd_737019 : Nat := 378444998496157143473017

theorem tailTrace_737019 : CollatzResearch.WordTrace tailWord_737019 prefixEnd_737019 378444998496157143473017 := by
  unfold tailWord_737019
  simp only [CollatzResearch.WordTrace]
  refine ⟨26881291316913510669062111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17920860877942340446041407 26881291316913510669062111)
  ·
    refine ⟨40321936975370266003593167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26881291316913510669062111 40321936975370266003593167)
    ·
      refine ⟨60482905463055399005389751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40321936975370266003593167 60482905463055399005389751)
      ·
        refine ⟨90724358194583098508084627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60482905463055399005389751 90724358194583098508084627)
        ·
          refine ⟨136086537291874647762126941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90724358194583098508084627 136086537291874647762126941)
          ·
            refine ⟨51032451484452992910797603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136086537291874647762126941 51032451484452992910797603)
            ·
              refine ⟨76548677226679489366196405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51032451484452992910797603 76548677226679489366196405)
              ·
                refine ⟨7176438490001202128080913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76548677226679489366196405 7176438490001202128080913)
                ·
                  refine ⟨5382328867500901596060685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7176438490001202128080913 5382328867500901596060685)
                  ·
                    refine ⟨2018373325312838098522757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5382328867500901596060685 2018373325312838098522757)
                    ·
                      refine ⟨378444998496157143473017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2018373325312838098522757 378444998496157143473017)
                      ·
                        rfl

theorem cell23_737019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_737019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737019 prefixEnd_737019 := by exact prefixLift 737019
  have htrace : WordTrace (prefixWord ++ tailWord_737019) baseStart_737019 baseEnd_737019 := by
    simpa [prefixWord, tailWord_737019, baseEnd_737019] using wordTrace_append hprefix tailTrace_737019
  have hstable : (prefixWord ++ tailWord_737019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737019).length < 2 ^ (prefixWord ++ tailWord_737019).sum := by decide
  have hdescent : baseEnd_737019 < baseStart_737019 := by decide
  rcases family_descends (prefixWord ++ tailWord_737019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737037 : List Nat := [1, 7, 2, 1, 1, 1, 1, 9]
def baseStart_737037 : Nat := 118140960795 + 737037 * 2 ^ 59
def prefixEnd_737037 : Nat := 4983230072969 + 3 ^ 40 * 737037 * 2
def baseEnd_737037 : Nat := 14016823746219928631405

theorem tailTrace_737037 : CollatzResearch.WordTrace tailWord_737037 prefixEnd_737037 14016823746219928631405 := by
  unfold tailWord_737037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26881947830848299743217365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17921298553898866495478243 26881947830848299743217365)
  ·
    refine ⟨630045652285507025231657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26881947830848299743217365 630045652285507025231657)
    ·
      refine ⟨472534239214130268923743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630045652285507025231657 472534239214130268923743)
      ·
        refine ⟨708801358821195403385615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472534239214130268923743 708801358821195403385615)
        ·
          refine ⟨1063202038231793105078423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708801358821195403385615 1063202038231793105078423)
          ·
            refine ⟨1594803057347689657617635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063202038231793105078423 1594803057347689657617635)
            ·
              refine ⟨2392204586021534486426453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594803057347689657617635 2392204586021534486426453)
              ·
                refine ⟨14016823746219928631405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2392204586021534486426453 14016823746219928631405)
                ·
                  rfl

theorem cell23_737037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 9].length) (baseStart_737037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737037 prefixEnd_737037 := by exact prefixLift 737037
  have htrace : WordTrace (prefixWord ++ tailWord_737037) baseStart_737037 baseEnd_737037 := by
    simpa [prefixWord, tailWord_737037, baseEnd_737037] using wordTrace_append hprefix tailTrace_737037
  have hstable : (prefixWord ++ tailWord_737037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737037).length < 2 ^ (prefixWord ++ tailWord_737037).sum := by decide
  have hdescent : baseEnd_737037 < baseStart_737037 := by decide
  rcases family_descends (prefixWord ++ tailWord_737037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737056 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_737056 : Nat := 118140960795 + 737056 * 2 ^ 59
def prefixEnd_737056 : Nat := 4983230072969 + 3 ^ 40 * 737056 * 2
def baseEnd_737056 : Nat := 378463997280373498710347

theorem tailTrace_737056 : CollatzResearch.WordTrace tailWord_737056 prefixEnd_737056 378463997280373498710347 := by
  unfold tailWord_737056
  simp only [CollatzResearch.WordTrace]
  refine ⟨13441320408889732994079511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17921760545186310658772681 13441320408889732994079511)
  ·
    refine ⟨20161980613334599491119267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13441320408889732994079511 20161980613334599491119267)
    ·
      refine ⟨30242970920001899236678901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20161980613334599491119267 30242970920001899236678901)
      ·
        refine ⟨2835278523750178053438647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30242970920001899236678901 2835278523750178053438647)
        ·
          refine ⟨4252917785625267080157971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835278523750178053438647 4252917785625267080157971)
          ·
            refine ⟨6379376678437900620236957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252917785625267080157971 6379376678437900620236957)
            ·
              refine ⟨2392266254414212732588859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6379376678437900620236957 2392266254414212732588859)
              ·
                refine ⟨3588399381621319098883289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392266254414212732588859 3588399381621319098883289)
                ·
                  refine ⟨2691299536215989324162467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588399381621319098883289 2691299536215989324162467)
                  ·
                    refine ⟨4036949304323983986243701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2691299536215989324162467 4036949304323983986243701)
                    ·
                      refine ⟨378463997280373498710347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4036949304323983986243701 378463997280373498710347)
                      ·
                        rfl

theorem cell23_737056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_737056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737056 prefixEnd_737056 := by exact prefixLift 737056
  have htrace : WordTrace (prefixWord ++ tailWord_737056) baseStart_737056 baseEnd_737056 := by
    simpa [prefixWord, tailWord_737056, baseEnd_737056] using wordTrace_append hprefix tailTrace_737056
  have hstable : (prefixWord ++ tailWord_737056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737056).length < 2 ^ (prefixWord ++ tailWord_737056).sum := by decide
  have hdescent : baseEnd_737056 < baseStart_737056 := by decide
  rcases family_descends (prefixWord ++ tailWord_737056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737059 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 9]
def baseStart_737059 : Nat := 118140960795 + 737059 * 2 ^ 59
def prefixEnd_737059 : Nat := 4983230072969 + 3 ^ 40 * 737059 * 2
def baseEnd_737059 : Nat := 42051726413592998552537

theorem tailTrace_737059 : CollatzResearch.WordTrace tailWord_737059 prefixEnd_737059 42051726413592998552537 := by
  unfold tailWord_737059
  simp only [CollatzResearch.WordTrace]
  refine ⟨26882750236768597500518231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17921833491179065000345487 26882750236768597500518231)
  ·
    refine ⟨40324125355152896250777347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26882750236768597500518231 40324125355152896250777347)
    ·
      refine ⟨60486188032729344376166021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40324125355152896250777347 60486188032729344376166021)
      ·
        refine ⟨11341160256136752070531129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60486188032729344376166021 11341160256136752070531129)
        ·
          refine ⟨8505870192102564052898347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11341160256136752070531129 8505870192102564052898347)
          ·
            refine ⟨12758805288153846079347521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8505870192102564052898347 12758805288153846079347521)
            ·
              refine ⟨9569103966115384559510641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12758805288153846079347521 9569103966115384559510641)
              ·
                refine ⟨7176827974586538419632981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9569103966115384559510641 7176827974586538419632981)
                ·
                  refine ⟨42051726413592998552537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7176827974586538419632981 42051726413592998552537)
                  ·
                    rfl

theorem cell23_737059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 9].length) (baseStart_737059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737059 prefixEnd_737059 := by exact prefixLift 737059
  have htrace : WordTrace (prefixWord ++ tailWord_737059) baseStart_737059 baseEnd_737059 := by
    simpa [prefixWord, tailWord_737059, baseEnd_737059] using wordTrace_append hprefix tailTrace_737059
  have hstable : (prefixWord ++ tailWord_737059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737059).length < 2 ^ (prefixWord ++ tailWord_737059).sum := by decide
  have hdescent : baseEnd_737059 < baseStart_737059 := by decide
  rcases family_descends (prefixWord ++ tailWord_737059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737079 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_737079 : Nat := 118140960795 + 737079 * 2 ^ 59
def prefixEnd_737079 : Nat := 4983230072969 + 3 ^ 40 * 737079 * 2
def baseEnd_737079 : Nat := 378475807335426908722741

theorem tailTrace_737079 : CollatzResearch.WordTrace tailWord_737079 prefixEnd_737079 378475807335426908722741 := by
  unfold tailWord_737079
  simp only [CollatzResearch.WordTrace]
  refine ⟨26883479696696140916246291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17922319797797427277497527 26883479696696140916246291)
  ·
    refine ⟨40325219545044211374369437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26883479696696140916246291 40325219545044211374369437)
    ·
      refine ⟨15121957329391579265388539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40325219545044211374369437 15121957329391579265388539)
      ·
        refine ⟨22682935994087368898082809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15121957329391579265388539 22682935994087368898082809)
        ·
          refine ⟨17012201995565526673562107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22682935994087368898082809 17012201995565526673562107)
          ·
            refine ⟨25518302993348290010343161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17012201995565526673562107 25518302993348290010343161)
            ·
              refine ⟨19138727245011217507757371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25518302993348290010343161 19138727245011217507757371)
              ·
                refine ⟨28708090867516826261636057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19138727245011217507757371 28708090867516826261636057)
                ·
                  refine ⟨21531068150637619696227043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28708090867516826261636057 21531068150637619696227043)
                  ·
                    refine ⟨32296602225956429544340565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21531068150637619696227043 32296602225956429544340565)
                    ·
                      refine ⟨378475807335426908722741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 32296602225956429544340565 378475807335426908722741)
                      ·
                        rfl

theorem cell23_737079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_737079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737079 prefixEnd_737079 := by exact prefixLift 737079
  have htrace : WordTrace (prefixWord ++ tailWord_737079) baseStart_737079 baseEnd_737079 := by
    simpa [prefixWord, tailWord_737079, baseEnd_737079] using wordTrace_append hprefix tailTrace_737079
  have hstable : (prefixWord ++ tailWord_737079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737079).length < 2 ^ (prefixWord ++ tailWord_737079).sum := by decide
  have hdescent : baseEnd_737079 < baseStart_737079 := by decide
  rcases family_descends (prefixWord ++ tailWord_737079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737081 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 2, 1, 3]
def baseStart_737081 : Nat := 118140960795 + 737081 * 2 ^ 59
def prefixEnd_737081 : Nat := 4983230072969 + 3 ^ 40 * 737081 * 2
def baseEnd_737081 : Nat := 378476834296735900897733

theorem tailTrace_737081 : CollatzResearch.WordTrace tailWord_737081 prefixEnd_737081 378476834296735900897733 := by
  unfold tailWord_737081
  simp only [CollatzResearch.WordTrace]
  refine ⟨26883552642688895257819097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17922368428459263505212731 26883552642688895257819097)
  ·
    refine ⟨20162664482016671443364323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26883552642688895257819097 20162664482016671443364323)
    ·
      refine ⟨30243996723025007165046485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20162664482016671443364323 30243996723025007165046485)
      ·
        refine ⟨708843673195898605430777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30243996723025007165046485 708843673195898605430777)
        ·
          refine ⟨531632754896923954073083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708843673195898605430777 531632754896923954073083)
          ·
            refine ⟨797449132345385931109625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531632754896923954073083 797449132345385931109625)
            ·
              refine ⟨598086849259039448332219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797449132345385931109625 598086849259039448332219)
              ·
                refine ⟨897130273888559172498329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598086849259039448332219 897130273888559172498329)
                ·
                  refine ⟨672847705416419379373747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 897130273888559172498329 672847705416419379373747)
                  ·
                    refine ⟨1009271558124629069060621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 672847705416419379373747 1009271558124629069060621)
                    ·
                      refine ⟨378476834296735900897733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009271558124629069060621 378476834296735900897733)
                      ·
                        rfl

theorem cell23_737081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_737081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737081 prefixEnd_737081 := by exact prefixLift 737081
  have htrace : WordTrace (prefixWord ++ tailWord_737081) baseStart_737081 baseEnd_737081 := by
    simpa [prefixWord, tailWord_737081, baseEnd_737081] using wordTrace_append hprefix tailTrace_737081
  have hstable : (prefixWord ++ tailWord_737081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737081).length < 2 ^ (prefixWord ++ tailWord_737081).sum := by decide
  have hdescent : baseEnd_737081 < baseStart_737081 := by decide
  rcases family_descends (prefixWord ++ tailWord_737081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737087 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 2, 2, 2]
def baseStart_737087 : Nat := 118140960795 + 737087 * 2 ^ 59
def prefixEnd_737087 : Nat := 4983230072969 + 3 ^ 40 * 737087 * 2
def baseEnd_737087 : Nat := 378479915180662877422705

theorem tailTrace_737087 : CollatzResearch.WordTrace tailWord_737087 prefixEnd_737087 378479915180662877422705 := by
  unfold tailWord_737087
  simp only [CollatzResearch.WordTrace]
  refine ⟨26883771480667158282537515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17922514320444772188358343 26883771480667158282537515)
  ·
    refine ⟨40325657221000737423806273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26883771480667158282537515 40325657221000737423806273)
    ·
      refine ⟨30244242915750553067854705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40325657221000737423806273 30244242915750553067854705)
      ·
        refine ⟨22683182186812914800891029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30244242915750553067854705 22683182186812914800891029)
        ·
          refine ⟨1063274165006855381291767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22683182186812914800891029 1063274165006855381291767)
          ·
            refine ⟨1594911247510283071937651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063274165006855381291767 1594911247510283071937651)
            ·
              refine ⟨2392366871265424607906477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594911247510283071937651 2392366871265424607906477)
              ·
                refine ⟨897137576724534227964929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2392366871265424607906477 897137576724534227964929)
                ·
                  refine ⟨672853182543400670973697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 897137576724534227964929 672853182543400670973697)
                  ·
                    refine ⟨504639886907550503230273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 672853182543400670973697 504639886907550503230273)
                    ·
                      refine ⟨378479915180662877422705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504639886907550503230273 378479915180662877422705)
                      ·
                        rfl

theorem cell23_737087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_737087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737087 prefixEnd_737087 := by exact prefixLift 737087
  have htrace : WordTrace (prefixWord ++ tailWord_737087) baseStart_737087 baseEnd_737087 := by
    simpa [prefixWord, tailWord_737087, baseEnd_737087] using wordTrace_append hprefix tailTrace_737087
  have hstable : (prefixWord ++ tailWord_737087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737087).length < 2 ^ (prefixWord ++ tailWord_737087).sum := by decide
  have hdescent : baseEnd_737087 < baseStart_737087 := by decide
  rcases family_descends (prefixWord ++ tailWord_737087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737183 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 8]
def baseStart_737183 : Nat := 118140960795 + 737183 * 2 ^ 59
def prefixEnd_737183 : Nat := 4983230072969 + 3 ^ 40 * 737183 * 2
def baseEnd_737183 : Nat := 42058801035943833535807

theorem tailTrace_737183 : CollatzResearch.WordTrace tailWord_737183 prefixEnd_737183 42058801035943833535807 := by
  unfold tailWord_737183
  simp only [CollatzResearch.WordTrace]
  refine ⟨26887272888319366678032203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17924848592212911118688135 26887272888319366678032203)
  ·
    refine ⟨40330909332479050017048305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26887272888319366678032203 40330909332479050017048305)
    ·
      refine ⟨30248181999359287512786229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40330909332479050017048305 30248181999359287512786229)
      ·
        refine ⟨2835767062439933204323709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30248181999359287512786229 2835767062439933204323709)
        ·
          refine ⟨1063412648414974951621391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2835767062439933204323709 1063412648414974951621391)
          ·
            refine ⟨1595118972622462427432087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063412648414974951621391 1595118972622462427432087)
            ·
              refine ⟨2392678458933693641148131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595118972622462427432087 2392678458933693641148131)
              ·
                refine ⟨3589017688400540461722197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392678458933693641148131 3589017688400540461722197)
                ·
                  refine ⟨42058801035943833535807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3589017688400540461722197 42058801035943833535807)
                  ·
                    rfl

theorem cell23_737183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 8].length) (baseStart_737183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737183 prefixEnd_737183 := by exact prefixLift 737183
  have htrace : WordTrace (prefixWord ++ tailWord_737183) baseStart_737183 baseEnd_737183 := by
    simpa [prefixWord, tailWord_737183, baseEnd_737183] using wordTrace_append hprefix tailTrace_737183
  have hstable : (prefixWord ++ tailWord_737183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737183).length < 2 ^ (prefixWord ++ tailWord_737183).sum := by decide
  have hdescent : baseEnd_737183 < baseStart_737183 := by decide
  rcases family_descends (prefixWord ++ tailWord_737183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737203 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 3, 5, 2]
def baseStart_737203 : Nat := 118140960795 + 737203 * 2 ^ 59
def prefixEnd_737203 : Nat := 4983230072969 + 3 ^ 40 * 737203 * 2
def baseEnd_737203 : Nat := 378539478936584423572171

theorem tailTrace_737203 : CollatzResearch.WordTrace tailWord_737203 prefixEnd_737203 378539478936584423572171 := by
  unfold tailWord_737203
  simp only [CollatzResearch.WordTrace]
  refine ⟨26888002348246910093760263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17925334898831273395840175 26888002348246910093760263)
  ·
    refine ⟨40332003522370365140640395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26888002348246910093760263 40332003522370365140640395)
    ·
      refine ⟨60498005283555547710960593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40332003522370365140640395 60498005283555547710960593)
      ·
        refine ⟨45373503962666660783220445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60498005283555547710960593 45373503962666660783220445)
        ·
          refine ⟨17015063985999997793707667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45373503962666660783220445 17015063985999997793707667)
          ·
            refine ⟨25522595978999996690561501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17015063985999997793707667 25522595978999996690561501)
            ·
              refine ⟨9570973492124998758960563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25522595978999996690561501 9570973492124998758960563)
              ·
                refine ⟨14356460238187498138440845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9570973492124998758960563 14356460238187498138440845)
                ·
                  refine ⟨5383672589320311801915317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14356460238187498138440845 5383672589320311801915317)
                  ·
                    refine ⟨504719305248779231429561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5383672589320311801915317 504719305248779231429561)
                    ·
                      refine ⟨378539478936584423572171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504719305248779231429561 378539478936584423572171)
                      ·
                        rfl

theorem cell23_737203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5, 2].length) (baseStart_737203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737203 prefixEnd_737203 := by exact prefixLift 737203
  have htrace : WordTrace (prefixWord ++ tailWord_737203) baseStart_737203 baseEnd_737203 := by
    simpa [prefixWord, tailWord_737203, baseEnd_737203] using wordTrace_append hprefix tailTrace_737203
  have hstable : (prefixWord ++ tailWord_737203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737203).length < 2 ^ (prefixWord ++ tailWord_737203).sum := by decide
  have hdescent : baseEnd_737203 < baseStart_737203 := by decide
  rcases family_descends (prefixWord ++ tailWord_737203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737237 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_737237 : Nat := 118140960795 + 737237 * 2 ^ 59
def prefixEnd_737237 : Nat := 4983230072969 + 3 ^ 40 * 737237 * 2
def baseEnd_737237 : Nat := 378556937278837290547015

theorem tailTrace_737237 : CollatzResearch.WordTrace tailWord_737237 prefixEnd_737237 378556937278837290547015 := by
  unfold tailWord_737237
  simp only [CollatzResearch.WordTrace]
  refine ⟨26889242430123733900497965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17926161620082489266998643 26889242430123733900497965)
  ·
    refine ⟨10083465911296400212686737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26889242430123733900497965 10083465911296400212686737)
    ·
      refine ⟨7562599433472300159515053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10083465911296400212686737 7562599433472300159515053)
      ·
        refine ⟨2835974787552112559818145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7562599433472300159515053 2835974787552112559818145)
        ·
          refine ⟨2126981090664084419863609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2835974787552112559818145 2126981090664084419863609)
          ·
            refine ⟨1595235817998063314897707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2126981090664084419863609 1595235817998063314897707)
            ·
              refine ⟨2392853726997094972346561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595235817998063314897707 2392853726997094972346561)
              ·
                refine ⟨1794640295247821229259921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2392853726997094972346561 1794640295247821229259921)
                ·
                  refine ⟨1345980221435865921944941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1794640295247821229259921 1345980221435865921944941)
                  ·
                    refine ⟨504742583038449720729353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1345980221435865921944941 504742583038449720729353)
                    ·
                      refine ⟨378556937278837290547015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504742583038449720729353 378556937278837290547015)
                      ·
                        rfl

theorem cell23_737237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_737237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737237 prefixEnd_737237 := by exact prefixLift 737237
  have htrace : WordTrace (prefixWord ++ tailWord_737237) baseStart_737237 baseEnd_737237 := by
    simpa [prefixWord, tailWord_737237, baseEnd_737237] using wordTrace_append hprefix tailTrace_737237
  have hstable : (prefixWord ++ tailWord_737237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737237).length < 2 ^ (prefixWord ++ tailWord_737237).sum := by decide
  have hdescent : baseEnd_737237 < baseStart_737237 := by decide
  rcases family_descends (prefixWord ++ tailWord_737237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737263 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_737263 : Nat := 118140960795 + 737263 * 2 ^ 59
def prefixEnd_737263 : Nat := 4983230072969 + 3 ^ 40 * 737263 * 2
def baseEnd_737263 : Nat := 378570287775854188821895

theorem tailTrace_737263 : CollatzResearch.WordTrace tailWord_737263 prefixEnd_737263 378570287775854188821895 := by
  unfold tailWord_737263
  simp only [CollatzResearch.WordTrace]
  refine ⟨26890190728029540340944443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17926793818686360227296295 26890190728029540340944443)
  ·
    refine ⟨40335286092044310511416665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26890190728029540340944443 40335286092044310511416665)
    ·
      refine ⟨30251464569033232883562499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40335286092044310511416665 30251464569033232883562499)
      ·
        refine ⟨45377196853549849325343749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30251464569033232883562499 45377196853549849325343749)
        ·
          refine ⟨8508224410040596748501953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45377196853549849325343749 8508224410040596748501953)
          ·
            refine ⟨6381168307530447561376465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8508224410040596748501953 6381168307530447561376465)
            ·
              refine ⟨4785876230647835671032349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6381168307530447561376465 4785876230647835671032349)
              ·
                refine ⟨1794703586492938376637131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4785876230647835671032349 1794703586492938376637131)
                ·
                  refine ⟨2692055379739407564955697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794703586492938376637131 2692055379739407564955697)
                  ·
                    refine ⟨2019041534804555673716773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2692055379739407564955697 2019041534804555673716773)
                    ·
                      refine ⟨378570287775854188821895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2019041534804555673716773 378570287775854188821895)
                      ·
                        rfl

theorem cell23_737263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_737263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737263 prefixEnd_737263 := by exact prefixLift 737263
  have htrace : WordTrace (prefixWord ++ tailWord_737263) baseStart_737263 baseEnd_737263 := by
    simpa [prefixWord, tailWord_737263, baseEnd_737263] using wordTrace_append hprefix tailTrace_737263
  have hstable : (prefixWord ++ tailWord_737263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737263).length < 2 ^ (prefixWord ++ tailWord_737263).sum := by decide
  have hdescent : baseEnd_737263 < baseStart_737263 := by decide
  rcases family_descends (prefixWord ++ tailWord_737263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737301 : List Nat := [1, 3, 2, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_737301 : Nat := 118140960795 + 737301 * 2 ^ 59
def prefixEnd_737301 : Nat := 4983230072969 + 3 ^ 40 * 737301 * 2
def baseEnd_737301 : Nat := 378589800040725040146721

theorem tailTrace_737301 : CollatzResearch.WordTrace tailWord_737301 prefixEnd_737301 378589800040725040146721 := by
  unfold tailWord_737301
  simp only [CollatzResearch.WordTrace]
  refine ⟨26891576701891872830827757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17927717801261248553885171 26891576701891872830827757)
  ·
    refine ⟨10084341263209452311560409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26891576701891872830827757 10084341263209452311560409)
    ·
      refine ⟨7563255947407089233670307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10084341263209452311560409 7563255947407089233670307)
      ·
        refine ⟨11344883921110633850505461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7563255947407089233670307 11344883921110633850505461)
        ·
          refine ⟨1063582867604121923484887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11344883921110633850505461 1063582867604121923484887)
          ·
            refine ⟨1595374301406182885227331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063582867604121923484887 1595374301406182885227331)
            ·
              refine ⟨2393061452109274327840997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595374301406182885227331 2393061452109274327840997)
              ·
                refine ⟨448699022270488936470187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2393061452109274327840997 448699022270488936470187)
                ·
                  refine ⟨673048533405733404705281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448699022270488936470187 673048533405733404705281)
                  ·
                    refine ⟨504786400054300053528961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673048533405733404705281 504786400054300053528961)
                    ·
                      refine ⟨378589800040725040146721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504786400054300053528961 378589800040725040146721)
                      ·
                        rfl

theorem cell23_737301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_737301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737301 prefixEnd_737301 := by exact prefixLift 737301
  have htrace : WordTrace (prefixWord ++ tailWord_737301) baseStart_737301 baseEnd_737301 := by
    simpa [prefixWord, tailWord_737301, baseEnd_737301] using wordTrace_append hprefix tailTrace_737301
  have hstable : (prefixWord ++ tailWord_737301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737301).length < 2 ^ (prefixWord ++ tailWord_737301).sum := by decide
  have hdescent : baseEnd_737301 < baseStart_737301 := by decide
  rcases family_descends (prefixWord ++ tailWord_737301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737317 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_737317 : Nat := 118140960795 + 737317 * 2 ^ 59
def prefixEnd_737317 : Nat := 4983230072969 + 3 ^ 40 * 737317 * 2
def baseEnd_737317 : Nat := 378598015731196977546647

theorem tailTrace_737317 : CollatzResearch.WordTrace tailWord_737317 prefixEnd_737317 378598015731196977546647 := by
  unfold tailWord_737317
  simp only [CollatzResearch.WordTrace]
  refine ⟨26892160269833907563410205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17928106846555938375606803 26892160269833907563410205)
  ·
    refine ⟨10084560101187715336278827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26892160269833907563410205 10084560101187715336278827)
    ·
      refine ⟨15126840151781573004418241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10084560101187715336278827 15126840151781573004418241)
      ·
        refine ⟨11345130113836179753313681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15126840151781573004418241 11345130113836179753313681)
        ·
          refine ⟨8508847585377134814985261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11345130113836179753313681 8508847585377134814985261)
          ·
            refine ⟨3190817844516425555619473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8508847585377134814985261 3190817844516425555619473)
            ·
              refine ⟨2393113383387319166714605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190817844516425555619473 2393113383387319166714605)
              ·
                refine ⟨897417518770244687517977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2393113383387319166714605 897417518770244687517977)
                ·
                  refine ⟨673063139077683515638483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 897417518770244687517977 673063139077683515638483)
                  ·
                    refine ⟨1009594708616525273457725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 673063139077683515638483 1009594708616525273457725)
                    ·
                      refine ⟨378598015731196977546647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009594708616525273457725 378598015731196977546647)
                      ·
                        rfl

theorem cell23_737317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_737317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737317 prefixEnd_737317 := by exact prefixLift 737317
  have htrace : WordTrace (prefixWord ++ tailWord_737317) baseStart_737317 baseEnd_737317 := by
    simpa [prefixWord, tailWord_737317, baseEnd_737317] using wordTrace_append hprefix tailTrace_737317
  have hstable : (prefixWord ++ tailWord_737317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737317).length < 2 ^ (prefixWord ++ tailWord_737317).sum := by decide
  have hdescent : baseEnd_737317 < baseStart_737317 := by decide
  rcases family_descends (prefixWord ++ tailWord_737317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737343 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_737343 : Nat := 118140960795 + 737343 * 2 ^ 59
def prefixEnd_737343 : Nat := 4983230072969 + 3 ^ 40 * 737343 * 2
def baseEnd_737343 : Nat := 378611366228213875821527

theorem tailTrace_737343 : CollatzResearch.WordTrace tailWord_737343 prefixEnd_737343 378611366228213875821527 := by
  unfold tailWord_737343
  simp only [CollatzResearch.WordTrace]
  refine ⟨26893108567739714003856683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17928739045159809335904455 26893108567739714003856683)
  ·
    refine ⟨40339662851609571005785025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26893108567739714003856683 40339662851609571005785025)
    ·
      refine ⟨30254747138707178254338769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40339662851609571005785025 30254747138707178254338769)
      ·
        refine ⟨22691060354030383690754077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30254747138707178254338769 22691060354030383690754077)
        ·
          refine ⟨8509147632761393884032779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22691060354030383690754077 8509147632761393884032779)
          ·
            refine ⟨12763721449142090826049169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509147632761393884032779 12763721449142090826049169)
            ·
              refine ⟨9572791086856568119536877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12763721449142090826049169 9572791086856568119536877)
              ·
                refine ⟨3589796657571213044826329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9572791086856568119536877 3589796657571213044826329)
                ·
                  refine ⟨2692347493178409783619747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3589796657571213044826329 2692347493178409783619747)
                  ·
                    refine ⟨4038521239767614675429621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2692347493178409783619747 4038521239767614675429621)
                    ·
                      refine ⟨378611366228213875821527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4038521239767614675429621 378611366228213875821527)
                      ·
                        rfl

theorem cell23_737343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_737343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737343 prefixEnd_737343 := by exact prefixLift 737343
  have htrace : WordTrace (prefixWord ++ tailWord_737343) baseStart_737343 baseEnd_737343 := by
    simpa [prefixWord, tailWord_737343, baseEnd_737343] using wordTrace_append hprefix tailTrace_737343
  have hstable : (prefixWord ++ tailWord_737343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737343).length < 2 ^ (prefixWord ++ tailWord_737343).sum := by decide
  have hdescent : baseEnd_737343 < baseStart_737343 := by decide
  rcases family_descends (prefixWord ++ tailWord_737343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737344 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 1, 3, 2]
def baseStart_737344 : Nat := 118140960795 + 737344 * 2 ^ 59
def prefixEnd_737344 : Nat := 4983230072969 + 3 ^ 40 * 737344 * 2
def baseEnd_737344 : Nat := 378611879708868371909023

theorem tailTrace_737344 : CollatzResearch.WordTrace tailWord_737344 prefixEnd_737344 378611879708868371909023 := by
  unfold tailWord_737344
  simp only [CollatzResearch.WordTrace]
  refine ⟨13446572520368045587321543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17928763360490727449762057 13446572520368045587321543)
  ·
    refine ⟨20169858780552068380982315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13446572520368045587321543 20169858780552068380982315)
    ·
      refine ⟨30254788170828102571473473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20169858780552068380982315 30254788170828102571473473)
      ·
        refine ⟨22691091128121076928605105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30254788170828102571473473 22691091128121076928605105)
        ·
          refine ⟨17018318346090807696453829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22691091128121076928605105 17018318346090807696453829)
          ·
            refine ⟨3190934689892026443085093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17018318346090807696453829 3190934689892026443085093)
            ·
              refine ⟨598300254354754958078455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3190934689892026443085093 598300254354754958078455)
              ·
                refine ⟨897450381532132437117683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598300254354754958078455 897450381532132437117683)
                ·
                  refine ⟨1346175572298198655676525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897450381532132437117683 1346175572298198655676525)
                  ·
                    refine ⟨504815839611824495878697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1346175572298198655676525 504815839611824495878697)
                    ·
                      refine ⟨378611879708868371909023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504815839611824495878697 378611879708868371909023)
                      ·
                        rfl

theorem cell23_737344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_737344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737344 prefixEnd_737344 := by exact prefixLift 737344
  have htrace : WordTrace (prefixWord ++ tailWord_737344) baseStart_737344 baseEnd_737344 := by
    simpa [prefixWord, tailWord_737344, baseEnd_737344] using wordTrace_append hprefix tailTrace_737344
  have hstable : (prefixWord ++ tailWord_737344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737344).length < 2 ^ (prefixWord ++ tailWord_737344).sum := by decide
  have hdescent : baseEnd_737344 < baseStart_737344 := by decide
  rcases family_descends (prefixWord ++ tailWord_737344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737353 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_737353 : Nat := 118140960795 + 737353 * 2 ^ 59
def prefixEnd_737353 : Nat := 4983230072969 + 3 ^ 40 * 737353 * 2
def baseEnd_737353 : Nat := 378616501034758836696481

theorem tailTrace_737353 : CollatzResearch.WordTrace tailWord_737353 prefixEnd_737353 378616501034758836696481 := by
  unfold tailWord_737353
  simp only [CollatzResearch.WordTrace]
  refine ⟨26893473297703485711720713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17928982198468990474480475 26893473297703485711720713)
  ·
    refine ⟨20170104973277614283790535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26893473297703485711720713 20170104973277614283790535)
    ·
      refine ⟨30255157459916421425685803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20170104973277614283790535 30255157459916421425685803)
      ·
        refine ⟨45382736189874632138528705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30255157459916421425685803 45382736189874632138528705)
        ·
          refine ⟨34037052142405974103896529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45382736189874632138528705 34037052142405974103896529)
          ·
            refine ⟨25527789106804480577922397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34037052142405974103896529 25527789106804480577922397)
            ·
              refine ⟨9572920915051680216720899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25527789106804480577922397 9572920915051680216720899)
              ·
                refine ⟨14359381372577520325081349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9572920915051680216720899 14359381372577520325081349)
                ·
                  refine ⟨2692384007358285060952753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14359381372577520325081349 2692384007358285060952753)
                  ·
                    refine ⟨2019288005518713795714565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2692384007358285060952753 2019288005518713795714565)
                    ·
                      refine ⟨378616501034758836696481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2019288005518713795714565 378616501034758836696481)
                      ·
                        rfl

theorem cell23_737353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_737353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737353 prefixEnd_737353 := by exact prefixLift 737353
  have htrace : WordTrace (prefixWord ++ tailWord_737353) baseStart_737353 baseEnd_737353 := by
    simpa [prefixWord, tailWord_737353, baseEnd_737353] using wordTrace_append hprefix tailTrace_737353
  have hstable : (prefixWord ++ tailWord_737353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737353).length < 2 ^ (prefixWord ++ tailWord_737353).sum := by decide
  have hdescent : baseEnd_737353 < baseStart_737353 := by decide
  rcases family_descends (prefixWord ++ tailWord_737353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737393 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 1, 7]
def baseStart_737393 : Nat := 118140960795 + 737393 * 2 ^ 59
def prefixEnd_737393 : Nat := 4983230072969 + 3 ^ 40 * 737393 * 2
def baseEnd_737393 : Nat := 126212346753646226732099

theorem tailTrace_737393 : CollatzResearch.WordTrace tailWord_737393 prefixEnd_737393 126212346753646226732099 := by
  unfold tailWord_737393
  simp only [CollatzResearch.WordTrace]
  refine ⟨26894932217558572543176833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17929954811705715028784555 26894932217558572543176833)
  ·
    refine ⟨20171199163168929407382625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26894932217558572543176833 20171199163168929407382625)
    ·
      refine ⟨15128399372376697055536969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20171199163168929407382625 15128399372376697055536969)
      ·
        refine ⟨11346299529282522791652727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15128399372376697055536969 11346299529282522791652727)
        ·
          refine ⟨17019449293923784187479091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11346299529282522791652727 17019449293923784187479091)
          ·
            refine ⟨25529173940885676281218637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17019449293923784187479091 25529173940885676281218637)
            ·
              refine ⟨9573440227832128605456989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25529173940885676281218637 9573440227832128605456989)
              ·
                refine ⟨3590040085437048227046371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9573440227832128605456989 3590040085437048227046371)
                ·
                  refine ⟨5385060128155572340569557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590040085437048227046371 5385060128155572340569557)
                  ·
                    refine ⟨126212346753646226732099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5385060128155572340569557 126212346753646226732099)
                    ·
                      rfl

theorem cell23_737393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_737393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737393 prefixEnd_737393 := by exact prefixLift 737393
  have htrace : WordTrace (prefixWord ++ tailWord_737393) baseStart_737393 baseEnd_737393 := by
    simpa [prefixWord, tailWord_737393, baseEnd_737393] using wordTrace_append hprefix tailTrace_737393
  have hstable : (prefixWord ++ tailWord_737393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737393).length < 2 ^ (prefixWord ++ tailWord_737393).sum := by decide
  have hdescent : baseEnd_737393 < baseStart_737393 := by decide
  rcases family_descends (prefixWord ++ tailWord_737393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737400 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 7, 2]
def baseStart_737400 : Nat := 118140960795 + 737400 * 2 ^ 59
def prefixEnd_737400 : Nat := 4983230072969 + 3 ^ 40 * 737400 * 2
def baseEnd_737400 : Nat := 378640634625520152808765

theorem tailTrace_737400 : CollatzResearch.WordTrace tailWord_737400 prefixEnd_737400 378640634625520152808765 := by
  unfold tailWord_737400
  simp only [CollatzResearch.WordTrace]
  refine ⟨13447593764266606369340827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17930125019022141825787769 13447593764266606369340827)
  ·
    refine ⟨20171390646399909554011241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13447593764266606369340827 20171390646399909554011241)
    ·
      refine ⟨15128542984799932165508431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20171390646399909554011241 15128542984799932165508431)
      ·
        refine ⟨22692814477199898248262647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15128542984799932165508431 22692814477199898248262647)
        ·
          refine ⟨34039221715799847372393971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22692814477199898248262647 34039221715799847372393971)
          ·
            refine ⟨51058832573699771058590957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34039221715799847372393971 51058832573699771058590957)
            ·
              refine ⟨19147062215137414146971609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51058832573699771058590957 19147062215137414146971609)
              ·
                refine ⟨14360296661353060610228707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19147062215137414146971609 14360296661353060610228707)
                ·
                  refine ⟨21540444992029590915343061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14360296661353060610228707 21540444992029590915343061)
                  ·
                    refine ⟨504854179500693537078353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21540444992029590915343061 504854179500693537078353)
                    ·
                      refine ⟨378640634625520152808765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504854179500693537078353 378640634625520152808765)
                      ·
                        rfl

theorem cell23_737400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_737400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737400 prefixEnd_737400 := by exact prefixLift 737400
  have htrace : WordTrace (prefixWord ++ tailWord_737400) baseStart_737400 baseEnd_737400 := by
    simpa [prefixWord, tailWord_737400, baseEnd_737400] using wordTrace_append hprefix tailTrace_737400
  have hstable : (prefixWord ++ tailWord_737400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737400).length < 2 ^ (prefixWord ++ tailWord_737400).sum := by decide
  have hdescent : baseEnd_737400 < baseStart_737400 := by decide
  rcases family_descends (prefixWord ++ tailWord_737400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737433 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_737433 : Nat := 118140960795 + 737433 * 2 ^ 59
def prefixEnd_737433 : Nat := 4983230072969 + 3 ^ 40 * 737433 * 2
def baseEnd_737433 : Nat := 378657579487118523696113

theorem tailTrace_737433 : CollatzResearch.WordTrace tailWord_737433 prefixEnd_737433 378657579487118523696113 := by
  unfold tailWord_737433
  simp only [CollatzResearch.WordTrace]
  refine ⟨26896391137413659374632953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17930927424942439583088635 26896391137413659374632953)
  ·
    refine ⟨20172293353060244530974715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26896391137413659374632953 20172293353060244530974715)
    ·
      refine ⟨30258440029590366796462073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20172293353060244530974715 30258440029590366796462073)
      ·
        refine ⟨22693830022192775097346555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30258440029590366796462073 22693830022192775097346555)
        ·
          refine ⟨34040745033289162646019833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22693830022192775097346555 34040745033289162646019833)
          ·
            refine ⟨25530558774966871984514875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34040745033289162646019833 25530558774966871984514875)
            ·
              refine ⟨38295838162450307976772313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25530558774966871984514875 38295838162450307976772313)
              ·
                refine ⟨28721878621837730982579235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38295838162450307976772313 28721878621837730982579235)
                ·
                  refine ⟨43082817932756596473868853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28721878621837730982579235 43082817932756596473868853)
                  ·
                    refine ⟨4039014181195930919425205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43082817932756596473868853 4039014181195930919425205)
                    ·
                      refine ⟨378657579487118523696113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4039014181195930919425205 378657579487118523696113)
                      ·
                        rfl

theorem cell23_737433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_737433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737433 prefixEnd_737433 := by exact prefixLift 737433
  have htrace : WordTrace (prefixWord ++ tailWord_737433) baseStart_737433 baseEnd_737433 := by
    simpa [prefixWord, tailWord_737433, baseEnd_737433] using wordTrace_append hprefix tailTrace_737433
  have hstable : (prefixWord ++ tailWord_737433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737433).length < 2 ^ (prefixWord ++ tailWord_737433).sum := by decide
  have hdescent : baseEnd_737433 < baseStart_737433 := by decide
  rcases family_descends (prefixWord ++ tailWord_737433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737443 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6]
def baseStart_737443 : Nat := 118140960795 + 737443 * 2 ^ 59
def prefixEnd_737443 : Nat := 4983230072969 + 3 ^ 40 * 737443 * 2
def baseEnd_737443 : Nat := 378662714293663484571067

theorem tailTrace_737443 : CollatzResearch.WordTrace tailWord_737443 prefixEnd_737443 378662714293663484571067 := by
  unfold tailWord_737443
  simp only [CollatzResearch.WordTrace]
  refine ⟨26896755867377431082496983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17931170578251620721664655 26896755867377431082496983)
  ·
    refine ⟨40345133801066146623745475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26896755867377431082496983 40345133801066146623745475)
    ·
      refine ⟨60517700701599219935618213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40345133801066146623745475 60517700701599219935618213)
      ·
        refine ⟨11347068881549853737928415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60517700701599219935618213 11347068881549853737928415)
        ·
          refine ⟨17020603322324780606892623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11347068881549853737928415 17020603322324780606892623)
          ·
            refine ⟨25530904983487170910338935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17020603322324780606892623 25530904983487170910338935)
            ·
              refine ⟨38296357475230756365508403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25530904983487170910338935 38296357475230756365508403)
              ·
                refine ⟨57444536212846134548262605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38296357475230756365508403 57444536212846134548262605)
                ·
                  refine ⟨21541701079817300455598477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57444536212846134548262605 21541701079817300455598477)
                  ·
                    refine ⟨8078137904931487670849429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21541701079817300455598477 8078137904931487670849429)
                    ·
                      refine ⟨378662714293663484571067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8078137904931487670849429 378662714293663484571067)
                      ·
                        rfl

theorem cell23_737443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_737443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737443 prefixEnd_737443 := by exact prefixLift 737443
  have htrace : WordTrace (prefixWord ++ tailWord_737443) baseStart_737443 baseEnd_737443 := by
    simpa [prefixWord, tailWord_737443, baseEnd_737443] using wordTrace_append hprefix tailTrace_737443
  have hstable : (prefixWord ++ tailWord_737443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737443).length < 2 ^ (prefixWord ++ tailWord_737443).sum := by decide
  have hdescent : baseEnd_737443 < baseStart_737443 := by decide
  rcases family_descends (prefixWord ++ tailWord_737443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737480 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_737480 : Nat := 118140960795 + 737480 * 2 ^ 59
def prefixEnd_737480 : Nat := 4983230072969 + 3 ^ 40 * 737480 * 2
def baseEnd_737480 : Nat := 378681713077879839808397

theorem tailTrace_737480 : CollatzResearch.WordTrace tailWord_737480 prefixEnd_737480 378681713077879839808397 := by
  unfold tailWord_737480
  simp only [CollatzResearch.WordTrace]
  refine ⟨13449052684121693200796947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17932070245495590934395929 13449052684121693200796947)
  ·
    refine ⟨20173579026182539801195421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13449052684121693200796947 20173579026182539801195421)
    ·
      refine ⟨7565092134818452425448283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20173579026182539801195421 7565092134818452425448283)
      ·
        refine ⟨11347638202227678638172425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565092134818452425448283 11347638202227678638172425)
        ·
          refine ⟨8510728651670758978629319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11347638202227678638172425 8510728651670758978629319)
          ·
            refine ⟨12766092977506138467943979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8510728651670758978629319 12766092977506138467943979)
            ·
              refine ⟨19149139466259207701915969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12766092977506138467943979 19149139466259207701915969)
              ·
                refine ⟨14361854599694405776436977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19149139466259207701915969 14361854599694405776436977)
                ·
                  refine ⟨10771390949770804332327733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14361854599694405776436977 10771390949770804332327733)
                  ·
                    refine ⟨1009817901541012906155725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10771390949770804332327733 1009817901541012906155725)
                    ·
                      refine ⟨378681713077879839808397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009817901541012906155725 378681713077879839808397)
                      ·
                        rfl

theorem cell23_737480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_737480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737480 prefixEnd_737480 := by exact prefixLift 737480
  have htrace : WordTrace (prefixWord ++ tailWord_737480) baseStart_737480 baseEnd_737480 := by
    simpa [prefixWord, tailWord_737480, baseEnd_737480] using wordTrace_append hprefix tailTrace_737480
  have hstable : (prefixWord ++ tailWord_737480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737480).length < 2 ^ (prefixWord ++ tailWord_737480).sum := by decide
  have hdescent : baseEnd_737480 < baseStart_737480 := by decide
  rcases family_descends (prefixWord ++ tailWord_737480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737497 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 3]
def baseStart_737497 : Nat := 118140960795 + 737497 * 2 ^ 59
def prefixEnd_737497 : Nat := 4983230072969 + 3 ^ 40 * 737497 * 2
def baseEnd_737497 : Nat := 378690442249006273295819

theorem tailTrace_737497 : CollatzResearch.WordTrace tailWord_737497 prefixEnd_737497 378690442249006273295819 := by
  unfold tailWord_737497
  simp only [CollatzResearch.WordTrace]
  refine ⟨26898725409181798304962745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17932483606121198869975163 26898725409181798304962745)
  ·
    refine ⟨20174044056886348728722059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26898725409181798304962745 20174044056886348728722059)
    ·
      refine ⟨30261066085329523093083089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20174044056886348728722059 30261066085329523093083089)
      ·
        refine ⟨22695799563997142319812317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30261066085329523093083089 22695799563997142319812317)
        ·
          refine ⟨8510924836498928369929619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22695799563997142319812317 8510924836498928369929619)
          ·
            refine ⟨12766387254748392554894429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8510924836498928369929619 12766387254748392554894429)
            ·
              refine ⟨4787395220530647208085411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12766387254748392554894429 4787395220530647208085411)
              ·
                refine ⟨7181092830795970812128117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787395220530647208085411 7181092830795970812128117)
                ·
                  refine ⟨673227452887122263637011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7181092830795970812128117 673227452887122263637011)
                  ·
                    refine ⟨1009841179330683395455517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 673227452887122263637011 1009841179330683395455517)
                    ·
                      refine ⟨378690442249006273295819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009841179330683395455517 378690442249006273295819)
                      ·
                        rfl

theorem cell23_737497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_737497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737497 prefixEnd_737497 := by exact prefixLift 737497
  have htrace : WordTrace (prefixWord ++ tailWord_737497) baseStart_737497 baseEnd_737497 := by
    simpa [prefixWord, tailWord_737497, baseEnd_737497] using wordTrace_append hprefix tailTrace_737497
  have hstable : (prefixWord ++ tailWord_737497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737497).length < 2 ^ (prefixWord ++ tailWord_737497).sum := by decide
  have hdescent : baseEnd_737497 < baseStart_737497 := by decide
  rcases family_descends (prefixWord ++ tailWord_737497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737501 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_737501 : Nat := 118140960795 + 737501 * 2 ^ 59
def prefixEnd_737501 : Nat := 4983230072969 + 3 ^ 40 * 737501 * 2
def baseEnd_737501 : Nat := 378692496171624257645801

theorem tailTrace_737501 : CollatzResearch.WordTrace tailWord_737501 prefixEnd_737501 378692496171624257645801 := by
  unfold tailWord_737501
  simp only [CollatzResearch.WordTrace]
  refine ⟨26898871301167306988108357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17932580867444871325405571 26898871301167306988108357)
  ·
    refine ⟨5043538368968870060270317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26898871301167306988108357 5043538368968870060270317)
    ·
      refine ⟨1891326888363326272601369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5043538368968870060270317 1891326888363326272601369)
      ·
        refine ⟨1418495166272494704451027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1891326888363326272601369 1418495166272494704451027)
        ·
          refine ⟨2127742749408742056676541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418495166272494704451027 2127742749408742056676541)
          ·
            refine ⟨797903531028278271253703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2127742749408742056676541 797903531028278271253703)
            ·
              refine ⟨1196855296542417406880555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797903531028278271253703 1196855296542417406880555)
              ·
                refine ⟨1795282944813626110320833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196855296542417406880555 1795282944813626110320833)
                ·
                  refine ⟨1346462208610219582740625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1795282944813626110320833 1346462208610219582740625)
                  ·
                    refine ⟨1009846656457664687055469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346462208610219582740625 1009846656457664687055469)
                    ·
                      refine ⟨378692496171624257645801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009846656457664687055469 378692496171624257645801)
                      ·
                        rfl

theorem cell23_737501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_737501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737501 prefixEnd_737501 := by exact prefixLift 737501
  have htrace : WordTrace (prefixWord ++ tailWord_737501) baseStart_737501 baseEnd_737501 := by
    simpa [prefixWord, tailWord_737501, baseEnd_737501] using wordTrace_append hprefix tailTrace_737501
  have hstable : (prefixWord ++ tailWord_737501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737501).length < 2 ^ (prefixWord ++ tailWord_737501).sum := by decide
  have hdescent : baseEnd_737501 < baseStart_737501 := by decide
  rcases family_descends (prefixWord ++ tailWord_737501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737557 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_737557 : Nat := 118140960795 + 737557 * 2 ^ 59
def prefixEnd_737557 : Nat := 4983230072969 + 3 ^ 40 * 737557 * 2
def baseEnd_737557 : Nat := 378721251088276038545543

theorem tailTrace_737557 : CollatzResearch.WordTrace tailWord_737557 prefixEnd_737557 378721251088276038545543 := by
  unfold tailWord_737557
  simp only [CollatzResearch.WordTrace]
  refine ⟨26900913788964428552146925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17933942525976285701431283 26900913788964428552146925)
  ·
    refine ⟨10087842670861660707055097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26900913788964428552146925 10087842670861660707055097)
    ·
      refine ⟨7565882003146245530291323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10087842670861660707055097 7565882003146245530291323)
      ·
        refine ⟨11348823004719368295436985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565882003146245530291323 11348823004719368295436985)
        ·
          refine ⟨8511617253539526221577739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11348823004719368295436985 8511617253539526221577739)
          ·
            refine ⟨12767425880309289332366609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511617253539526221577739 12767425880309289332366609)
            ·
              refine ⟨9575569410231966999274957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12767425880309289332366609 9575569410231966999274957)
              ·
                refine ⟨3590838528836987624728109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9575569410231966999274957 3590838528836987624728109)
                ·
                  refine ⟨1346564448313870359273041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3590838528836987624728109 1346564448313870359273041)
                  ·
                    refine ⟨1009923336235402769454781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346564448313870359273041 1009923336235402769454781)
                    ·
                      refine ⟨378721251088276038545543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009923336235402769454781 378721251088276038545543)
                      ·
                        rfl

theorem cell23_737557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_737557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737557 prefixEnd_737557 := by exact prefixLift 737557
  have htrace : WordTrace (prefixWord ++ tailWord_737557) baseStart_737557 baseEnd_737557 := by
    simpa [prefixWord, tailWord_737557, baseEnd_737557] using wordTrace_append hprefix tailTrace_737557
  have hstable : (prefixWord ++ tailWord_737557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737557).length < 2 ^ (prefixWord ++ tailWord_737557).sum := by decide
  have hdescent : baseEnd_737557 < baseStart_737557 := by decide
  rcases family_descends (prefixWord ++ tailWord_737557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737560 : List Nat := [2, 1, 2, 3, 1, 2, 3, 9]
def baseStart_737560 : Nat := 118140960795 + 737560 * 2 ^ 59
def prefixEnd_737560 : Nat := 4983230072969 + 3 ^ 40 * 737560 * 2
def baseEnd_737560 : Nat := 14026770056675538029927

theorem tailTrace_737560 : CollatzResearch.WordTrace tailWord_737560 prefixEnd_737560 14026770056675538029927 := by
  unfold tailWord_737560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13450511603976780032253067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17934015471969040043004089 13450511603976780032253067)
  ·
    refine ⟨20175767405965170048379601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13450511603976780032253067 20175767405965170048379601)
    ·
      refine ⟨15131825554473877536284701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20175767405965170048379601 15131825554473877536284701)
      ·
        refine ⟨5674434582927704076106763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15131825554473877536284701 5674434582927704076106763)
        ·
          refine ⟨8511651874391556114160145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5674434582927704076106763 8511651874391556114160145)
          ·
            refine ⟨6383738905793667085620109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8511651874391556114160145 6383738905793667085620109)
            ·
              refine ⟨2393902089672625157107541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6383738905793667085620109 2393902089672625157107541)
              ·
                refine ⟨14026770056675538029927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2393902089672625157107541 14026770056675538029927)
                ·
                  rfl

theorem cell23_737560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 9].length) (baseStart_737560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737560 prefixEnd_737560 := by exact prefixLift 737560
  have htrace : WordTrace (prefixWord ++ tailWord_737560) baseStart_737560 baseEnd_737560 := by
    simpa [prefixWord, tailWord_737560, baseEnd_737560] using wordTrace_append hprefix tailTrace_737560
  have hstable : (prefixWord ++ tailWord_737560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737560).length < 2 ^ (prefixWord ++ tailWord_737560).sum := by decide
  have hdescent : baseEnd_737560 < baseStart_737560 := by decide
  rcases family_descends (prefixWord ++ tailWord_737560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737565 : List Nat := [1, 4, 2, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_737565 : Nat := 118140960795 + 737565 * 2 ^ 59
def prefixEnd_737565 : Nat := 4983230072969 + 3 ^ 40 * 737565 * 2
def baseEnd_737565 : Nat := 378725358933512007245507

theorem tailTrace_737565 : CollatzResearch.WordTrace tailWord_737565 prefixEnd_737565 378725358933512007245507 := by
  unfold tailWord_737565
  simp only [CollatzResearch.WordTrace]
  refine ⟨26901205572935445918438149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17934137048623630612292099 26901205572935445918438149)
  ·
    refine ⟨5043976044925396109707153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26901205572935445918438149 5043976044925396109707153)
    ·
      refine ⟨3782982033694047082280365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5043976044925396109707153 3782982033694047082280365)
      ·
        refine ⟨1418618262635267655855137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3782982033694047082280365 1418618262635267655855137)
        ·
          refine ⟨1063963696976450741891353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418618262635267655855137 1063963696976450741891353)
          ·
            refine ⟨797972772732338056418515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1063963696976450741891353 797972772732338056418515)
            ·
              refine ⟨1196959159098507084627773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797972772732338056418515 1196959159098507084627773)
              ·
                refine ⟨448859684661940156735415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196959159098507084627773 448859684661940156735415)
                ·
                  refine ⟨673289526992910235103123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448859684661940156735415 673289526992910235103123)
                  ·
                    refine ⟨1009934290489365352654685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 673289526992910235103123 1009934290489365352654685)
                    ·
                      refine ⟨378725358933512007245507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009934290489365352654685 378725358933512007245507)
                      ·
                        rfl

theorem cell23_737565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_737565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737565 prefixEnd_737565 := by exact prefixLift 737565
  have htrace : WordTrace (prefixWord ++ tailWord_737565) baseStart_737565 baseEnd_737565 := by
    simpa [prefixWord, tailWord_737565, baseEnd_737565] using wordTrace_append hprefix tailTrace_737565
  have hstable : (prefixWord ++ tailWord_737565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737565).length < 2 ^ (prefixWord ++ tailWord_737565).sum := by decide
  have hdescent : baseEnd_737565 < baseStart_737565 := by decide
  rcases family_descends (prefixWord ++ tailWord_737565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737575 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_737575 : Nat := 118140960795 + 737575 * 2 ^ 59
def prefixEnd_737575 : Nat := 4983230072969 + 3 ^ 40 * 737575 * 2
def baseEnd_737575 : Nat := 378730493740056968120461

theorem tailTrace_737575 : CollatzResearch.WordTrace tailWord_737575 prefixEnd_737575 378730493740056968120461 := by
  unfold tailWord_737575
  simp only [CollatzResearch.WordTrace]
  refine ⟨26901570302899217626302179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17934380201932811750868119 26901570302899217626302179)
  ·
    refine ⟨40352355454348826439453269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26901570302899217626302179 40352355454348826439453269)
    ·
      refine ⟨472879165480650309837343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 40352355454348826439453269 472879165480650309837343)
      ·
        refine ⟨709318748220975464756015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472879165480650309837343 709318748220975464756015)
        ·
          refine ⟨1063978122331463197134023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709318748220975464756015 1063978122331463197134023)
          ·
            refine ⟨1595967183497194795701035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063978122331463197134023 1595967183497194795701035)
            ·
              refine ⟨2393950775245792193551553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595967183497194795701035 2393950775245792193551553)
              ·
                refine ⟨1795463081434344145163665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393950775245792193551553 1795463081434344145163665)
                ·
                  refine ⟨1346597311075758108872749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1795463081434344145163665 1346597311075758108872749)
                  ·
                    refine ⟨504973991653409290827281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1346597311075758108872749 504973991653409290827281)
                    ·
                      refine ⟨378730493740056968120461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504973991653409290827281 378730493740056968120461)
                      ·
                        rfl

theorem cell23_737575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_737575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737575 prefixEnd_737575 := by exact prefixLift 737575
  have htrace : WordTrace (prefixWord ++ tailWord_737575) baseStart_737575 baseEnd_737575 := by
    simpa [prefixWord, tailWord_737575, baseEnd_737575] using wordTrace_append hprefix tailTrace_737575
  have hstable : (prefixWord ++ tailWord_737575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737575).length < 2 ^ (prefixWord ++ tailWord_737575).sum := by decide
  have hdescent : baseEnd_737575 < baseStart_737575 := by decide
  rcases family_descends (prefixWord ++ tailWord_737575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737582 : List Nat := [4, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_737582 : Nat := 118140960795 + 737582 * 2 ^ 59
def prefixEnd_737582 : Nat := 4983230072969 + 3 ^ 40 * 737582 * 2
def baseEnd_737582 : Nat := 378734088104638440732929

theorem tailTrace_737582 : CollatzResearch.WordTrace tailWord_737582 prefixEnd_737582 378734088104638440732929 := by
  unfold tailWord_737582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362728201734232227725875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17934550409249238547871333 3362728201734232227725875)
  ·
    refine ⟨5044092302601348341588813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3362728201734232227725875 5044092302601348341588813)
    ·
      refine ⟨1891534613475505628095805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5044092302601348341588813 1891534613475505628095805)
      ·
        refine ⟨709325480053314610535927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1891534613475505628095805 709325480053314610535927)
        ·
          refine ⟨1063988220079971915803891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709325480053314610535927 1063988220079971915803891)
          ·
            refine ⟨1595982330119957873705837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063988220079971915803891 1595982330119957873705837)
            ·
              refine ⟨598493373794984202639689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1595982330119957873705837 598493373794984202639689)
              ·
                refine ⟨448870030346238151979767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598493373794984202639689 448870030346238151979767)
                ·
                  refine ⟨673305045519357227969651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448870030346238151979767 673305045519357227969651)
                  ·
                    refine ⟨1009957568279035841954477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 673305045519357227969651 1009957568279035841954477)
                    ·
                      refine ⟨378734088104638440732929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1009957568279035841954477 378734088104638440732929)
                      ·
                        rfl

theorem cell23_737582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_737582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737582 prefixEnd_737582 := by exact prefixLift 737582
  have htrace : WordTrace (prefixWord ++ tailWord_737582) baseStart_737582 baseEnd_737582 := by
    simpa [prefixWord, tailWord_737582, baseEnd_737582] using wordTrace_append hprefix tailTrace_737582
  have hstable : (prefixWord ++ tailWord_737582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737582).length < 2 ^ (prefixWord ++ tailWord_737582).sum := by decide
  have hdescent : baseEnd_737582 < baseStart_737582 := by decide
  rcases family_descends (prefixWord ++ tailWord_737582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737588 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_737588 : Nat := 118140960795 + 737588 * 2 ^ 59
def prefixEnd_737588 : Nat := 4983230072969 + 3 ^ 40 * 737588 * 2
def baseEnd_737588 : Nat := 378737168988565417257901

theorem tailTrace_737588 : CollatzResearch.WordTrace tailWord_737588 prefixEnd_737588 378737168988565417257901 := by
  unfold tailWord_737588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13451022225926060423262709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17934696301234747231016945 13451022225926060423262709)
  ·
    refine ⟨1261033333680568164680879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13451022225926060423262709 1261033333680568164680879)
    ·
      refine ⟨1891550000520852247021319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261033333680568164680879 1891550000520852247021319)
      ·
        refine ⟨2837325000781278370531979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891550000520852247021319 2837325000781278370531979)
        ·
          refine ⟨4255987501171917555797969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837325000781278370531979 4255987501171917555797969)
          ·
            refine ⟨3191990625878938166848477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4255987501171917555797969 3191990625878938166848477)
            ·
              refine ⟨1196996484704601812568179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3191990625878938166848477 1196996484704601812568179)
              ·
                refine ⟨1795494727056902718852269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196996484704601812568179 1795494727056902718852269)
                ·
                  refine ⟨673310522646338519569601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1795494727056902718852269 673310522646338519569601)
                  ·
                    refine ⟨504982891984753889677201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673310522646338519569601 504982891984753889677201)
                    ·
                      refine ⟨378737168988565417257901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 504982891984753889677201 378737168988565417257901)
                      ·
                        rfl

theorem cell23_737588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_737588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737588 prefixEnd_737588 := by exact prefixLift 737588
  have htrace : WordTrace (prefixWord ++ tailWord_737588) baseStart_737588 baseEnd_737588 := by
    simpa [prefixWord, tailWord_737588, baseEnd_737588] using wordTrace_append hprefix tailTrace_737588
  have hstable : (prefixWord ++ tailWord_737588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737588).length < 2 ^ (prefixWord ++ tailWord_737588).sum := by decide
  have hdescent : baseEnd_737588 < baseStart_737588 := by decide
  rcases family_descends (prefixWord ++ tailWord_737588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737598 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_737598 : Nat := 118140960795 + 737598 * 2 ^ 59
def prefixEnd_737598 : Nat := 4983230072969 + 3 ^ 40 * 737598 * 2
def baseEnd_737598 : Nat := 126247434598370126044285

theorem tailTrace_737598 : CollatzResearch.WordTrace tailWord_737598 prefixEnd_737598 126247434598370126044285 := by
  unfold tailWord_737598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362801147726986569298681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17934939454543928369592965 3362801147726986569298681)
  ·
    refine ⟨2522100860795239926974011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3362801147726986569298681 2522100860795239926974011)
    ·
      refine ⟨3783151291192859890461017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522100860795239926974011 3783151291192859890461017)
      ·
        refine ⟨2837363468394644917845763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3783151291192859890461017 2837363468394644917845763)
        ·
          refine ⟨4256045202591967376768645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837363468394644917845763 4256045202591967376768645)
          ·
            refine ⟨798008475485993883144121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4256045202591967376768645 798008475485993883144121)
            ·
              refine ⟨598506356614495412358091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798008475485993883144121 598506356614495412358091)
              ·
                refine ⟨897759534921743118537137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598506356614495412358091 897759534921743118537137)
                ·
                  refine ⟨673319651191307338902853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 897759534921743118537137 673319651191307338902853)
                  ·
                    refine ⟨126247434598370126044285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 673319651191307338902853 126247434598370126044285)
                    ·
                      rfl

theorem cell23_737598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_737598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737598 prefixEnd_737598 := by exact prefixLift 737598
  have htrace : WordTrace (prefixWord ++ tailWord_737598) baseStart_737598 baseEnd_737598 := by
    simpa [prefixWord, tailWord_737598, baseEnd_737598] using wordTrace_append hprefix tailTrace_737598
  have hstable : (prefixWord ++ tailWord_737598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737598).length < 2 ^ (prefixWord ++ tailWord_737598).sum := by decide
  have hdescent : baseEnd_737598 < baseStart_737598 := by decide
  rcases family_descends (prefixWord ++ tailWord_737598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737600 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_737600 : Nat := 118140960795 + 737600 * 2 ^ 59
def prefixEnd_737600 : Nat := 4983230072969 + 3 ^ 40 * 737600 * 2
def baseEnd_737600 : Nat := 378743330756419370307845

theorem tailTrace_737600 : CollatzResearch.WordTrace tailWord_737600 prefixEnd_737600 378743330756419370307845 := by
  unfold tailWord_737600
  simp only [CollatzResearch.WordTrace]
  refine ⟨13451241063904323447981127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17934988085205764597308169 13451241063904323447981127)
  ·
    refine ⟨20176861595856485171971691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13451241063904323447981127 20176861595856485171971691)
    ·
      refine ⟨30265292393784727757957537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20176861595856485171971691 30265292393784727757957537)
      ·
        refine ⟨22698969295338545818468153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30265292393784727757957537 22698969295338545818468153)
        ·
          refine ⟨17024226971503909363851115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22698969295338545818468153 17024226971503909363851115)
          ·
            refine ⟨25536340457255864045776673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17024226971503909363851115 25536340457255864045776673)
            ·
              refine ⟨19152255342941898034332505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25536340457255864045776673 19152255342941898034332505)
              ·
                refine ⟨14364191507206423525749379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19152255342941898034332505 14364191507206423525749379)
                ·
                  refine ⟨21546287260809635288624069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14364191507206423525749379 21546287260809635288624069)
                  ·
                    refine ⟨4039928861401806616617013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21546287260809635288624069 4039928861401806616617013)
                    ·
                      refine ⟨378743330756419370307845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4039928861401806616617013 378743330756419370307845)
                      ·
                        rfl

theorem cell23_737600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_737600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737600 prefixEnd_737600 := by exact prefixLift 737600
  have htrace : WordTrace (prefixWord ++ tailWord_737600) baseStart_737600 baseEnd_737600 := by
    simpa [prefixWord, tailWord_737600, baseEnd_737600] using wordTrace_append hprefix tailTrace_737600
  have hstable : (prefixWord ++ tailWord_737600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737600).length < 2 ^ (prefixWord ++ tailWord_737600).sum := by decide
  have hdescent : baseEnd_737600 < baseStart_737600 := by decide
  rcases family_descends (prefixWord ++ tailWord_737600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737610 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_737610 : Nat := 118140960795 + 737610 * 2 ^ 59
def prefixEnd_737610 : Nat := 4983230072969 + 3 ^ 40 * 737610 * 2
def baseEnd_737610 : Nat := 378748465562964331182799

theorem tailTrace_737610 : CollatzResearch.WordTrace tailWord_737610 prefixEnd_737610 378748465562964331182799 := by
  unfold tailWord_737610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725711714443104650956571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17935231238514945735884189 6725711714443104650956571)
  ·
    refine ⟨10088567571664656976434857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6725711714443104650956571 10088567571664656976434857)
    ·
      refine ⟨7566425678748492732326143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10088567571664656976434857 7566425678748492732326143)
      ·
        refine ⟨11349638518122739098489215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7566425678748492732326143 11349638518122739098489215)
        ·
          refine ⟨17024457777184108647733823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11349638518122739098489215 17024457777184108647733823)
          ·
            refine ⟨25536686665776162971600735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17024457777184108647733823 25536686665776162971600735)
            ·
              refine ⟨38305029998664244457401103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25536686665776162971600735 38305029998664244457401103)
              ·
                refine ⟨57457544997996366686101655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38305029998664244457401103 57457544997996366686101655)
                ·
                  refine ⟨86186317496994550029152483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57457544997996366686101655 86186317496994550029152483)
                  ·
                    refine ⟨129279476245491825043728725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86186317496994550029152483 129279476245491825043728725)
                    ·
                      refine ⟨378748465562964331182799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 129279476245491825043728725 378748465562964331182799)
                      ·
                        rfl

theorem cell23_737610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_737610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737610 prefixEnd_737610 := by exact prefixLift 737610
  have htrace : WordTrace (prefixWord ++ tailWord_737610) baseStart_737610 baseEnd_737610 := by
    simpa [prefixWord, tailWord_737610, baseEnd_737610] using wordTrace_append hprefix tailTrace_737610
  have hstable : (prefixWord ++ tailWord_737610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737610).length < 2 ^ (prefixWord ++ tailWord_737610).sum := by decide
  have hdescent : baseEnd_737610 < baseStart_737610 := by decide
  rcases family_descends (prefixWord ++ tailWord_737610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737661 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_737661 : Nat := 118140960795 + 737661 * 2 ^ 59
def prefixEnd_737661 : Nat := 4983230072969 + 3 ^ 40 * 737661 * 2
def baseEnd_737661 : Nat := 378774653076343631645065

theorem tailTrace_737661 : CollatzResearch.WordTrace tailWord_737661 prefixEnd_737661 378774653076343631645065 := by
  unfold tailWord_737661
  simp only [CollatzResearch.WordTrace]
  refine ⟨26904706980587654313932837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17936471320391769542621891 26904706980587654313932837)
  ·
    refine ⟨5044632558860185183862407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26904706980587654313932837 5044632558860185183862407)
    ·
      refine ⟨7566948838290277775793611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5044632558860185183862407 7566948838290277775793611)
      ·
        refine ⟨11350423257435416663690417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7566948838290277775793611 11350423257435416663690417)
        ·
          refine ⟨8512817443076562497767813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11350423257435416663690417 8512817443076562497767813)
          ·
            refine ⟨1596153270576855468331465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8512817443076562497767813 1596153270576855468331465)
            ·
              refine ⟨1197114952932641601248599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596153270576855468331465 1197114952932641601248599)
              ·
                refine ⟨1795672429398962401872899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197114952932641601248599 1795672429398962401872899)
                ·
                  refine ⟨2693508644098443602809349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795672429398962401872899 2693508644098443602809349)
                  ·
                    refine ⟨505032870768458175526753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2693508644098443602809349 505032870768458175526753)
                    ·
                      refine ⟨378774653076343631645065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505032870768458175526753 378774653076343631645065)
                      ·
                        rfl

theorem cell23_737661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_737661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737661 prefixEnd_737661 := by exact prefixLift 737661
  have htrace : WordTrace (prefixWord ++ tailWord_737661) baseStart_737661 baseEnd_737661 := by
    simpa [prefixWord, tailWord_737661, baseEnd_737661] using wordTrace_append hprefix tailTrace_737661
  have hstable : (prefixWord ++ tailWord_737661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737661).length < 2 ^ (prefixWord ++ tailWord_737661).sum := by decide
  have hdescent : baseEnd_737661 < baseStart_737661 := by decide
  rcases family_descends (prefixWord ++ tailWord_737661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737805 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_737805 : Nat := 118140960795 + 737805 * 2 ^ 59
def prefixEnd_737805 : Nat := 4983230072969 + 3 ^ 40 * 737805 * 2
def baseEnd_737805 : Nat := 378848594290591068244403

theorem tailTrace_737805 : CollatzResearch.WordTrace tailWord_737805 prefixEnd_737805 378848594290591068244403 := by
  unfold tailWord_737805
  simp only [CollatzResearch.WordTrace]
  refine ⟨26909959092065966907174869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17939972728043977938116579 26909959092065966907174869)
  ·
    refine ⟨630702166220296099386911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26909959092065966907174869 630702166220296099386911)
    ·
      refine ⟨946053249330444149080367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630702166220296099386911 946053249330444149080367)
      ·
        refine ⟨1419079873995666223620551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946053249330444149080367 1419079873995666223620551)
        ·
          refine ⟨2128619810993499335430827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419079873995666223620551 2128619810993499335430827)
          ·
            refine ⟨3192929716490249003146241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128619810993499335430827 3192929716490249003146241)
            ·
              refine ⟨2394697287367686752359681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192929716490249003146241 2394697287367686752359681)
              ·
                refine ⟨1796022965525765064269761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394697287367686752359681 1796022965525765064269761)
                ·
                  refine ⟨1347017224144323798202321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796022965525765064269761 1347017224144323798202321)
                  ·
                    refine ⟨1010262918108242848651741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1347017224144323798202321 1010262918108242848651741)
                    ·
                      refine ⟨378848594290591068244403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1010262918108242848651741 378848594290591068244403)
                      ·
                        rfl

theorem cell23_737805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_737805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737805 prefixEnd_737805 := by exact prefixLift 737805
  have htrace : WordTrace (prefixWord ++ tailWord_737805) baseStart_737805 baseEnd_737805 := by
    simpa [prefixWord, tailWord_737805, baseEnd_737805] using wordTrace_append hprefix tailTrace_737805
  have hstable : (prefixWord ++ tailWord_737805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737805).length < 2 ^ (prefixWord ++ tailWord_737805).sum := by decide
  have hdescent : baseEnd_737805 < baseStart_737805 := by decide
  rcases family_descends (prefixWord ++ tailWord_737805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737811 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 2, 3, 2]
def baseStart_737811 : Nat := 118140960795 + 737811 * 2 ^ 59
def prefixEnd_737811 : Nat := 4983230072969 + 3 ^ 40 * 737811 * 2
def baseEnd_737811 : Nat := 378851675174518044769375

theorem tailTrace_737811 : CollatzResearch.WordTrace tailWord_737811 prefixEnd_737811 378851675174518044769375 := by
  unfold tailWord_737811
  simp only [CollatzResearch.WordTrace]
  refine ⟨26910177930044229931893287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17940118620029486621262191 26910177930044229931893287)
  ·
    refine ⟨40365266895066344897839931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26910177930044229931893287 40365266895066344897839931)
    ·
      refine ⟨60547900342599517346759897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40365266895066344897839931 60547900342599517346759897)
      ·
        refine ⟨45410925256949638010069923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60547900342599517346759897 45410925256949638010069923)
        ·
          refine ⟨68116387885424457015104885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45410925256949638010069923 68116387885424457015104885)
          ·
            refine ⟨6385911364258542845166083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68116387885424457015104885 6385911364258542845166083)
            ·
              refine ⟨9578867046387814267749125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385911364258542845166083 9578867046387814267749125)
              ·
                refine ⟨1796037571197715175202961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9578867046387814267749125 1796037571197715175202961)
                ·
                  refine ⟨1347028178398286381402221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796037571197715175202961 1347028178398286381402221)
                  ·
                    refine ⟨505135566899357393025833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347028178398286381402221 505135566899357393025833)
                    ·
                      refine ⟨378851675174518044769375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505135566899357393025833 378851675174518044769375)
                      ·
                        rfl

theorem cell23_737811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3, 2].length) (baseStart_737811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737811 prefixEnd_737811 := by exact prefixLift 737811
  have htrace : WordTrace (prefixWord ++ tailWord_737811) baseStart_737811 baseEnd_737811 := by
    simpa [prefixWord, tailWord_737811, baseEnd_737811] using wordTrace_append hprefix tailTrace_737811
  have hstable : (prefixWord ++ tailWord_737811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737811).length < 2 ^ (prefixWord ++ tailWord_737811).sum := by decide
  have hdescent : baseEnd_737811 < baseStart_737811 := by decide
  rcases family_descends (prefixWord ++ tailWord_737811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737812 : List Nat := [2, 4, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_737812 : Nat := 118140960795 + 737812 * 2 ^ 59
def prefixEnd_737812 : Nat := 4983230072969 + 3 ^ 40 * 737812 * 2
def baseEnd_737812 : Nat := 126284062885057513618957

theorem tailTrace_737812 : CollatzResearch.WordTrace tailWord_737812 prefixEnd_737812 126284062885057513618957 := by
  unfold tailWord_737812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13455107201520303551339845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17940142935360404735119793 13455107201520303551339845)
  ·
    refine ⟨2522832600285056915876221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13455107201520303551339845 2522832600285056915876221)
    ·
      refine ⟨946062225106896343453583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2522832600285056915876221 946062225106896343453583)
      ·
        refine ⟨1419093337660344515180375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946062225106896343453583 1419093337660344515180375)
        ·
          refine ⟨2128640006490516772770563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419093337660344515180375 2128640006490516772770563)
          ·
            refine ⟨3192960009735775159155845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128640006490516772770563 3192960009735775159155845)
            ·
              refine ⟨598680001825457842341721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3192960009735775159155845 598680001825457842341721)
              ·
                refine ⟨449010001369093381756291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598680001825457842341721 449010001369093381756291)
                ·
                  refine ⟨673515002053640072634437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449010001369093381756291 673515002053640072634437)
                  ·
                    refine ⟨126284062885057513618957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 673515002053640072634437 126284062885057513618957)
                    ·
                      rfl

theorem cell23_737812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_737812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737812 prefixEnd_737812 := by exact prefixLift 737812
  have htrace : WordTrace (prefixWord ++ tailWord_737812) baseStart_737812 baseEnd_737812 := by
    simpa [prefixWord, tailWord_737812, baseEnd_737812] using wordTrace_append hprefix tailTrace_737812
  have hstable : (prefixWord ++ tailWord_737812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737812).length < 2 ^ (prefixWord ++ tailWord_737812).sum := by decide
  have hdescent : baseEnd_737812 < baseStart_737812 := by decide
  rcases family_descends (prefixWord ++ tailWord_737812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737931 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 5, 4, 2]
def baseStart_737931 : Nat := 118140960795 + 737931 * 2 ^ 59
def prefixEnd_737931 : Nat := 4983230072969 + 3 ^ 40 * 737931 * 2
def baseEnd_737931 : Nat := 378913292853057575268823

theorem tailTrace_737931 : CollatzResearch.WordTrace tailWord_737931 prefixEnd_737931 378913292853057575268823 := by
  unfold tailWord_737931
  simp only [CollatzResearch.WordTrace]
  refine ⟨26914554689609490426261647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17943036459739660284174431 26914554689609490426261647)
  ·
    refine ⟨40371832034414235639392471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26914554689609490426261647 40371832034414235639392471)
    ·
      refine ⟨60557748051621353459088707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40371832034414235639392471 60557748051621353459088707)
      ·
        refine ⟨90836622077432030188633061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60557748051621353459088707 90836622077432030188633061)
        ·
          refine ⟨17031866639518505660368699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90836622077432030188633061 17031866639518505660368699)
          ·
            refine ⟨25547799959277758490553049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17031866639518505660368699 25547799959277758490553049)
            ·
              refine ⟨19160849969458318867914787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25547799959277758490553049 19160849969458318867914787)
              ·
                refine ⟨28741274954187478301872181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19160849969458318867914787 28741274954187478301872181)
                ·
                  refine ⟨2694494526955076090800517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28741274954187478301872181 2694494526955076090800517)
                  ·
                    refine ⟨505217723804076767025097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694494526955076090800517 505217723804076767025097)
                    ·
                      refine ⟨378913292853057575268823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505217723804076767025097 378913292853057575268823)
                      ·
                        rfl

theorem cell23_737931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4, 2].length) (baseStart_737931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737931 prefixEnd_737931 := by exact prefixLift 737931
  have htrace : WordTrace (prefixWord ++ tailWord_737931) baseStart_737931 baseEnd_737931 := by
    simpa [prefixWord, tailWord_737931, baseEnd_737931] using wordTrace_append hprefix tailTrace_737931
  have hstable : (prefixWord ++ tailWord_737931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737931).length < 2 ^ (prefixWord ++ tailWord_737931).sum := by decide
  have hdescent : baseEnd_737931 < baseStart_737931 := by decide
  rcases family_descends (prefixWord ++ tailWord_737931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737952 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 1, 3, 2]
def baseStart_737952 : Nat := 118140960795 + 737952 * 2 ^ 59
def prefixEnd_737952 : Nat := 4983230072969 + 3 ^ 40 * 737952 * 2
def baseEnd_737952 : Nat := 378924075946801993106227

theorem tailTrace_737952 : CollatzResearch.WordTrace tailWord_737952 prefixEnd_737952 378924075946801993106227 := by
  unfold tailWord_737952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13457660311266705506388055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17943547081688940675184073 13457660311266705506388055)
  ·
    refine ⟨20186490466900058259582083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13457660311266705506388055 20186490466900058259582083)
    ·
      refine ⟨30279735700350087389373125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20186490466900058259582083 30279735700350087389373125)
      ·
        refine ⟨5677450443815641385507461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30279735700350087389373125 5677450443815641385507461)
        ·
          refine ⟨1064521958215432759782649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5677450443815641385507461 1064521958215432759782649)
          ·
            refine ⟨798391468661574569836987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064521958215432759782649 798391468661574569836987)
            ·
              refine ⟨1197587202992361854755481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798391468661574569836987 1197587202992361854755481)
              ·
                refine ⟨898190402244271391066611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197587202992361854755481 898190402244271391066611)
                ·
                  refine ⟨1347285603366407086599917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898190402244271391066611 1347285603366407086599917)
                  ·
                    refine ⟨505232101262402657474969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347285603366407086599917 505232101262402657474969)
                    ·
                      refine ⟨378924075946801993106227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505232101262402657474969 378924075946801993106227)
                      ·
                        rfl

theorem cell23_737952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_737952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737952 prefixEnd_737952 := by exact prefixLift 737952
  have htrace : WordTrace (prefixWord ++ tailWord_737952) baseStart_737952 baseEnd_737952 := by
    simpa [prefixWord, tailWord_737952, baseEnd_737952] using wordTrace_append hprefix tailTrace_737952
  have hstable : (prefixWord ++ tailWord_737952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737952).length < 2 ^ (prefixWord ++ tailWord_737952).sum := by decide
  have hdescent : baseEnd_737952 < baseStart_737952 := by decide
  rcases family_descends (prefixWord ++ tailWord_737952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737965 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_737965 : Nat := 118140960795 + 737965 * 2 ^ 59
def prefixEnd_737965 : Nat := 4983230072969 + 3 ^ 40 * 737965 * 2
def baseEnd_737965 : Nat := 378930751195310442243667

theorem tailTrace_737965 : CollatzResearch.WordTrace tailWord_737965 prefixEnd_737965 378930751195310442243667 := by
  unfold tailWord_737965
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915794771486314232999349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17943863180990876155332899 26915794771486314232999349)
  ·
    refine ⟨2523355759826841959343689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26915794771486314232999349 2523355759826841959343689)
    ·
      refine ⟨1892516819870131469507767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2523355759826841959343689 1892516819870131469507767)
      ·
        refine ⟨2838775229805197204261651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892516819870131469507767 2838775229805197204261651)
        ·
          refine ⟨4258162844707795806392477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838775229805197204261651 4258162844707795806392477)
          ·
            refine ⟨1596811066765423427397179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4258162844707795806392477 1596811066765423427397179)
            ·
              refine ⟨2395216600148135141095769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596811066765423427397179 2395216600148135141095769)
              ·
                refine ⟨1796412450111101355821827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2395216600148135141095769 1796412450111101355821827)
                ·
                  refine ⟨2694618675166652033732741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796412450111101355821827 2694618675166652033732741)
                  ·
                    refine ⟨505241001593747256324889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694618675166652033732741 505241001593747256324889)
                    ·
                      refine ⟨378930751195310442243667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505241001593747256324889 378930751195310442243667)
                      ·
                        rfl

theorem cell23_737965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_737965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737965 prefixEnd_737965 := by exact prefixLift 737965
  have htrace : WordTrace (prefixWord ++ tailWord_737965) baseStart_737965 baseEnd_737965 := by
    simpa [prefixWord, tailWord_737965, baseEnd_737965] using wordTrace_append hprefix tailTrace_737965
  have hstable : (prefixWord ++ tailWord_737965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737965).length < 2 ^ (prefixWord ++ tailWord_737965).sum := by decide
  have hdescent : baseEnd_737965 < baseStart_737965 := by decide
  rcases family_descends (prefixWord ++ tailWord_737965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737969 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 1, 3, 2]
def baseStart_737969 : Nat := 118140960795 + 737969 * 2 ^ 59
def prefixEnd_737969 : Nat := 4983230072969 + 3 ^ 40 * 737969 * 2
def baseEnd_737969 : Nat := 378932805117928426593649

theorem tailTrace_737969 : CollatzResearch.WordTrace tailWord_737969 prefixEnd_737969 378932805117928426593649 := by
  unfold tailWord_737969
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915940663471822916144961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17943960442314548610763307 26915940663471822916144961)
  ·
    refine ⟨20186955497603867187108721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26915940663471822916144961 20186955497603867187108721)
    ·
      refine ⟨15140216623202900390331541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20186955497603867187108721 15140216623202900390331541)
      ·
        refine ⟨709697654212635955796791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15140216623202900390331541 709697654212635955796791)
        ·
          refine ⟨1064546481318953933695187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709697654212635955796791 1064546481318953933695187)
          ·
            refine ⟨1596819721978430900542781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064546481318953933695187 1596819721978430900542781)
            ·
              refine ⟨598807395741911587703543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1596819721978430900542781 598807395741911587703543)
              ·
                refine ⟨898211093612867381555315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598807395741911587703543 898211093612867381555315)
                ·
                  refine ⟨1347316640419301072332973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898211093612867381555315 1347316640419301072332973)
                  ·
                    refine ⟨505243740157237902124865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347316640419301072332973 505243740157237902124865)
                    ·
                      refine ⟨378932805117928426593649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505243740157237902124865 378932805117928426593649)
                      ·
                        rfl

theorem cell23_737969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_737969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737969 prefixEnd_737969 := by exact prefixLift 737969
  have htrace : WordTrace (prefixWord ++ tailWord_737969) baseStart_737969 baseEnd_737969 := by
    simpa [prefixWord, tailWord_737969, baseEnd_737969] using wordTrace_append hprefix tailTrace_737969
  have hstable : (prefixWord ++ tailWord_737969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737969).length < 2 ^ (prefixWord ++ tailWord_737969).sum := by decide
  have hdescent : baseEnd_737969 < baseStart_737969 := by decide
  rcases family_descends (prefixWord ++ tailWord_737969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737982 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_737982 : Nat := 118140960795 + 737982 * 2 ^ 59
def prefixEnd_737982 : Nat := 4983230072969 + 3 ^ 40 * 737982 * 2
def baseEnd_737982 : Nat := 378939480366436875731089

theorem tailTrace_737982 : CollatzResearch.WordTrace tailWord_737982 prefixEnd_737982 378939480366436875731089 := by
  unfold tailWord_737982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364551851553090767046025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17944276541616484090912133 3364551851553090767046025)
  ·
    refine ⟨2523413888664818075284519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3364551851553090767046025 2523413888664818075284519)
    ·
      refine ⟨3785120832997227112926779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523413888664818075284519 3785120832997227112926779)
      ·
        refine ⟨5677681249495840669390169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785120832997227112926779 5677681249495840669390169)
        ·
          refine ⟨4258260937121880502042627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5677681249495840669390169 4258260937121880502042627)
          ·
            refine ⟨6387391405682820753063941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258260937121880502042627 6387391405682820753063941)
            ·
              refine ⟨1197635888565528891199489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6387391405682820753063941 1197635888565528891199489)
              ·
                refine ⟨898226916424146668399617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197635888565528891199489 898226916424146668399617)
                ·
                  refine ⟨673670187318110001299713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 898226916424146668399617 673670187318110001299713)
                  ·
                    refine ⟨505252640488582500974785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673670187318110001299713 505252640488582500974785)
                    ·
                      refine ⟨378939480366436875731089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505252640488582500974785 378939480366436875731089)
                      ·
                        rfl

theorem cell23_737982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_737982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737982 prefixEnd_737982 := by exact prefixLift 737982
  have htrace : WordTrace (prefixWord ++ tailWord_737982) baseStart_737982 baseEnd_737982 := by
    simpa [prefixWord, tailWord_737982, baseEnd_737982] using wordTrace_append hprefix tailTrace_737982
  have hstable : (prefixWord ++ tailWord_737982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737982).length < 2 ^ (prefixWord ++ tailWord_737982).sum := by decide
  have hdescent : baseEnd_737982 < baseStart_737982 := by decide
  rcases family_descends (prefixWord ++ tailWord_737982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737998 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_737998 : Nat := 118140960795 + 737998 * 2 ^ 59
def prefixEnd_737998 : Nat := 4983230072969 + 3 ^ 40 * 737998 * 2
def baseEnd_737998 : Nat := 378947696056908813131015

theorem tailTrace_737998 : CollatzResearch.WordTrace tailWord_737998 prefixEnd_737998 378947696056908813131015 := by
  unfold tailWord_737998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364624797545845108618831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17944665586911173912633765 3364624797545845108618831)
  ·
    refine ⟨5046937196318767662928247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3364624797545845108618831 5046937196318767662928247)
    ·
      refine ⟨7570405794478151494392371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5046937196318767662928247 7570405794478151494392371)
      ·
        refine ⟨11355608691717227241588557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7570405794478151494392371 11355608691717227241588557)
        ·
          refine ⟨4258353259393960215595709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11355608691717227241588557 4258353259393960215595709)
          ·
            refine ⟨1596882472272735080848391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4258353259393960215595709 1596882472272735080848391)
            ·
              refine ⟨2395323708409102621272587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596882472272735080848391 2395323708409102621272587)
              ·
                refine ⟨3592985562613653931908881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395323708409102621272587 3592985562613653931908881)
                ·
                  refine ⟨2694739171960240448931661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3592985562613653931908881 2694739171960240448931661)
                  ·
                    refine ⟨1010527189485090168349373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694739171960240448931661 1010527189485090168349373)
                    ·
                      refine ⟨378947696056908813131015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1010527189485090168349373 378947696056908813131015)
                      ·
                        rfl

theorem cell23_737998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_737998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_737998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_737998 prefixEnd_737998 := by exact prefixLift 737998
  have htrace : WordTrace (prefixWord ++ tailWord_737998) baseStart_737998 baseEnd_737998 := by
    simpa [prefixWord, tailWord_737998, baseEnd_737998] using wordTrace_append hprefix tailTrace_737998
  have hstable : (prefixWord ++ tailWord_737998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737998).length < 2 ^ (prefixWord ++ tailWord_737998).sum := by decide
  have hdescent : baseEnd_737998 < baseStart_737998 := by decide
  rcases family_descends (prefixWord ++ tailWord_737998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738038 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_738038 : Nat := 118140960795 + 738038 * 2 ^ 59
def prefixEnd_738038 : Nat := 4983230072969 + 3 ^ 40 * 738038 * 2
def baseEnd_738038 : Nat := 378968235283088656630831

theorem tailTrace_738038 : CollatzResearch.WordTrace tailWord_738038 prefixEnd_738038 378968235283088656630831 := by
  unfold tailWord_738038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682403581263865481275423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17945638200147898466937845 1682403581263865481275423)
  ·
    refine ⟨2523605371895798221913135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682403581263865481275423 2523605371895798221913135)
    ·
      refine ⟨3785408057843697332869703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523605371895798221913135 3785408057843697332869703)
      ·
        refine ⟨5678112086765545999304555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785408057843697332869703 5678112086765545999304555)
        ·
          refine ⟨8517168130148318998956833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678112086765545999304555 8517168130148318998956833)
          ·
            refine ⟨6387876097611239249217625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8517168130148318998956833 6387876097611239249217625)
            ·
              refine ⟨4790907073208429436913219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6387876097611239249217625 4790907073208429436913219)
              ·
                refine ⟨7186360609812644155369829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790907073208429436913219 7186360609812644155369829)
                ·
                  refine ⟨1347442614339870779131843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7186360609812644155369829 1347442614339870779131843)
                  ·
                    refine ⟨2021163921509806168697765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1347442614339870779131843 2021163921509806168697765)
                    ·
                      refine ⟨378968235283088656630831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2021163921509806168697765 378968235283088656630831)
                      ·
                        rfl

theorem cell23_738038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_738038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738038 prefixEnd_738038 := by exact prefixLift 738038
  have htrace : WordTrace (prefixWord ++ tailWord_738038) baseStart_738038 baseEnd_738038 := by
    simpa [prefixWord, tailWord_738038, baseEnd_738038] using wordTrace_append hprefix tailTrace_738038
  have hstable : (prefixWord ++ tailWord_738038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738038).length < 2 ^ (prefixWord ++ tailWord_738038).sum := by decide
  have hdescent : baseEnd_738038 < baseStart_738038 := by decide
  rcases family_descends (prefixWord ++ tailWord_738038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738055 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_738055 : Nat := 118140960795 + 738055 * 2 ^ 59
def prefixEnd_738055 : Nat := 4983230072969 + 3 ^ 40 * 738055 * 2
def baseEnd_738055 : Nat := 378976964454215090118253

theorem tailTrace_738055 : CollatzResearch.WordTrace tailWord_738055 prefixEnd_738055 378976964454215090118253 := by
  unfold tailWord_738055
  simp only [CollatzResearch.WordTrace]
  refine ⟨26919077341160259603775619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17946051560773506402517079 26919077341160259603775619)
  ·
    refine ⟨40378616011740389405663429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26919077341160259603775619 40378616011740389405663429)
    ·
      refine ⟨7570990502201323013561893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40378616011740389405663429 7570990502201323013561893)
      ·
        refine ⟨1419560719162748065042855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7570990502201323013561893 1419560719162748065042855)
        ·
          refine ⟨2129341078744122097564283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419560719162748065042855 2129341078744122097564283)
          ·
            refine ⟨3194011618116183146346425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129341078744122097564283 3194011618116183146346425)
            ·
              refine ⟨2395508713587137359759819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3194011618116183146346425 2395508713587137359759819)
              ·
                refine ⟨3593263070380706039639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395508713587137359759819 3593263070380706039639729)
                ·
                  refine ⟨2694947302785529529729797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593263070380706039639729 2694947302785529529729797)
                  ·
                    refine ⟨505302619272286786824337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694947302785529529729797 505302619272286786824337)
                    ·
                      refine ⟨378976964454215090118253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505302619272286786824337 378976964454215090118253)
                      ·
                        rfl

theorem cell23_738055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_738055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738055 prefixEnd_738055 := by exact prefixLift 738055
  have htrace : WordTrace (prefixWord ++ tailWord_738055) baseStart_738055 baseEnd_738055 := by
    simpa [prefixWord, tailWord_738055, baseEnd_738055] using wordTrace_append hprefix tailTrace_738055
  have hstable : (prefixWord ++ tailWord_738055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738055).length < 2 ^ (prefixWord ++ tailWord_738055).sum := by decide
  have hdescent : baseEnd_738055 < baseStart_738055 := by decide
  rcases family_descends (prefixWord ++ tailWord_738055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738082 : List Nat := [3, 3, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_738082 : Nat := 118140960795 + 738082 * 2 ^ 59
def prefixEnd_738082 : Nat := 4983230072969 + 3 ^ 40 * 738082 * 2
def baseEnd_738082 : Nat := 126330276143962161493543

theorem tailTrace_738082 : CollatzResearch.WordTrace tailWord_738082 prefixEnd_738082 126330276143962161493543 := by
  unfold tailWord_738082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6730015528015610803752125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17946708074708295476672333 6730015528015610803752125)
  ·
    refine ⟨2523755823005854051407047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6730015528015610803752125 2523755823005854051407047)
    ·
      refine ⟨3785633734508781077110571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523755823005854051407047 3785633734508781077110571)
      ·
        refine ⟨5678450601763171615665857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785633734508781077110571 5678450601763171615665857)
        ·
          refine ⟨4258837951322378711749393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5678450601763171615665857 4258837951322378711749393)
          ·
            refine ⟨3194128463491784033812045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4258837951322378711749393 3194128463491784033812045)
            ·
              refine ⟨1197798173809419012679517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3194128463491784033812045 1197798173809419012679517)
              ·
                refine ⟨449174315178532129754819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1197798173809419012679517 449174315178532129754819)
                ·
                  refine ⟨673761472767798194632229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449174315178532129754819 673761472767798194632229)
                  ·
                    refine ⟨126330276143962161493543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 673761472767798194632229 126330276143962161493543)
                    ·
                      rfl

theorem cell23_738082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_738082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738082 prefixEnd_738082 := by exact prefixLift 738082
  have htrace : WordTrace (prefixWord ++ tailWord_738082) baseStart_738082 baseEnd_738082 := by
    simpa [prefixWord, tailWord_738082, baseEnd_738082] using wordTrace_append hprefix tailTrace_738082
  have hstable : (prefixWord ++ tailWord_738082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738082).length < 2 ^ (prefixWord ++ tailWord_738082).sum := by decide
  have hdescent : baseEnd_738082 < baseStart_738082 := by decide
  rcases family_descends (prefixWord ++ tailWord_738082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738128 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 2, 6, 2]
def baseStart_738128 : Nat := 118140960795 + 738128 * 2 ^ 59
def prefixEnd_738128 : Nat := 4983230072969 + 3 ^ 40 * 738128 * 2
def baseEnd_738128 : Nat := 379014448541993304505417

theorem tailTrace_738128 : CollatzResearch.WordTrace tailWord_738128 prefixEnd_738128 379014448541993304505417 := by
  unfold tailWord_738128
  simp only [CollatzResearch.WordTrace]
  refine ⟨13460869934947896535591519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17947826579930528714122025 13460869934947896535591519)
  ·
    refine ⟨20191304902421844803387279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13460869934947896535591519 20191304902421844803387279)
    ·
      refine ⟨30286957353632767205080919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20191304902421844803387279 30286957353632767205080919)
      ·
        refine ⟨45430436030449150807621379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30286957353632767205080919 45430436030449150807621379)
        ·
          refine ⟨68145654045673726211432069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45430436030449150807621379 68145654045673726211432069)
          ·
            refine ⟨12777310133563823664643513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68145654045673726211432069 12777310133563823664643513)
            ·
              refine ⟨9582982600172867748482635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12777310133563823664643513 9582982600172867748482635)
              ·
                refine ⟨14374473900259301622723953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9582982600172867748482635 14374473900259301622723953)
                ·
                  refine ⟨10780855425194476217042965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14374473900259301622723953 10780855425194476217042965)
                  ·
                    refine ⟨505352598055991072673889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10780855425194476217042965 505352598055991072673889)
                    ·
                      refine ⟨379014448541993304505417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505352598055991072673889 379014448541993304505417)
                      ·
                        rfl

theorem cell23_738128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 6, 2].length) (baseStart_738128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738128 prefixEnd_738128 := by exact prefixLift 738128
  have htrace : WordTrace (prefixWord ++ tailWord_738128) baseStart_738128 baseEnd_738128 := by
    simpa [prefixWord, tailWord_738128, baseEnd_738128] using wordTrace_append hprefix tailTrace_738128
  have hstable : (prefixWord ++ tailWord_738128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738128).length < 2 ^ (prefixWord ++ tailWord_738128).sum := by decide
  have hdescent : baseEnd_738128 < baseStart_738128 := by decide
  rcases family_descends (prefixWord ++ tailWord_738128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738131 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5]
def baseStart_738131 : Nat := 118140960795 + 738131 * 2 ^ 59
def prefixEnd_738131 : Nat := 4983230072969 + 3 ^ 40 * 738131 * 2
def baseEnd_738131 : Nat := 379015988983956792767903

theorem tailTrace_738131 : CollatzResearch.WordTrace tailWord_738131 prefixEnd_738131 379015988983956792767903 := by
  unfold tailWord_738131
  simp only [CollatzResearch.WordTrace]
  refine ⟨26921849288884924583542247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17947899525923283055694831 26921849288884924583542247)
  ·
    refine ⟨40382773933327386875313371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26921849288884924583542247 40382773933327386875313371)
    ·
      refine ⟨60574160899991080312970057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40382773933327386875313371 60574160899991080312970057)
      ·
        refine ⟨45430620674993310234727543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60574160899991080312970057 45430620674993310234727543)
        ·
          refine ⟨68145931012489965352091315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45430620674993310234727543 68145931012489965352091315)
          ·
            refine ⟨102218896518734948028136973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68145931012489965352091315 102218896518734948028136973)
            ·
              refine ⟨38332086194525605510551365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102218896518734948028136973 38332086194525605510551365)
              ·
                refine ⟨7187266161473551033228381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38332086194525605510551365 7187266161473551033228381)
                ·
                  refine ⟨2695224810552581637460643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7187266161473551033228381 2695224810552581637460643)
                  ·
                    refine ⟨4042837215828872456190965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695224810552581637460643 4042837215828872456190965)
                    ·
                      refine ⟨379015988983956792767903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4042837215828872456190965 379015988983956792767903)
                      ·
                        rfl

theorem cell23_738131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_738131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738131 prefixEnd_738131 := by exact prefixLift 738131
  have htrace : WordTrace (prefixWord ++ tailWord_738131) baseStart_738131 baseEnd_738131 := by
    simpa [prefixWord, tailWord_738131, baseEnd_738131] using wordTrace_append hprefix tailTrace_738131
  have hstable : (prefixWord ++ tailWord_738131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738131).length < 2 ^ (prefixWord ++ tailWord_738131).sum := by decide
  have hdescent : baseEnd_738131 < baseStart_738131 := by decide
  rcases family_descends (prefixWord ++ tailWord_738131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738138 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_738138 : Nat := 118140960795 + 738138 * 2 ^ 59
def prefixEnd_738138 : Nat := 4983230072969 + 3 ^ 40 * 738138 * 2
def baseEnd_738138 : Nat := 126339861116179421793457

theorem tailTrace_738138 : CollatzResearch.WordTrace tailWord_738138 prefixEnd_738138 126339861116179421793457 := by
  unfold tailWord_738138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6730526149964891194761767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17948069733239709852698045 6730526149964891194761767)
  ·
    refine ⟨10095789224947336792142651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6730526149964891194761767 10095789224947336792142651)
    ·
      refine ⟨15143683837421005188213977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10095789224947336792142651 15143683837421005188213977)
      ·
        refine ⟨11357762878065753891160483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15143683837421005188213977 11357762878065753891160483)
        ·
          refine ⟨17036644317098630836740725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11357762878065753891160483 17036644317098630836740725)
          ·
            refine ⟨1597185404727996640944443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17036644317098630836740725 1597185404727996640944443)
            ·
              refine ⟨2395778107091994961416665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597185404727996640944443 2395778107091994961416665)
              ·
                refine ⟨1796833580318996221062499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2395778107091994961416665 1796833580318996221062499)
                ·
                  refine ⟨2695250370478494331593749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796833580318996221062499 2695250370478494331593749)
                  ·
                    refine ⟨126339861116179421793457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2695250370478494331593749 126339861116179421793457)
                    ·
                      rfl

theorem cell23_738138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_738138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738138 prefixEnd_738138 := by exact prefixLift 738138
  have htrace : WordTrace (prefixWord ++ tailWord_738138) baseStart_738138 baseEnd_738138 := by
    simpa [prefixWord, tailWord_738138, baseEnd_738138] using wordTrace_append hprefix tailTrace_738138
  have hstable : (prefixWord ++ tailWord_738138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738138).length < 2 ^ (prefixWord ++ tailWord_738138).sum := by decide
  have hdescent : baseEnd_738138 < baseStart_738138 := by decide
  rcases family_descends (prefixWord ++ tailWord_738138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738145 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_738145 : Nat := 118140960795 + 738145 * 2 ^ 59
def prefixEnd_738145 : Nat := 4983230072969 + 3 ^ 40 * 738145 * 2
def baseEnd_738145 : Nat := 379023177713119737992839

theorem tailTrace_738145 : CollatzResearch.WordTrace tailWord_738145 prefixEnd_738145 379023177713119737992839 := by
  unfold tailWord_738145
  simp only [CollatzResearch.WordTrace]
  refine ⟨26922359910834204974551889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17948239940556136649701259 26922359910834204974551889)
  ·
    refine ⟨20191769933125653730913917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26922359910834204974551889 20191769933125653730913917)
    ·
      refine ⟨7571913724922120149092719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20191769933125653730913917 7571913724922120149092719)
      ·
        refine ⟨11357870587383180223639079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7571913724922120149092719 11357870587383180223639079)
        ·
          refine ⟨17036805881074770335458619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11357870587383180223639079 17036805881074770335458619)
          ·
            refine ⟨25555208821612155503187929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17036805881074770335458619 25555208821612155503187929)
            ·
              refine ⟨19166406616209116627390947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25555208821612155503187929 19166406616209116627390947)
              ·
                refine ⟨28749609924313674941086421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19166406616209116627390947 28749609924313674941086421)
                ·
                  refine ⟨673818982601101756431713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 28749609924313674941086421 673818982601101756431713)
                  ·
                    refine ⟨505364236950826317323785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673818982601101756431713 505364236950826317323785)
                    ·
                      refine ⟨379023177713119737992839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505364236950826317323785 379023177713119737992839)
                      ·
                        rfl

theorem cell23_738145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_738145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738145 prefixEnd_738145 := by exact prefixLift 738145
  have htrace : WordTrace (prefixWord ++ tailWord_738145) baseStart_738145 baseEnd_738145 := by
    simpa [prefixWord, tailWord_738145, baseEnd_738145] using wordTrace_append hprefix tailTrace_738145
  have hstable : (prefixWord ++ tailWord_738145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738145).length < 2 ^ (prefixWord ++ tailWord_738145).sum := by decide
  have hdescent : baseEnd_738145 < baseStart_738145 := by decide
  rcases family_descends (prefixWord ++ tailWord_738145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738151 : List Nat := [1, 1, 5, 1, 2, 13]
def baseStart_738151 : Nat := 118140960795 + 738151 * 2 ^ 59
def prefixEnd_738151 : Nat := 4983230072969 + 3 ^ 40 * 738151 * 2
def baseEnd_738151 : Nat := 1559778841963155203777

theorem tailTrace_738151 : CollatzResearch.WordTrace tailWord_738151 prefixEnd_738151 1559778841963155203777 := by
  unfold tailWord_738151
  simp only [CollatzResearch.WordTrace]
  refine ⟨26922578748812467999270307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17948385832541645332846871 26922578748812467999270307)
  ·
    refine ⟨40383868123218701998905461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26922578748812467999270307 40383868123218701998905461)
    ·
      refine ⟨3785987636551753312397387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40383868123218701998905461 3785987636551753312397387)
      ·
        refine ⟨5678981454827629968596081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785987636551753312397387 5678981454827629968596081)
        ·
          refine ⟨4259236091120722476447061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5678981454827629968596081 4259236091120722476447061)
          ·
            refine ⟨1559778841963155203777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 4259236091120722476447061 1559778841963155203777)
            ·
              rfl

theorem cell23_738151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 13].length) (baseStart_738151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738151 prefixEnd_738151 := by exact prefixLift 738151
  have htrace : WordTrace (prefixWord ++ tailWord_738151) baseStart_738151 baseEnd_738151 := by
    simpa [prefixWord, tailWord_738151, baseEnd_738151] using wordTrace_append hprefix tailTrace_738151
  have hstable : (prefixWord ++ tailWord_738151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738151).length < 2 ^ (prefixWord ++ tailWord_738151).sum := by decide
  have hdescent : baseEnd_738151 < baseStart_738151 := by decide
  rcases family_descends (prefixWord ++ tailWord_738151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738165 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_738165 : Nat := 118140960795 + 738165 * 2 ^ 59
def prefixEnd_738165 : Nat := 4983230072969 + 3 ^ 40 * 738165 * 2
def baseEnd_738165 : Nat := 379033447326209659742747

theorem tailTrace_738165 : CollatzResearch.WordTrace tailWord_738165 prefixEnd_738165 379033447326209659742747 := by
  unfold tailWord_738165
  simp only [CollatzResearch.WordTrace]
  refine ⟨26923089370761748390279949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17948726247174498926853299 26923089370761748390279949)
  ·
    refine ⟨10096158514035655646354981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26923089370761748390279949 10096158514035655646354981)
    ·
      refine ⟨1893029721381685433691559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10096158514035655646354981 1893029721381685433691559)
      ·
        refine ⟨2839544582072528150537339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893029721381685433691559 2839544582072528150537339)
        ·
          refine ⟨4259316873108792225806009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839544582072528150537339 4259316873108792225806009)
          ·
            refine ⟨3194487654831594169354507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4259316873108792225806009 3194487654831594169354507)
            ·
              refine ⟨4791731482247391254031761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194487654831594169354507 4791731482247391254031761)
              ·
                refine ⟨3593798611685543440523821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791731482247391254031761 3593798611685543440523821)
                ·
                  refine ⟨1347674479382078790196433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3593798611685543440523821 1347674479382078790196433)
                  ·
                    refine ⟨1010755859536559092647325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1347674479382078790196433 1010755859536559092647325)
                    ·
                      refine ⟨379033447326209659742747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1010755859536559092647325 379033447326209659742747)
                      ·
                        rfl

theorem cell23_738165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_738165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738165 prefixEnd_738165 := by exact prefixLift 738165
  have htrace : WordTrace (prefixWord ++ tailWord_738165) baseStart_738165 baseEnd_738165 := by
    simpa [prefixWord, tailWord_738165, baseEnd_738165] using wordTrace_append hprefix tailTrace_738165
  have hstable : (prefixWord ++ tailWord_738165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738165).length < 2 ^ (prefixWord ++ tailWord_738165).sum := by decide
  have hdescent : baseEnd_738165 < baseStart_738165 := by decide
  rcases family_descends (prefixWord ++ tailWord_738165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738171 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6]
def baseStart_738171 : Nat := 118140960795 + 738171 * 2 ^ 59
def prefixEnd_738171 : Nat := 4983230072969 + 3 ^ 40 * 738171 * 2
def baseEnd_738171 : Nat := 379036528210136636267719

theorem tailTrace_738171 : CollatzResearch.WordTrace tailWord_738171 prefixEnd_738171 379036528210136636267719 := by
  unfold tailWord_738171
  simp only [CollatzResearch.WordTrace]
  refine ⟨26923308208740011414998367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17948872139160007609998911 26923308208740011414998367)
  ·
    refine ⟨40384962313110017122497551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26923308208740011414998367 40384962313110017122497551)
    ·
      refine ⟨60577443469665025683746327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40384962313110017122497551 60577443469665025683746327)
      ·
        refine ⟨90866165204497538525619491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60577443469665025683746327 90866165204497538525619491)
        ·
          refine ⟨136299247806746307788429237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90866165204497538525619491 136299247806746307788429237)
          ·
            refine ⟨12778054481882466355165241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136299247806746307788429237 12778054481882466355165241)
            ·
              refine ⟨9583540861411849766373931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12778054481882466355165241 9583540861411849766373931)
              ·
                refine ⟨14375311292117774649560897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9583540861411849766373931 14375311292117774649560897)
                ·
                  refine ⟨10781483469088330987170673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375311292117774649560897 10781483469088330987170673)
                  ·
                    refine ⟨8086112601816248240378005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10781483469088330987170673 8086112601816248240378005)
                    ·
                      refine ⟨379036528210136636267719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8086112601816248240378005 379036528210136636267719)
                      ·
                        rfl

theorem cell23_738171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_738171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738171 prefixEnd_738171 := by exact prefixLift 738171
  have htrace : WordTrace (prefixWord ++ tailWord_738171) baseStart_738171 baseEnd_738171 := by
    simpa [prefixWord, tailWord_738171, baseEnd_738171] using wordTrace_append hprefix tailTrace_738171
  have hstable : (prefixWord ++ tailWord_738171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738171).length < 2 ^ (prefixWord ++ tailWord_738171).sum := by decide
  have hdescent : baseEnd_738171 < baseStart_738171 := by decide
  rcases family_descends (prefixWord ++ tailWord_738171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738196 : List Nat := [2, 4, 2, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_738196 : Nat := 118140960795 + 738196 * 2 ^ 59
def prefixEnd_738196 : Nat := 4983230072969 + 3 ^ 40 * 738196 * 2
def baseEnd_738196 : Nat := 379049365226499038455105

theorem tailTrace_738196 : CollatzResearch.WordTrace tailWord_738196 prefixEnd_738196 379049365226499038455105 := by
  unfold tailWord_738196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462110016824720342329221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17949480022432960456438961 13462110016824720342329221)
  ·
    refine ⟨2524145628154635064186729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13462110016824720342329221 2524145628154635064186729)
    ·
      refine ⟨1893109221115976298140047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2524145628154635064186729 1893109221115976298140047)
      ·
        refine ⟨2839663831673964447210071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893109221115976298140047 2839663831673964447210071)
        ·
          refine ⟨4259495747510946670815107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839663831673964447210071 4259495747510946670815107)
          ·
            refine ⟨6389243621266420006222661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259495747510946670815107 6389243621266420006222661)
            ·
              refine ⟨1197983178987453751166749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6389243621266420006222661 1197983178987453751166749)
              ·
                refine ⟨449243692120295156687531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1197983178987453751166749 449243692120295156687531)
                ·
                  refine ⟨673865538180442735031297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449243692120295156687531 673865538180442735031297)
                  ·
                    refine ⟨505399153635332051273473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673865538180442735031297 505399153635332051273473)
                    ·
                      refine ⟨379049365226499038455105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505399153635332051273473 379049365226499038455105)
                      ·
                        rfl

theorem cell23_738196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_738196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738196 prefixEnd_738196 := by exact prefixLift 738196
  have htrace : WordTrace (prefixWord ++ tailWord_738196) baseStart_738196 baseEnd_738196 := by
    simpa [prefixWord, tailWord_738196, baseEnd_738196] using wordTrace_append hprefix tailTrace_738196
  have hstable : (prefixWord ++ tailWord_738196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738196).length < 2 ^ (prefixWord ++ tailWord_738196).sum := by decide
  have hdescent : baseEnd_738196 < baseStart_738196 := by decide
  rcases family_descends (prefixWord ++ tailWord_738196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738229 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_738229 : Nat := 118140960795 + 738229 * 2 ^ 59
def prefixEnd_738229 : Nat := 4983230072969 + 3 ^ 40 * 738229 * 2
def baseEnd_738229 : Nat := 379066310088097409342453

theorem tailTrace_738229 : CollatzResearch.WordTrace tailWord_738229 prefixEnd_738229 379066310088097409342453 := by
  unfold tailWord_738229
  simp only [CollatzResearch.WordTrace]
  refine ⟨26925423642529887320609741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17950282428353258213739827 26925423642529887320609741)
  ·
    refine ⟨10097033865948707745228653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26925423642529887320609741 10097033865948707745228653)
    ·
      refine ⟨3786387699730765404460745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10097033865948707745228653 3786387699730765404460745)
      ·
        refine ⟨2839790774798074053345559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3786387699730765404460745 2839790774798074053345559)
        ·
          refine ⟨4259686162197111080018339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839790774798074053345559 4259686162197111080018339)
          ·
            refine ⟨6389529243295666620027509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259686162197111080018339 6389529243295666620027509)
            ·
              refine ⟨599018366558968745627579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6389529243295666620027509 599018366558968745627579)
              ·
                refine ⟨898527549838453118441369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599018366558968745627579 898527549838453118441369)
                ·
                  refine ⟨673895662378839838831027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 898527549838453118441369 673895662378839838831027)
                  ·
                    refine ⟨1010843493568259758246541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 673895662378839838831027 1010843493568259758246541)
                    ·
                      refine ⟨379066310088097409342453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1010843493568259758246541 379066310088097409342453)
                      ·
                        rfl

theorem cell23_738229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_738229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738229 prefixEnd_738229 := by exact prefixLift 738229
  have htrace : WordTrace (prefixWord ++ tailWord_738229) baseStart_738229 baseEnd_738229 := by
    simpa [prefixWord, tailWord_738229, baseEnd_738229] using wordTrace_append hprefix tailTrace_738229
  have hstable : (prefixWord ++ tailWord_738229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738229).length < 2 ^ (prefixWord ++ tailWord_738229).sum := by decide
  have hdescent : baseEnd_738229 < baseStart_738229 := by decide
  rcases family_descends (prefixWord ++ tailWord_738229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738252 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 6, 2, 2]
def baseStart_738252 : Nat := 118140960795 + 738252 * 2 ^ 59
def prefixEnd_738252 : Nat := 4983230072969 + 3 ^ 40 * 738252 * 2
def baseEnd_738252 : Nat := 379078120143150819354847

theorem tailTrace_738252 : CollatzResearch.WordTrace tailWord_738252 prefixEnd_738252 379078120143150819354847 := by
  unfold tailWord_738252
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463131260723281124348505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17950841680964374832464673 13463131260723281124348505)
  ·
    refine ⟨10097348445542460843261379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13463131260723281124348505 10097348445542460843261379)
    ·
      refine ⟨15146022668313691264892069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10097348445542460843261379 15146022668313691264892069)
      ·
        refine ⟨2839879250308817112167263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15146022668313691264892069 2839879250308817112167263)
        ·
          refine ⟨4259818875463225668250895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839879250308817112167263 4259818875463225668250895)
          ·
            refine ⟨6389728313194838502376343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259818875463225668250895 6389728313194838502376343)
            ·
              refine ⟨9584592469792257753564515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389728313194838502376343 9584592469792257753564515)
              ·
                refine ⟨14376888704688386630346773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584592469792257753564515 14376888704688386630346773)
                ·
                  refine ⟨673916658032268123297505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14376888704688386630346773 673916658032268123297505)
                  ·
                    refine ⟨505437493524201092473129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673916658032268123297505 505437493524201092473129)
                    ·
                      refine ⟨379078120143150819354847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505437493524201092473129 379078120143150819354847)
                      ·
                        rfl

theorem cell23_738252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_738252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738252 prefixEnd_738252 := by exact prefixLift 738252
  have htrace : WordTrace (prefixWord ++ tailWord_738252) baseStart_738252 baseEnd_738252 := by
    simpa [prefixWord, tailWord_738252, baseEnd_738252] using wordTrace_append hprefix tailTrace_738252
  have hstable : (prefixWord ++ tailWord_738252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738252).length < 2 ^ (prefixWord ++ tailWord_738252).sum := by decide
  have hdescent : baseEnd_738252 < baseStart_738252 := by decide
  rcases family_descends (prefixWord ++ tailWord_738252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738269 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_738269 : Nat := 118140960795 + 738269 * 2 ^ 59
def prefixEnd_738269 : Nat := 4983230072969 + 3 ^ 40 * 738269 * 2
def baseEnd_738269 : Nat := 379086849314277252842269

theorem tailTrace_738269 : CollatzResearch.WordTrace tailWord_738269 prefixEnd_738269 379086849314277252842269 := by
  unfold tailWord_738269
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926882562384974152065861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17951255041589982768043907 26926882562384974152065861)
  ·
    refine ⟨5048790480447182653512349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26926882562384974152065861 5048790480447182653512349)
    ·
      refine ⟨1893296430167693495067131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5048790480447182653512349 1893296430167693495067131)
      ·
        refine ⟨2839944645251540242600697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893296430167693495067131 2839944645251540242600697)
        ·
          refine ⟨2129958483938655181950523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2839944645251540242600697 2129958483938655181950523)
          ·
            refine ⟨3194937725907982772925785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129958483938655181950523 3194937725907982772925785)
            ·
              refine ⟨2396203294430987079694339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3194937725907982772925785 2396203294430987079694339)
              ·
                refine ⟨3594304941646480619541509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396203294430987079694339 3594304941646480619541509)
                ·
                  refine ⟨673932176558715116164033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3594304941646480619541509 673932176558715116164033)
                  ·
                    refine ⟨505449132419036337123025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673932176558715116164033 505449132419036337123025)
                    ·
                      refine ⟨379086849314277252842269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505449132419036337123025 379086849314277252842269)
                      ·
                        rfl

theorem cell23_738269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_738269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738269 prefixEnd_738269 := by exact prefixLift 738269
  have htrace : WordTrace (prefixWord ++ tailWord_738269) baseStart_738269 baseEnd_738269 := by
    simpa [prefixWord, tailWord_738269, baseEnd_738269] using wordTrace_append hprefix tailTrace_738269
  have hstable : (prefixWord ++ tailWord_738269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738269).length < 2 ^ (prefixWord ++ tailWord_738269).sum := by decide
  have hdescent : baseEnd_738269 < baseStart_738269 := by decide
  rcases family_descends (prefixWord ++ tailWord_738269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738286 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_738286 : Nat := 118140960795 + 738286 * 2 ^ 59
def prefixEnd_738286 : Nat := 4983230072969 + 3 ^ 40 * 738286 * 2
def baseEnd_738286 : Nat := 379095578485403686329691

theorem tailTrace_738286 : CollatzResearch.WordTrace tailWord_738286 prefixEnd_738286 379095578485403686329691 := by
  unfold tailWord_738286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365937825415423256929339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17951668402215590703623141 3365937825415423256929339)
  ·
    refine ⟨5048906738123134885394009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3365937825415423256929339 5048906738123134885394009)
    ·
      refine ⟨3786680053592351164045507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5048906738123134885394009 3786680053592351164045507)
      ·
        refine ⟨5680020080388526746068261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786680053592351164045507 5680020080388526746068261)
        ·
          refine ⟨1065003765072848764887799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5680020080388526746068261 1065003765072848764887799)
          ·
            refine ⟨1597505647609273147331699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065003765072848764887799 1597505647609273147331699)
            ·
              refine ⟨2396258471413909720997549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597505647609273147331699 2396258471413909720997549)
              ·
                refine ⟨898596926780216145374081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396258471413909720997549 898596926780216145374081)
                ·
                  refine ⟨673947695085162109030561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 898596926780216145374081 673947695085162109030561)
                  ·
                    refine ⟨505460771313871581772921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673947695085162109030561 505460771313871581772921)
                    ·
                      refine ⟨379095578485403686329691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505460771313871581772921 379095578485403686329691)
                      ·
                        rfl

theorem cell23_738286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_738286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738286 prefixEnd_738286 := by exact prefixLift 738286
  have htrace : WordTrace (prefixWord ++ tailWord_738286) baseStart_738286 baseEnd_738286 := by
    simpa [prefixWord, tailWord_738286, baseEnd_738286] using wordTrace_append hprefix tailTrace_738286
  have hstable : (prefixWord ++ tailWord_738286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738286).length < 2 ^ (prefixWord ++ tailWord_738286).sum := by decide
  have hdescent : baseEnd_738286 < baseStart_738286 := by decide
  rcases family_descends (prefixWord ++ tailWord_738286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738288 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 6, 5]
def baseStart_738288 : Nat := 118140960795 + 738288 * 2 ^ 59
def prefixEnd_738288 : Nat := 4983230072969 + 3 ^ 40 * 738288 * 2
def baseEnd_738288 : Nat := 126365535148904226168227

theorem tailTrace_738288 : CollatzResearch.WordTrace tailWord_738288 prefixEnd_738288 126365535148904226168227 := by
  unfold tailWord_738288
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463787774658070198503759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17951717032877426931338345 13463787774658070198503759)
  ·
    refine ⟨20195681661987105297755639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13463787774658070198503759 20195681661987105297755639)
    ·
      refine ⟨30293522492980657946633459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20195681661987105297755639 30293522492980657946633459)
      ·
        refine ⟨45440283739470986919950189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30293522492980657946633459 45440283739470986919950189)
        ·
          refine ⟨17040106402301620094981321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45440283739470986919950189 17040106402301620094981321)
          ·
            refine ⟨12780079801726215071235991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17040106402301620094981321 12780079801726215071235991)
            ·
              refine ⟨19170119702589322606853987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12780079801726215071235991 19170119702589322606853987)
              ·
                refine ⟨28755179553883983910280981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19170119702589322606853987 28755179553883983910280981)
                ·
                  refine ⟨1347899041588311745794421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28755179553883983910280981 1347899041588311745794421)
                  ·
                    refine ⟨126365535148904226168227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1347899041588311745794421 126365535148904226168227)
                    ·
                      rfl

theorem cell23_738288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_738288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738288 prefixEnd_738288 := by exact prefixLift 738288
  have htrace : WordTrace (prefixWord ++ tailWord_738288) baseStart_738288 baseEnd_738288 := by
    simpa [prefixWord, tailWord_738288, baseEnd_738288] using wordTrace_append hprefix tailTrace_738288
  have hstable : (prefixWord ++ tailWord_738288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738288).length < 2 ^ (prefixWord ++ tailWord_738288).sum := by decide
  have hdescent : baseEnd_738288 < baseStart_738288 := by decide
  rcases family_descends (prefixWord ++ tailWord_738288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738305 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 2, 5]
def baseStart_738305 : Nat := 118140960795 + 738305 * 2 ^ 59
def prefixEnd_738305 : Nat := 4983230072969 + 3 ^ 40 * 738305 * 2
def baseEnd_738305 : Nat := 126368444872613037330701

theorem tailTrace_738305 : CollatzResearch.WordTrace tailWord_738305 prefixEnd_738305 126368444872613037330701 := by
  unfold tailWord_738305
  simp only [CollatzResearch.WordTrace]
  refine ⟨26928195590254552300376369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17952130393503034866917579 26928195590254552300376369)
  ·
    refine ⟨20196146692690914225282277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26928195590254552300376369 20196146692690914225282277)
    ·
      refine ⟨3786777504879546417240427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20196146692690914225282277 3786777504879546417240427)
      ·
        refine ⟨5680166257319319625860641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786777504879546417240427 5680166257319319625860641)
        ·
          refine ⟨4260124692989489719395481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5680166257319319625860641 4260124692989489719395481)
          ·
            refine ⟨3195093519742117289546611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4260124692989489719395481 3195093519742117289546611)
            ·
              refine ⟨4792640279613175934319917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195093519742117289546611 4792640279613175934319917)
              ·
                refine ⟨1797240104854940975369969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4792640279613175934319917 1797240104854940975369969)
                ·
                  refine ⟨1347930078641205731527477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797240104854940975369969 1347930078641205731527477)
                  ·
                    refine ⟨126368444872613037330701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1347930078641205731527477 126368444872613037330701)
                    ·
                      rfl

theorem cell23_738305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_738305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738305 prefixEnd_738305 := by exact prefixLift 738305
  have htrace : WordTrace (prefixWord ++ tailWord_738305) baseStart_738305 baseEnd_738305 := by
    simpa [prefixWord, tailWord_738305, baseEnd_738305] using wordTrace_append hprefix tailTrace_738305
  have hstable : (prefixWord ++ tailWord_738305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738305).length < 2 ^ (prefixWord ++ tailWord_738305).sum := by decide
  have hdescent : baseEnd_738305 < baseStart_738305 := by decide
  rcases family_descends (prefixWord ++ tailWord_738305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738362 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_738362 : Nat := 118140960795 + 738362 * 2 ^ 59
def prefixEnd_738362 : Nat := 4983230072969 + 3 ^ 40 * 738362 * 2
def baseEnd_738362 : Nat := 379134603015145388979341

theorem tailTrace_738362 : CollatzResearch.WordTrace tailWord_738362 prefixEnd_738362 379134603015145388979341 := by
  unfold tailWord_738362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732568637762012758800335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17953516367365367356800893 6732568637762012758800335)
  ·
    refine ⟨10098852956643019138200503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6732568637762012758800335 10098852956643019138200503)
    ·
      refine ⟨15148279434964528707300755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10098852956643019138200503 15148279434964528707300755)
      ·
        refine ⟨22722419152446793060951133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15148279434964528707300755 22722419152446793060951133)
        ·
          refine ⟨8520907182167547397856675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22722419152446793060951133 8520907182167547397856675)
          ·
            refine ⟨12781360773251321096785013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8520907182167547397856675 12781360773251321096785013)
            ·
              refine ⟨1198252572492311352823595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12781360773251321096785013 1198252572492311352823595)
              ·
                refine ⟨1797378858738467029235393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198252572492311352823595 1797378858738467029235393)
                ·
                  refine ⟨1348034144053850271926545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797378858738467029235393 1348034144053850271926545)
                  ·
                    refine ⟨1011025608040387703944909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1348034144053850271926545 1011025608040387703944909)
                    ·
                      refine ⟨379134603015145388979341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1011025608040387703944909 379134603015145388979341)
                      ·
                        rfl

theorem cell23_738362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_738362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738362 prefixEnd_738362 := by exact prefixLift 738362
  have htrace : WordTrace (prefixWord ++ tailWord_738362) baseStart_738362 baseEnd_738362 := by
    simpa [prefixWord, tailWord_738362, baseEnd_738362] using wordTrace_append hprefix tailTrace_738362
  have hstable : (prefixWord ++ tailWord_738362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738362).length < 2 ^ (prefixWord ++ tailWord_738362).sum := by decide
  have hdescent : baseEnd_738362 < baseStart_738362 := by decide
  rcases family_descends (prefixWord ++ tailWord_738362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738412 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_738412 : Nat := 118140960795 + 738412 * 2 ^ 59
def prefixEnd_738412 : Nat := 4983230072969 + 3 ^ 40 * 738412 * 2
def baseEnd_738412 : Nat := 126386759015956731118037

theorem tailTrace_738412 : CollatzResearch.WordTrace tailWord_738412 prefixEnd_738412 126386759015956731118037 := by
  unfold tailWord_738412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466049100433454787260745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17954732133911273049680993 13466049100433454787260745)
  ·
    refine ⟨10099536825325091090445559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13466049100433454787260745 10099536825325091090445559)
    ·
      refine ⟨15149305237987636635668339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10099536825325091090445559 15149305237987636635668339)
      ·
        refine ⟨22723957856981454953502509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15149305237987636635668339 22723957856981454953502509)
        ·
          refine ⟨8521484196368045607563441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22723957856981454953502509 8521484196368045607563441)
          ·
            refine ⟨6391113147276034205672581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8521484196368045607563441 6391113147276034205672581)
            ·
              refine ⟨1198333715114256413563609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6391113147276034205672581 1198333715114256413563609)
              ·
                refine ⟨898750286335692310172707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198333715114256413563609 898750286335692310172707)
                ·
                  refine ⟨1348125429503538465259061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898750286335692310172707 1348125429503538465259061)
                  ·
                    refine ⟨126386759015956731118037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1348125429503538465259061 126386759015956731118037)
                    ·
                      rfl

theorem cell23_738412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_738412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738412 prefixEnd_738412 := by exact prefixLift 738412
  have htrace : WordTrace (prefixWord ++ tailWord_738412) baseStart_738412 baseEnd_738412 := by
    simpa [prefixWord, tailWord_738412, baseEnd_738412] using wordTrace_append hprefix tailTrace_738412
  have hstable : (prefixWord ++ tailWord_738412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738412).length < 2 ^ (prefixWord ++ tailWord_738412).sum := by decide
  have hdescent : baseEnd_738412 < baseStart_738412 := by decide
  rcases family_descends (prefixWord ++ tailWord_738412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738432 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4]
def baseStart_738432 : Nat := 118140960795 + 738432 * 2 ^ 59
def prefixEnd_738432 : Nat := 4983230072969 + 3 ^ 40 * 738432 * 2
def baseEnd_738432 : Nat := 379170546660960115104019

theorem tailTrace_738432 : CollatzResearch.WordTrace tailWord_738432 prefixEnd_738432 379170546660960115104019 := by
  unfold tailWord_738432
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466413830397226495124775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17955218440529635326833033 13466413830397226495124775)
  ·
    refine ⟨20199620745595839742687163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13466413830397226495124775 20199620745595839742687163)
    ·
      refine ⟨30299431118393759614030745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20199620745595839742687163 30299431118393759614030745)
      ·
        refine ⟨22724573338795319710523059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30299431118393759614030745 22724573338795319710523059)
        ·
          refine ⟨34086860008192979565784589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22724573338795319710523059 34086860008192979565784589)
          ·
            refine ⟨12782572503072367337169221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34086860008192979565784589 12782572503072367337169221)
            ·
              refine ⟨2396732344326068875719229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12782572503072367337169221 2396732344326068875719229)
              ·
                refine ⟨898774629122275828394711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396732344326068875719229 898774629122275828394711)
                ·
                  refine ⟨1348161943683413742592067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898774629122275828394711 1348161943683413742592067)
                  ·
                    refine ⟨2022242915525120613888101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1348161943683413742592067 2022242915525120613888101)
                    ·
                      refine ⟨379170546660960115104019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2022242915525120613888101 379170546660960115104019)
                      ·
                        rfl

theorem cell23_738432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_738432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738432 prefixEnd_738432 := by exact prefixLift 738432
  have htrace : WordTrace (prefixWord ++ tailWord_738432) baseStart_738432 baseEnd_738432 := by
    simpa [prefixWord, tailWord_738432, baseEnd_738432] using wordTrace_append hprefix tailTrace_738432
  have hstable : (prefixWord ++ tailWord_738432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738432).length < 2 ^ (prefixWord ++ tailWord_738432).sum := by decide
  have hdescent : baseEnd_738432 < baseStart_738432 := by decide
  rcases family_descends (prefixWord ++ tailWord_738432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738442 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_738442 : Nat := 118140960795 + 738442 * 2 ^ 59
def prefixEnd_738442 : Nat := 4983230072969 + 3 ^ 40 * 738442 * 2
def baseEnd_738442 : Nat := 126391893822501691992991

theorem tailTrace_738442 : CollatzResearch.WordTrace tailWord_738442 prefixEnd_738442 126391893822501691992991 := by
  unfold tailWord_738442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733298097689556174528395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17955461593838816465409053 6733298097689556174528395)
  ·
    refine ⟨10099947146534334261792593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6733298097689556174528395 10099947146534334261792593)
    ·
      refine ⟨7574960359900750696344445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10099947146534334261792593 7574960359900750696344445)
      ·
        refine ⟨2840610134962781511129167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7574960359900750696344445 2840610134962781511129167)
        ·
          refine ⟨4260915202444172266693751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840610134962781511129167 4260915202444172266693751)
          ·
            refine ⟨6391372803666258400040627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260915202444172266693751 6391372803666258400040627)
            ·
              refine ⟨9587059205499387600060941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391372803666258400040627 9587059205499387600060941)
              ·
                refine ⟨3595147202062270350022853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9587059205499387600060941 3595147202062270350022853)
                ·
                  refine ⟨674090100386675690629285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3595147202062270350022853 674090100386675690629285)
                  ·
                    refine ⟨126391893822501691992991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674090100386675690629285 126391893822501691992991)
                    ·
                      rfl

theorem cell23_738442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_738442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738442 prefixEnd_738442 := by exact prefixLift 738442
  have htrace : WordTrace (prefixWord ++ tailWord_738442) baseStart_738442 baseEnd_738442 := by
    simpa [prefixWord, tailWord_738442, baseEnd_738442] using wordTrace_append hprefix tailTrace_738442
  have hstable : (prefixWord ++ tailWord_738442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738442).length < 2 ^ (prefixWord ++ tailWord_738442).sum := by decide
  have hdescent : baseEnd_738442 < baseStart_738442 := by decide
  rcases family_descends (prefixWord ++ tailWord_738442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738455 : List Nat := [1, 1, 3, 3, 3, 1, 1, 10]
def baseStart_738455 : Nat := 118140960795 + 738455 * 2 ^ 59
def prefixEnd_738455 : Nat := 4983230072969 + 3 ^ 40 * 738455 * 2
def baseEnd_738455 : Nat := 14043790989481982411719

theorem tailTrace_738455 : CollatzResearch.WordTrace tailWord_738455 prefixEnd_738455 14043790989481982411719 := by
  unfold tailWord_738455
  simp only [CollatzResearch.WordTrace]
  refine ⟨26933666539711127918336819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17955777693140751945557879 26933666539711127918336819)
  ·
    refine ⟨40400499809566691877505229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26933666539711127918336819 40400499809566691877505229)
    ·
      refine ⟨15150187428587509454064461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40400499809566691877505229 15150187428587509454064461)
      ·
        refine ⟨5681320285720316045274173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15150187428587509454064461 5681320285720316045274173)
        ·
          refine ⟨2130495107145118516977815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5681320285720316045274173 2130495107145118516977815)
          ·
            refine ⟨3195742660717677775466723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130495107145118516977815 3195742660717677775466723)
            ·
              refine ⟨4793613991076516663200085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195742660717677775466723 4793613991076516663200085)
              ·
                refine ⟨14043790989481982411719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4793613991076516663200085 14043790989481982411719)
                ·
                  rfl

theorem cell23_738455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 10].length) (baseStart_738455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738455 prefixEnd_738455 := by exact prefixLift 738455
  have htrace : WordTrace (prefixWord ++ tailWord_738455) baseStart_738455 baseEnd_738455 := by
    simpa [prefixWord, tailWord_738455, baseEnd_738455] using wordTrace_append hprefix tailTrace_738455
  have hstable : (prefixWord ++ tailWord_738455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738455).length < 2 ^ (prefixWord ++ tailWord_738455).sum := by decide
  have hdescent : baseEnd_738455 < baseStart_738455 := by decide
  rcases family_descends (prefixWord ++ tailWord_738455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738469 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_738469 : Nat := 118140960795 + 738469 * 2 ^ 59
def prefixEnd_738469 : Nat := 4983230072969 + 3 ^ 40 * 738469 * 2
def baseEnd_738469 : Nat := 379189545445176470341349

theorem tailTrace_738469 : CollatzResearch.WordTrace tailWord_738469 prefixEnd_738469 379189545445176470341349 := by
  unfold tailWord_738469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26934177161660408309346461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17956118107773605539564307 26934177161660408309346461)
  ·
    refine ⟨10100316435622653116004923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26934177161660408309346461 10100316435622653116004923)
    ·
      refine ⟨15150474653433979674007385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10100316435622653116004923 15150474653433979674007385)
      ·
        refine ⟨11362855990075484755505539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15150474653433979674007385 11362855990075484755505539)
        ·
          refine ⟨17044283985113227133258309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11362855990075484755505539 17044283985113227133258309)
          ·
            refine ⟨3195803247208730087485933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17044283985113227133258309 3195803247208730087485933)
            ·
              refine ⟨1198426217703273782807225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3195803247208730087485933 1198426217703273782807225)
              ·
                refine ⟨898819663277455337105419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198426217703273782807225 898819663277455337105419)
                ·
                  refine ⟨1348229494916183005658129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898819663277455337105419 1348229494916183005658129)
                  ·
                    refine ⟨1011172121187137254243597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1348229494916183005658129 1011172121187137254243597)
                    ·
                      refine ⟨379189545445176470341349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1011172121187137254243597 379189545445176470341349)
                      ·
                        rfl

theorem cell23_738469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_738469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738469 prefixEnd_738469 := by exact prefixLift 738469
  have htrace : WordTrace (prefixWord ++ tailWord_738469) baseStart_738469 baseEnd_738469 := by
    simpa [prefixWord, tailWord_738469, baseEnd_738469] using wordTrace_append hprefix tailTrace_738469
  have hstable : (prefixWord ++ tailWord_738469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738469).length < 2 ^ (prefixWord ++ tailWord_738469).sum := by decide
  have hdescent : baseEnd_738469 < baseStart_738469 := by decide
  rcases family_descends (prefixWord ++ tailWord_738469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738482 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_738482 : Nat := 118140960795 + 738482 * 2 ^ 59
def prefixEnd_738482 : Nat := 4983230072969 + 3 ^ 40 * 738482 * 2
def baseEnd_738482 : Nat := 379196220693684919478789

theorem tailTrace_738482 : CollatzResearch.WordTrace tailWord_738482 prefixEnd_738482 379196220693684919478789 := by
  unfold tailWord_738482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733662827653327882392425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17956434207075541019713133 6733662827653327882392425)
  ·
    refine ⟨5050247120739995911794319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6733662827653327882392425 5050247120739995911794319)
    ·
      refine ⟨7575370681109993867691479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5050247120739995911794319 7575370681109993867691479)
      ·
        refine ⟨11363056021664990801537219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7575370681109993867691479 11363056021664990801537219)
        ·
          refine ⟨17044584032497486202305829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11363056021664990801537219 17044584032497486202305829)
          ·
            refine ⟨3195859506093278662932343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17044584032497486202305829 3195859506093278662932343)
            ·
              refine ⟨4793789259139917994398515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195859506093278662932343 4793789259139917994398515)
              ·
                refine ⟨7190683888709876991597773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4793789259139917994398515 7190683888709876991597773)
                ·
                  refine ⟨2696506458266203871849165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7190683888709876991597773 2696506458266203871849165)
                  ·
                    refine ⟨1011189921849826451943437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696506458266203871849165 1011189921849826451943437)
                    ·
                      refine ⟨379196220693684919478789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1011189921849826451943437 379196220693684919478789)
                      ·
                        rfl

theorem cell23_738482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_738482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738482 prefixEnd_738482 := by exact prefixLift 738482
  have htrace : WordTrace (prefixWord ++ tailWord_738482) baseStart_738482 baseEnd_738482 := by
    simpa [prefixWord, tailWord_738482, baseEnd_738482] using wordTrace_append hprefix tailTrace_738482
  have hstable : (prefixWord ++ tailWord_738482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738482).length < 2 ^ (prefixWord ++ tailWord_738482).sum := by decide
  have hdescent : baseEnd_738482 < baseStart_738482 := by decide
  rcases family_descends (prefixWord ++ tailWord_738482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738495 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_738495 : Nat := 118140960795 + 738495 * 2 ^ 59
def prefixEnd_738495 : Nat := 4983230072969 + 3 ^ 40 * 738495 * 2
def baseEnd_738495 : Nat := 379202895942193368616229

theorem tailTrace_738495 : CollatzResearch.WordTrace tailWord_738495 prefixEnd_738495 379202895942193368616229 := by
  unfold tailWord_738495
  simp only [CollatzResearch.WordTrace]
  refine ⟨26935125459566214749792939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17956750306377476499861959 26935125459566214749792939)
  ·
    refine ⟨40402688189349322124689409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26935125459566214749792939 40402688189349322124689409)
    ·
      refine ⟨30302016142011991593517057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40402688189349322124689409 30302016142011991593517057)
      ·
        refine ⟨22726512106508993695137793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30302016142011991593517057 22726512106508993695137793)
        ·
          refine ⟨17044884079881745271353345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22726512106508993695137793 17044884079881745271353345)
          ·
            refine ⟨12783663059911308953515009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17044884079881745271353345 12783663059911308953515009)
            ·
              refine ⟨9587747294933481715136257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12783663059911308953515009 9587747294933481715136257)
              ·
                refine ⟨7190810471200111286352193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9587747294933481715136257 7190810471200111286352193)
                ·
                  refine ⟨5393107853400083464764145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7190810471200111286352193 5393107853400083464764145)
                  ·
                    refine ⟨4044830890050062598573109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5393107853400083464764145 4044830890050062598573109)
                    ·
                      refine ⟨379202895942193368616229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4044830890050062598573109 379202895942193368616229)
                      ·
                        rfl

theorem cell23_738495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_738495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738495 prefixEnd_738495 := by exact prefixLift 738495
  have htrace : WordTrace (prefixWord ++ tailWord_738495) baseStart_738495 baseEnd_738495 := by
    simpa [prefixWord, tailWord_738495, baseEnd_738495] using wordTrace_append hprefix tailTrace_738495
  have hstable : (prefixWord ++ tailWord_738495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738495).length < 2 ^ (prefixWord ++ tailWord_738495).sum := by decide
  have hdescent : baseEnd_738495 < baseStart_738495 := by decide
  rcases family_descends (prefixWord ++ tailWord_738495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738500 : List Nat := [2, 3, 3, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_738500 : Nat := 118140960795 + 738500 * 2 ^ 59
def prefixEnd_738500 : Nat := 4983230072969 + 3 ^ 40 * 738500 * 2
def baseEnd_738500 : Nat := 379205463345465849053707

theorem tailTrace_738500 : CollatzResearch.WordTrace tailWord_738500 prefixEnd_738500 379205463345465849053707 := by
  unfold tailWord_738500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467653912274050301862477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17956871883032067069149969 13467653912274050301862477)
  ·
    refine ⟨5050370217102768863198429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13467653912274050301862477 5050370217102768863198429)
    ·
      refine ⟨1893888831413538323699411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5050370217102768863198429 1893888831413538323699411)
      ·
        refine ⟨2840833247120307485549117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893888831413538323699411 2840833247120307485549117)
        ·
          refine ⟨1065312467670115307080919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2840833247120307485549117 1065312467670115307080919)
          ·
            refine ⟨1597968701505172960621379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065312467670115307080919 1597968701505172960621379)
            ·
              refine ⟨2396953052257759440932069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597968701505172960621379 2396953052257759440932069)
              ·
                refine ⟨449428697298329895174763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2396953052257759440932069 449428697298329895174763)
                ·
                  refine ⟨674143045947494842762145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449428697298329895174763 674143045947494842762145)
                  ·
                    refine ⟨505607284460621132071609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 674143045947494842762145 505607284460621132071609)
                    ·
                      refine ⟨379205463345465849053707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505607284460621132071609 379205463345465849053707)
                      ·
                        rfl

theorem cell23_738500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_738500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738500 prefixEnd_738500 := by exact prefixLift 738500
  have htrace : WordTrace (prefixWord ++ tailWord_738500) baseStart_738500 baseEnd_738500 := by
    simpa [prefixWord, tailWord_738500, baseEnd_738500] using wordTrace_append hprefix tailTrace_738500
  have hstable : (prefixWord ++ tailWord_738500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738500).length < 2 ^ (prefixWord ++ tailWord_738500).sum := by decide
  have hdescent : baseEnd_738500 < baseStart_738500 := by decide
  rcases family_descends (prefixWord ++ tailWord_738500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738515 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 2, 6]
def baseStart_738515 : Nat := 118140960795 + 738515 * 2 ^ 59
def prefixEnd_738515 : Nat := 4983230072969 + 3 ^ 40 * 738515 * 2
def baseEnd_738515 : Nat := 126404388518427763455379

theorem tailTrace_738515 : CollatzResearch.WordTrace tailWord_738515 prefixEnd_738515 126404388518427763455379 := by
  unfold tailWord_738515
  simp only [CollatzResearch.WordTrace]
  refine ⟨26935854919493758165520999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17957236612995838777013999 26935854919493758165520999)
  ·
    refine ⟨40403782379240637248281499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26935854919493758165520999 40403782379240637248281499)
    ·
      refine ⟨60605673568860955872422249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40403782379240637248281499 60605673568860955872422249)
      ·
        refine ⟨45454255176645716904316687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60605673568860955872422249 45454255176645716904316687)
        ·
          refine ⟨68181382764968575356475031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45454255176645716904316687 68181382764968575356475031)
          ·
            refine ⟨102272074147452863034712547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68181382764968575356475031 102272074147452863034712547)
            ·
              refine ⟨153408111221179294552068821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102272074147452863034712547 153408111221179294552068821)
              ·
                refine ⟨3595502606746389716064113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153408111221179294552068821 3595502606746389716064113)
                ·
                  refine ⟨2696626955059792287048085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3595502606746389716064113 2696626955059792287048085)
                  ·
                    refine ⟨126404388518427763455379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2696626955059792287048085 126404388518427763455379)
                    ·
                      rfl

theorem cell23_738515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 6].length) (baseStart_738515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738515 prefixEnd_738515 := by exact prefixLift 738515
  have htrace : WordTrace (prefixWord ++ tailWord_738515) baseStart_738515 baseEnd_738515 := by
    simpa [prefixWord, tailWord_738515, baseEnd_738515] using wordTrace_append hprefix tailTrace_738515
  have hstable : (prefixWord ++ tailWord_738515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738515).length < 2 ^ (prefixWord ++ tailWord_738515).sum := by decide
  have hdescent : baseEnd_738515 < baseStart_738515 := by decide
  rcases family_descends (prefixWord ++ tailWord_738515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738539 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 1, 4, 2]
def baseStart_738539 : Nat := 118140960795 + 738539 * 2 ^ 59
def prefixEnd_738539 : Nat := 4983230072969 + 3 ^ 40 * 738539 * 2
def baseEnd_738539 : Nat := 379225489090991196466027

theorem tailTrace_738539 : CollatzResearch.WordTrace tailWord_738539 prefixEnd_738539 379225489090991196466027 := by
  unfold tailWord_738539
  simp only [CollatzResearch.WordTrace]
  refine ⟨26936730271406810264394671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17957820180937873509596447 26936730271406810264394671)
  ·
    refine ⟨40405095407110215396592007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26936730271406810264394671 40405095407110215396592007)
    ·
      refine ⟨60607643110665323094888011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40405095407110215396592007 60607643110665323094888011)
      ·
        refine ⟨90911464665997984642332017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60607643110665323094888011 90911464665997984642332017)
        ·
          refine ⟨68183598499498488481749013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90911464665997984642332017 68183598499498488481749013)
          ·
            refine ⟨3196106179663991647581985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68183598499498488481749013 3196106179663991647581985)
            ·
              refine ⟨2397079634747993735686489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3196106179663991647581985 2397079634747993735686489)
              ·
                refine ⟨1797809726060995301764867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397079634747993735686489 1797809726060995301764867)
                ·
                  refine ⟨2696714589091492952647301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797809726060995301764867 2696714589091492952647301)
                  ·
                    refine ⟨505633985454654928621369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2696714589091492952647301 505633985454654928621369)
                    ·
                      refine ⟨379225489090991196466027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505633985454654928621369 379225489090991196466027)
                      ·
                        rfl

theorem cell23_738539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4, 2].length) (baseStart_738539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738539 prefixEnd_738539 := by exact prefixLift 738539
  have htrace : WordTrace (prefixWord ++ tailWord_738539) baseStart_738539 baseEnd_738539 := by
    simpa [prefixWord, tailWord_738539, baseEnd_738539] using wordTrace_append hprefix tailTrace_738539
  have hstable : (prefixWord ++ tailWord_738539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738539).length < 2 ^ (prefixWord ++ tailWord_738539).sum := by decide
  have hdescent : baseEnd_738539 < baseStart_738539 := by decide
  rcases family_descends (prefixWord ++ tailWord_738539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738542 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_738542 : Nat := 118140960795 + 738542 * 2 ^ 59
def prefixEnd_738542 : Nat := 4983230072969 + 3 ^ 40 * 738542 * 2
def baseEnd_738542 : Nat := 379227029532954684728513

theorem tailTrace_738542 : CollatzResearch.WordTrace tailWord_738542 prefixEnd_738542 379227029532954684728513 := by
  unfold tailWord_738542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3367104961299492722094235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17957893126930627851169253 3367104961299492722094235)
  ·
    refine ⟨5050657441949239083141353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3367104961299492722094235 5050657441949239083141353)
    ·
      refine ⟨3787993081461929312356015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5050657441949239083141353 3787993081461929312356015)
      ·
        refine ⟨5681989622192893968534023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787993081461929312356015 5681989622192893968534023)
        ·
          refine ⟨8522984433289340952801035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5681989622192893968534023 8522984433289340952801035)
          ·
            refine ⟨12784476649934011429201553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522984433289340952801035 12784476649934011429201553)
            ·
              refine ⟨9588357487450508571901165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12784476649934011429201553 9588357487450508571901165)
              ·
                refine ⟨3595634057793940714462937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9588357487450508571901165 3595634057793940714462937)
                ·
                  refine ⟨2696725543345455535847203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3595634057793940714462937 2696725543345455535847203)
                  ·
                    refine ⟨4045088315018183303770805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2696725543345455535847203 4045088315018183303770805)
                    ·
                      refine ⟨379227029532954684728513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4045088315018183303770805 379227029532954684728513)
                      ·
                        rfl

theorem cell23_738542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_738542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738542 prefixEnd_738542 := by exact prefixLift 738542
  have htrace : WordTrace (prefixWord ++ tailWord_738542) baseStart_738542 baseEnd_738542 := by
    simpa [prefixWord, tailWord_738542, baseEnd_738542] using wordTrace_append hprefix tailTrace_738542
  have hstable : (prefixWord ++ tailWord_738542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738542).length < 2 ^ (prefixWord ++ tailWord_738542).sum := by decide
  have hdescent : baseEnd_738542 < baseStart_738542 := by decide
  rcases family_descends (prefixWord ++ tailWord_738542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738545 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 11]
def baseStart_738545 : Nat := 118140960795 + 738545 * 2 ^ 59
def prefixEnd_738545 : Nat := 4983230072969 + 3 ^ 40 * 738545 * 2
def baseEnd_738545 : Nat := 42136507774990908110111

theorem tailTrace_738545 : CollatzResearch.WordTrace tailWord_738545 prefixEnd_738545 42136507774990908110111 := by
  unfold tailWord_738545
  simp only [CollatzResearch.WordTrace]
  refine ⟨26936949109385073289113089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17957966072923382192742059 26936949109385073289113089)
  ·
    refine ⟨20202711832038804966834817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26936949109385073289113089 20202711832038804966834817)
    ·
      refine ⟨15152033874029103725126113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20202711832038804966834817 15152033874029103725126113)
      ·
        refine ⟨11364025405521827793844585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15152033874029103725126113 11364025405521827793844585)
        ·
          refine ⟨8523019054141370845383439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11364025405521827793844585 8523019054141370845383439)
          ·
            refine ⟨12784528581212056268075159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523019054141370845383439 12784528581212056268075159)
            ·
              refine ⟨19176792871818084402112739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12784528581212056268075159 19176792871818084402112739)
              ·
                refine ⟨28765189307727126603169109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19176792871818084402112739 28765189307727126603169109)
                ·
                  refine ⟨42136507774990908110111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 28765189307727126603169109 42136507774990908110111)
                  ·
                    rfl

theorem cell23_738545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 11].length) (baseStart_738545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738545 prefixEnd_738545 := by exact prefixLift 738545
  have htrace : WordTrace (prefixWord ++ tailWord_738545) baseStart_738545 baseEnd_738545 := by
    simpa [prefixWord, tailWord_738545, baseEnd_738545] using wordTrace_append hprefix tailTrace_738545
  have hstable : (prefixWord ++ tailWord_738545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738545).length < 2 ^ (prefixWord ++ tailWord_738545).sum := by decide
  have hdescent : baseEnd_738545 < baseStart_738545 := by decide
  rcases family_descends (prefixWord ++ tailWord_738545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738609 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 2, 5]
def baseStart_738609 : Nat := 118140960795 + 738609 * 2 ^ 59
def prefixEnd_738609 : Nat := 4983230072969 + 3 ^ 40 * 738609 * 2
def baseEnd_738609 : Nat := 126420477578935307530235

theorem tailTrace_738609 : CollatzResearch.WordTrace tailWord_738609 prefixEnd_738609 126420477578935307530235 := by
  unfold tailWord_738609
  simp only [CollatzResearch.WordTrace]
  refine ⟨26939283381153212219442881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17959522254102141479628587 26939283381153212219442881)
  ·
    refine ⟨20204462535864909164582161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26939283381153212219442881 20204462535864909164582161)
    ·
      refine ⟨15153346901898681873436621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20204462535864909164582161 15153346901898681873436621)
      ·
        refine ⟨5682505088212005702538733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15153346901898681873436621 5682505088212005702538733)
        ·
          refine ⟨2130939408079502138452025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5682505088212005702538733 2130939408079502138452025)
          ·
            refine ⟨1598204556059626603839019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2130939408079502138452025 1598204556059626603839019)
            ·
              refine ⟨2397306834089439905758529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598204556059626603839019 2397306834089439905758529)
              ·
                refine ⟨1797980125567079929318897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397306834089439905758529 1797980125567079929318897)
                ·
                  refine ⟨1348485094175309946989173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797980125567079929318897 1348485094175309946989173)
                  ·
                    refine ⟨126420477578935307530235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1348485094175309946989173 126420477578935307530235)
                    ·
                      rfl

theorem cell23_738609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_738609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738609 prefixEnd_738609 := by exact prefixLift 738609
  have htrace : WordTrace (prefixWord ++ tailWord_738609) baseStart_738609 baseEnd_738609 := by
    simpa [prefixWord, tailWord_738609, baseEnd_738609] using wordTrace_append hprefix tailTrace_738609
  have hstable : (prefixWord ++ tailWord_738609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738609).length < 2 ^ (prefixWord ++ tailWord_738609).sum := by decide
  have hdescent : baseEnd_738609 < baseStart_738609 := by decide
  rcases family_descends (prefixWord ++ tailWord_738609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738629 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 2, 4, 2]
def baseStart_738629 : Nat := 118140960795 + 738629 * 2 ^ 59
def prefixEnd_738629 : Nat := 4983230072969 + 3 ^ 40 * 738629 * 2
def baseEnd_738629 : Nat := 379271702349895844340613

theorem tailTrace_738629 : CollatzResearch.WordTrace tailWord_738629 prefixEnd_738629 379271702349895844340613 := by
  unfold tailWord_738629
  simp only [CollatzResearch.WordTrace]
  refine ⟨26940012841080755635170941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17960008560720503756780627 26940012841080755635170941)
  ·
    refine ⟨10102504815405283363189103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26940012841080755635170941 10102504815405283363189103)
    ·
      refine ⟨15153757223107925044783655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10102504815405283363189103 15153757223107925044783655)
      ·
        refine ⟨22730635834661887567175483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15153757223107925044783655 22730635834661887567175483)
        ·
          refine ⟨34095953751992831350763225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22730635834661887567175483 34095953751992831350763225)
          ·
            refine ⟨25571965313994623513072419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34095953751992831350763225 25571965313994623513072419)
            ·
              refine ⟨38357947970991935269608629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25571965313994623513072419 38357947970991935269608629)
              ·
                refine ⟨3596057622280493931525809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38357947970991935269608629 3596057622280493931525809)
                ·
                  refine ⟨2697043216710370448644357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3596057622280493931525809 2697043216710370448644357)
                  ·
                    refine ⟨505695603133194459120817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697043216710370448644357 505695603133194459120817)
                    ·
                      refine ⟨379271702349895844340613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505695603133194459120817 379271702349895844340613)
                      ·
                        rfl

theorem cell23_738629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_738629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738629 prefixEnd_738629 := by exact prefixLift 738629
  have htrace : WordTrace (prefixWord ++ tailWord_738629) baseStart_738629 baseEnd_738629 := by
    simpa [prefixWord, tailWord_738629, baseEnd_738629] using wordTrace_append hprefix tailTrace_738629
  have hstable : (prefixWord ++ tailWord_738629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738629).length < 2 ^ (prefixWord ++ tailWord_738629).sum := by decide
  have hdescent : baseEnd_738629 < baseStart_738629 := by decide
  rcases family_descends (prefixWord ++ tailWord_738629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738642 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_738642 : Nat := 118140960795 + 738642 * 2 ^ 59
def prefixEnd_738642 : Nat := 4983230072969 + 3 ^ 40 * 738642 * 2
def baseEnd_738642 : Nat := 379278377598404293478053

theorem tailTrace_738642 : CollatzResearch.WordTrace tailWord_738642 prefixEnd_738642 379278377598404293478053 := by
  unfold tailWord_738642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735121747508414713848545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17960324660022439236929453 6735121747508414713848545)
  ·
    refine ⟨5051341310631311035386409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6735121747508414713848545 5051341310631311035386409)
    ·
      refine ⟨3788505982973483276539807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5051341310631311035386409 3788505982973483276539807)
      ·
        refine ⟨5682758974460224914809711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788505982973483276539807 5682758974460224914809711)
        ·
          refine ⟨8524138461690337372214567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682758974460224914809711 8524138461690337372214567)
          ·
            refine ⟨12786207692535506058321851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8524138461690337372214567 12786207692535506058321851)
            ·
              refine ⟨19179311538803259087482777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12786207692535506058321851 19179311538803259087482777)
              ·
                refine ⟨14384483654102444315612083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19179311538803259087482777 14384483654102444315612083)
                ·
                  refine ⟨21576725481153666473418125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14384483654102444315612083 21576725481153666473418125)
                  ·
                    refine ⟨8091272055432624927531797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21576725481153666473418125 8091272055432624927531797)
                    ·
                      refine ⟨379278377598404293478053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8091272055432624927531797 379278377598404293478053)
                      ·
                        rfl

theorem cell23_738642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_738642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738642 prefixEnd_738642 := by exact prefixLift 738642
  have htrace : WordTrace (prefixWord ++ tailWord_738642) baseStart_738642 baseEnd_738642 := by
    simpa [prefixWord, tailWord_738642, baseEnd_738642] using wordTrace_append hprefix tailTrace_738642
  have hstable : (prefixWord ++ tailWord_738642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738642).length < 2 ^ (prefixWord ++ tailWord_738642).sum := by decide
  have hdescent : baseEnd_738642 < baseStart_738642 := by decide
  rcases family_descends (prefixWord ++ tailWord_738642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738649 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 3]
def baseStart_738649 : Nat := 118140960795 + 738649 * 2 ^ 59
def prefixEnd_738649 : Nat := 4983230072969 + 3 ^ 40 * 738649 * 2
def baseEnd_738649 : Nat := 379281971962985766090521

theorem tailTrace_738649 : CollatzResearch.WordTrace tailWord_738649 prefixEnd_738649 379281971962985766090521 := by
  unfold tailWord_738649
  simp only [CollatzResearch.WordTrace]
  refine ⟨26940742301008299050899001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17960494867338866033932667 26940742301008299050899001)
  ·
    refine ⟨20205556725756224288174251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26940742301008299050899001 20205556725756224288174251)
    ·
      refine ⟨30308335088634336432261377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20205556725756224288174251 30308335088634336432261377)
      ·
        refine ⟨22731251316475752324196033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30308335088634336432261377 22731251316475752324196033)
        ·
          refine ⟨17048438487356814243147025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22731251316475752324196033 17048438487356814243147025)
          ·
            refine ⟨12786328865517610682360269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17048438487356814243147025 12786328865517610682360269)
            ·
              refine ⟨4794873324569104005885101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12786328865517610682360269 4794873324569104005885101)
              ·
                refine ⟨1798077496713414002206913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4794873324569104005885101 1798077496713414002206913)
                ·
                  refine ⟨1348558122535060501655185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1798077496713414002206913 1348558122535060501655185)
                  ·
                    refine ⟨1011418591901295376241389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1348558122535060501655185 1011418591901295376241389)
                    ·
                      refine ⟨379281971962985766090521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1011418591901295376241389 379281971962985766090521)
                      ·
                        rfl

theorem cell23_738649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_738649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738649 prefixEnd_738649 := by exact prefixLift 738649
  have htrace : WordTrace (prefixWord ++ tailWord_738649) baseStart_738649 baseEnd_738649 := by
    simpa [prefixWord, tailWord_738649, baseEnd_738649] using wordTrace_append hprefix tailTrace_738649
  have hstable : (prefixWord ++ tailWord_738649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738649).length < 2 ^ (prefixWord ++ tailWord_738649).sum := by decide
  have hdescent : baseEnd_738649 < baseStart_738649 := by decide
  rcases family_descends (prefixWord ++ tailWord_738649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738669 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 6]
def baseStart_738669 : Nat := 118140960795 + 738669 * 2 ^ 59
def prefixEnd_738669 : Nat := 4983230072969 + 3 ^ 40 * 738669 * 2
def baseEnd_738669 : Nat := 42143582397341743093381

theorem tailTrace_738669 : CollatzResearch.WordTrace tailWord_738669 prefixEnd_738669 42143582397341743093381 := by
  unfold tailWord_738669
  simp only [CollatzResearch.WordTrace]
  refine ⟨26941471760935842466627061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17960981173957228311084707 26941471760935842466627061)
  ·
    refine ⟨2525762977587735231246287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26941471760935842466627061 2525762977587735231246287)
    ·
      refine ⟨3788644466381602846869431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2525762977587735231246287 3788644466381602846869431)
      ·
        refine ⟨5682966699572404270304147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788644466381602846869431 5682966699572404270304147)
        ·
          refine ⟨8524450049358606405456221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682966699572404270304147 8524450049358606405456221)
          ·
            refine ⟨3196668768509477402046083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8524450049358606405456221 3196668768509477402046083)
            ·
              refine ⟨4795003152764216103069125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196668768509477402046083 4795003152764216103069125)
              ·
                refine ⟨899063091143290519325461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4795003152764216103069125 899063091143290519325461)
                ·
                  refine ⟨42143582397341743093381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 899063091143290519325461 42143582397341743093381)
                  ·
                    rfl

theorem cell23_738669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_738669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738669 prefixEnd_738669 := by exact prefixLift 738669
  have htrace : WordTrace (prefixWord ++ tailWord_738669) baseStart_738669 baseEnd_738669 := by
    simpa [prefixWord, tailWord_738669, baseEnd_738669] using wordTrace_append hprefix tailTrace_738669
  have hstable : (prefixWord ++ tailWord_738669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738669).length < 2 ^ (prefixWord ++ tailWord_738669).sum := by decide
  have hdescent : baseEnd_738669 < baseStart_738669 := by decide
  rcases family_descends (prefixWord ++ tailWord_738669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738672 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_738672 : Nat := 118140960795 + 738672 * 2 ^ 59
def prefixEnd_738672 : Nat := 4983230072969 + 3 ^ 40 * 738672 * 2
def baseEnd_738672 : Nat := 379293782018039176102915

theorem tailTrace_738672 : CollatzResearch.WordTrace tailWord_738672 prefixEnd_738672 379293782018039176102915 := by
  unfold tailWord_738672
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470790589962486989493135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17961054119949982652657513 13470790589962486989493135)
  ·
    refine ⟨20206185884943730484239703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13470790589962486989493135 20206185884943730484239703)
    ·
      refine ⟨30309278827415595726359555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20206185884943730484239703 30309278827415595726359555)
      ·
        refine ⟨45463918241123393589539333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30309278827415595726359555 45463918241123393589539333)
        ·
          refine ⟨8524484670210636298038625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45463918241123393589539333 8524484670210636298038625)
          ·
            refine ⟨6393363502657977223528969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8524484670210636298038625 6393363502657977223528969)
            ·
              refine ⟨4795022626993482917646727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393363502657977223528969 4795022626993482917646727)
              ·
                refine ⟨7192533940490224376470091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795022626993482917646727 7192533940490224376470091)
                ·
                  refine ⟨10788800910735336564705137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192533940490224376470091 10788800910735336564705137)
                  ·
                    refine ⟨8091600683051502423528853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10788800910735336564705137 8091600683051502423528853)
                    ·
                      refine ⟨379293782018039176102915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8091600683051502423528853 379293782018039176102915)
                      ·
                        rfl

theorem cell23_738672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_738672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738672 prefixEnd_738672 := by exact prefixLift 738672
  have htrace : WordTrace (prefixWord ++ tailWord_738672) baseStart_738672 baseEnd_738672 := by
    simpa [prefixWord, tailWord_738672, baseEnd_738672] using wordTrace_append hprefix tailTrace_738672
  have hstable : (prefixWord ++ tailWord_738672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738672).length < 2 ^ (prefixWord ++ tailWord_738672).sum := by decide
  have hdescent : baseEnd_738672 < baseStart_738672 := by decide
  rcases family_descends (prefixWord ++ tailWord_738672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738673 : List Nat := [1, 2, 2, 2, 1, 2, 6, 2, 1, 4]
def baseStart_738673 : Nat := 118140960795 + 738673 * 2 ^ 59
def prefixEnd_738673 : Nat := 4983230072969 + 3 ^ 40 * 738673 * 2
def baseEnd_738673 : Nat := 126431431832897890730137

theorem tailTrace_738673 : CollatzResearch.WordTrace tailWord_738673 prefixEnd_738673 126431431832897890730137 := by
  unfold tailWord_738673
  simp only [CollatzResearch.WordTrace]
  refine ⟨26941617652921351149772673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17961078435280900766515115 26941617652921351149772673)
  ·
    refine ⟨20206213239691013362329505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26941617652921351149772673 20206213239691013362329505)
    ·
      refine ⟨15154659929768260021747129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20206213239691013362329505 15154659929768260021747129)
      ·
        refine ⟨11365994947326195016310347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15154659929768260021747129 11365994947326195016310347)
        ·
          refine ⟨17048992420989292524465521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11365994947326195016310347 17048992420989292524465521)
          ·
            refine ⟨12786744315741969393349141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17048992420989292524465521 12786744315741969393349141)
            ·
              refine ⟨599378639800404815313241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12786744315741969393349141 599378639800404815313241)
              ·
                refine ⟨449533979850303611484931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599378639800404815313241 449533979850303611484931)
                ·
                  refine ⟨674300969775455417227397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449533979850303611484931 674300969775455417227397)
                  ·
                    refine ⟨126431431832897890730137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674300969775455417227397 126431431832897890730137)
                    ·
                      rfl

theorem cell23_738673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_738673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738673 prefixEnd_738673 := by exact prefixLift 738673
  have htrace : WordTrace (prefixWord ++ tailWord_738673) baseStart_738673 baseEnd_738673 := by
    simpa [prefixWord, tailWord_738673, baseEnd_738673] using wordTrace_append hprefix tailTrace_738673
  have hstable : (prefixWord ++ tailWord_738673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738673).length < 2 ^ (prefixWord ++ tailWord_738673).sum := by decide
  have hdescent : baseEnd_738673 < baseStart_738673 := by decide
  rcases family_descends (prefixWord ++ tailWord_738673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738696 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_738696 : Nat := 118140960795 + 738696 * 2 ^ 59
def prefixEnd_738696 : Nat := 4983230072969 + 3 ^ 40 * 738696 * 2
def baseEnd_738696 : Nat := 379306105553747082202805

theorem tailTrace_738696 : CollatzResearch.WordTrace tailWord_738696 prefixEnd_738696 379306105553747082202805 := by
  unfold tailWord_738696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471228265919013038929971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17961637687892017385239961 13471228265919013038929971)
  ·
    refine ⟨20206842398878519558394957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13471228265919013038929971 20206842398878519558394957)
    ·
      refine ⟨7577565899579444834398109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20206842398878519558394957 7577565899579444834398109)
      ·
        refine ⟨2841587212342291812899291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7577565899579444834398109 2841587212342291812899291)
        ·
          refine ⟨4262380818513437719348937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841587212342291812899291 4262380818513437719348937)
          ·
            refine ⟨3196785613885078289511703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4262380818513437719348937 3196785613885078289511703)
            ·
              refine ⟨4795178420827617434267555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196785613885078289511703 4795178420827617434267555)
              ·
                refine ⟨7192767631241426151401333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795178420827617434267555 7192767631241426151401333)
                ·
                  refine ⟨674321965428883701693875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7192767631241426151401333 674321965428883701693875)
                  ·
                    refine ⟨1011482948143325552540813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 674321965428883701693875 1011482948143325552540813)
                    ·
                      refine ⟨379306105553747082202805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1011482948143325552540813 379306105553747082202805)
                      ·
                        rfl

theorem cell23_738696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_738696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738696 prefixEnd_738696 := by exact prefixLift 738696
  have htrace : WordTrace (prefixWord ++ tailWord_738696) baseStart_738696 baseEnd_738696 := by
    simpa [prefixWord, tailWord_738696, baseEnd_738696] using wordTrace_append hprefix tailTrace_738696
  have hstable : (prefixWord ++ tailWord_738696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738696).length < 2 ^ (prefixWord ++ tailWord_738696).sum := by decide
  have hdescent : baseEnd_738696 < baseStart_738696 := by decide
  rcases family_descends (prefixWord ++ tailWord_738696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738699 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 1, 5]
def baseStart_738699 : Nat := 118140960795 + 738699 * 2 ^ 59
def prefixEnd_738699 : Nat := 4983230072969 + 3 ^ 40 * 738699 * 2
def baseEnd_738699 : Nat := 126435881998570190155097

theorem tailTrace_738699 : CollatzResearch.WordTrace tailWord_738699 prefixEnd_738699 126435881998570190155097 := by
  unfold tailWord_738699
  simp only [CollatzResearch.WordTrace]
  refine ⟨26942565950827157590219151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17961710633884771726812767 26942565950827157590219151)
  ·
    refine ⟨40413848926240736385328727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26942565950827157590219151 40413848926240736385328727)
    ·
      refine ⟨60620773389361104577993091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40413848926240736385328727 60620773389361104577993091)
      ·
        refine ⟨90931160084041656866989637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60620773389361104577993091 90931160084041656866989637)
        ·
          refine ⟨17049592515757810662560557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90931160084041656866989637 17049592515757810662560557)
          ·
            refine ⟨6393597193409178998460209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17049592515757810662560557 6393597193409178998460209)
            ·
              refine ⟨4795197895056884248845157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393597193409178998460209 4795197895056884248845157)
              ·
                refine ⟨899099605323165796658467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4795197895056884248845157 899099605323165796658467)
                ·
                  refine ⟨1348649407984748694987701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899099605323165796658467 1348649407984748694987701)
                  ·
                    refine ⟨126435881998570190155097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1348649407984748694987701 126435881998570190155097)
                    ·
                      rfl

theorem cell23_738699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 5].length) (baseStart_738699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738699 prefixEnd_738699 := by exact prefixLift 738699
  have htrace : WordTrace (prefixWord ++ tailWord_738699) baseStart_738699 baseEnd_738699 := by
    simpa [prefixWord, tailWord_738699, baseEnd_738699] using wordTrace_append hprefix tailTrace_738699
  have hstable : (prefixWord ++ tailWord_738699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738699).length < 2 ^ (prefixWord ++ tailWord_738699).sum := by decide
  have hdescent : baseEnd_738699 < baseStart_738699 := by decide
  rcases family_descends (prefixWord ++ tailWord_738699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738713 : List Nat := [1, 2, 1, 2, 1, 5, 1, 5, 1, 1, 3]
def baseStart_738713 : Nat := 118140960795 + 738713 * 2 ^ 59
def prefixEnd_738713 : Nat := 4983230072969 + 3 ^ 40 * 738713 * 2
def baseEnd_738713 : Nat := 379314834724873515690227

theorem tailTrace_738713 : CollatzResearch.WordTrace tailWord_738713 prefixEnd_738713 379314834724873515690227 := by
  unfold tailWord_738713
  simp only [CollatzResearch.WordTrace]
  refine ⟨26943076572776437981228793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17962051048517625320819195 26943076572776437981228793)
  ·
    refine ⟨20207307429582328485921595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26943076572776437981228793 20207307429582328485921595)
    ·
      refine ⟨30310961144373492728882393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20207307429582328485921595 30310961144373492728882393)
      ·
        refine ⟨22733220858280119546661795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30310961144373492728882393 22733220858280119546661795)
        ·
          refine ⟨34099831287420179319992693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22733220858280119546661795 34099831287420179319992693)
          ·
            refine ⟨3196859183195641811249315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34099831287420179319992693 3196859183195641811249315)
            ·
              refine ⟨4795288774793462716873973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196859183195641811249315 4795288774793462716873973)
              ·
                refine ⟨449558322636887129706935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4795288774793462716873973 449558322636887129706935)
                ·
                  refine ⟨674337483955330694560403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449558322636887129706935 674337483955330694560403)
                  ·
                    refine ⟨1011506225932996041840605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 674337483955330694560403 1011506225932996041840605)
                    ·
                      refine ⟨379314834724873515690227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1011506225932996041840605 379314834724873515690227)
                      ·
                        rfl

theorem cell23_738713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_738713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738713 prefixEnd_738713 := by exact prefixLift 738713
  have htrace : WordTrace (prefixWord ++ tailWord_738713) baseStart_738713 baseEnd_738713 := by
    simpa [prefixWord, tailWord_738713, baseEnd_738713] using wordTrace_append hprefix tailTrace_738713
  have hstable : (prefixWord ++ tailWord_738713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738713).length < 2 ^ (prefixWord ++ tailWord_738713).sum := by decide
  have hdescent : baseEnd_738713 < baseStart_738713 := by decide
  rcases family_descends (prefixWord ++ tailWord_738713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738739 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 3]
def baseStart_738739 : Nat := 118140960795 + 738739 * 2 ^ 59
def prefixEnd_738739 : Nat := 4983230072969 + 3 ^ 40 * 738739 * 2
def baseEnd_738739 : Nat := 379328185221890413965107

theorem tailTrace_738739 : CollatzResearch.WordTrace tailWord_738739 prefixEnd_738739 379328185221890413965107 := by
  unfold tailWord_738739
  simp only [CollatzResearch.WordTrace]
  refine ⟨26944024870682244421675271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17962683247121496281116847 26944024870682244421675271)
  ·
    refine ⟨40416037306023366632512907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26944024870682244421675271 40416037306023366632512907)
    ·
      refine ⟨60624055959035049948769361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40416037306023366632512907 60624055959035049948769361)
      ·
        refine ⟨45468041969276287461577021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60624055959035049948769361 45468041969276287461577021)
        ·
          refine ⟨17050515738478607798091383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45468041969276287461577021 17050515738478607798091383)
          ·
            refine ⟨25575773607717911697137075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17050515738478607798091383 25575773607717911697137075)
            ·
              refine ⟨38363660411576867545705613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25575773607717911697137075 38363660411576867545705613)
              ·
                refine ⟨14386372654341325329639605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38363660411576867545705613 14386372654341325329639605)
                ·
                  refine ⟨1348722436344499249653713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14386372654341325329639605 1348722436344499249653713)
                  ·
                    refine ⟨1011541827258374437240285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1348722436344499249653713 1011541827258374437240285)
                    ·
                      refine ⟨379328185221890413965107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1011541827258374437240285 379328185221890413965107)
                      ·
                        rfl

theorem cell23_738739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_738739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738739 prefixEnd_738739 := by exact prefixLift 738739
  have htrace : WordTrace (prefixWord ++ tailWord_738739) baseStart_738739 baseEnd_738739 := by
    simpa [prefixWord, tailWord_738739, baseEnd_738739] using wordTrace_append hprefix tailTrace_738739
  have hstable : (prefixWord ++ tailWord_738739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738739).length < 2 ^ (prefixWord ++ tailWord_738739).sum := by decide
  have hdescent : baseEnd_738739 < baseStart_738739 := by decide
  rcases family_descends (prefixWord ++ tailWord_738739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738749 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_738749 : Nat := 118140960795 + 738749 * 2 ^ 59
def prefixEnd_738749 : Nat := 4983230072969 + 3 ^ 40 * 738749 * 2
def baseEnd_738749 : Nat := 379333320028435374840061

theorem tailTrace_738749 : CollatzResearch.WordTrace tailWord_738749 prefixEnd_738749 379333320028435374840061 := by
  unfold tailWord_738749
  simp only [CollatzResearch.WordTrace]
  refine ⟨26944389600646016129539301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17962926400430677419692867 26944389600646016129539301)
  ·
    refine ⟨5052073050121128024288619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26944389600646016129539301 5052073050121128024288619)
    ·
      refine ⟨7578109575181692036432929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5052073050121128024288619 7578109575181692036432929)
      ·
        refine ⟨5683582181386269027324697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7578109575181692036432929 5683582181386269027324697)
        ·
          refine ⟨4262686636039701770493523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5683582181386269027324697 4262686636039701770493523)
          ·
            refine ⟨6394029954059552655740285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262686636039701770493523 6394029954059552655740285)
            ·
              refine ⟨2397761232772332245902607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6394029954059552655740285 2397761232772332245902607)
              ·
                refine ⟨3596641849158498368853911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397761232772332245902607 3596641849158498368853911)
                ·
                  refine ⟨5394962773737747553280867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596641849158498368853911 5394962773737747553280867)
                  ·
                    refine ⟨8092444160606621329921301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5394962773737747553280867 8092444160606621329921301)
                    ·
                      refine ⟨379333320028435374840061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8092444160606621329921301 379333320028435374840061)
                      ·
                        rfl

theorem cell23_738749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_738749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738749 prefixEnd_738749 := by exact prefixLift 738749
  have htrace : WordTrace (prefixWord ++ tailWord_738749) baseStart_738749 baseEnd_738749 := by
    simpa [prefixWord, tailWord_738749, baseEnd_738749] using wordTrace_append hprefix tailTrace_738749
  have hstable : (prefixWord ++ tailWord_738749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738749).length < 2 ^ (prefixWord ++ tailWord_738749).sum := by decide
  have hdescent : baseEnd_738749 < baseStart_738749 := by decide
  rcases family_descends (prefixWord ++ tailWord_738749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738797 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_738797 : Nat := 118140960795 + 738797 * 2 ^ 59
def prefixEnd_738797 : Nat := 4983230072969 + 3 ^ 40 * 738797 * 2
def baseEnd_738797 : Nat := 126452655699950395679947

theorem tailTrace_738797 : CollatzResearch.WordTrace tailWord_738797 prefixEnd_738797 126452655699950395679947 := by
  unfold tailWord_738797
  simp only [CollatzResearch.WordTrace]
  refine ⟨26946140304472120327286645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17964093536314746884857763 26946140304472120327286645)
  ·
    refine ⟨2526200653544261280683123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26946140304472120327286645 2526200653544261280683123)
    ·
      refine ⟨3789300980316391921024685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2526200653544261280683123 3789300980316391921024685)
      ·
        refine ⟨1420987867618646970384257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3789300980316391921024685 1420987867618646970384257)
        ·
          refine ⟨1065740900713985227788193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1420987867618646970384257 1065740900713985227788193)
          ·
            refine ⟨799305675535488920841145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065740900713985227788193 799305675535488920841145)
            ·
              refine ⟨599479256651616690630859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799305675535488920841145 599479256651616690630859)
              ·
                refine ⟨899218884977425035946289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599479256651616690630859 899218884977425035946289)
                ·
                  refine ⟨674414163733068776959717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 899218884977425035946289 674414163733068776959717)
                  ·
                    refine ⟨126452655699950395679947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674414163733068776959717 126452655699950395679947)
                    ·
                      rfl

theorem cell23_738797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_738797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738797 prefixEnd_738797 := by exact prefixLift 738797
  have htrace : WordTrace (prefixWord ++ tailWord_738797) baseStart_738797 baseEnd_738797 := by
    simpa [prefixWord, tailWord_738797, baseEnd_738797] using wordTrace_append hprefix tailTrace_738797
  have hstable : (prefixWord ++ tailWord_738797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738797).length < 2 ^ (prefixWord ++ tailWord_738797).sum := by decide
  have hdescent : baseEnd_738797 < baseStart_738797 := by decide
  rcases family_descends (prefixWord ++ tailWord_738797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738813 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_738813 : Nat := 118140960795 + 738813 * 2 ^ 59
def prefixEnd_738813 : Nat := 4983230072969 + 3 ^ 40 * 738813 * 2
def baseEnd_738813 : Nat := 379366182790323124439767

theorem tailTrace_738813 : CollatzResearch.WordTrace tailWord_738813 prefixEnd_738813 379366182790323124439767 := by
  unfold tailWord_738813
  simp only [CollatzResearch.WordTrace]
  refine ⟨26946723872414155059869093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17964482581609436706579395 26946723872414155059869093)
  ·
    refine ⟨5052510726077654073725455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26946723872414155059869093 5052510726077654073725455)
    ·
      refine ⟨7578766089116481110588183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5052510726077654073725455 7578766089116481110588183)
      ·
        refine ⟨11368149133674721665882275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7578766089116481110588183 11368149133674721665882275)
        ·
          refine ⟨17052223700512082498823413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11368149133674721665882275 17052223700512082498823413)
          ·
            refine ⟨1598645971923007734264695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17052223700512082498823413 1598645971923007734264695)
            ·
              refine ⟨2397968957884511601397043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598645971923007734264695 2397968957884511601397043)
              ·
                refine ⟨3596953436826767402095565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397968957884511601397043 3596953436826767402095565)
                ·
                  refine ⟨1348857538810037775785837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3596953436826767402095565 1348857538810037775785837)
                  ·
                    refine ⟨505821577053764165919689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348857538810037775785837 505821577053764165919689)
                    ·
                      refine ⟨379366182790323124439767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505821577053764165919689 379366182790323124439767)
                      ·
                        rfl

theorem cell23_738813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_738813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738813 prefixEnd_738813 := by exact prefixLift 738813
  have htrace : WordTrace (prefixWord ++ tailWord_738813) baseStart_738813 baseEnd_738813 := by
    simpa [prefixWord, tailWord_738813, baseEnd_738813] using wordTrace_append hprefix tailTrace_738813
  have hstable : (prefixWord ++ tailWord_738813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738813).length < 2 ^ (prefixWord ++ tailWord_738813).sum := by decide
  have hdescent : baseEnd_738813 < baseStart_738813 := by decide
  rcases family_descends (prefixWord ++ tailWord_738813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738889 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_738889 : Nat := 118140960795 + 738889 * 2 ^ 59
def prefixEnd_738889 : Nat := 4983230072969 + 3 ^ 40 * 738889 * 2
def baseEnd_738889 : Nat := 379405207320064827089417

theorem tailTrace_738889 : CollatzResearch.WordTrace tailWord_738889 prefixEnd_738889 379405207320064827089417 := by
  unfold tailWord_738889
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949495820138820039635721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17966330546759213359757147 26949495820138820039635721)
  ·
    refine ⟨20212121865104115029726791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26949495820138820039635721 20212121865104115029726791)
    ·
      refine ⟨30318182797656172544590187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20212121865104115029726791 30318182797656172544590187)
      ·
        refine ⟨45477274196484258816885281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30318182797656172544590187 45477274196484258816885281)
        ·
          refine ⟨34107955647363194112663961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45477274196484258816885281 34107955647363194112663961)
          ·
            refine ⟨25580966735522395584497971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34107955647363194112663961 25580966735522395584497971)
            ·
              refine ⟨38371450103283593376746957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25580966735522395584497971 38371450103283593376746957)
              ·
                refine ⟨14389293788731347516280109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38371450103283593376746957 14389293788731347516280109)
                ·
                  refine ⟨5395985170774255318605041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14389293788731347516280109 5395985170774255318605041)
                  ·
                    refine ⟨4046988878080691488953781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395985170774255318605041 4046988878080691488953781)
                    ·
                      refine ⟨379405207320064827089417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4046988878080691488953781 379405207320064827089417)
                      ·
                        rfl

theorem cell23_738889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_738889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738889 prefixEnd_738889 := by exact prefixLift 738889
  have htrace : WordTrace (prefixWord ++ tailWord_738889) baseStart_738889 baseEnd_738889 := by
    simpa [prefixWord, tailWord_738889, baseEnd_738889] using wordTrace_append hprefix tailTrace_738889
  have hstable : (prefixWord ++ tailWord_738889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738889).length < 2 ^ (prefixWord ++ tailWord_738889).sum := by decide
  have hdescent : baseEnd_738889 < baseStart_738889 := by decide
  rcases family_descends (prefixWord ++ tailWord_738889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738899 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4]
def baseStart_738899 : Nat := 118140960795 + 738899 * 2 ^ 59
def prefixEnd_738899 : Nat := 4983230072969 + 3 ^ 40 * 738899 * 2
def baseEnd_738899 : Nat := 379410342126609787964371

theorem tailTrace_738899 : CollatzResearch.WordTrace tailWord_738899 prefixEnd_738899 379410342126609787964371 := by
  unfold tailWord_738899
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949860550102591747499751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17966573700068394498333167 26949860550102591747499751)
  ·
    refine ⟨40424790825153887621249627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26949860550102591747499751 40424790825153887621249627)
    ·
      refine ⟨60637186237730831431874441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40424790825153887621249627 60637186237730831431874441)
      ·
        refine ⟨45477889678298123573905831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60637186237730831431874441 45477889678298123573905831)
        ·
          refine ⟨68216834517447185360858747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45477889678298123573905831 68216834517447185360858747)
          ·
            refine ⟨102325251776170778041288121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68216834517447185360858747 102325251776170778041288121)
            ·
              refine ⟨76743938832128083530966091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102325251776170778041288121 76743938832128083530966091)
              ·
                refine ⟨115115908248192125296449137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76743938832128083530966091 115115908248192125296449137)
                ·
                  refine ⟨86336931186144093972336853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115115908248192125296449137 86336931186144093972336853)
                  ·
                    refine ⟨2023521824675252202476645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86336931186144093972336853 2023521824675252202476645)
                    ·
                      refine ⟨379410342126609787964371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2023521824675252202476645 379410342126609787964371)
                      ·
                        rfl

theorem cell23_738899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_738899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738899 prefixEnd_738899 := by exact prefixLift 738899
  have htrace : WordTrace (prefixWord ++ tailWord_738899) baseStart_738899 baseEnd_738899 := by
    simpa [prefixWord, tailWord_738899, baseEnd_738899] using wordTrace_append hprefix tailTrace_738899
  have hstable : (prefixWord ++ tailWord_738899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738899).length < 2 ^ (prefixWord ++ tailWord_738899).sum := by decide
  have hdescent : baseEnd_738899 < baseStart_738899 := by decide
  rcases family_descends (prefixWord ++ tailWord_738899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738916 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_738916 : Nat := 118140960795 + 738916 * 2 ^ 59
def prefixEnd_738916 : Nat := 4983230072969 + 3 ^ 40 * 738916 * 2
def baseEnd_738916 : Nat := 379419071297736221451793

theorem tailTrace_738916 : CollatzResearch.WordTrace tailWord_738916 prefixEnd_738916 379419071297736221451793 := by
  unfold tailWord_738916
  simp only [CollatzResearch.WordTrace]
  refine ⟨13475240295520501825434301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17966987060694002433912401 13475240295520501825434301)
  ·
    refine ⟨5053215110820188184537863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13475240295520501825434301 5053215110820188184537863)
    ·
      refine ⟨7579822666230282276806795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053215110820188184537863 7579822666230282276806795)
      ·
        refine ⟨11369733999345423415210193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7579822666230282276806795 11369733999345423415210193)
        ·
          refine ⟨8527300499509067561407645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11369733999345423415210193 8527300499509067561407645)
          ·
            refine ⟨3197737687315900335527867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8527300499509067561407645 3197737687315900335527867)
            ·
              refine ⟨4796606530973850503291801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197737687315900335527867 4796606530973850503291801)
              ·
                refine ⟨3597454898230387877468851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796606530973850503291801 3597454898230387877468851)
                ·
                  refine ⟨5396182347345581816203277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597454898230387877468851 5396182347345581816203277)
                  ·
                    refine ⟨2023568380254593181076229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5396182347345581816203277 2023568380254593181076229)
                    ·
                      refine ⟨379419071297736221451793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2023568380254593181076229 379419071297736221451793)
                      ·
                        rfl

theorem cell23_738916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_738916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738916 prefixEnd_738916 := by exact prefixLift 738916
  have htrace : WordTrace (prefixWord ++ tailWord_738916) baseStart_738916 baseEnd_738916 := by
    simpa [prefixWord, tailWord_738916, baseEnd_738916] using wordTrace_append hprefix tailTrace_738916
  have hstable : (prefixWord ++ tailWord_738916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738916).length < 2 ^ (prefixWord ++ tailWord_738916).sum := by decide
  have hdescent : baseEnd_738916 < baseStart_738916 := by decide
  rcases family_descends (prefixWord ++ tailWord_738916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738933 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_738933 : Nat := 118140960795 + 738933 * 2 ^ 59
def prefixEnd_738933 : Nat := 4983230072969 + 3 ^ 40 * 738933 * 2
def baseEnd_738933 : Nat := 379427800468862654939215

theorem tailTrace_738933 : CollatzResearch.WordTrace tailWord_738933 prefixEnd_738933 379427800468862654939215 := by
  unfold tailWord_738933
  simp only [CollatzResearch.WordTrace]
  refine ⟨26951100631979415554237453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17967400421319610369491635 26951100631979415554237453)
  ·
    refine ⟨10106662736992280832839045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26951100631979415554237453 10106662736992280832839045)
    ·
      refine ⟨1894999263186052656157321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10106662736992280832839045 1894999263186052656157321)
      ·
        refine ⟨1421249447389539492117991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1894999263186052656157321 1421249447389539492117991)
        ·
          refine ⟨2131874171084309238176987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421249447389539492117991 2131874171084309238176987)
          ·
            refine ⟨3197811256626463857265481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131874171084309238176987 3197811256626463857265481)
            ·
              refine ⟨2398358442469847892949111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197811256626463857265481 2398358442469847892949111)
              ·
                refine ⟨3597537663704771839423667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398358442469847892949111 3597537663704771839423667)
                ·
                  refine ⟨5396306495557157759135501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597537663704771839423667 5396306495557157759135501)
                  ·
                    refine ⟨2023614935833934159675813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5396306495557157759135501 2023614935833934159675813)
                    ·
                      refine ⟨379427800468862654939215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2023614935833934159675813 379427800468862654939215)
                      ·
                        rfl

theorem cell23_738933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_738933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738933 prefixEnd_738933 := by exact prefixLift 738933
  have htrace : WordTrace (prefixWord ++ tailWord_738933) baseStart_738933 baseEnd_738933 := by
    simpa [prefixWord, tailWord_738933, baseEnd_738933] using wordTrace_append hprefix tailTrace_738933
  have hstable : (prefixWord ++ tailWord_738933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738933).length < 2 ^ (prefixWord ++ tailWord_738933).sum := by decide
  have hdescent : baseEnd_738933 < baseStart_738933 := by decide
  rcases family_descends (prefixWord ++ tailWord_738933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738939 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 10]
def baseStart_738939 : Nat := 118140960795 + 738939 * 2 ^ 59
def prefixEnd_738939 : Nat := 4983230072969 + 3 ^ 40 * 738939 * 2
def baseEnd_738939 : Nat := 42158986816976625718243

theorem tailTrace_738939 : CollatzResearch.WordTrace tailWord_738939 prefixEnd_738939 42158986816976625718243 := by
  unfold tailWord_738939
  simp only [CollatzResearch.WordTrace]
  refine ⟨26951319469957678578955871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17967546313305119052637247 26951319469957678578955871)
  ·
    refine ⟨40426979204936517868433807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26951319469957678578955871 40426979204936517868433807)
    ·
      refine ⟨60640468807404776802650711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40426979204936517868433807 60640468807404776802650711)
      ·
        refine ⟨90960703211107165203976067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60640468807404776802650711 90960703211107165203976067)
        ·
          refine ⟨136441054816660747805964101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90960703211107165203976067 136441054816660747805964101)
          ·
            refine ⟨25582697778123890213618269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136441054816660747805964101 25582697778123890213618269)
            ·
              refine ⟨9593511666796458830106851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25582697778123890213618269 9593511666796458830106851)
              ·
                refine ⟨14390267500194688245160277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9593511666796458830106851 14390267500194688245160277)
                ·
                  refine ⟨42158986816976625718243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14390267500194688245160277 42158986816976625718243)
                  ·
                    rfl

theorem cell23_738939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 10].length) (baseStart_738939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738939 prefixEnd_738939 := by exact prefixLift 738939
  have htrace : WordTrace (prefixWord ++ tailWord_738939) baseStart_738939 baseEnd_738939 := by
    simpa [prefixWord, tailWord_738939, baseEnd_738939] using wordTrace_append hprefix tailTrace_738939
  have hstable : (prefixWord ++ tailWord_738939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738939).length < 2 ^ (prefixWord ++ tailWord_738939).sum := by decide
  have hdescent : baseEnd_738939 < baseStart_738939 := by decide
  rcases family_descends (prefixWord ++ tailWord_738939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738956 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 6]
def baseStart_738956 : Nat := 118140960795 + 738956 * 2 ^ 59
def prefixEnd_738956 : Nat := 4983230072969 + 3 ^ 40 * 738956 * 2
def baseEnd_738956 : Nat := 42159956724879562772401

theorem tailTrace_738956 : CollatzResearch.WordTrace tailWord_738956 prefixEnd_738956 42159956724879562772401 := by
  unfold tailWord_738956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13475969755448045241162361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17967959673930726988216481 13475969755448045241162361)
  ·
    refine ⟨10106977316586033930871771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13475969755448045241162361 10106977316586033930871771)
    ·
      refine ⟨15160465974879050896307657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10106977316586033930871771 15160465974879050896307657)
      ·
        refine ⟨11370349481159288172230743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15160465974879050896307657 11370349481159288172230743)
        ·
          refine ⟨17055524221738932258346115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11370349481159288172230743 17055524221738932258346115)
          ·
            refine ⟨25583286332608398387519173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17055524221738932258346115 25583286332608398387519173)
            ·
              refine ⟨4796866187364074697659845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25583286332608398387519173 4796866187364074697659845)
              ·
                refine ⟨899412410130764005811221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4796866187364074697659845 899412410130764005811221)
                ·
                  refine ⟨42159956724879562772401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 899412410130764005811221 42159956724879562772401)
                  ·
                    rfl

theorem cell23_738956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_738956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738956 prefixEnd_738956 := by exact prefixLift 738956
  have htrace : WordTrace (prefixWord ++ tailWord_738956) baseStart_738956 baseEnd_738956 := by
    simpa [prefixWord, tailWord_738956, baseEnd_738956] using wordTrace_append hprefix tailTrace_738956
  have hstable : (prefixWord ++ tailWord_738956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738956).length < 2 ^ (prefixWord ++ tailWord_738956).sum := by decide
  have hdescent : baseEnd_738956 < baseStart_738956 := by decide
  rcases family_descends (prefixWord ++ tailWord_738956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738984 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_738984 : Nat := 118140960795 + 738984 * 2 ^ 59
def prefixEnd_738984 : Nat := 4983230072969 + 3 ^ 40 * 738984 * 2
def baseEnd_738984 : Nat := 379453987982241955401481

theorem tailTrace_738984 : CollatzResearch.WordTrace tailWord_738984 prefixEnd_738984 379453987982241955401481 := by
  unfold tailWord_738984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13476480377397325632172003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17968640503196434176229337 13476480377397325632172003)
  ·
    refine ⟨20214720566095988448258005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13476480377397325632172003 20214720566095988448258005)
    ·
      refine ⟨473782513267874729256047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 20214720566095988448258005 473782513267874729256047)
      ·
        refine ⟨710673769901812093884071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473782513267874729256047 710673769901812093884071)
        ·
          refine ⟨1066010654852718140826107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710673769901812093884071 1066010654852718140826107)
          ·
            refine ⟨1599015982279077211239161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066010654852718140826107 1599015982279077211239161)
            ·
              refine ⟨1199261986709307908429371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599015982279077211239161 1199261986709307908429371)
              ·
                refine ⟨1798892980063961862644057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199261986709307908429371 1798892980063961862644057)
                ·
                  refine ⟨1349169735047971396983043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1798892980063961862644057 1349169735047971396983043)
                  ·
                    refine ⟨2023754602571957095474565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349169735047971396983043 2023754602571957095474565)
                    ·
                      refine ⟨379453987982241955401481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2023754602571957095474565 379453987982241955401481)
                      ·
                        rfl

theorem cell23_738984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_738984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_738984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_738984 prefixEnd_738984 := by exact prefixLift 738984
  have htrace : WordTrace (prefixWord ++ tailWord_738984) baseStart_738984 baseEnd_738984 := by
    simpa [prefixWord, tailWord_738984, baseEnd_738984] using wordTrace_append hprefix tailTrace_738984
  have hstable : (prefixWord ++ tailWord_738984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738984).length < 2 ^ (prefixWord ++ tailWord_738984).sum := by decide
  have hdescent : baseEnd_738984 < baseStart_738984 := by decide
  rcases family_descends (prefixWord ++ tailWord_738984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739016 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 3, 6]
def baseStart_739016 : Nat := 118140960795 + 739016 * 2 ^ 59
def prefixEnd_739016 : Nat := 4983230072969 + 3 ^ 40 * 739016 * 2
def baseEnd_739016 : Nat := 126490139787728610067111

theorem tailTrace_739016 : CollatzResearch.WordTrace tailWord_739016 prefixEnd_739016 126490139787728610067111 := by
  unfold tailWord_739016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13477063945339360364754451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17969418593785813819672601 13477063945339360364754451)
  ·
    refine ⟨20215595918009040547131677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13477063945339360364754451 20215595918009040547131677)
    ·
      refine ⟨7580848469253390205174379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20215595918009040547131677 7580848469253390205174379)
      ·
        refine ⟨11371272703880085307761569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7580848469253390205174379 11371272703880085307761569)
        ·
          refine ⟨8528454527910063980821177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11371272703880085307761569 8528454527910063980821177)
          ·
            refine ⟨6396340895932547985615883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8528454527910063980821177 6396340895932547985615883)
            ·
              refine ⟨9594511343898821978423825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396340895932547985615883 9594511343898821978423825)
              ·
                refine ⟨7195883507924116483817869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9594511343898821978423825 7195883507924116483817869)
                ·
                  refine ⟨2698456315471543681431701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7195883507924116483817869 2698456315471543681431701)
                  ·
                    refine ⟨126490139787728610067111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2698456315471543681431701 126490139787728610067111)
                    ·
                      rfl

theorem cell23_739016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_739016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739016 prefixEnd_739016 := by exact prefixLift 739016
  have htrace : WordTrace (prefixWord ++ tailWord_739016) baseStart_739016 baseEnd_739016 := by
    simpa [prefixWord, tailWord_739016, baseEnd_739016] using wordTrace_append hprefix tailTrace_739016
  have hstable : (prefixWord ++ tailWord_739016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739016).length < 2 ^ (prefixWord ++ tailWord_739016).sum := by decide
  have hdescent : baseEnd_739016 < baseStart_739016 := by decide
  rcases family_descends (prefixWord ++ tailWord_739016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739033 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 1, 6]
def baseStart_739033 : Nat := 118140960795 + 739033 * 2 ^ 59
def prefixEnd_739033 : Nat := 4983230072969 + 3 ^ 40 * 739033 * 2
def baseEnd_739033 : Nat := 126493049511437421229585

theorem tailTrace_739033 : CollatzResearch.WordTrace tailWord_739033 prefixEnd_739033 126493049511437421229585 := by
  unfold tailWord_739033
  simp only [CollatzResearch.WordTrace]
  refine ⟨26954747931617132632877753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17969831954411421755251835 26954747931617132632877753)
  ·
    refine ⟨20216060948712849474658315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26954747931617132632877753 20216060948712849474658315)
    ·
      refine ⟨30324091423069274211987473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20216060948712849474658315 30324091423069274211987473)
      ·
        refine ⟨22743068567301955658990605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30324091423069274211987473 22743068567301955658990605)
        ·
          refine ⟨8528650712738233372121477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22743068567301955658990605 8528650712738233372121477)
          ·
            refine ⟨1599122008638418757272777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8528650712738233372121477 1599122008638418757272777)
            ·
              refine ⟨1199341506478814067954583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599122008638418757272777 1199341506478814067954583)
              ·
                refine ⟨1799012259718221101931875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199341506478814067954583 1799012259718221101931875)
                ·
                  refine ⟨2698518389577331652897813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799012259718221101931875 2698518389577331652897813)
                  ·
                    refine ⟨126493049511437421229585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2698518389577331652897813 126493049511437421229585)
                    ·
                      rfl

theorem cell23_739033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_739033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739033 prefixEnd_739033 := by exact prefixLift 739033
  have htrace : WordTrace (prefixWord ++ tailWord_739033) baseStart_739033 baseEnd_739033 := by
    simpa [prefixWord, tailWord_739033, baseEnd_739033] using wordTrace_append hprefix tailTrace_739033
  have hstable : (prefixWord ++ tailWord_739033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739033).length < 2 ^ (prefixWord ++ tailWord_739033).sum := by decide
  have hdescent : baseEnd_739033 < baseStart_739033 := by decide
  rcases family_descends (prefixWord ++ tailWord_739033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739040 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 5, 2, 2]
def baseStart_739040 : Nat := 118140960795 + 739040 * 2 ^ 59
def prefixEnd_739040 : Nat := 4983230072969 + 3 ^ 40 * 739040 * 2
def baseEnd_739040 : Nat := 379482742898893736301223

theorem tailTrace_739040 : CollatzResearch.WordTrace tailWord_739040 prefixEnd_739040 379482742898893736301223 := by
  unfold tailWord_739040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13477501621295886414191287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17970002161727848552255049 13477501621295886414191287)
  ·
    refine ⟨20216252431943829621286931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13477501621295886414191287 20216252431943829621286931)
    ·
      refine ⟨30324378647915744431930397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20216252431943829621286931 30324378647915744431930397)
      ·
        refine ⟨11371641992968404161973899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30324378647915744431930397 11371641992968404161973899)
        ·
          refine ⟨17057462989452606242960849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11371641992968404161973899 17057462989452606242960849)
          ·
            refine ⟨12793097242089454682220637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17057462989452606242960849 12793097242089454682220637)
            ·
              refine ⟨4797411465783545505832739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12793097242089454682220637 4797411465783545505832739)
              ·
                refine ⟨7196117198675318258749109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4797411465783545505832739 7196117198675318258749109)
                ·
                  refine ⟨674635987375811086757729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7196117198675318258749109 674635987375811086757729)
                  ·
                    refine ⟨505976990531858315068297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 674635987375811086757729 505976990531858315068297)
                    ·
                      refine ⟨379482742898893736301223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 505976990531858315068297 379482742898893736301223)
                      ·
                        rfl

theorem cell23_739040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_739040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739040 prefixEnd_739040 := by exact prefixLift 739040
  have htrace : WordTrace (prefixWord ++ tailWord_739040) baseStart_739040 baseEnd_739040 := by
    simpa [prefixWord, tailWord_739040, baseEnd_739040] using wordTrace_append hprefix tailTrace_739040
  have hstable : (prefixWord ++ tailWord_739040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739040).length < 2 ^ (prefixWord ++ tailWord_739040).sum := by decide
  have hdescent : baseEnd_739040 < baseStart_739040 := by decide
  rcases family_descends (prefixWord ++ tailWord_739040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739057 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 1, 1, 4]
def baseStart_739057 : Nat := 118140960795 + 739057 * 2 ^ 59
def prefixEnd_739057 : Nat := 4983230072969 + 3 ^ 40 * 739057 * 2
def baseEnd_739057 : Nat := 379491472070020169788645

theorem tailTrace_739057 : CollatzResearch.WordTrace tailWord_739057 prefixEnd_739057 379491472070020169788645 := by
  unfold tailWord_739057
  simp only [CollatzResearch.WordTrace]
  refine ⟨26955623283530184731751425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17970415522353456487834283 26955623283530184731751425)
  ·
    refine ⟨20216717462647638548813569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26955623283530184731751425 20216717462647638548813569)
    ·
      refine ⟨15162538096985728911610177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20216717462647638548813569 15162538096985728911610177)
      ·
        refine ⟨11371903572739296683707633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15162538096985728911610177 11371903572739296683707633)
        ·
          refine ⟨8528927679554472512780725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11371903572739296683707633 8528927679554472512780725)
          ·
            refine ⟨799586969958231798073193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8528927679554472512780725 799586969958231798073193)
            ·
              refine ⟨599690227468673848554895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799586969958231798073193 599690227468673848554895)
              ·
                refine ⟨899535341203010772832343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599690227468673848554895 899535341203010772832343)
                ·
                  refine ⟨1349303011804516159248515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899535341203010772832343 1349303011804516159248515)
                  ·
                    refine ⟨2023954517706774238872773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349303011804516159248515 2023954517706774238872773)
                    ·
                      refine ⟨379491472070020169788645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2023954517706774238872773 379491472070020169788645)
                      ·
                        rfl

theorem cell23_739057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_739057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739057 prefixEnd_739057 := by exact prefixLift 739057
  have htrace : WordTrace (prefixWord ++ tailWord_739057) baseStart_739057 baseEnd_739057 := by
    simpa [prefixWord, tailWord_739057, baseEnd_739057] using wordTrace_append hprefix tailTrace_739057
  have hstable : (prefixWord ++ tailWord_739057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739057).length < 2 ^ (prefixWord ++ tailWord_739057).sum := by decide
  have hdescent : baseEnd_739057 < baseStart_739057 := by decide
  rcases family_descends (prefixWord ++ tailWord_739057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739066 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_739066 : Nat := 118140960795 + 739066 * 2 ^ 59
def prefixEnd_739066 : Nat := 4983230072969 + 3 ^ 40 * 739066 * 2
def baseEnd_739066 : Nat := 379496093395910634576103

theorem tailTrace_739066 : CollatzResearch.WordTrace tailWord_739066 prefixEnd_739066 379496093395910634576103 := by
  unfold tailWord_739066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738987885124394817207263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17970634360331719512552701 6738987885124394817207263)
  ·
    refine ⟨10108481827686592225810895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6738987885124394817207263 10108481827686592225810895)
    ·
      refine ⟨15162722741529888338716343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10108481827686592225810895 15162722741529888338716343)
      ·
        refine ⟨22744084112294832508074515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15162722741529888338716343 22744084112294832508074515)
        ·
          refine ⟨34116126168442248762111773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22744084112294832508074515 34116126168442248762111773)
          ·
            refine ⟨12793547313165843285791915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34116126168442248762111773 12793547313165843285791915)
            ·
              refine ⟨19190320969748764928687873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12793547313165843285791915 19190320969748764928687873)
              ·
                refine ⟨14392740727311573696515905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19190320969748764928687873 14392740727311573696515905)
                ·
                  refine ⟨10794555545483680272386929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14392740727311573696515905 10794555545483680272386929)
                  ·
                    refine ⟨8095916659112760204290197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10794555545483680272386929 8095916659112760204290197)
                    ·
                      refine ⟨379496093395910634576103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8095916659112760204290197 379496093395910634576103)
                      ·
                        rfl

theorem cell23_739066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_739066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739066 prefixEnd_739066 := by exact prefixLift 739066
  have htrace : WordTrace (prefixWord ++ tailWord_739066) baseStart_739066 baseEnd_739066 := by
    simpa [prefixWord, tailWord_739066, baseEnd_739066] using wordTrace_append hprefix tailTrace_739066
  have hstable : (prefixWord ++ tailWord_739066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739066).length < 2 ^ (prefixWord ++ tailWord_739066).sum := by decide
  have hdescent : baseEnd_739066 < baseStart_739066 := by decide
  rcases family_descends (prefixWord ++ tailWord_739066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739073 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_739073 : Nat := 118140960795 + 739073 * 2 ^ 59
def prefixEnd_739073 : Nat := 4983230072969 + 3 ^ 40 * 739073 * 2
def baseEnd_739073 : Nat := 379499687760492107188571

theorem tailTrace_739073 : CollatzResearch.WordTrace tailWord_739073 prefixEnd_739073 379499687760492107188571 := by
  unfold tailWord_739073
  simp only [CollatzResearch.WordTrace]
  refine ⟨26956206851472219464333873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17970804567648146309555915 26956206851472219464333873)
  ·
    refine ⟨20217155138604164598250405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26956206851472219464333873 20217155138604164598250405)
    ·
      refine ⟨3790716588488280862171951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20217155138604164598250405 3790716588488280862171951)
      ·
        refine ⟨5686074882732421293257927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3790716588488280862171951 5686074882732421293257927)
        ·
          refine ⟨8529112324098631939886891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686074882732421293257927 8529112324098631939886891)
          ·
            refine ⟨12793668486147947909830337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8529112324098631939886891 12793668486147947909830337)
            ·
              refine ⟨9595251364610960932372753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12793668486147947909830337 9595251364610960932372753)
              ·
                refine ⟨7196438523458220699279565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9595251364610960932372753 7196438523458220699279565)
                ·
                  refine ⟨2698664446296832762229837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7196438523458220699279565 2698664446296832762229837)
                  ·
                    refine ⟨1011999167361312285836189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698664446296832762229837 1011999167361312285836189)
                    ·
                      refine ⟨379499687760492107188571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1011999167361312285836189 379499687760492107188571)
                      ·
                        rfl

theorem cell23_739073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_739073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739073 prefixEnd_739073 := by exact prefixLift 739073
  have htrace : WordTrace (prefixWord ++ tailWord_739073) baseStart_739073 baseEnd_739073 := by
    simpa [prefixWord, tailWord_739073, baseEnd_739073] using wordTrace_append hprefix tailTrace_739073
  have hstable : (prefixWord ++ tailWord_739073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739073).length < 2 ^ (prefixWord ++ tailWord_739073).sum := by decide
  have hdescent : baseEnd_739073 < baseStart_739073 := by decide
  rcases family_descends (prefixWord ++ tailWord_739073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739074 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_739074 : Nat := 118140960795 + 739074 * 2 ^ 59
def prefixEnd_739074 : Nat := 4983230072969 + 3 ^ 40 * 739074 * 2
def baseEnd_739074 : Nat := 379500201241146603276067

theorem tailTrace_739074 : CollatzResearch.WordTrace tailWord_739074 prefixEnd_739074 379500201241146603276067 := by
  unfold tailWord_739074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739060831117149158780069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17970828882979064423413517 6739060831117149158780069)
  ·
    refine ⟨1263573905834465467271263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6739060831117149158780069 1263573905834465467271263)
    ·
      refine ⟨1895360858751698200906895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263573905834465467271263 1895360858751698200906895)
      ·
        refine ⟨2843041288127547301360343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895360858751698200906895 2843041288127547301360343)
        ·
          refine ⟨4264561932191320952040515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843041288127547301360343 4264561932191320952040515)
          ·
            refine ⟨6396842898286981428060773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264561932191320952040515 6396842898286981428060773)
            ·
              refine ⟨1199408043428809017761395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6396842898286981428060773 1199408043428809017761395)
              ·
                refine ⟨1799112065143213526642093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199408043428809017761395 1799112065143213526642093)
                ·
                  refine ⟨674667024428705072490785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1799112065143213526642093 674667024428705072490785)
                  ·
                    refine ⟨506000268321528804368089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 674667024428705072490785 506000268321528804368089)
                    ·
                      refine ⟨379500201241146603276067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506000268321528804368089 379500201241146603276067)
                      ·
                        rfl

theorem cell23_739074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_739074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739074 prefixEnd_739074 := by exact prefixLift 739074
  have htrace : WordTrace (prefixWord ++ tailWord_739074) baseStart_739074 baseEnd_739074 := by
    simpa [prefixWord, tailWord_739074, baseEnd_739074] using wordTrace_append hprefix tailTrace_739074
  have hstable : (prefixWord ++ tailWord_739074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739074).length < 2 ^ (prefixWord ++ tailWord_739074).sum := by decide
  have hdescent : baseEnd_739074 < baseStart_739074 := by decide
  rcases family_descends (prefixWord ++ tailWord_739074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739143 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_739143 : Nat := 118140960795 + 739143 * 2 ^ 59
def prefixEnd_739143 : Nat := 4983230072969 + 3 ^ 40 * 739143 * 2
def baseEnd_739143 : Nat := 379535631406306833313249

theorem tailTrace_739143 : CollatzResearch.WordTrace tailWord_739143 prefixEnd_739143 379535631406306833313249 := by
  unfold tailWord_739143
  simp only [CollatzResearch.WordTrace]
  refine ⟨26958759961218621419382083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17972506640812414279588055 26958759961218621419382083)
  ·
    refine ⟨40438139941827932129073125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26958759961218621419382083 40438139941827932129073125)
    ·
      refine ⟨7582151239092737274201211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40438139941827932129073125 7582151239092737274201211)
      ·
        refine ⟨11373226858639105911301817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7582151239092737274201211 11373226858639105911301817)
        ·
          refine ⟨8529920143979329433476363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11373226858639105911301817 8529920143979329433476363)
          ·
            refine ⟨12794880215968994150214545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8529920143979329433476363 12794880215968994150214545)
            ·
              refine ⟨9596160161976745612660909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12794880215968994150214545 9596160161976745612660909)
              ·
                refine ⟨3598560060741279604747841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9596160161976745612660909 3598560060741279604747841)
                ·
                  refine ⟨2698920045555959703560881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3598560060741279604747841 2698920045555959703560881)
                  ·
                    refine ⟨2024190034166969777670661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698920045555959703560881 2024190034166969777670661)
                    ·
                      refine ⟨379535631406306833313249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2024190034166969777670661 379535631406306833313249)
                      ·
                        rfl

theorem cell23_739143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_739143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739143 prefixEnd_739143 := by exact prefixLift 739143
  have htrace : WordTrace (prefixWord ++ tailWord_739143) baseStart_739143 baseEnd_739143 := by
    simpa [prefixWord, tailWord_739143, baseEnd_739143] using wordTrace_append hprefix tailTrace_739143
  have hstable : (prefixWord ++ tailWord_739143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739143).length < 2 ^ (prefixWord ++ tailWord_739143).sum := by decide
  have hdescent : baseEnd_739143 < baseStart_739143 := by decide
  rcases family_descends (prefixWord ++ tailWord_739143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739164 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_739164 : Nat := 118140960795 + 739164 * 2 ^ 59
def prefixEnd_739164 : Nat := 4983230072969 + 3 ^ 40 * 739164 * 2
def baseEnd_739164 : Nat := 379546414500051251150653

theorem tailTrace_739164 : CollatzResearch.WordTrace tailWord_739164 prefixEnd_739164 379546414500051251150653 := by
  unfold tailWord_739164
  simp only [CollatzResearch.WordTrace]
  refine ⟨13479762947071271002948273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17973017262761694670597697 13479762947071271002948273)
  ·
    refine ⟨10109822210303453252211205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13479762947071271002948273 10109822210303453252211205)
    ·
      refine ⟨1895591664431897484789601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10109822210303453252211205 1895591664431897484789601)
      ·
        refine ⟨1421693748323923113592201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1895591664431897484789601 1421693748323923113592201)
        ·
          refine ⟨1066270311242942335194151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421693748323923113592201 1066270311242942335194151)
          ·
            refine ⟨1599405466864413502791227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066270311242942335194151 1599405466864413502791227)
            ·
              refine ⟨2399108200296620254186841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599405466864413502791227 2399108200296620254186841)
              ·
                refine ⟨1799331150222465190640131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399108200296620254186841 1799331150222465190640131)
                ·
                  refine ⟨2698996725333697785960197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799331150222465190640131 2698996725333697785960197)
                  ·
                    refine ⟨506061886000068334867537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2698996725333697785960197 506061886000068334867537)
                    ·
                      refine ⟨379546414500051251150653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506061886000068334867537 379546414500051251150653)
                      ·
                        rfl

theorem cell23_739164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_739164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739164 prefixEnd_739164 := by exact prefixLift 739164
  have htrace : WordTrace (prefixWord ++ tailWord_739164) baseStart_739164 baseEnd_739164 := by
    simpa [prefixWord, tailWord_739164, baseEnd_739164] using wordTrace_append hprefix tailTrace_739164
  have hstable : (prefixWord ++ tailWord_739164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739164).length < 2 ^ (prefixWord ++ tailWord_739164).sum := by decide
  have hdescent : baseEnd_739164 < baseStart_739164 := by decide
  rcases family_descends (prefixWord ++ tailWord_739164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739193 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_739193 : Nat := 118140960795 + 739193 * 2 ^ 59
def prefixEnd_739193 : Nat := 4983230072969 + 3 ^ 40 * 739193 * 2
def baseEnd_739193 : Nat := 379561305439031637688019

theorem tailTrace_739193 : CollatzResearch.WordTrace tailWord_739193 prefixEnd_739193 379561305439031637688019 := by
  unfold tailWord_739193
  simp only [CollatzResearch.WordTrace]
  refine ⟨26960583611037479958702233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17973722407358319972468155 26960583611037479958702233)
  ·
    refine ⟨20220437708278109969026675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26960583611037479958702233 20220437708278109969026675)
    ·
      refine ⟨30330656562417164953540013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20220437708278109969026675 30330656562417164953540013)
      ·
        refine ⟨11373996210906436857577505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30330656562417164953540013 11373996210906436857577505)
        ·
          refine ⟨8530497158179827643183129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11373996210906436857577505 8530497158179827643183129)
          ·
            refine ⟨6397872868634870732387347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8530497158179827643183129 6397872868634870732387347)
            ·
              refine ⟨9596809302952306098581021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397872868634870732387347 9596809302952306098581021)
              ·
                refine ⟨3598803488607114786967883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9596809302952306098581021 3598803488607114786967883)
                ·
                  refine ⟨5398205232910672180451825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598803488607114786967883 5398205232910672180451825)
                  ·
                    refine ⟨4048653924683004135338869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398205232910672180451825 4048653924683004135338869)
                    ·
                      refine ⟨379561305439031637688019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4048653924683004135338869 379561305439031637688019)
                      ·
                        rfl

theorem cell23_739193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_739193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739193 prefixEnd_739193 := by exact prefixLift 739193
  have htrace : WordTrace (prefixWord ++ tailWord_739193) baseStart_739193 baseEnd_739193 := by
    simpa [prefixWord, tailWord_739193, baseEnd_739193] using wordTrace_append hprefix tailTrace_739193
  have hstable : (prefixWord ++ tailWord_739193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739193).length < 2 ^ (prefixWord ++ tailWord_739193).sum := by decide
  have hdescent : baseEnd_739193 < baseStart_739193 := by decide
  rcases family_descends (prefixWord ++ tailWord_739193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739247 : List Nat := [1, 1, 2, 1, 2, 2, 3, 6, 1, 4]
def baseStart_739247 : Nat := 118140960795 + 739247 * 2 ^ 59
def prefixEnd_739247 : Nat := 4983230072969 + 3 ^ 40 * 739247 * 2
def baseEnd_739247 : Nat := 126529677798124808804257

theorem tailTrace_739247 : CollatzResearch.WordTrace tailWord_739247 prefixEnd_739247 126529677798124808804257 := by
  unfold tailWord_739247
  simp only [CollatzResearch.WordTrace]
  refine ⟨26962553152841847181167995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17975035435227898120778663 26962553152841847181167995)
  ·
    refine ⟨40443829729262770771751993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26962553152841847181167995 40443829729262770771751993)
    ·
      refine ⟨30332872296947078078813995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40443829729262770771751993 30332872296947078078813995)
      ·
        refine ⟨45499308445420617118220993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30332872296947078078813995 45499308445420617118220993)
        ·
          refine ⟨34124481334065462838665745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45499308445420617118220993 34124481334065462838665745)
          ·
            refine ⟨25593361000549097128999309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34124481334065462838665745 25593361000549097128999309)
            ·
              refine ⟨9597510375205911423374741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25593361000549097128999309 9597510375205911423374741)
              ·
                refine ⟨449883298837777097970691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9597510375205911423374741 449883298837777097970691)
                ·
                  refine ⟨674824948256665646956037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449883298837777097970691 674824948256665646956037)
                  ·
                    refine ⟨126529677798124808804257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674824948256665646956037 126529677798124808804257)
                    ·
                      rfl

theorem cell23_739247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 4].length) (baseStart_739247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739247 prefixEnd_739247 := by exact prefixLift 739247
  have htrace : WordTrace (prefixWord ++ tailWord_739247) baseStart_739247 baseEnd_739247 := by
    simpa [prefixWord, tailWord_739247, baseEnd_739247] using wordTrace_append hprefix tailTrace_739247
  have hstable : (prefixWord ++ tailWord_739247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739247).length < 2 ^ (prefixWord ++ tailWord_739247).sum := by decide
  have hdescent : baseEnd_739247 < baseStart_739247 := by decide
  rcases family_descends (prefixWord ++ tailWord_739247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739263 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_739263 : Nat := 118140960795 + 739263 * 2 ^ 59
def prefixEnd_739263 : Nat := 4983230072969 + 3 ^ 40 * 739263 * 2
def baseEnd_739263 : Nat := 379597249084846363812697

theorem tailTrace_739263 : CollatzResearch.WordTrace tailWord_739263 prefixEnd_739263 379597249084846363812697 := by
  unfold tailWord_739263
  simp only [CollatzResearch.WordTrace]
  refine ⟨26963136720783881913750443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17975424480522587942500295 26963136720783881913750443)
  ·
    refine ⟨40444705081175822870625665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26963136720783881913750443 40444705081175822870625665)
    ·
      refine ⟨30333528810881867152969249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40444705081175822870625665 30333528810881867152969249)
      ·
        refine ⟨22750146608161400364726937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30333528810881867152969249 22750146608161400364726937)
        ·
          refine ⟨17062609956121050273545203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22750146608161400364726937 17062609956121050273545203)
          ·
            refine ⟨25593914934181575410317805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17062609956121050273545203 25593914934181575410317805)
            ·
              refine ⟨9597718100318090778869177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25593914934181575410317805 9597718100318090778869177)
              ·
                refine ⟨7198288575238568084151883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9597718100318090778869177 7198288575238568084151883)
                ·
                  refine ⟨10797432862857852126227825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7198288575238568084151883 10797432862857852126227825)
                  ·
                    refine ⟨8098074647143389094670869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10797432862857852126227825 8098074647143389094670869)
                    ·
                      refine ⟨379597249084846363812697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8098074647143389094670869 379597249084846363812697)
                      ·
                        rfl

theorem cell23_739263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_739263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739263 prefixEnd_739263 := by exact prefixLift 739263
  have htrace : WordTrace (prefixWord ++ tailWord_739263) baseStart_739263 baseEnd_739263 := by
    simpa [prefixWord, tailWord_739263, baseEnd_739263] using wordTrace_append hprefix tailTrace_739263
  have hstable : (prefixWord ++ tailWord_739263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739263).length < 2 ^ (prefixWord ++ tailWord_739263).sum := by decide
  have hdescent : baseEnd_739263 < baseStart_739263 := by decide
  rcases family_descends (prefixWord ++ tailWord_739263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739297 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_739297 : Nat := 118140960795 + 739297 * 2 ^ 59
def prefixEnd_739297 : Nat := 4983230072969 + 3 ^ 40 * 739297 * 2
def baseEnd_739297 : Nat := 379614707427099230787541

theorem tailTrace_739297 : CollatzResearch.WordTrace tailWord_739297 prefixEnd_739297 379614707427099230787541 := by
  unfold tailWord_739297
  simp only [CollatzResearch.WordTrace]
  refine ⟨26964376802660705720488145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17976251201773803813658763 26964376802660705720488145)
  ·
    refine ⟨20223282601995529290366109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26964376802660705720488145 20223282601995529290366109)
    ·
      refine ⟨7583730975748323483887291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20223282601995529290366109 7583730975748323483887291)
      ·
        refine ⟨11375596463622485225830937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7583730975748323483887291 11375596463622485225830937)
        ·
          refine ⟨8531697347716863919373203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11375596463622485225830937 8531697347716863919373203)
          ·
            refine ⟨12797546021575295879059805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8531697347716863919373203 12797546021575295879059805)
            ·
              refine ⟨4799079758090735954647427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12797546021575295879059805 4799079758090735954647427)
              ·
                refine ⟨7198619637136103931971141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799079758090735954647427 7198619637136103931971141)
                ·
                  refine ⟨1349741181963019487244589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7198619637136103931971141 1349741181963019487244589)
                  ·
                    refine ⟨506152943236132307716721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349741181963019487244589 506152943236132307716721)
                    ·
                      refine ⟨379614707427099230787541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506152943236132307716721 379614707427099230787541)
                      ·
                        rfl

theorem cell23_739297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_739297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739297 prefixEnd_739297 := by exact prefixLift 739297
  have htrace : WordTrace (prefixWord ++ tailWord_739297) baseStart_739297 baseEnd_739297 := by
    simpa [prefixWord, tailWord_739297, baseEnd_739297] using wordTrace_append hprefix tailTrace_739297
  have hstable : (prefixWord ++ tailWord_739297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739297).length < 2 ^ (prefixWord ++ tailWord_739297).sum := by decide
  have hdescent : baseEnd_739297 < baseStart_739297 := by decide
  rcases family_descends (prefixWord ++ tailWord_739297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739298 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_739298 : Nat := 118140960795 + 739298 * 2 ^ 59
def prefixEnd_739298 : Nat := 4983230072969 + 3 ^ 40 * 739298 * 2
def baseEnd_739298 : Nat := 126538406969251242291679

theorem tailTrace_739298 : CollatzResearch.WordTrace tailWord_739298 prefixEnd_739298 126538406969251242291679 := by
  unfold tailWord_739298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6741103318914270722818637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17976275517104721927516365 6741103318914270722818637)
  ·
    refine ⟨2527913744592851521056989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6741103318914270722818637 2527913744592851521056989)
    ·
      refine ⟨947967654222319320396371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2527913744592851521056989 947967654222319320396371)
      ·
        refine ⟨1421951481333478980594557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947967654222319320396371 1421951481333478980594557)
        ·
          refine ⟨533231805500054617722959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1421951481333478980594557 533231805500054617722959)
          ·
            refine ⟨799847708250081926584439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533231805500054617722959 799847708250081926584439)
            ·
              refine ⟨1199771562375122889876659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799847708250081926584439 1199771562375122889876659)
              ·
                refine ⟨1799657343562684334814989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199771562375122889876659 1799657343562684334814989)
                ·
                  refine ⟨674871503836006625555621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1799657343562684334814989 674871503836006625555621)
                  ·
                    refine ⟨126538406969251242291679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674871503836006625555621 126538406969251242291679)
                    ·
                      rfl

theorem cell23_739298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_739298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739298 prefixEnd_739298 := by exact prefixLift 739298
  have htrace : WordTrace (prefixWord ++ tailWord_739298) baseStart_739298 baseEnd_739298 := by
    simpa [prefixWord, tailWord_739298, baseEnd_739298] using wordTrace_append hprefix tailTrace_739298
  have hstable : (prefixWord ++ tailWord_739298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739298).length < 2 ^ (prefixWord ++ tailWord_739298).sum := by decide
  have hdescent : baseEnd_739298 < baseStart_739298 := by decide
  rcases family_descends (prefixWord ++ tailWord_739298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739347 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 3]
def baseStart_739347 : Nat := 118140960795 + 739347 * 2 ^ 59
def prefixEnd_739347 : Nat := 4983230072969 + 3 ^ 40 * 739347 * 2
def baseEnd_739347 : Nat := 379640381459824035162311

theorem tailTrace_739347 : CollatzResearch.WordTrace tailWord_739347 prefixEnd_739347 379640381459824035162311 := by
  unfold tailWord_739347
  simp only [CollatzResearch.WordTrace]
  refine ⟨26966200452479564259808295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17977466968319709506538863 26966200452479564259808295)
  ·
    refine ⟨40449300678719346389712443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26966200452479564259808295 40449300678719346389712443)
    ·
      refine ⟨60673951018079019584568665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40449300678719346389712443 60673951018079019584568665)
      ·
        refine ⟨45505463263559264688426499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60673951018079019584568665 45505463263559264688426499)
        ·
          refine ⟨68258194895338897032639749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45505463263559264688426499 68258194895338897032639749)
          ·
            refine ⟨12798411542876043193619953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68258194895338897032639749 12798411542876043193619953)
            ·
              refine ⟨9598808657157032395214965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12798411542876043193619953 9598808657157032395214965)
              ·
                refine ⟨899888311608471787051403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9598808657157032395214965 899888311608471787051403)
                ·
                  refine ⟨1349832467412707680577105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899888311608471787051403 1349832467412707680577105)
                  ·
                    refine ⟨1012374350559530760432829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1349832467412707680577105 1012374350559530760432829)
                    ·
                      refine ⟨379640381459824035162311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1012374350559530760432829 379640381459824035162311)
                      ·
                        rfl

theorem cell23_739347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_739347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739347 prefixEnd_739347 := by exact prefixLift 739347
  have htrace : WordTrace (prefixWord ++ tailWord_739347) baseStart_739347 baseEnd_739347 := by
    simpa [prefixWord, tailWord_739347, baseEnd_739347] using wordTrace_append hprefix tailTrace_739347
  have hstable : (prefixWord ++ tailWord_739347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739347).length < 2 ^ (prefixWord ++ tailWord_739347).sum := by decide
  have hdescent : baseEnd_739347 < baseStart_739347 := by decide
  rcases family_descends (prefixWord ++ tailWord_739347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739354 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_739354 : Nat := 118140960795 + 739354 * 2 ^ 59
def prefixEnd_739354 : Nat := 4983230072969 + 3 ^ 40 * 739354 * 2
def baseEnd_739354 : Nat := 126547991941468502591593

theorem tailTrace_739354 : CollatzResearch.WordTrace tailWord_739354 prefixEnd_739354 126547991941468502591593 := by
  unfold tailWord_739354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6741613940863551113828279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17977637175636136303542077 6741613940863551113828279)
  ·
    refine ⟨10112420911295326670742419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6741613940863551113828279 10112420911295326670742419)
    ·
      refine ⟨15168631366942990006113629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10112420911295326670742419 15168631366942990006113629)
      ·
        refine ⟨5688236762603621252292611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15168631366942990006113629 5688236762603621252292611)
        ·
          refine ⟨8532355143905431878438917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5688236762603621252292611 8532355143905431878438917)
          ·
            refine ⟨1599816589482268477207297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8532355143905431878438917 1599816589482268477207297)
            ·
              refine ⟨1199862442111701357905473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599816589482268477207297 1199862442111701357905473)
              ·
                refine ⟨899896831583776018429105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199862442111701357905473 899896831583776018429105)
                ·
                  refine ⟨674922623687832013821829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 899896831583776018429105 674922623687832013821829)
                  ·
                    refine ⟨126547991941468502591593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674922623687832013821829 126547991941468502591593)
                    ·
                      rfl

theorem cell23_739354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_739354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739354 prefixEnd_739354 := by exact prefixLift 739354
  have htrace : WordTrace (prefixWord ++ tailWord_739354) baseStart_739354 baseEnd_739354 := by
    simpa [prefixWord, tailWord_739354, baseEnd_739354] using wordTrace_append hprefix tailTrace_739354
  have hstable : (prefixWord ++ tailWord_739354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739354).length < 2 ^ (prefixWord ++ tailWord_739354).sum := by decide
  have hdescent : baseEnd_739354 < baseStart_739354 := by decide
  rcases family_descends (prefixWord ++ tailWord_739354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739374 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_739374 : Nat := 118140960795 + 739374 * 2 ^ 59
def prefixEnd_739374 : Nat := 4983230072969 + 3 ^ 40 * 739374 * 2
def baseEnd_739374 : Nat := 379654245437495429524687

theorem tailTrace_739374 : CollatzResearch.WordTrace tailWord_739374 prefixEnd_739374 379654245437495429524687 := by
  unfold tailWord_739374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3370898152922718483880147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17978123482254498580694117 3370898152922718483880147)
  ·
    refine ⟨5056347229384077725820221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3370898152922718483880147 5056347229384077725820221)
    ·
      refine ⟨1896130211019029147182583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5056347229384077725820221 1896130211019029147182583)
      ·
        refine ⟨2844195316528543720773875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896130211019029147182583 2844195316528543720773875)
        ·
          refine ⟨4266292974792815581160813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844195316528543720773875 4266292974792815581160813)
          ·
            refine ⟨1599859865547305842935305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4266292974792815581160813 1599859865547305842935305)
            ·
              refine ⟨1199894899160479382201479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599859865547305842935305 1199894899160479382201479)
              ·
                refine ⟨1799842348740719073302219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199894899160479382201479 1799842348740719073302219)
                ·
                  refine ⟨2699763523111078609953329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799842348740719073302219 2699763523111078609953329)
                  ·
                    refine ⟨2024822642333308957464997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2699763523111078609953329 2024822642333308957464997)
                    ·
                      refine ⟨379654245437495429524687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2024822642333308957464997 379654245437495429524687)
                      ·
                        rfl

theorem cell23_739374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_739374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739374 prefixEnd_739374 := by exact prefixLift 739374
  have htrace : WordTrace (prefixWord ++ tailWord_739374) baseStart_739374 baseEnd_739374 := by
    simpa [prefixWord, tailWord_739374, baseEnd_739374] using wordTrace_append hprefix tailTrace_739374
  have hstable : (prefixWord ++ tailWord_739374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739374).length < 2 ^ (prefixWord ++ tailWord_739374).sum := by decide
  have hdescent : baseEnd_739374 < baseStart_739374 := by decide
  rcases family_descends (prefixWord ++ tailWord_739374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739377 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_739377 : Nat := 118140960795 + 739377 * 2 ^ 59
def prefixEnd_739377 : Nat := 4983230072969 + 3 ^ 40 * 739377 * 2
def baseEnd_739377 : Nat := 379655785879458917787173

theorem tailTrace_739377 : CollatzResearch.WordTrace tailWord_739377 prefixEnd_739377 379655785879458917787173 := by
  unfold tailWord_739377
  simp only [CollatzResearch.WordTrace]
  refine ⟨26967294642370879383400385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17978196428247252922266923 26967294642370879383400385)
  ·
    refine ⟨20225470981778159537550289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26967294642370879383400385 20225470981778159537550289)
    ·
      refine ⟨15169103236333619653162717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20225470981778159537550289 15169103236333619653162717)
      ·
        refine ⟨5688413713625107369936019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15169103236333619653162717 5688413713625107369936019)
        ·
          refine ⟨8532620570437661054904029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5688413713625107369936019 8532620570437661054904029)
          ·
            refine ⟨3199732713914122895589011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8532620570437661054904029 3199732713914122895589011)
            ·
              refine ⟨4799599070871184343383517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199732713914122895589011 4799599070871184343383517)
              ·
                refine ⟨1799849651576694128768819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4799599070871184343383517 1799849651576694128768819)
                ·
                  refine ⟨2699774477365041193153229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799849651576694128768819 2699774477365041193153229)
                  ·
                    refine ⟨1012415429011890447432461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699774477365041193153229 1012415429011890447432461)
                    ·
                      refine ⟨379655785879458917787173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1012415429011890447432461 379655785879458917787173)
                      ·
                        rfl

theorem cell23_739377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_739377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739377 prefixEnd_739377 := by exact prefixLift 739377
  have htrace : WordTrace (prefixWord ++ tailWord_739377) baseStart_739377 baseEnd_739377 := by
    simpa [prefixWord, tailWord_739377, baseEnd_739377] using wordTrace_append hprefix tailTrace_739377
  have hstable : (prefixWord ++ tailWord_739377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739377).length < 2 ^ (prefixWord ++ tailWord_739377).sum := by decide
  have hdescent : baseEnd_739377 < baseStart_739377 := by decide
  rcases family_descends (prefixWord ++ tailWord_739377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739400 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_739400 : Nat := 118140960795 + 739400 * 2 ^ 59
def prefixEnd_739400 : Nat := 4983230072969 + 3 ^ 40 * 739400 * 2
def baseEnd_739400 : Nat := 379667595934512327799567

theorem tailTrace_739400 : CollatzResearch.WordTrace tailWord_739400 prefixEnd_739400 379667595934512327799567 := by
  unfold tailWord_739400
  simp only [CollatzResearch.WordTrace]
  refine ⟨13484066760643777155743827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17978755680858369540991769 13484066760643777155743827)
  ·
    refine ⟨20226100140965665733615741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13484066760643777155743827 20226100140965665733615741)
    ·
      refine ⟨7584787552862124650105903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20226100140965665733615741 7584787552862124650105903)
      ·
        refine ⟨11377181329293186975158855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584787552862124650105903 11377181329293186975158855)
        ·
          refine ⟨17065771993939780462738283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377181329293186975158855 17065771993939780462738283)
          ·
            refine ⟨25598657990909670694107425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17065771993939780462738283 25598657990909670694107425)
            ·
              refine ⟨19198993493182253020580569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25598657990909670694107425 19198993493182253020580569)
              ·
                refine ⟨14399245119886689765435427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19198993493182253020580569 14399245119886689765435427)
                ·
                  refine ⟨21598867679830034648153141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14399245119886689765435427 21598867679830034648153141)
                  ·
                    refine ⟨2024893844984065748264357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21598867679830034648153141 2024893844984065748264357)
                    ·
                      refine ⟨379667595934512327799567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2024893844984065748264357 379667595934512327799567)
                      ·
                        rfl

theorem cell23_739400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_739400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739400 prefixEnd_739400 := by exact prefixLift 739400
  have htrace : WordTrace (prefixWord ++ tailWord_739400) baseStart_739400 baseEnd_739400 := by
    simpa [prefixWord, tailWord_739400, baseEnd_739400] using wordTrace_append hprefix tailTrace_739400
  have hstable : (prefixWord ++ tailWord_739400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739400).length < 2 ^ (prefixWord ++ tailWord_739400).sum := by decide
  have hdescent : baseEnd_739400 < baseStart_739400 := by decide
  rcases family_descends (prefixWord ++ tailWord_739400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739437 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_739437 : Nat := 118140960795 + 739437 * 2 ^ 59
def prefixEnd_739437 : Nat := 4983230072969 + 3 ^ 40 * 739437 * 2
def baseEnd_739437 : Nat := 379686594718728683036897

theorem tailTrace_739437 : CollatzResearch.WordTrace tailWord_739437 prefixEnd_739437 379686594718728683036897 := by
  unfold tailWord_739437
  simp only [CollatzResearch.WordTrace]
  refine ⟨26969483022153509630584565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17979655348102339753723043 26969483022153509630584565)
  ·
    refine ⟨2528389033326891527867303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26969483022153509630584565 2528389033326891527867303)
    ·
      refine ⟨3792583549990337291800955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528389033326891527867303 3792583549990337291800955)
      ·
        refine ⟨5688875324985505937701433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792583549990337291800955 5688875324985505937701433)
        ·
          refine ⟨4266656493739129453276075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5688875324985505937701433 4266656493739129453276075)
          ·
            refine ⟨6399984740608694179914113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266656493739129453276075 6399984740608694179914113)
            ·
              refine ⟨4799988555456520634935585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6399984740608694179914113 4799988555456520634935585)
              ·
                refine ⟨3599991416592390476201689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4799988555456520634935585 3599991416592390476201689)
                ·
                  refine ⟨2699993562444292857151267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3599991416592390476201689 2699993562444292857151267)
                  ·
                    refine ⟨4049990343666439285726901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2699993562444292857151267 4049990343666439285726901)
                    ·
                      refine ⟨379686594718728683036897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4049990343666439285726901 379686594718728683036897)
                      ·
                        rfl

theorem cell23_739437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_739437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739437 prefixEnd_739437 := by exact prefixLift 739437
  have htrace : WordTrace (prefixWord ++ tailWord_739437) baseStart_739437 baseEnd_739437 := by
    simpa [prefixWord, tailWord_739437, baseEnd_739437] using wordTrace_append hprefix tailTrace_739437
  have hstable : (prefixWord ++ tailWord_739437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739437).length < 2 ^ (prefixWord ++ tailWord_739437).sum := by decide
  have hdescent : baseEnd_739437 < baseStart_739437 := by decide
  rcases family_descends (prefixWord ++ tailWord_739437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739485 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_739485 : Nat := 118140960795 + 739485 * 2 ^ 59
def prefixEnd_739485 : Nat := 4983230072969 + 3 ^ 40 * 739485 * 2
def baseEnd_739485 : Nat := 379711241790144495236677

theorem tailTrace_739485 : CollatzResearch.WordTrace tailWord_739485 prefixEnd_739485 379711241790144495236677 := by
  unfold tailWord_739485
  simp only [CollatzResearch.WordTrace]
  refine ⟨26971233725979613828331909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17980822483986409218887939 26971233725979613828331909)
  ·
    refine ⟨5057106323621177592812233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26971233725979613828331909 5057106323621177592812233)
    ·
      refine ⟨3792829742715883194609175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5057106323621177592812233 3792829742715883194609175)
      ·
        refine ⟨5689244614073824791913763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792829742715883194609175 5689244614073824791913763)
        ·
          refine ⟨8533866921110737187870645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5689244614073824791913763 8533866921110737187870645)
          ·
            refine ⟨800050023854131611362873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8533866921110737187870645 800050023854131611362873)
            ·
              refine ⟨600037517890598708522155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800050023854131611362873 600037517890598708522155)
              ·
                refine ⟨900056276835898062783233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600037517890598708522155 900056276835898062783233)
                ·
                  refine ⟨675042207626923547087425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 900056276835898062783233 675042207626923547087425)
                  ·
                    refine ⟨506281655720192660315569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 675042207626923547087425 506281655720192660315569)
                    ·
                      refine ⟨379711241790144495236677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506281655720192660315569 379711241790144495236677)
                      ·
                        rfl

theorem cell23_739485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_739485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739485 prefixEnd_739485 := by exact prefixLift 739485
  have htrace : WordTrace (prefixWord ++ tailWord_739485) baseStart_739485 baseEnd_739485 := by
    simpa [prefixWord, tailWord_739485, baseEnd_739485] using wordTrace_append hprefix tailTrace_739485
  have hstable : (prefixWord ++ tailWord_739485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739485).length < 2 ^ (prefixWord ++ tailWord_739485).sum := by decide
  have hdescent : baseEnd_739485 < baseStart_739485 := by decide
  rcases family_descends (prefixWord ++ tailWord_739485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739527 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_739527 : Nat := 118140960795 + 739527 * 2 ^ 59
def prefixEnd_739527 : Nat := 4983230072969 + 3 ^ 40 * 739527 * 2
def baseEnd_739527 : Nat := 379732807977633330911483

theorem tailTrace_739527 : CollatzResearch.WordTrace tailWord_739527 prefixEnd_739527 379732807977633330911483 := by
  unfold tailWord_739527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26972765591827455001360835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17981843727884970000907223 26972765591827455001360835)
  ·
    refine ⟨40459148387741182502041253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26972765591827455001360835 40459148387741182502041253)
    ·
      refine ⟨7586090322701471719132735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40459148387741182502041253 7586090322701471719132735)
      ·
        refine ⟨11379135484052207578699103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7586090322701471719132735 11379135484052207578699103)
        ·
          refine ⟨17068703226078311368048655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11379135484052207578699103 17068703226078311368048655)
          ·
            refine ⟨25603054839117467052072983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17068703226078311368048655 25603054839117467052072983)
            ·
              refine ⟨38404582258676200578109475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25603054839117467052072983 38404582258676200578109475)
              ·
                refine ⟨57606873388014300867164213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38404582258676200578109475 57606873388014300867164213)
                ·
                  refine ⟨5400644380126340706296645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57606873388014300867164213 5400644380126340706296645)
                  ·
                    refine ⟨1012620821273688882430621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400644380126340706296645 1012620821273688882430621)
                    ·
                      refine ⟨379732807977633330911483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1012620821273688882430621 379732807977633330911483)
                      ·
                        rfl

theorem cell23_739527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_739527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739527 prefixEnd_739527 := by exact prefixLift 739527
  have htrace : WordTrace (prefixWord ++ tailWord_739527) baseStart_739527 baseEnd_739527 := by
    simpa [prefixWord, tailWord_739527, baseEnd_739527] using wordTrace_append hprefix tailTrace_739527
  have hstable : (prefixWord ++ tailWord_739527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739527).length < 2 ^ (prefixWord ++ tailWord_739527).sum := by decide
  have hdescent : baseEnd_739527 < baseStart_739527 := by decide
  rcases family_descends (prefixWord ++ tailWord_739527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739577 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 5, 5]
def baseStart_739577 : Nat := 118140960795 + 739577 * 2 ^ 59
def prefixEnd_739577 : Nat := 4983230072969 + 3 ^ 40 * 739577 * 2
def baseEnd_739577 : Nat := 126586160670119378428751

theorem tailTrace_739577 : CollatzResearch.WordTrace tailWord_739577 prefixEnd_739577 126586160670119378428751 := by
  unfold tailWord_739577
  simp only [CollatzResearch.WordTrace]
  refine ⟨26974589241646313540680985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17983059494430875693787323 26974589241646313540680985)
  ·
    refine ⟨20230941931234735155510739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26974589241646313540680985 20230941931234735155510739)
    ·
      refine ⟨30346412896852102733266109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20230941931234735155510739 30346412896852102733266109)
      ·
        refine ⟨11379904836319538524974791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30346412896852102733266109 11379904836319538524974791)
        ·
          refine ⟨17069857254479307787462187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11379904836319538524974791 17069857254479307787462187)
          ·
            refine ⟨25604785881718961681193281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17069857254479307787462187 25604785881718961681193281)
            ·
              refine ⟨19203589411289221260894961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25604785881718961681193281 19203589411289221260894961)
              ·
                refine ⟨14402692058466915945671221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19203589411289221260894961 14402692058466915945671221)
                ·
                  refine ⟨1350252380481273369906677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14402692058466915945671221 1350252380481273369906677)
                  ·
                    refine ⟨126586160670119378428751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1350252380481273369906677 126586160670119378428751)
                    ·
                      rfl

theorem cell23_739577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_739577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739577 prefixEnd_739577 := by exact prefixLift 739577
  have htrace : WordTrace (prefixWord ++ tailWord_739577) baseStart_739577 baseEnd_739577 := by
    simpa [prefixWord, tailWord_739577, baseEnd_739577] using wordTrace_append hprefix tailTrace_739577
  have hstable : (prefixWord ++ tailWord_739577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739577).length < 2 ^ (prefixWord ++ tailWord_739577).sum := by decide
  have hdescent : baseEnd_739577 < baseStart_739577 := by decide
  rcases family_descends (prefixWord ++ tailWord_739577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739631 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 5, 2, 2]
def baseStart_739631 : Nat := 118140960795 + 739631 * 2 ^ 59
def prefixEnd_739631 : Nat := 4983230072969 + 3 ^ 40 * 739631 * 2
def baseEnd_739631 : Nat := 379786209965700924011005

theorem tailTrace_739631 : CollatzResearch.WordTrace tailWord_739631 prefixEnd_739631 379786209965700924011005 := by
  unfold tailWord_739631
  simp only [CollatzResearch.WordTrace]
  refine ⟨26976558783450680763146747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17984372522300453842097831 26976558783450680763146747)
  ·
    refine ⟨40464838175176021144720121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26976558783450680763146747 40464838175176021144720121)
    ·
      refine ⟨30348628631382015858540091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40464838175176021144720121 30348628631382015858540091)
      ·
        refine ⟨45522942947073023787810137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30348628631382015858540091 45522942947073023787810137)
        ·
          refine ⟨34142207210304767840857603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45522942947073023787810137 34142207210304767840857603)
          ·
            refine ⟨51213310815457151761286405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34142207210304767840857603 51213310815457151761286405)
            ·
              refine ⟨9602495777898215955241201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51213310815457151761286405 9602495777898215955241201)
              ·
                refine ⟨7201871833423661966430901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9602495777898215955241201 7201871833423661966430901)
                ·
                  refine ⟨675175484383468309352897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7201871833423661966430901 675175484383468309352897)
                  ·
                    refine ⟨506381613287601232014673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 675175484383468309352897 506381613287601232014673)
                    ·
                      refine ⟨379786209965700924011005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506381613287601232014673 379786209965700924011005)
                      ·
                        rfl

theorem cell23_739631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 2, 2].length) (baseStart_739631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739631 prefixEnd_739631 := by exact prefixLift 739631
  have htrace : WordTrace (prefixWord ++ tailWord_739631) baseStart_739631 baseEnd_739631 := by
    simpa [prefixWord, tailWord_739631, baseEnd_739631] using wordTrace_append hprefix tailTrace_739631
  have hstable : (prefixWord ++ tailWord_739631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739631).length < 2 ^ (prefixWord ++ tailWord_739631).sum := by decide
  have hdescent : baseEnd_739631 < baseStart_739631 := by decide
  rcases family_descends (prefixWord ++ tailWord_739631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739641 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 4, 4]
def baseStart_739641 : Nat := 118140960795 + 739641 * 2 ^ 59
def prefixEnd_739641 : Nat := 4983230072969 + 3 ^ 40 * 739641 * 2
def baseEnd_739641 : Nat := 126597114924081961628653

theorem tailTrace_739641 : CollatzResearch.WordTrace tailWord_739641 prefixEnd_739641 126597114924081961628653 := by
  unfold tailWord_739641
  simp only [CollatzResearch.WordTrace]
  refine ⟨26976923513414452471010777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17984615675609634980673851 26976923513414452471010777)
  ·
    refine ⟨20232692635060839353258083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26976923513414452471010777 20232692635060839353258083)
    ·
      refine ⟨30349038952591259029887125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20232692635060839353258083 30349038952591259029887125)
      ·
        refine ⟨1422611200902715267025959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30349038952591259029887125 1422611200902715267025959)
        ·
          refine ⟨2133916801354072900538939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422611200902715267025959 2133916801354072900538939)
          ·
            refine ⟨3200875202031109350808409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133916801354072900538939 3200875202031109350808409)
            ·
              refine ⟨2400656401523332013106307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3200875202031109350808409 2400656401523332013106307)
              ·
                refine ⟨3600984602284998019659461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400656401523332013106307 3600984602284998019659461)
                ·
                  refine ⟨675184612928437128686149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3600984602284998019659461 675184612928437128686149)
                  ·
                    refine ⟨126597114924081961628653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675184612928437128686149 126597114924081961628653)
                    ·
                      rfl

theorem cell23_739641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_739641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739641 prefixEnd_739641 := by exact prefixLift 739641
  have htrace : WordTrace (prefixWord ++ tailWord_739641) baseStart_739641 baseEnd_739641 := by
    simpa [prefixWord, tailWord_739641, baseEnd_739641] using wordTrace_append hprefix tailTrace_739641
  have hstable : (prefixWord ++ tailWord_739641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739641).length < 2 ^ (prefixWord ++ tailWord_739641).sum := by decide
  have hdescent : baseEnd_739641 < baseStart_739641 := by decide
  rcases family_descends (prefixWord ++ tailWord_739641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739657 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_739657 : Nat := 118140960795 + 739657 * 2 ^ 59
def prefixEnd_739657 : Nat := 4983230072969 + 3 ^ 40 * 739657 * 2
def baseEnd_739657 : Nat := 379799560462717822285885

theorem tailTrace_739657 : CollatzResearch.WordTrace tailWord_739657 prefixEnd_739657 379799560462717822285885 := by
  unfold tailWord_739657
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977507081356487203593225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17985004720904324802395483 26977507081356487203593225)
  ·
    refine ⟨20233130311017365402694919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26977507081356487203593225 20233130311017365402694919)
    ·
      refine ⟨30349695466526048104042379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20233130311017365402694919 30349695466526048104042379)
      ·
        refine ⟨45524543199789072156063569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30349695466526048104042379 45524543199789072156063569)
        ·
          refine ⟨34143407399841804117047677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45524543199789072156063569 34143407399841804117047677)
          ·
            refine ⟨12803777774940676543892879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34143407399841804117047677 12803777774940676543892879)
            ·
              refine ⟨19205666662411014815839319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803777774940676543892879 19205666662411014815839319)
              ·
                refine ⟨28808499993616522223758979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19205666662411014815839319 28808499993616522223758979)
                ·
                  refine ⟨43212749990424783335638469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28808499993616522223758979 43212749990424783335638469)
                  ·
                    refine ⟨8102390623204646875432213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43212749990424783335638469 8102390623204646875432213)
                    ·
                      refine ⟨379799560462717822285885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8102390623204646875432213 379799560462717822285885)
                      ·
                        rfl

theorem cell23_739657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_739657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739657 prefixEnd_739657 := by exact prefixLift 739657
  have htrace : WordTrace (prefixWord ++ tailWord_739657) baseStart_739657 baseEnd_739657 := by
    simpa [prefixWord, tailWord_739657, baseEnd_739657] using wordTrace_append hprefix tailTrace_739657
  have hstable : (prefixWord ++ tailWord_739657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739657).length < 2 ^ (prefixWord ++ tailWord_739657).sum := by decide
  have hdescent : baseEnd_739657 < baseStart_739657 := by decide
  rcases family_descends (prefixWord ++ tailWord_739657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739667 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 4, 7]
def baseStart_739667 : Nat := 118140960795 + 739667 * 2 ^ 59
def prefixEnd_739667 : Nat := 4983230072969 + 3 ^ 40 * 739667 * 2
def baseEnd_739667 : Nat := 126601565089754261053613

theorem tailTrace_739667 : CollatzResearch.WordTrace tailWord_739667 prefixEnd_739667 126601565089754261053613 := by
  unfold tailWord_739667
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977871811320258911457255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17985247874213505940971503 26977871811320258911457255)
  ·
    refine ⟨40466807716980388367185883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26977871811320258911457255 40466807716980388367185883)
    ·
      refine ⟨60700211575470582550778825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40466807716980388367185883 60700211575470582550778825)
      ·
        refine ⟨45525158681602936913084119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60700211575470582550778825 45525158681602936913084119)
        ·
          refine ⟨68287738022404405369626179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45525158681602936913084119 68287738022404405369626179)
          ·
            refine ⟨102431607033606608054439269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68287738022404405369626179 102431607033606608054439269)
            ·
              refine ⟨19205926318801239010207363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102431607033606608054439269 19205926318801239010207363)
              ·
                refine ⟨28808889478201858515311045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19205926318801239010207363 28808889478201858515311045)
                ·
                  refine ⟨5401666777162848471620821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28808889478201858515311045 5401666777162848471620821)
                  ·
                    refine ⟨126601565089754261053613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5401666777162848471620821 126601565089754261053613)
                    ·
                      rfl

theorem cell23_739667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 7].length) (baseStart_739667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739667 prefixEnd_739667 := by exact prefixLift 739667
  have htrace : WordTrace (prefixWord ++ tailWord_739667) baseStart_739667 baseEnd_739667 := by
    simpa [prefixWord, tailWord_739667, baseEnd_739667] using wordTrace_append hprefix tailTrace_739667
  have hstable : (prefixWord ++ tailWord_739667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739667).length < 2 ^ (prefixWord ++ tailWord_739667).sum := by decide
  have hdescent : baseEnd_739667 < baseStart_739667 := by decide
  rcases family_descends (prefixWord ++ tailWord_739667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739668 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_739668 : Nat := 118140960795 + 739668 * 2 ^ 59
def prefixEnd_739668 : Nat := 4983230072969 + 3 ^ 40 * 739668 * 2
def baseEnd_739668 : Nat := 379805208749917279248335

theorem tailTrace_739668 : CollatzResearch.WordTrace tailWord_739668 prefixEnd_739668 379805208749917279248335 := by
  unfold tailWord_739668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488954142158318041121829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17985272189544424054829105 13488954142158318041121829)
  ·
    refine ⟨2529178901654684632710343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13488954142158318041121829 2529178901654684632710343)
    ·
      refine ⟨3793768352482026949065515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2529178901654684632710343 3793768352482026949065515)
      ·
        refine ⟨5690652528723040423598273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793768352482026949065515 5690652528723040423598273)
        ·
          refine ⟨4267989396542280317698705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5690652528723040423598273 4267989396542280317698705)
          ·
            refine ⟨3200992047406710238274029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267989396542280317698705 3200992047406710238274029)
            ·
              refine ⟨1200372017777516339352761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3200992047406710238274029 1200372017777516339352761)
              ·
                refine ⟨900279013333137254514571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200372017777516339352761 900279013333137254514571)
                ·
                  refine ⟨1350418519999705881771857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900279013333137254514571 1350418519999705881771857)
                  ·
                    refine ⟨1012813889999779411328893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1350418519999705881771857 1012813889999779411328893)
                    ·
                      refine ⟨379805208749917279248335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1012813889999779411328893 379805208749917279248335)
                      ·
                        rfl

theorem cell23_739668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_739668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739668 prefixEnd_739668 := by exact prefixLift 739668
  have htrace : WordTrace (prefixWord ++ tailWord_739668) baseStart_739668 baseEnd_739668 := by
    simpa [prefixWord, tailWord_739668, baseEnd_739668] using wordTrace_append hprefix tailTrace_739668
  have hstable : (prefixWord ++ tailWord_739668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739668).length < 2 ^ (prefixWord ++ tailWord_739668).sum := by decide
  have hdescent : baseEnd_739668 < baseStart_739668 := by decide
  rcases family_descends (prefixWord ++ tailWord_739668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739698 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_739698 : Nat := 118140960795 + 739698 * 2 ^ 59
def prefixEnd_739698 : Nat := 4983230072969 + 3 ^ 40 * 739698 * 2
def baseEnd_739698 : Nat := 379820613169552161873197

theorem tailTrace_739698 : CollatzResearch.WordTrace tailWord_739698 prefixEnd_739698 379820613169552161873197 := by
  unfold tailWord_739698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744750618551987801458937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17986001649471967470557165 6744750618551987801458937)
  ·
    refine ⟨5058562963913990851094203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6744750618551987801458937 5058562963913990851094203)
    ·
      refine ⟨7587844445870986276641305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5058562963913990851094203 7587844445870986276641305)
      ·
        refine ⟨5690883334403239707480979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7587844445870986276641305 5690883334403239707480979)
        ·
          refine ⟨8536325001604859561221469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690883334403239707480979 8536325001604859561221469)
          ·
            refine ⟨3201121875601822335458051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8536325001604859561221469 3201121875601822335458051)
            ·
              refine ⟨4801682813402733503187077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201121875601822335458051 4801682813402733503187077)
              ·
                refine ⟨900315527513012531847577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4801682813402733503187077 900315527513012531847577)
                ·
                  refine ⟨675236645634759398885683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 900315527513012531847577 675236645634759398885683)
                  ·
                    refine ⟨1012854968452139098328525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 675236645634759398885683 1012854968452139098328525)
                    ·
                      refine ⟨379820613169552161873197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1012854968452139098328525 379820613169552161873197)
                      ·
                        rfl

theorem cell23_739698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_739698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739698 prefixEnd_739698 := by exact prefixLift 739698
  have htrace : WordTrace (prefixWord ++ tailWord_739698) baseStart_739698 baseEnd_739698 := by
    simpa [prefixWord, tailWord_739698, baseEnd_739698] using wordTrace_append hprefix tailTrace_739698
  have hstable : (prefixWord ++ tailWord_739698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739698).length < 2 ^ (prefixWord ++ tailWord_739698).sum := by decide
  have hdescent : baseEnd_739698 < baseStart_739698 := by decide
  rcases family_descends (prefixWord ++ tailWord_739698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739738 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2]
def baseStart_739738 : Nat := 118140960795 + 739738 * 2 ^ 59
def prefixEnd_739738 : Nat := 4983230072969 + 3 ^ 40 * 739738 * 2
def baseEnd_739738 : Nat := 379841152395732005373013

theorem tailTrace_739738 : CollatzResearch.WordTrace tailWord_739738 prefixEnd_739738 379841152395732005373013 := by
  unfold tailWord_739738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745115348515759509322967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17986974262708692024861245 6745115348515759509322967)
  ·
    refine ⟨10117673022773639263984451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6745115348515759509322967 10117673022773639263984451)
    ·
      refine ⟨15176509534160458895976677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10117673022773639263984451 15176509534160458895976677)
      ·
        refine ⟨2845595537655086042995627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15176509534160458895976677 2845595537655086042995627)
        ·
          refine ⟨4268393306482629064493441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845595537655086042995627 4268393306482629064493441)
          ·
            refine ⟨3201294979861971798370081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268393306482629064493441 3201294979861971798370081)
            ·
              refine ⟨2400971234896478848777561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3201294979861971798370081 2400971234896478848777561)
              ·
                refine ⟨1800728426172359136583171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400971234896478848777561 1800728426172359136583171)
                ·
                  refine ⟨2701092639258538704874757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800728426172359136583171 2701092639258538704874757)
                  ·
                    refine ⟨506454869860976007164017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2701092639258538704874757 506454869860976007164017)
                    ·
                      refine ⟨379841152395732005373013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506454869860976007164017 379841152395732005373013)
                      ·
                        rfl

theorem cell23_739738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_739738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739738 prefixEnd_739738 := by exact prefixLift 739738
  have htrace : WordTrace (prefixWord ++ tailWord_739738) baseStart_739738 baseEnd_739738 := by
    simpa [prefixWord, tailWord_739738, baseEnd_739738] using wordTrace_append hprefix tailTrace_739738
  have hstable : (prefixWord ++ tailWord_739738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739738).length < 2 ^ (prefixWord ++ tailWord_739738).sum := by decide
  have hdescent : baseEnd_739738 < baseStart_739738 := by decide
  rcases family_descends (prefixWord ++ tailWord_739738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739742 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_739742 : Nat := 118140960795 + 739742 * 2 ^ 59
def prefixEnd_739742 : Nat := 4983230072969 + 3 ^ 40 * 739742 * 2
def baseEnd_739742 : Nat := 379843206318349989722995

theorem tailTrace_739742 : CollatzResearch.WordTrace tailWord_739742 prefixEnd_739742 379843206318349989722995 := by
  unfold tailWord_739742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372575910756068340054685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17987071524032364480291653 3372575910756068340054685)
  ·
    refine ⟨1264715966533525627520507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3372575910756068340054685 1264715966533525627520507)
    ·
      refine ⟨1897073949800288441280761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264715966533525627520507 1897073949800288441280761)
      ·
        refine ⟨1422805462350216330960571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1897073949800288441280761 1422805462350216330960571)
        ·
          refine ⟨2134208193525324496440857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422805462350216330960571 2134208193525324496440857)
          ·
            refine ⟨1600656145143993372330643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134208193525324496440857 1600656145143993372330643)
            ·
              refine ⟨2400984217715990058495965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600656145143993372330643 2400984217715990058495965)
              ·
                refine ⟨900369081643496271935987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2400984217715990058495965 900369081643496271935987)
                ·
                  refine ⟨1350553622465244407903981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900369081643496271935987 1350553622465244407903981)
                  ·
                    refine ⟨506457608424466652963993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350553622465244407903981 506457608424466652963993)
                    ·
                      refine ⟨379843206318349989722995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506457608424466652963993 379843206318349989722995)
                      ·
                        rfl

theorem cell23_739742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_739742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739742 prefixEnd_739742 := by exact prefixLift 739742
  have htrace : WordTrace (prefixWord ++ tailWord_739742) baseStart_739742 baseEnd_739742 := by
    simpa [prefixWord, tailWord_739742, baseEnd_739742] using wordTrace_append hprefix tailTrace_739742
  have hstable : (prefixWord ++ tailWord_739742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739742).length < 2 ^ (prefixWord ++ tailWord_739742).sum := by decide
  have hdescent : baseEnd_739742 < baseStart_739742 := by decide
  rcases family_descends (prefixWord ++ tailWord_739742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739751 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_739751 : Nat := 118140960795 + 739751 * 2 ^ 59
def prefixEnd_739751 : Nat := 4983230072969 + 3 ^ 40 * 739751 * 2
def baseEnd_739751 : Nat := 379847827644240454510453

theorem tailTrace_739751 : CollatzResearch.WordTrace tailWord_739751 prefixEnd_739751 379847827644240454510453 := by
  unfold tailWord_739751
  simp only [CollatzResearch.WordTrace]
  refine ⟨26980935543015941257515107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17987290362010627505010071 26980935543015941257515107)
  ·
    refine ⟨40471403314523911886272661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26980935543015941257515107 40471403314523911886272661)
    ·
      refine ⟨1897097030368308369669031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40471403314523911886272661 1897097030368308369669031)
      ·
        refine ⟨2845645545552462554503547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897097030368308369669031 2845645545552462554503547)
        ·
          refine ⟨4268468318328693831755321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845645545552462554503547 4268468318328693831755321)
          ·
            refine ⟨3201351238746520373816491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268468318328693831755321 3201351238746520373816491)
            ·
              refine ⟨4802026858119780560724737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201351238746520373816491 4802026858119780560724737)
              ·
                refine ⟨3601520143589835420543553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802026858119780560724737 3601520143589835420543553)
                ·
                  refine ⟨2701140107692376565407665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601520143589835420543553 2701140107692376565407665)
                  ·
                    refine ⟨2025855080769282424055749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701140107692376565407665 2025855080769282424055749)
                    ·
                      refine ⟨379847827644240454510453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2025855080769282424055749 379847827644240454510453)
                      ·
                        rfl

theorem cell23_739751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_739751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739751 prefixEnd_739751 := by exact prefixLift 739751
  have htrace : WordTrace (prefixWord ++ tailWord_739751) baseStart_739751 baseEnd_739751 := by
    simpa [prefixWord, tailWord_739751, baseEnd_739751] using wordTrace_append hprefix tailTrace_739751
  have hstable : (prefixWord ++ tailWord_739751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739751).length < 2 ^ (prefixWord ++ tailWord_739751).sum := by decide
  have hdescent : baseEnd_739751 < baseStart_739751 := by decide
  rcases family_descends (prefixWord ++ tailWord_739751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739761 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 7]
def baseStart_739761 : Nat := 118140960795 + 739761 * 2 ^ 59
def prefixEnd_739761 : Nat := 4983230072969 + 3 ^ 40 * 739761 * 2
def baseEnd_739761 : Nat := 42205884716753935042823

theorem tailTrace_739761 : CollatzResearch.WordTrace tailWord_739761 prefixEnd_739761 42205884716753935042823 := by
  unfold tailWord_739761
  simp only [CollatzResearch.WordTrace]
  refine ⟨26981300272979712965379137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17987533515319808643586091 26981300272979712965379137)
  ·
    refine ⟨20235975204734784724034353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26981300272979712965379137 20235975204734784724034353)
    ·
      refine ⟨15176981403551088543025765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20235975204734784724034353 15176981403551088543025765)
      ·
        refine ⟨2845684013165829101817331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15176981403551088543025765 2845684013165829101817331)
        ·
          refine ⟨4268526019748743652725997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845684013165829101817331 4268526019748743652725997)
          ·
            refine ⟨1600697257405778869772249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4268526019748743652725997 1600697257405778869772249)
            ·
              refine ⟨1200522943054334152329187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600697257405778869772249 1200522943054334152329187)
              ·
                refine ⟨1800784414581501228493781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200522943054334152329187 1800784414581501228493781)
                ·
                  refine ⟨42205884716753935042823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1800784414581501228493781 42205884716753935042823)
                  ·
                    rfl

theorem cell23_739761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 7].length) (baseStart_739761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739761 prefixEnd_739761 := by exact prefixLift 739761
  have htrace : WordTrace (prefixWord ++ tailWord_739761) baseStart_739761 baseEnd_739761 := by
    simpa [prefixWord, tailWord_739761, baseEnd_739761] using wordTrace_append hprefix tailTrace_739761
  have hstable : (prefixWord ++ tailWord_739761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739761).length < 2 ^ (prefixWord ++ tailWord_739761).sum := by decide
  have hdescent : baseEnd_739761 < baseStart_739761 := by decide
  rcases family_descends (prefixWord ++ tailWord_739761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739834 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 10]
def baseStart_739834 : Nat := 118140960795 + 739834 * 2 ^ 59
def prefixEnd_739834 : Nat := 4983230072969 + 3 ^ 40 * 739834 * 2
def baseEnd_739834 : Nat := 42210049615395958863619

theorem tailTrace_739834 : CollatzResearch.WordTrace tailWord_739834 prefixEnd_739834 42210049615395958863619 := by
  unfold tailWord_739834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745990700428811608196639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17989308534476830955191037 6745990700428811608196639)
  ·
    refine ⟨10118986050643217412294959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6745990700428811608196639 10118986050643217412294959)
    ·
      refine ⟨15178479075964826118442439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10118986050643217412294959 15178479075964826118442439)
      ·
        refine ⟨22767718613947239177663659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15178479075964826118442439 22767718613947239177663659)
        ·
          refine ⟨34151577920920858766495489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22767718613947239177663659 34151577920920858766495489)
          ·
            refine ⟨25613683440690644074871617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34151577920920858766495489 25613683440690644074871617)
            ·
              refine ⟨19210262580517983056153713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25613683440690644074871617 19210262580517983056153713)
              ·
                refine ⟨14407696935388487292115285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19210262580517983056153713 14407696935388487292115285)
                ·
                  refine ⟨42210049615395958863619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14407696935388487292115285 42210049615395958863619)
                  ·
                    rfl

theorem cell23_739834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_739834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739834 prefixEnd_739834 := by exact prefixLift 739834
  have htrace : WordTrace (prefixWord ++ tailWord_739834) baseStart_739834 baseEnd_739834 := by
    simpa [prefixWord, tailWord_739834, baseEnd_739834] using wordTrace_append hprefix tailTrace_739834
  have hstable : (prefixWord ++ tailWord_739834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739834).length < 2 ^ (prefixWord ++ tailWord_739834).sum := by decide
  have hdescent : baseEnd_739834 < baseStart_739834 := by decide
  rcases family_descends (prefixWord ++ tailWord_739834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739868 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 6]
def baseStart_739868 : Nat := 118140960795 + 739868 * 2 ^ 59
def prefixEnd_739868 : Nat := 4983230072969 + 3 ^ 40 * 739868 * 2
def baseEnd_739868 : Nat := 42211989431201832971935

theorem tailTrace_739868 : CollatzResearch.WordTrace tailWord_739868 prefixEnd_739868 42211989431201832971935 := by
  unfold tailWord_739868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492601441796035119762129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17990135255728046826349505 13492601441796035119762129)
  ·
    refine ⟨10119451081347026339821597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13492601441796035119762129 10119451081347026339821597)
    ·
      refine ⟨3794794155505134877433099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10119451081347026339821597 3794794155505134877433099)
      ·
        refine ⟨5692191233257702316149649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794794155505134877433099 5692191233257702316149649)
        ·
          refine ⟨4269143424943276737112237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5692191233257702316149649 4269143424943276737112237)
          ·
            refine ⟨1600928784353728776417089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4269143424943276737112237 1600928784353728776417089)
            ·
              refine ⟨1200696588265296582312817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600928784353728776417089 1200696588265296582312817)
              ·
                refine ⟨900522441198972436734613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200696588265296582312817 900522441198972436734613)
                ·
                  refine ⟨42211989431201832971935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 900522441198972436734613 42211989431201832971935)
                  ·
                    rfl

theorem cell23_739868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_739868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739868 prefixEnd_739868 := by exact prefixLift 739868
  have htrace : WordTrace (prefixWord ++ tailWord_739868) baseStart_739868 baseEnd_739868 := by
    simpa [prefixWord, tailWord_739868, baseEnd_739868] using wordTrace_append hprefix tailTrace_739868
  have hstable : (prefixWord ++ tailWord_739868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739868).length < 2 ^ (prefixWord ++ tailWord_739868).sum := by decide
  have hdescent : baseEnd_739868 < baseStart_739868 := by decide
  rcases family_descends (prefixWord ++ tailWord_739868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739872 : List Nat := [2, 1, 1, 6, 2, 1, 1, 4, 1, 4]
def baseStart_739872 : Nat := 118140960795 + 739872 * 2 ^ 59
def prefixEnd_739872 : Nat := 4983230072969 + 3 ^ 40 * 739872 * 2
def baseEnd_739872 : Nat := 126636652934478160365799

theorem tailTrace_739872 : CollatzResearch.WordTrace tailWord_739872 prefixEnd_739872 126636652934478160365799 := by
  unfold tailWord_739872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492674387788789461334935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17990232517051719281779913 13492674387788789461334935)
  ·
    refine ⟨20239011581683184192002403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13492674387788789461334935 20239011581683184192002403)
    ·
      refine ⟨30358517372524776288003605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20239011581683184192002403 30358517372524776288003605)
      ·
        refine ⟨1423055501837098888500169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30358517372524776288003605 1423055501837098888500169)
        ·
          refine ⟨1067291626377824166375127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423055501837098888500169 1067291626377824166375127)
          ·
            refine ⟨1600937439566736249562691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067291626377824166375127 1600937439566736249562691)
            ·
              refine ⟨2401406159350104374344037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600937439566736249562691 2401406159350104374344037)
              ·
                refine ⟨450263654878144570189507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2401406159350104374344037 450263654878144570189507)
                ·
                  refine ⟨675395482317216855284261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450263654878144570189507 675395482317216855284261)
                  ·
                    refine ⟨126636652934478160365799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675395482317216855284261 126636652934478160365799)
                    ·
                      rfl

theorem cell23_739872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 4].length) (baseStart_739872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739872 prefixEnd_739872 := by exact prefixLift 739872
  have htrace : WordTrace (prefixWord ++ tailWord_739872) baseStart_739872 baseEnd_739872 := by
    simpa [prefixWord, tailWord_739872, baseEnd_739872] using wordTrace_append hprefix tailTrace_739872
  have hstable : (prefixWord ++ tailWord_739872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739872).length < 2 ^ (prefixWord ++ tailWord_739872).sum := by decide
  have hdescent : baseEnd_739872 < baseStart_739872 := by decide
  rcases family_descends (prefixWord ++ tailWord_739872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739888 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 4, 3, 2]
def baseStart_739888 : Nat := 118140960795 + 739888 * 2 ^ 59
def prefixEnd_739888 : Nat := 4983230072969 + 3 ^ 40 * 739888 * 2
def baseEnd_739888 : Nat := 379918174493906418497323

theorem tailTrace_739888 : CollatzResearch.WordTrace tailWord_739888 prefixEnd_739888 379918174493906418497323 := by
  unfold tailWord_739888
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492966171759806827626159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17990621562346409103501545 13492966171759806827626159)
  ·
    refine ⟨20239449257639710241439239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13492966171759806827626159 20239449257639710241439239)
    ·
      refine ⟨30359173886459565362158859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20239449257639710241439239 30359173886459565362158859)
      ·
        refine ⟨45538760829689348043238289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30359173886459565362158859 45538760829689348043238289)
        ·
          refine ⟨34154070622267011032428717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45538760829689348043238289 34154070622267011032428717)
          ·
            refine ⟨12807776483350129137160769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34154070622267011032428717 12807776483350129137160769)
            ·
              refine ⟨9605832362512596852870577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12807776483350129137160769 9605832362512596852870577)
              ·
                refine ⟨7204374271884447639652933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605832362512596852870577 7204374271884447639652933)
                ·
                  refine ⟨1350820175978333932434925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7204374271884447639652933 1350820175978333932434925)
                  ·
                    refine ⟨506557565991875224663097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350820175978333932434925 506557565991875224663097)
                    ·
                      refine ⟨379918174493906418497323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506557565991875224663097 379918174493906418497323)
                      ·
                        rfl

theorem cell23_739888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 3, 2].length) (baseStart_739888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739888 prefixEnd_739888 := by exact prefixLift 739888
  have htrace : WordTrace (prefixWord ++ tailWord_739888) baseStart_739888 baseEnd_739888 := by
    simpa [prefixWord, tailWord_739888, baseEnd_739888] using wordTrace_append hprefix tailTrace_739888
  have hstable : (prefixWord ++ tailWord_739888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739888).length < 2 ^ (prefixWord ++ tailWord_739888).sum := by decide
  have hdescent : baseEnd_739888 < baseStart_739888 := by decide
  rcases family_descends (prefixWord ++ tailWord_739888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739905 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_739905 : Nat := 118140960795 + 739905 * 2 ^ 59
def prefixEnd_739905 : Nat := 4983230072969 + 3 ^ 40 * 739905 * 2
def baseEnd_739905 : Nat := 379926903665032851984745

theorem tailTrace_739905 : CollatzResearch.WordTrace tailWord_739905 prefixEnd_739905 379926903665032851984745 := by
  unfold tailWord_739905
  simp only [CollatzResearch.WordTrace]
  refine ⟨26986552384458025558621169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17991034922972017039080779 26986552384458025558621169)
  ·
    refine ⟨20239914288343519168965877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26986552384458025558621169 20239914288343519168965877)
    ·
      refine ⟨1897491964532204922090551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20239914288343519168965877 1897491964532204922090551)
      ·
        refine ⟨2846237946798307383135827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897491964532204922090551 2846237946798307383135827)
        ·
          refine ⟨4269356920197461074703741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846237946798307383135827 4269356920197461074703741)
          ·
            refine ⟨1601008845074047903013903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4269356920197461074703741 1601008845074047903013903)
            ·
              refine ⟨2401513267611071854520855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601008845074047903013903 2401513267611071854520855)
              ·
                refine ⟨3602269901416607781781283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401513267611071854520855 3602269901416607781781283)
                ·
                  refine ⟨5403404852124911672671925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602269901416607781781283 5403404852124911672671925)
                  ·
                    refine ⟨506569204886710469312993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5403404852124911672671925 506569204886710469312993)
                    ·
                      refine ⟨379926903665032851984745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506569204886710469312993 379926903665032851984745)
                      ·
                        rfl

theorem cell23_739905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_739905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739905 prefixEnd_739905 := by exact prefixLift 739905
  have htrace : WordTrace (prefixWord ++ tailWord_739905) baseStart_739905 baseEnd_739905 := by
    simpa [prefixWord, tailWord_739905, baseEnd_739905] using wordTrace_append hprefix tailTrace_739905
  have hstable : (prefixWord ++ tailWord_739905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739905).length < 2 ^ (prefixWord ++ tailWord_739905).sum := by decide
  have hdescent : baseEnd_739905 < baseStart_739905 := by decide
  rcases family_descends (prefixWord ++ tailWord_739905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739948 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_739948 : Nat := 118140960795 + 739948 * 2 ^ 59
def prefixEnd_739948 : Nat := 4983230072969 + 3 ^ 40 * 739948 * 2
def baseEnd_739948 : Nat := 379948983333176183747047

theorem tailTrace_739948 : CollatzResearch.WordTrace tailWord_739948 prefixEnd_739948 379948983333176183747047 := by
  unfold tailWord_739948
  simp only [CollatzResearch.WordTrace]
  refine ⟨13494060361651121951218249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17992080482201495934957665 13494060361651121951218249)
  ·
    refine ⟨10120545271238341463413687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13494060361651121951218249 10120545271238341463413687)
    ·
      refine ⟨15180817906857512195120531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10120545271238341463413687 15180817906857512195120531)
      ·
        refine ⟨22771226860286268292680797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15180817906857512195120531 22771226860286268292680797)
        ·
          refine ⟨8539210072607350609755299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22771226860286268292680797 8539210072607350609755299)
          ·
            refine ⟨12808815108911025914632949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8539210072607350609755299 12808815108911025914632949)
            ·
              refine ⟨1200826416460408679496839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12808815108911025914632949 1200826416460408679496839)
              ·
                refine ⟨1801239624690613019245259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200826416460408679496839 1801239624690613019245259)
                ·
                  refine ⟨2701859437035919528867889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801239624690613019245259 2701859437035919528867889)
                  ·
                    refine ⟨2026394577776939646650917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701859437035919528867889 2026394577776939646650917)
                    ·
                      refine ⟨379948983333176183747047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2026394577776939646650917 379948983333176183747047)
                      ·
                        rfl

theorem cell23_739948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_739948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_739948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_739948 prefixEnd_739948 := by exact prefixLift 739948
  have htrace : WordTrace (prefixWord ++ tailWord_739948) baseStart_739948 baseEnd_739948 := by
    simpa [prefixWord, tailWord_739948, baseEnd_739948] using wordTrace_append hprefix tailTrace_739948
  have hstable : (prefixWord ++ tailWord_739948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739948).length < 2 ^ (prefixWord ++ tailWord_739948).sum := by decide
  have hdescent : baseEnd_739948 < baseStart_739948 := by decide
  rcases family_descends (prefixWord ++ tailWord_739948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
