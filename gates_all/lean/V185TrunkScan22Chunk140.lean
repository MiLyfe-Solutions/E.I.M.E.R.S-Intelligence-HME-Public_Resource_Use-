import V185TrunkScan22Chunk139

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1253487 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 2, 3]
def baseStart_1253487 : Nat := 118140960795 + 1253487 * 2 ^ 59
def prefixEnd_1253487 : Nat := 4983230072969 + 3 ^ 40 * 1253487 * 2
def baseEnd_1253487 : Nat := 429094216774961640031883

theorem tailTrace_1253487 : CollatzResearch.WordTrace tailWord_1253487 prefixEnd_1253487 429094216774961640031883 := by
  unfold tailWord_1253487
  simp only [CollatzResearch.WordTrace]
  refine ⟨45718426809838152381046715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30478951206558768254031143 45718426809838152381046715)
  ·
    refine ⟨68577640214757228571570073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45718426809838152381046715 68577640214757228571570073)
    ·
      refine ⟨51433230161067921428677555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68577640214757228571570073 51433230161067921428677555)
      ·
        refine ⟨77149845241601882143016333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51433230161067921428677555 77149845241601882143016333)
        ·
          refine ⟨28931191965600705803631125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77149845241601882143016333 28931191965600705803631125)
          ·
            refine ⟨1356149623387533084545209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28931191965600705803631125 1356149623387533084545209)
            ·
              refine ⟨1017112217540649813408907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356149623387533084545209 1017112217540649813408907)
              ·
                refine ⟨1525668326310974720113361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017112217540649813408907 1525668326310974720113361)
                ·
                  refine ⟨1144251244733231040085021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525668326310974720113361 1144251244733231040085021)
                  ·
                    refine ⟨429094216774961640031883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144251244733231040085021 429094216774961640031883)
                    ·
                      rfl

theorem cell22_1253487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_1253487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253487 prefixEnd_1253487 := by exact prefixLift 1253487
  have htrace : WordTrace (prefixWord ++ tailWord_1253487) baseStart_1253487 baseEnd_1253487 := by
    simpa [prefixWord, tailWord_1253487, baseEnd_1253487] using wordTrace_append hprefix tailTrace_1253487
  have hstable : (prefixWord ++ tailWord_1253487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253487).length < 2 ^ (prefixWord ++ tailWord_1253487).sum := by decide
  have hdescent : baseEnd_1253487 < baseStart_1253487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253511 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 9]
def baseStart_1253511 : Nat := 118140960795 + 1253511 * 2 ^ 59
def prefixEnd_1253511 : Nat := 4983230072969 + 3 ^ 40 * 1253511 * 2
def baseEnd_1253511 : Nat := 143034144155144525810603

theorem tailTrace_1253511 : CollatzResearch.WordTrace tailWord_1253511 prefixEnd_1253511 143034144155144525810603 := by
  unfold tailWord_1253511
  simp only [CollatzResearch.WordTrace]
  refine ⟨45719302161751204479920387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30479534774500802986613591 45719302161751204479920387)
  ·
    refine ⟨68578953242626806719880581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45719302161751204479920387 68578953242626806719880581)
    ·
      refine ⟨12858553732992526259977609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68578953242626806719880581 12858553732992526259977609)
      ·
        refine ⟨9643915299744394694983207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12858553732992526259977609 9643915299744394694983207)
        ·
          refine ⟨14465872949616592042474811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9643915299744394694983207 14465872949616592042474811)
          ·
            refine ⟨21698809424424888063712217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14465872949616592042474811 21698809424424888063712217)
            ·
              refine ⟨16274107068318666047784163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21698809424424888063712217 16274107068318666047784163)
              ·
                refine ⟨24411160602477999071676245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16274107068318666047784163 24411160602477999071676245)
                ·
                  refine ⟨143034144155144525810603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24411160602477999071676245 143034144155144525810603)
                  ·
                    rfl

theorem cell22_1253511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 9].length) (baseStart_1253511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253511 prefixEnd_1253511 := by exact prefixLift 1253511
  have htrace : WordTrace (prefixWord ++ tailWord_1253511) baseStart_1253511 baseEnd_1253511 := by
    simpa [prefixWord, tailWord_1253511, baseEnd_1253511] using wordTrace_append hprefix tailTrace_1253511
  have hstable : (prefixWord ++ tailWord_1253511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253511).length < 2 ^ (prefixWord ++ tailWord_1253511).sum := by decide
  have hdescent : baseEnd_1253511 < baseStart_1253511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253532 : List Nat := [2, 2, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_1253532 : Nat := 118140960795 + 1253532 * 2 ^ 59
def prefixEnd_1253532 : Nat := 4983230072969 + 3 ^ 40 * 1253532 * 2
def baseEnd_1253532 : Nat := 429109621194596522656745

theorem tailTrace_1253532 : CollatzResearch.WordTrace tailWord_1253532 prefixEnd_1253532 429109621194596522656745 := by
  unfold tailWord_1253532
  simp only [CollatzResearch.WordTrace]
  refine ⟨22860034047337562533217425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30480045396450083377623233 22860034047337562533217425)
  ·
    refine ⟨17145025535503171899913069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22860034047337562533217425 17145025535503171899913069)
    ·
      refine ⟨6429384575813689462467401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17145025535503171899913069 6429384575813689462467401)
      ·
        refine ⟨4822038431860267096850551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6429384575813689462467401 4822038431860267096850551)
        ·
          refine ⟨7233057647790400645275827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4822038431860267096850551 7233057647790400645275827)
          ·
            refine ⟨10849586471685600967913741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7233057647790400645275827 10849586471685600967913741)
            ·
              refine ⟨4068594926882100362967653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10849586471685600967913741 4068594926882100362967653)
              ·
                refine ⟨762861548790393818056435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4068594926882100362967653 762861548790393818056435)
                ·
                  refine ⟨1144292323185590727084653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762861548790393818056435 1144292323185590727084653)
                  ·
                    refine ⟨429109621194596522656745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144292323185590727084653 429109621194596522656745)
                    ·
                      rfl

theorem cell22_1253532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_1253532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253532 prefixEnd_1253532 := by exact prefixLift 1253532
  have htrace : WordTrace (prefixWord ++ tailWord_1253532) baseStart_1253532 baseEnd_1253532 := by
    simpa [prefixWord, tailWord_1253532, baseEnd_1253532] using wordTrace_append hprefix tailTrace_1253532
  have hstable : (prefixWord ++ tailWord_1253532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253532).length < 2 ^ (prefixWord ++ tailWord_1253532).sum := by decide
  have hdescent : baseEnd_1253532 < baseStart_1253532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253571 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 9]
def baseStart_1253571 : Nat := 118140960795 + 1253571 * 2 ^ 59
def prefixEnd_1253571 : Nat := 4983230072969 + 3 ^ 40 * 1253571 * 2
def baseEnd_1253571 : Nat := 429122971691613420931625

theorem tailTrace_1253571 : CollatzResearch.WordTrace tailWord_1253571 prefixEnd_1253571 429122971691613420931625 := by
  unfold tailWord_1253571
  simp only [CollatzResearch.WordTrace]
  refine ⟨45721490541533834727104567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30480993694355889818069711 45721490541533834727104567)
  ·
    refine ⟨68582235812300752090656851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45721490541533834727104567 68582235812300752090656851)
    ·
      refine ⟨102873353718451128135985277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68582235812300752090656851 102873353718451128135985277)
      ·
        refine ⟨38577507644419173050994479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102873353718451128135985277 38577507644419173050994479)
        ·
          refine ⟨57866261466628759576491719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38577507644419173050994479 57866261466628759576491719)
          ·
            refine ⟨86799392199943139364737579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57866261466628759576491719 86799392199943139364737579)
            ·
              refine ⟨130199088299914709047106369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86799392199943139364737579 130199088299914709047106369)
              ·
                refine ⟨97649316224936031785329777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130199088299914709047106369 97649316224936031785329777)
                ·
                  refine ⟨73236987168702023838997333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97649316224936031785329777 73236987168702023838997333)
                  ·
                    refine ⟨429122971691613420931625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73236987168702023838997333 429122971691613420931625)
                    ·
                      rfl

theorem cell22_1253571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_1253571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253571 prefixEnd_1253571 := by exact prefixLift 1253571
  have htrace : WordTrace (prefixWord ++ tailWord_1253571) baseStart_1253571 baseEnd_1253571 := by
    simpa [prefixWord, tailWord_1253571, baseEnd_1253571] using wordTrace_append hprefix tailTrace_1253571
  have hstable : (prefixWord ++ tailWord_1253571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253571).length < 2 ^ (prefixWord ++ tailWord_1253571).sum := by decide
  have hdescent : baseEnd_1253571 < baseStart_1253571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253605 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_1253605 : Nat := 118140960795 + 1253605 * 2 ^ 59
def prefixEnd_1253605 : Nat := 4983230072969 + 3 ^ 40 * 1253605 * 2
def baseEnd_1253605 : Nat := 429134610586448665581521

theorem tailTrace_1253605 : CollatzResearch.WordTrace tailWord_1253605 prefixEnd_1253605 429134610586448665581521 := by
  unfold tailWord_1253605
  simp only [CollatzResearch.WordTrace]
  refine ⟨45722730623410658533842269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30481820415607105689228179 45722730623410658533842269)
  ·
    refine ⟨17146023983778996950190851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45722730623410658533842269 17146023983778996950190851)
    ·
      refine ⟨25719035975668495425286277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17146023983778996950190851 25719035975668495425286277)
      ·
        refine ⟨4822319245437842892241177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25719035975668495425286277 4822319245437842892241177)
        ·
          refine ⟨3616739434078382169180883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4822319245437842892241177 3616739434078382169180883)
          ·
            refine ⟨5425109151117573253771325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616739434078382169180883 5425109151117573253771325)
            ·
              refine ⟨2034415931669089970164247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5425109151117573253771325 2034415931669089970164247)
              ·
                refine ⟨3051623897503634955246371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034415931669089970164247 3051623897503634955246371)
                ·
                  refine ⟨4577435846255452432869557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051623897503634955246371 4577435846255452432869557)
                  ·
                    refine ⟨429134610586448665581521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4577435846255452432869557 429134610586448665581521)
                    ·
                      rfl

theorem cell22_1253605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_1253605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253605 prefixEnd_1253605 := by exact prefixLift 1253605
  have htrace : WordTrace (prefixWord ++ tailWord_1253605) baseStart_1253605 baseEnd_1253605 := by
    simpa [prefixWord, tailWord_1253605, baseEnd_1253605] using wordTrace_append hprefix tailTrace_1253605
  have hstable : (prefixWord ++ tailWord_1253605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253605).length < 2 ^ (prefixWord ++ tailWord_1253605).sum := by decide
  have hdescent : baseEnd_1253605 < baseStart_1253605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253671 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1253671 : Nat := 118140960795 + 1253671 * 2 ^ 59
def prefixEnd_1253671 : Nat := 4983230072969 + 3 ^ 40 * 1253671 * 2
def baseEnd_1253671 : Nat := 429157203735246493431319

theorem tailTrace_1253671 : CollatzResearch.WordTrace tailWord_1253671 prefixEnd_1253671 429157203735246493431319 := by
  unfold tailWord_1253671
  simp only [CollatzResearch.WordTrace]
  refine ⟨45725137841171551805744867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30483425227447701203829911 45725137841171551805744867)
  ·
    refine ⟨68587706761757327708617301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45725137841171551805744867 68587706761757327708617301)
    ·
      refine ⟨803762188614343684085359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 68587706761757327708617301 803762188614343684085359)
      ·
        refine ⟨1205643282921515526128039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803762188614343684085359 1205643282921515526128039)
        ·
          refine ⟨1808464924382273289192059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205643282921515526128039 1808464924382273289192059)
          ·
            refine ⟨2712697386573409933788089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808464924382273289192059 2712697386573409933788089)
            ·
              refine ⟨2034523039930057450341067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712697386573409933788089 2034523039930057450341067)
              ·
                refine ⟨3051784559895086175511601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034523039930057450341067 3051784559895086175511601)
                ·
                  refine ⟨2288838419921314631633701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051784559895086175511601 2288838419921314631633701)
                  ·
                    refine ⟨429157203735246493431319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288838419921314631633701 429157203735246493431319)
                    ·
                      rfl

theorem cell22_1253671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1253671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253671 prefixEnd_1253671 := by exact prefixLift 1253671
  have htrace : WordTrace (prefixWord ++ tailWord_1253671) baseStart_1253671 baseEnd_1253671 := by
    simpa [prefixWord, tailWord_1253671, baseEnd_1253671] using wordTrace_append hprefix tailTrace_1253671
  have hstable : (prefixWord ++ tailWord_1253671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253671).length < 2 ^ (prefixWord ++ tailWord_1253671).sum := by decide
  have hdescent : baseEnd_1253671 < baseStart_1253671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253744 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 1, 4]
def baseStart_1253744 : Nat := 118140960795 + 1253744 * 2 ^ 59
def prefixEnd_1253744 : Nat := 4983230072969 + 3 ^ 40 * 1253744 * 2
def baseEnd_1253744 : Nat := 429182193127098636356095

theorem tailTrace_1253744 : CollatzResearch.WordTrace tailWord_1253744 prefixEnd_1253744 429182193127098636356095 := by
  unfold tailWord_1253744
  simp only [CollatzResearch.WordTrace]
  refine ⟨22863900184953542636576143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30485200246604723515434857 22863900184953542636576143)
  ·
    refine ⟨34295850277430313954864215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22863900184953542636576143 34295850277430313954864215)
    ·
      refine ⟨51443775416145470932296323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34295850277430313954864215 51443775416145470932296323)
      ·
        refine ⟨77165663124218206398444485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51443775416145470932296323 77165663124218206398444485)
        ·
          refine ⟨14468561835790913699708341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77165663124218206398444485 14468561835790913699708341)
          ·
            refine ⟨1356427672105398159347657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14468561835790913699708341 1356427672105398159347657)
            ·
              refine ⟨1017320754079048619510743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356427672105398159347657 1017320754079048619510743)
              ·
                refine ⟨1525981131118572929266115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017320754079048619510743 1525981131118572929266115)
                ·
                  refine ⟨2288971696677859393899173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525981131118572929266115 2288971696677859393899173)
                  ·
                    refine ⟨429182193127098636356095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288971696677859393899173 429182193127098636356095)
                    ·
                      rfl

theorem cell22_1253744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_1253744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253744 prefixEnd_1253744 := by exact prefixLift 1253744
  have htrace : WordTrace (prefixWord ++ tailWord_1253744) baseStart_1253744 baseEnd_1253744 := by
    simpa [prefixWord, tailWord_1253744, baseEnd_1253744] using wordTrace_append hprefix tailTrace_1253744
  have hstable : (prefixWord ++ tailWord_1253744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253744).length < 2 ^ (prefixWord ++ tailWord_1253744).sum := by decide
  have hdescent : baseEnd_1253744 < baseStart_1253744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253757 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1253757 : Nat := 118140960795 + 1253757 * 2 ^ 59
def prefixEnd_1253757 : Nat := 4983230072969 + 3 ^ 40 * 1253757 * 2
def baseEnd_1253757 : Nat := 429186643292770935781055

theorem tailTrace_1253757 : CollatzResearch.WordTrace tailWord_1253757 prefixEnd_1253757 429186643292770935781055 := by
  unfold tailWord_1253757
  simp only [CollatzResearch.WordTrace]
  refine ⟨45728274518859988493375525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30485516345906658995583683 45728274518859988493375525)
  ·
    refine ⟨8574051472286247842507911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45728274518859988493375525 8574051472286247842507911)
    ·
      refine ⟨12861077208429371763761867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8574051472286247842507911 12861077208429371763761867)
      ·
        refine ⟨19291615812644057645642801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12861077208429371763761867 19291615812644057645642801)
        ·
          refine ⟨14468711859483043234232101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19291615812644057645642801 14468711859483043234232101)
          ·
            refine ⟨2712883473653070606418519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14468711859483043234232101 2712883473653070606418519)
            ·
              refine ⟨4069325210479605909627779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712883473653070606418519 4069325210479605909627779)
              ·
                refine ⟨6103987815719408864441669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4069325210479605909627779 6103987815719408864441669)
                ·
                  refine ⟨1144497715447389162082813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6103987815719408864441669 1144497715447389162082813)
                  ·
                    refine ⟨429186643292770935781055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144497715447389162082813 429186643292770935781055)
                    ·
                      rfl

theorem cell22_1253757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1253757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253757 prefixEnd_1253757 := by exact prefixLift 1253757
  have htrace : WordTrace (prefixWord ++ tailWord_1253757) baseStart_1253757 baseEnd_1253757 := by
    simpa [prefixWord, tailWord_1253757, baseEnd_1253757] using wordTrace_append hprefix tailTrace_1253757
  have hstable : (prefixWord ++ tailWord_1253757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253757).length < 2 ^ (prefixWord ++ tailWord_1253757).sum := by decide
  have hdescent : baseEnd_1253757 < baseStart_1253757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253774 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_1253774 : Nat := 118140960795 + 1253774 * 2 ^ 59
def prefixEnd_1253774 : Nat := 4983230072969 + 3 ^ 40 * 1253774 * 2
def baseEnd_1253774 : Nat := 429192462740188558106003

theorem tailTrace_1253774 : CollatzResearch.WordTrace tailWord_1253774 prefixEnd_1253774 429192462740188558106003 := by
  unfold tailWord_1253774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716111819974800049593047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30485929706532266931162917 5716111819974800049593047)
  ·
    refine ⟨8574167729962200074389571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5716111819974800049593047 8574167729962200074389571)
    ·
      refine ⟨12861251594943300111584357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8574167729962200074389571 12861251594943300111584357)
      ·
        refine ⟨2411484674051868770922067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12861251594943300111584357 2411484674051868770922067)
        ·
          refine ⟨3617227011077803156383101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411484674051868770922067 3617227011077803156383101)
          ·
            refine ⟨1356460129154176183643663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3617227011077803156383101 1356460129154176183643663)
            ·
              refine ⟨2034690193731264275465495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356460129154176183643663 2034690193731264275465495)
              ·
                refine ⟨3052035290596896413198243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034690193731264275465495 3052035290596896413198243)
                ·
                  refine ⟨4578052935895344619797365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052035290596896413198243 4578052935895344619797365)
                  ·
                    refine ⟨429192462740188558106003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4578052935895344619797365 429192462740188558106003)
                    ·
                      rfl

theorem cell22_1253774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_1253774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253774 prefixEnd_1253774 := by exact prefixLift 1253774
  have htrace : WordTrace (prefixWord ++ tailWord_1253774) baseStart_1253774 baseEnd_1253774 := by
    simpa [prefixWord, tailWord_1253774, baseEnd_1253774] using wordTrace_append hprefix tailTrace_1253774
  have hstable : (prefixWord ++ tailWord_1253774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253774).length < 2 ^ (prefixWord ++ tailWord_1253774).sum := by decide
  have hdescent : baseEnd_1253774 < baseStart_1253774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253793 : List Nat := [1, 2, 3, 5, 2, 1, 1, 3, 4]
def baseStart_1253793 : Nat := 118140960795 + 1253793 * 2 ^ 59
def prefixEnd_1253793 : Nat := 4983230072969 + 3 ^ 40 * 1253793 * 2
def baseEnd_1253793 : Nat := 143066322276159613960315

theorem tailTrace_1253793 : CollatzResearch.WordTrace tailWord_1253793 prefixEnd_1253793 143066322276159613960315 := by
  unfold tailWord_1253793
  simp only [CollatzResearch.WordTrace]
  refine ⟨45729587546729566641686033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30486391697819711094457355 45729587546729566641686033)
  ·
    refine ⟨34297190660047174981264525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45729587546729566641686033 34297190660047174981264525)
    ·
      refine ⟨12861446497517690617974197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34297190660047174981264525 12861446497517690617974197)
      ·
        refine ⟨1205760609142283495435081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12861446497517690617974197 1205760609142283495435081)
        ·
          refine ⟨904320456856712621576311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205760609142283495435081 904320456856712621576311)
          ·
            refine ⟨1356480685285068932364467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904320456856712621576311 1356480685285068932364467)
            ·
              refine ⟨2034721027927603398546701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356480685285068932364467 2034721027927603398546701)
              ·
                refine ⟨763020385472851274455013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2034721027927603398546701 763020385472851274455013)
                ·
                  refine ⟨143066322276159613960315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763020385472851274455013 143066322276159613960315)
                  ·
                    rfl

theorem cell22_1253793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_1253793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253793 prefixEnd_1253793 := by exact prefixLift 1253793
  have htrace : WordTrace (prefixWord ++ tailWord_1253793) baseStart_1253793 baseEnd_1253793 := by
    simpa [prefixWord, tailWord_1253793, baseEnd_1253793] using wordTrace_append hprefix tailTrace_1253793
  have hstable : (prefixWord ++ tailWord_1253793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253793).length < 2 ^ (prefixWord ++ tailWord_1253793).sum := by decide
  have hdescent : baseEnd_1253793 < baseStart_1253793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253815 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 7]
def baseStart_1253815 : Nat := 118140960795 + 1253815 * 2 ^ 59
def prefixEnd_1253815 : Nat := 4983230072969 + 3 ^ 40 * 1253815 * 2
def baseEnd_1253815 : Nat := 143068832626026039276959

theorem tailTrace_1253815 : CollatzResearch.WordTrace tailWord_1253815 prefixEnd_1253815 143068832626026039276959 := by
  unfold tailWord_1253815
  simp only [CollatzResearch.WordTrace]
  refine ⟨45730389952649864398986899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30486926635099909599324599 45730389952649864398986899)
  ·
    refine ⟨68595584928974796598480349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45730389952649864398986899 68595584928974796598480349)
    ·
      refine ⟨25723344348365548724430131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68595584928974796598480349 25723344348365548724430131)
      ·
        refine ⟨38585016522548323086645197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25723344348365548724430131 38585016522548323086645197)
        ·
          refine ⟨14469381195955621157491949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38585016522548323086645197 14469381195955621157491949)
          ·
            refine ⟨5426017948483357934059481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14469381195955621157491949 5426017948483357934059481)
            ·
              refine ⟨4069513461362518450544611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426017948483357934059481 4069513461362518450544611)
              ·
                refine ⟨6104270192043777675816917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4069513461362518450544611 6104270192043777675816917)
                ·
                  refine ⟨143068832626026039276959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6104270192043777675816917 143068832626026039276959)
                  ·
                    rfl

theorem cell22_1253815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 7].length) (baseStart_1253815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253815 prefixEnd_1253815 := by exact prefixLift 1253815
  have htrace : WordTrace (prefixWord ++ tailWord_1253815) baseStart_1253815 baseEnd_1253815 := by
    simpa [prefixWord, tailWord_1253815, baseEnd_1253815] using wordTrace_append hprefix tailTrace_1253815
  have hstable : (prefixWord ++ tailWord_1253815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253815).length < 2 ^ (prefixWord ++ tailWord_1253815).sum := by decide
  have hdescent : baseEnd_1253815 < baseStart_1253815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253832 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 5]
def baseStart_1253832 : Nat := 118140960795 + 1253832 * 2 ^ 59
def prefixEnd_1253832 : Nat := 4983230072969 + 3 ^ 40 * 1253832 * 2
def baseEnd_1253832 : Nat := 143070772441831913385275

theorem tailTrace_1253832 : CollatzResearch.WordTrace tailWord_1253832 prefixEnd_1253832 143070772441831913385275 := by
  unfold tailWord_1253832
  simp only [CollatzResearch.WordTrace]
  refine ⟨22865504996794138151177875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30487339995725517534903833 22865504996794138151177875)
  ·
    refine ⟨34298257495191207226766813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22865504996794138151177875 34298257495191207226766813)
    ·
      refine ⟨12861846560696702710037555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34298257495191207226766813 12861846560696702710037555)
      ·
        refine ⟨19292769841045054065056333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12861846560696702710037555 19292769841045054065056333)
        ·
          refine ⟨7234788690391895274396125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19292769841045054065056333 7234788690391895274396125)
          ·
            refine ⟨2713045758896960727898547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7234788690391895274396125 2713045758896960727898547)
            ·
              refine ⟨4069568638345441091847821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713045758896960727898547 4069568638345441091847821)
              ·
                refine ⟨1526088239379540409442933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4069568638345441091847821 1526088239379540409442933)
                ·
                  refine ⟨143070772441831913385275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1526088239379540409442933 143070772441831913385275)
                  ·
                    rfl

theorem cell22_1253832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_1253832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253832 prefixEnd_1253832 := by exact prefixLift 1253832
  have htrace : WordTrace (prefixWord ++ tailWord_1253832) baseStart_1253832 baseEnd_1253832 := by
    simpa [prefixWord, tailWord_1253832, baseEnd_1253832] using wordTrace_append hprefix tailTrace_1253832
  have hstable : (prefixWord ++ tailWord_1253832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253832).length < 2 ^ (prefixWord ++ tailWord_1253832).sum := by decide
  have hdescent : baseEnd_1253832 < baseStart_1253832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253875 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 3, 5]
def baseStart_1253875 : Nat := 118140960795 + 1253875 * 2 ^ 59
def prefixEnd_1253875 : Nat := 4983230072969 + 3 ^ 40 * 1253875 * 2
def baseEnd_1253875 : Nat := 429227037104257961330693

theorem tailTrace_1253875 : CollatzResearch.WordTrace tailWord_1253875 prefixEnd_1253875 429227037104257961330693 := by
  unfold tailWord_1253875
  simp only [CollatzResearch.WordTrace]
  refine ⟨45732578332432494646171079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30488385554954996430780719 45732578332432494646171079)
  ·
    refine ⟨68598867498648741969256619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45732578332432494646171079 68598867498648741969256619)
    ·
      refine ⟨102898301247973112953884929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68598867498648741969256619 102898301247973112953884929)
      ·
        refine ⟨77173725935979834715413697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102898301247973112953884929 77173725935979834715413697)
        ·
          refine ⟨57880294451984876036560273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77173725935979834715413697 57880294451984876036560273)
          ·
            refine ⟨43410220838988657027420205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57880294451984876036560273 43410220838988657027420205)
            ·
              refine ⟨16278832814620746385282577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43410220838988657027420205 16278832814620746385282577)
              ·
                refine ⟨12209124610965559788961933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16278832814620746385282577 12209124610965559788961933)
                ·
                  refine ⟨4578421729112084920860725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12209124610965559788961933 4578421729112084920860725)
                  ·
                    refine ⟨429227037104257961330693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4578421729112084920860725 429227037104257961330693)
                    ·
                      rfl

theorem cell22_1253875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_1253875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253875 prefixEnd_1253875 := by exact prefixLift 1253875
  have htrace : WordTrace (prefixWord ++ tailWord_1253875) baseStart_1253875 baseEnd_1253875 := by
    simpa [prefixWord, tailWord_1253875, baseEnd_1253875] using wordTrace_append hprefix tailTrace_1253875
  have hstable : (prefixWord ++ tailWord_1253875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253875).length < 2 ^ (prefixWord ++ tailWord_1253875).sum := by decide
  have hdescent : baseEnd_1253875 < baseStart_1253875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253988 : List Nat := [2, 3, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_1253988 : Nat := 118140960795 + 1253988 * 2 ^ 59
def prefixEnd_1253988 : Nat := 4983230072969 + 3 ^ 40 * 1253988 * 2
def baseEnd_1253988 : Nat := 429265719313563333255347

theorem tailTrace_1253988 : CollatzResearch.WordTrace tailWord_1253988 prefixEnd_1253988 429265719313563333255347 := by
  unfold tailWord_1253988
  simp only [CollatzResearch.WordTrace]
  refine ⟨22868349890511557472517309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30491133187348743296689745 22868349890511557472517309)
  ·
    refine ⟨8575631208941834052193991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22868349890511557472517309 8575631208941834052193991)
    ·
      refine ⟨12863446813412751078290987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8575631208941834052193991 12863446813412751078290987)
      ·
        refine ⟨19295170220119126617436481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12863446813412751078290987 19295170220119126617436481)
        ·
          refine ⟨14471377665089344963077361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19295170220119126617436481 14471377665089344963077361)
          ·
            refine ⟨10853533248817008722308021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14471377665089344963077361 10853533248817008722308021)
            ·
              refine ⟨1017518742076594567716377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10853533248817008722308021 1017518742076594567716377)
              ·
                refine ⟨763139056557445925787283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017518742076594567716377 763139056557445925787283)
                ·
                  refine ⟨1144708584836168888680925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763139056557445925787283 1144708584836168888680925)
                  ·
                    refine ⟨429265719313563333255347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144708584836168888680925 429265719313563333255347)
                    ·
                      rfl

theorem cell22_1253988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_1253988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253988 prefixEnd_1253988 := by exact prefixLift 1253988
  have htrace : WordTrace (prefixWord ++ tailWord_1253988) baseStart_1253988 baseEnd_1253988 := by
    simpa [prefixWord, tailWord_1253988, baseEnd_1253988] using wordTrace_append hprefix tailTrace_1253988
  have hstable : (prefixWord ++ tailWord_1253988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253988).length < 2 ^ (prefixWord ++ tailWord_1253988).sum := by decide
  have hdescent : baseEnd_1253988 < baseStart_1253988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254012 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 6]
def baseStart_1254012 : Nat := 118140960795 + 1254012 * 2 ^ 59
def prefixEnd_1254012 : Nat := 4983230072969 + 3 ^ 40 * 1254012 * 2
def baseEnd_1254012 : Nat := 143091311668011756885091

theorem tailTrace_1254012 : CollatzResearch.WordTrace tailWord_1254012 prefixEnd_1254012 143091311668011756885091 := by
  unfold tailWord_1254012
  simp only [CollatzResearch.WordTrace]
  refine ⟨22868787566468083521954145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30491716755290778029272193 22868787566468083521954145)
  ·
    refine ⟨17151590674851062641465609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22868787566468083521954145 17151590674851062641465609)
    ·
      refine ⟨12863693006138296981099207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17151590674851062641465609 12863693006138296981099207)
      ·
        refine ⟨19295539509207445471648811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12863693006138296981099207 19295539509207445471648811)
        ·
          refine ⟨28943309263811168207473217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19295539509207445471648811 28943309263811168207473217)
          ·
            refine ⟨21707481947858376155604913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28943309263811168207473217 21707481947858376155604913)
            ·
              refine ⟨16280611460893782116703685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21707481947858376155604913 16280611460893782116703685)
              ·
                refine ⟨3052614648917584146881941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16280611460893782116703685 3052614648917584146881941)
                ·
                  refine ⟨143091311668011756885091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3052614648917584146881941 143091311668011756885091)
                  ·
                    rfl

theorem cell22_1254012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_1254012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254012 prefixEnd_1254012 := by exact prefixLift 1254012
  have htrace : WordTrace (prefixWord ++ tailWord_1254012) baseStart_1254012 baseEnd_1254012 := by
    simpa [prefixWord, tailWord_1254012, baseEnd_1254012] using wordTrace_append hprefix tailTrace_1254012
  have hstable : (prefixWord ++ tailWord_1254012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254012).length < 2 ^ (prefixWord ++ tailWord_1254012).sum := by decide
  have hdescent : baseEnd_1254012 < baseStart_1254012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254061 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1254061 : Nat := 118140960795 + 1254061 * 2 ^ 59
def prefixEnd_1254061 : Nat := 4983230072969 + 3 ^ 40 * 1254061 * 2
def baseEnd_1254061 : Nat := 429290708705415476180123

theorem tailTrace_1254061 : CollatzResearch.WordTrace tailWord_1254061 prefixEnd_1254061 429290708705415476180123 := by
  unfold tailWord_1254061
  simp only [CollatzResearch.WordTrace]
  refine ⟨45739362309758648412442037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30492908206505765608294691 45739362309758648412442037)
  ·
    refine ⟨4288065216539873288666441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45739362309758648412442037 4288065216539873288666441)
    ·
      refine ⟨3216048912404904966499831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4288065216539873288666441 3216048912404904966499831)
      ·
        refine ⟨4824073368607357449749747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3216048912404904966499831 4824073368607357449749747)
        ·
          refine ⟨7236110052911036174624621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4824073368607357449749747 7236110052911036174624621)
          ·
            refine ⟨2713541269841638565484233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7236110052911036174624621 2713541269841638565484233)
            ·
              refine ⟨2035155952381228924113175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2713541269841638565484233 2035155952381228924113175)
              ·
                refine ⟨3052733928571843386169763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035155952381228924113175 3052733928571843386169763)
                ·
                  refine ⟨4579100892857765079254645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052733928571843386169763 4579100892857765079254645)
                  ·
                    refine ⟨429290708705415476180123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4579100892857765079254645 429290708705415476180123)
                    ·
                      rfl

theorem cell22_1254061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1254061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254061 prefixEnd_1254061 := by exact prefixLift 1254061
  have htrace : WordTrace (prefixWord ++ tailWord_1254061) baseStart_1254061 baseEnd_1254061 := by
    simpa [prefixWord, tailWord_1254061, baseEnd_1254061] using wordTrace_append hprefix tailTrace_1254061
  have hstable : (prefixWord ++ tailWord_1254061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254061).length < 2 ^ (prefixWord ++ tailWord_1254061).sum := by decide
  have hdescent : baseEnd_1254061 < baseStart_1254061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254074 : List Nat := [3, 1, 1, 1, 2, 3, 5, 6]
def baseStart_1254074 : Nat := 118140960795 + 1254074 * 2 ^ 59
def prefixEnd_1254074 : Nat := 4983230072969 + 3 ^ 40 * 1254074 * 2
def baseEnd_1254074 : Nat := 47699462096787530622787

theorem tailTrace_1254074 : CollatzResearch.WordTrace tailWord_1254074 prefixEnd_1254074 47699462096787530622787 := by
  unfold tailWord_1254074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11434959114677887908166319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30493224305807701088443517 11434959114677887908166319)
  ·
    refine ⟨17152438672016831862249479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11434959114677887908166319 17152438672016831862249479)
    ·
      refine ⟨25728658008025247793374219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17152438672016831862249479 25728658008025247793374219)
      ·
        refine ⟨38592987012037871690061329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25728658008025247793374219 38592987012037871690061329)
        ·
          refine ⟨28944740259028403767545997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38592987012037871690061329 28944740259028403767545997)
          ·
            refine ⟨10854277597135651412829749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28944740259028403767545997 10854277597135651412829749)
            ·
              refine ⟨1017588524731467319952789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10854277597135651412829749 1017588524731467319952789)
              ·
                refine ⟨47699462096787530622787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1017588524731467319952789 47699462096787530622787)
                ·
                  rfl

theorem cell22_1254074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_1254074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254074 prefixEnd_1254074 := by exact prefixLift 1254074
  have htrace : WordTrace (prefixWord ++ tailWord_1254074) baseStart_1254074 baseEnd_1254074 := by
    simpa [prefixWord, tailWord_1254074, baseEnd_1254074] using wordTrace_append hprefix tailTrace_1254074
  have hstable : (prefixWord ++ tailWord_1254074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254074).length < 2 ^ (prefixWord ++ tailWord_1254074).sum := by decide
  have hdescent : baseEnd_1254074 < baseStart_1254074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254087 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1254087 : Nat := 118140960795 + 1254087 * 2 ^ 59
def prefixEnd_1254087 : Nat := 4983230072969 + 3 ^ 40 * 1254087 * 2
def baseEnd_1254087 : Nat := 429299609036760075030043

theorem tailTrace_1254087 : CollatzResearch.WordTrace tailWord_1254087 prefixEnd_1254087 429299609036760075030043 := by
  unfold tailWord_1254087
  simp only [CollatzResearch.WordTrace]
  refine ⟨45740310607664454852888515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30493540405109636568592343 45740310607664454852888515)
  ·
    refine ⟨68610465911496682279332773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45740310607664454852888515 68610465911496682279332773)
    ·
      refine ⟨12864462358405627927374895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68610465911496682279332773 12864462358405627927374895)
      ·
        refine ⟨19296693537608441891062343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12864462358405627927374895 19296693537608441891062343)
        ·
          refine ⟨28945040306412662836593515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19296693537608441891062343 28945040306412662836593515)
          ·
            refine ⟨43417560459618994254890273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28945040306412662836593515 43417560459618994254890273)
            ·
              refine ⟨32563170344714245691167705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43417560459618994254890273 32563170344714245691167705)
              ·
                refine ⟨24422377758535684268375779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32563170344714245691167705 24422377758535684268375779)
                ·
                  refine ⟨36633566637803526402563669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24422377758535684268375779 36633566637803526402563669)
                  ·
                    refine ⟨429299609036760075030043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36633566637803526402563669 429299609036760075030043)
                    ·
                      rfl

theorem cell22_1254087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1254087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254087 prefixEnd_1254087 := by exact prefixLift 1254087
  have htrace : WordTrace (prefixWord ++ tailWord_1254087) baseStart_1254087 baseEnd_1254087 := by
    simpa [prefixWord, tailWord_1254087, baseEnd_1254087] using wordTrace_append hprefix tailTrace_1254087
  have hstable : (prefixWord ++ tailWord_1254087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254087).length < 2 ^ (prefixWord ++ tailWord_1254087).sum := by decide
  have hdescent : baseEnd_1254087 < baseStart_1254087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254106 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_1254106 : Nat := 118140960795 + 1254106 * 2 ^ 59
def prefixEnd_1254106 : Nat := 4983230072969 + 3 ^ 40 * 1254106 * 2
def baseEnd_1254106 : Nat := 429306113125050358804985

theorem tailTrace_1254106 : CollatzResearch.WordTrace tailWord_1254106 prefixEnd_1254106 429306113125050358804985 := by
  unfold tailWord_1254106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11435250898648905274457543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30494002396397080731886781 11435250898648905274457543)
  ·
    refine ⟨17152876347973357911686315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11435250898648905274457543 17152876347973357911686315)
    ·
      refine ⟨25729314521960036867529473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17152876347973357911686315 25729314521960036867529473)
      ·
        refine ⟨19296985891470027650647105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25729314521960036867529473 19296985891470027650647105)
        ·
          refine ⟨14472739418602520737985329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19296985891470027650647105 14472739418602520737985329)
          ·
            refine ⟨10854554563951890553488997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14472739418602520737985329 10854554563951890553488997)
            ·
              refine ⟨2035228980740979478779187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10854554563951890553488997 2035228980740979478779187)
              ·
                refine ⟨3052843471111469218168781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035228980740979478779187 3052843471111469218168781)
                ·
                  refine ⟨1144816301666800956813293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3052843471111469218168781 1144816301666800956813293)
                  ·
                    refine ⟨429306113125050358804985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144816301666800956813293 429306113125050358804985)
                    ·
                      rfl

theorem cell22_1254106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_1254106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254106 prefixEnd_1254106 := by exact prefixLift 1254106
  have htrace : WordTrace (prefixWord ++ tailWord_1254106) baseStart_1254106 baseEnd_1254106 := by
    simpa [prefixWord, tailWord_1254106, baseEnd_1254106] using wordTrace_append hprefix tailTrace_1254106
  have hstable : (prefixWord ++ tailWord_1254106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254106).length < 2 ^ (prefixWord ++ tailWord_1254106).sum := by decide
  have hdescent : baseEnd_1254106 < baseStart_1254106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254140 : List Nat := [2, 2, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_1254140 : Nat := 118140960795 + 1254140 * 2 ^ 59
def prefixEnd_1254140 : Nat := 4983230072969 + 3 ^ 40 * 1254140 * 2
def baseEnd_1254140 : Nat := 429317752019885603454881

theorem tailTrace_1254140 : CollatzResearch.WordTrace tailWord_1254140 prefixEnd_1254140 429317752019885603454881 := by
  unfold tailWord_1254140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22871121838236222452283937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30494829117648296603045249 22871121838236222452283937)
  ·
    refine ⟨17153341378677166839212953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22871121838236222452283937 17153341378677166839212953)
    ·
      refine ⟨12865006034007875129409715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17153341378677166839212953 12865006034007875129409715)
      ·
        refine ⟨19297509051011812694114573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12865006034007875129409715 19297509051011812694114573)
        ·
          refine ⟨7236565894129429760292965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19297509051011812694114573 7236565894129429760292965)
          ·
            refine ⟨1356856105149268080054931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7236565894129429760292965 1356856105149268080054931)
            ·
              refine ⟨2035284157723902120082397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356856105149268080054931 2035284157723902120082397)
              ·
                refine ⟨763231559146463295030899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2035284157723902120082397 763231559146463295030899)
                ·
                  refine ⟨1144847338719694942546349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763231559146463295030899 1144847338719694942546349)
                  ·
                    refine ⟨429317752019885603454881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144847338719694942546349 429317752019885603454881)
                    ·
                      rfl

theorem cell22_1254140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_1254140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254140 prefixEnd_1254140 := by exact prefixLift 1254140
  have htrace : WordTrace (prefixWord ++ tailWord_1254140) baseStart_1254140 baseEnd_1254140 := by
    simpa [prefixWord, tailWord_1254140, baseEnd_1254140] using wordTrace_append hprefix tailTrace_1254140
  have hstable : (prefixWord ++ tailWord_1254140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254140).length < 2 ^ (prefixWord ++ tailWord_1254140).sum := by decide
  have hdescent : baseEnd_1254140 < baseStart_1254140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254179 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 1, 5]
def baseStart_1254179 : Nat := 118140960795 + 1254179 * 2 ^ 59
def prefixEnd_1254179 : Nat := 4983230072969 + 3 ^ 40 * 1254179 * 2
def baseEnd_1254179 : Nat := 429331102516902501729761

theorem tailTrace_1254179 : CollatzResearch.WordTrace tailWord_1254179 prefixEnd_1254179 429331102516902501729761 := by
  unfold tailWord_1254179
  simp only [CollatzResearch.WordTrace]
  refine ⟨45743666123331154565237591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30495777415554103043491727 45743666123331154565237591)
  ·
    refine ⟨68615499184996731847856387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45743666123331154565237591 68615499184996731847856387)
    ·
      refine ⟨102923248777495097771784581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68615499184996731847856387 102923248777495097771784581)
      ·
        refine ⟨19298109145780330832209609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102923248777495097771784581 19298109145780330832209609)
        ·
          refine ⟨14473581859335248124157207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19298109145780330832209609 14473581859335248124157207)
          ·
            refine ⟨21710372789002872186235811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14473581859335248124157207 21710372789002872186235811)
            ·
              refine ⟨32565559183504308279353717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21710372789002872186235811 32565559183504308279353717)
              ·
                refine ⟨3053021173453528901189411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32565559183504308279353717 3053021173453528901189411)
                ·
                  refine ⟨4579531760180293351784117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053021173453528901189411 4579531760180293351784117)
                  ·
                    refine ⟨429331102516902501729761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4579531760180293351784117 429331102516902501729761)
                    ·
                      rfl

theorem cell22_1254179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_1254179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254179 prefixEnd_1254179 := by exact prefixLift 1254179
  have htrace : WordTrace (prefixWord ++ tailWord_1254179) baseStart_1254179 baseEnd_1254179 := by
    simpa [prefixWord, tailWord_1254179, baseEnd_1254179] using wordTrace_append hprefix tailTrace_1254179
  have hstable : (prefixWord ++ tailWord_1254179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254179).length < 2 ^ (prefixWord ++ tailWord_1254179).sum := by decide
  have hdescent : baseEnd_1254179 < baseStart_1254179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254239 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 2, 6]
def baseStart_1254239 : Nat := 118140960795 + 1254239 * 2 ^ 59
def prefixEnd_1254239 : Nat := 4983230072969 + 3 ^ 40 * 1254239 * 2
def baseEnd_1254239 : Nat := 429351641743082345229577

theorem tailTrace_1254239 : CollatzResearch.WordTrace tailWord_1254239 prefixEnd_1254239 429351641743082345229577 := by
  unfold tailWord_1254239
  simp only [CollatzResearch.WordTrace]
  refine ⟨45745854503113784812421771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30497236335409189874947847 45745854503113784812421771)
  ·
    refine ⟨68618781754670677218632657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45745854503113784812421771 68618781754670677218632657)
    ·
      refine ⟨51464086316003007913974493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68618781754670677218632657 51464086316003007913974493)
      ·
        refine ⟨19299032368501127967740435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51464086316003007913974493 19299032368501127967740435)
        ·
          refine ⟨28948548552751691951610653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19299032368501127967740435 28948548552751691951610653)
          ·
            refine ⟨10855705707281884481853995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28948548552751691951610653 10855705707281884481853995)
            ·
              refine ⟨16283558560922826722780993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10855705707281884481853995 16283558560922826722780993)
              ·
                refine ⟨12212668920692120042085745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16283558560922826722780993 12212668920692120042085745)
                ·
                  refine ⟨9159501690519090031564309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12212668920692120042085745 9159501690519090031564309)
                  ·
                    refine ⟨429351641743082345229577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9159501690519090031564309 429351641743082345229577)
                    ·
                      rfl

theorem cell22_1254239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_1254239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254239 prefixEnd_1254239 := by exact prefixLift 1254239
  have htrace : WordTrace (prefixWord ++ tailWord_1254239) baseStart_1254239 baseEnd_1254239 := by
    simpa [prefixWord, tailWord_1254239, baseEnd_1254239] using wordTrace_append hprefix tailTrace_1254239
  have hstable : (prefixWord ++ tailWord_1254239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254239).length < 2 ^ (prefixWord ++ tailWord_1254239).sum := by decide
  have hdescent : baseEnd_1254239 < baseStart_1254239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254271 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 5]
def baseStart_1254271 : Nat := 118140960795 + 1254271 * 2 ^ 59
def prefixEnd_1254271 : Nat := 4983230072969 + 3 ^ 40 * 1254271 * 2
def baseEnd_1254271 : Nat := 143120865332348309476493

theorem tailTrace_1254271 : CollatzResearch.WordTrace tailWord_1254271 prefixEnd_1254271 143120865332348309476493 := by
  unfold tailWord_1254271
  simp only [CollatzResearch.WordTrace]
  refine ⟨45747021638997854277586667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30498014425998569518391111 45747021638997854277586667)
  ·
    refine ⟨68620532458496781416380001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45747021638997854277586667 68620532458496781416380001)
    ·
      refine ⟨51465399343872586062285001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68620532458496781416380001 51465399343872586062285001)
      ·
        refine ⟨38599049507904439546713751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51465399343872586062285001 38599049507904439546713751)
        ·
          refine ⟨57898574261856659320070627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38599049507904439546713751 57898574261856659320070627)
          ·
            refine ⟨86847861392784988980105941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57898574261856659320070627 86847861392784988980105941)
            ·
              refine ⟨2035496751393398179221233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86847861392784988980105941 2035496751393398179221233)
              ·
                refine ⟨1526622563545048634415925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035496751393398179221233 1526622563545048634415925)
                ·
                  refine ⟨143120865332348309476493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1526622563545048634415925 143120865332348309476493)
                  ·
                    rfl

theorem cell22_1254271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 5].length) (baseStart_1254271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254271 prefixEnd_1254271 := by exact prefixLift 1254271
  have htrace : WordTrace (prefixWord ++ tailWord_1254271) baseStart_1254271 baseEnd_1254271 := by
    simpa [prefixWord, tailWord_1254271, baseEnd_1254271] using wordTrace_append hprefix tailTrace_1254271
  have hstable : (prefixWord ++ tailWord_1254271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254271).length < 2 ^ (prefixWord ++ tailWord_1254271).sum := by decide
  have hdescent : baseEnd_1254271 < baseStart_1254271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254326 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1254326 : Nat := 118140960795 + 1254326 * 2 ^ 59
def prefixEnd_1254326 : Nat := 4983230072969 + 3 ^ 40 * 1254326 * 2
def baseEnd_1254326 : Nat := 429381423621043118304311

theorem tailTrace_1254326 : CollatzResearch.WordTrace tailWord_1254326 prefixEnd_1254326 429381423621043118304311 := by
  unfold tailWord_1254326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859314228362412416927427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30499351769199065780559221 2859314228362412416927427)
  ·
    refine ⟨4288971342543618625391141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859314228362412416927427 4288971342543618625391141)
    ·
      refine ⟨804182126726928492260839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4288971342543618625391141 804182126726928492260839)
      ·
        refine ⟨1206273190090392738391259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804182126726928492260839 1206273190090392738391259)
        ·
          refine ⟨1809409785135589107586889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206273190090392738391259 1809409785135589107586889)
          ·
            refine ⟨1357057338851691830690167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1809409785135589107586889 1357057338851691830690167)
            ·
              refine ⟨2035586008277537746035251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357057338851691830690167 2035586008277537746035251)
              ·
                refine ⟨3053379012416306619052877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035586008277537746035251 3053379012416306619052877)
                ·
                  refine ⟨1145017129656114982144829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3053379012416306619052877 1145017129656114982144829)
                  ·
                    refine ⟨429381423621043118304311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145017129656114982144829 429381423621043118304311)
                    ·
                      rfl

theorem cell22_1254326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1254326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254326 prefixEnd_1254326 := by exact prefixLift 1254326
  have htrace : WordTrace (prefixWord ++ tailWord_1254326) baseStart_1254326 baseEnd_1254326 := by
    simpa [prefixWord, tailWord_1254326, baseEnd_1254326] using wordTrace_append hprefix tailTrace_1254326
  have hstable : (prefixWord ++ tailWord_1254326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254326).length < 2 ^ (prefixWord ++ tailWord_1254326).sum := by decide
  have hdescent : baseEnd_1254326 < baseStart_1254326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254331 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 8, 3]
def baseStart_1254331 : Nat := 118140960795 + 1254331 * 2 ^ 59
def prefixEnd_1254331 : Nat := 4983230072969 + 3 ^ 40 * 1254331 * 2
def baseEnd_1254331 : Nat := 429383135223224771929295

theorem tailTrace_1254331 : CollatzResearch.WordTrace tailWord_1254331 prefixEnd_1254331 429383135223224771929295 := by
  unfold tailWord_1254331
  simp only [CollatzResearch.WordTrace]
  refine ⟨45749210018780484524770847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30499473345853656349847231 45749210018780484524770847)
  ·
    refine ⟨68623815028170726787156271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45749210018780484524770847 68623815028170726787156271)
    ·
      refine ⟨102935722542256090180734407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68623815028170726787156271 102935722542256090180734407)
      ·
        refine ⟨154403583813384135271101611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102935722542256090180734407 154403583813384135271101611)
        ·
          refine ⟨231605375720076202906652417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154403583813384135271101611 231605375720076202906652417)
          ·
            refine ⟨173704031790057152179989313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231605375720076202906652417 173704031790057152179989313)
            ·
              refine ⟨130278023842542864134991985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173704031790057152179989313 130278023842542864134991985)
              ·
                refine ⟨97708517881907148101243989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130278023842542864134991985 97708517881907148101243989)
                ·
                  refine ⟨1145021693928599391811453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 97708517881907148101243989 1145021693928599391811453)
                  ·
                    refine ⟨429383135223224771929295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145021693928599391811453 429383135223224771929295)
                    ·
                      rfl

theorem cell22_1254331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 3].length) (baseStart_1254331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254331 prefixEnd_1254331 := by exact prefixLift 1254331
  have htrace : WordTrace (prefixWord ++ tailWord_1254331) baseStart_1254331 baseEnd_1254331 := by
    simpa [prefixWord, tailWord_1254331, baseEnd_1254331] using wordTrace_append hprefix tailTrace_1254331
  have hstable : (prefixWord ++ tailWord_1254331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254331).length < 2 ^ (prefixWord ++ tailWord_1254331).sum := by decide
  have hdescent : baseEnd_1254331 < baseStart_1254331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254346 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1254346 : Nat := 118140960795 + 1254346 * 2 ^ 59
def prefixEnd_1254346 : Nat := 4983230072969 + 3 ^ 40 * 1254346 * 2
def baseEnd_1254346 : Nat := 429388270029769732804249

theorem tailTrace_1254346 : CollatzResearch.WordTrace tailWord_1254346 prefixEnd_1254346 429388270029769732804249 := by
  unfold tailWord_1254346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11437439278431535521641723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30499838075817428057711261 11437439278431535521641723)
  ·
    refine ⟨17156158917647303282462585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11437439278431535521641723 17156158917647303282462585)
    ·
      refine ⟨12867119188235477461846939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17156158917647303282462585 12867119188235477461846939)
      ·
        refine ⟨19300678782353216192770409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12867119188235477461846939 19300678782353216192770409)
        ·
          refine ⟨14475509086764912144577807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19300678782353216192770409 14475509086764912144577807)
          ·
            refine ⟨21713263630147368216866711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14475509086764912144577807 21713263630147368216866711)
            ·
              refine ⟨32569895445221052325300067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21713263630147368216866711 32569895445221052325300067)
              ·
                refine ⟨48854843167831578487950101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32569895445221052325300067 48854843167831578487950101)
                ·
                  refine ⟨2290070773492105241622661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48854843167831578487950101 2290070773492105241622661)
                  ·
                    refine ⟨429388270029769732804249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2290070773492105241622661 429388270029769732804249)
                    ·
                      rfl

theorem cell22_1254346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1254346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254346 prefixEnd_1254346 := by exact prefixLift 1254346
  have htrace : WordTrace (prefixWord ++ tailWord_1254346) baseStart_1254346 baseEnd_1254346 := by
    simpa [prefixWord, tailWord_1254346, baseEnd_1254346] using wordTrace_append hprefix tailTrace_1254346
  have hstable : (prefixWord ++ tailWord_1254346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254346).length < 2 ^ (prefixWord ++ tailWord_1254346).sum := by decide
  have hdescent : baseEnd_1254346 < baseStart_1254346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254361 : List Nat := [1, 2, 1, 2, 5, 1, 2, 8]
def baseStart_1254361 : Nat := 118140960795 + 1254361 * 2 ^ 59
def prefixEnd_1254361 : Nat := 4983230072969 + 3 ^ 40 * 1254361 * 2
def baseEnd_1254361 : Nat := 47710378315146077075467

theorem tailTrace_1254361 : CollatzResearch.WordTrace tailWord_1254361 prefixEnd_1254361 47710378315146077075467 := by
  unfold tailWord_1254361
  simp only [CollatzResearch.WordTrace]
  refine ⟨45750304208671799648362937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30500202805781199765575291 45750304208671799648362937)
  ·
    refine ⟨34312728156503849736272203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45750304208671799648362937 34312728156503849736272203)
    ·
      refine ⟨51469092234755774604408305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34312728156503849736272203 51469092234755774604408305)
      ·
        refine ⟨38601819176066830953306229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51469092234755774604408305 38601819176066830953306229)
        ·
          refine ⟨3618920547756265401872459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38601819176066830953306229 3618920547756265401872459)
          ·
            refine ⟨5428380821634398102808689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618920547756265401872459 5428380821634398102808689)
            ·
              refine ⟨4071285616225798577106517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5428380821634398102808689 4071285616225798577106517)
              ·
                refine ⟨47710378315146077075467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4071285616225798577106517 47710378315146077075467)
                ·
                  rfl

theorem cell22_1254361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 8].length) (baseStart_1254361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254361 prefixEnd_1254361 := by exact prefixLift 1254361
  have htrace : WordTrace (prefixWord ++ tailWord_1254361) baseStart_1254361 baseEnd_1254361 := by
    simpa [prefixWord, tailWord_1254361, baseEnd_1254361] using wordTrace_append hprefix tailTrace_1254361
  have hstable : (prefixWord ++ tailWord_1254361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254361).length < 2 ^ (prefixWord ++ tailWord_1254361).sum := by decide
  have hdescent : baseEnd_1254361 < baseStart_1254361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254382 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1254382 : Nat := 118140960795 + 1254382 * 2 ^ 59
def prefixEnd_1254382 : Nat := 4983230072969 + 3 ^ 40 * 1254382 * 2
def baseEnd_1254382 : Nat := 429400593565477638904139

theorem tailTrace_1254382 : CollatzResearch.WordTrace tailWord_1254382 prefixEnd_1254382 429400593565477638904139 := by
  unfold tailWord_1254382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5718883767699465029359675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30500713427730480156584933 5718883767699465029359675)
  ·
    refine ⟨8578325651549197544039513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5718883767699465029359675 8578325651549197544039513)
    ·
      refine ⟨6433744238661898158029635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8578325651549197544039513 6433744238661898158029635)
      ·
        refine ⟨9650616357992847237044453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6433744238661898158029635 9650616357992847237044453)
        ·
          refine ⟨1809490567123658856945835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9650616357992847237044453 1809490567123658856945835)
          ·
            refine ⟨2714235850685488285418753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809490567123658856945835 2714235850685488285418753)
            ·
              refine ⟨2035676888014116214064065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2714235850685488285418753 2035676888014116214064065)
              ·
                refine ⟨1526757666010587160548049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035676888014116214064065 1526757666010587160548049)
                ·
                  refine ⟨1145068249507940370411037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1526757666010587160548049 1145068249507940370411037)
                  ·
                    refine ⟨429400593565477638904139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145068249507940370411037 429400593565477638904139)
                    ·
                      rfl

theorem cell22_1254382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1254382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254382 prefixEnd_1254382 := by exact prefixLift 1254382
  have htrace : WordTrace (prefixWord ++ tailWord_1254382) baseStart_1254382 baseEnd_1254382 := by
    simpa [prefixWord, tailWord_1254382, baseEnd_1254382] using wordTrace_append hprefix tailTrace_1254382
  have hstable : (prefixWord ++ tailWord_1254382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254382).length < 2 ^ (prefixWord ++ tailWord_1254382).sum := by decide
  have hdescent : baseEnd_1254382 < baseStart_1254382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254393 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 3, 3]
def baseStart_1254393 : Nat := 118140960795 + 1254393 * 2 ^ 59
def prefixEnd_1254393 : Nat := 4983230072969 + 3 ^ 40 * 1254393 * 2
def baseEnd_1254393 : Nat := 429404359090277276879105

theorem tailTrace_1254393 : CollatzResearch.WordTrace tailWord_1254393 prefixEnd_1254393 429404359090277276879105 := by
  unfold tailWord_1254393
  simp only [CollatzResearch.WordTrace]
  refine ⟨45751471344555869113527833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30500980896370579409018555 45751471344555869113527833)
  ·
    refine ⟨34313603508416901835145875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45751471344555869113527833 34313603508416901835145875)
    ·
      refine ⟨51470405262625352752718813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34313603508416901835145875 51470405262625352752718813)
      ·
        refine ⟨19301401973484507282269555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51470405262625352752718813 19301401973484507282269555)
        ·
          refine ⟨28952102960226760923404333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19301401973484507282269555 28952102960226760923404333)
          ·
            refine ⟨10857038610085035346276625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28952102960226760923404333 10857038610085035346276625)
            ·
              refine ⟨8142778957563776509707469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10857038610085035346276625 8142778957563776509707469)
              ·
                refine ⟨3053542109086416191140301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8142778957563776509707469 3053542109086416191140301)
                ·
                  refine ⟨1145078290907406071677613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3053542109086416191140301 1145078290907406071677613)
                  ·
                    refine ⟨429404359090277276879105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145078290907406071677613 429404359090277276879105)
                    ·
                      rfl

theorem cell22_1254393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_1254393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254393 prefixEnd_1254393 := by exact prefixLift 1254393
  have htrace : WordTrace (prefixWord ++ tailWord_1254393) baseStart_1254393 baseEnd_1254393 := by
    simpa [prefixWord, tailWord_1254393, baseEnd_1254393] using wordTrace_append hprefix tailTrace_1254393
  have hstable : (prefixWord ++ tailWord_1254393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254393).length < 2 ^ (prefixWord ++ tailWord_1254393).sum := by decide
  have hdescent : baseEnd_1254393 < baseStart_1254393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254410 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_1254410 : Nat := 118140960795 + 1254410 * 2 ^ 59
def prefixEnd_1254410 : Nat := 4983230072969 + 3 ^ 40 * 1254410 * 2
def baseEnd_1254410 : Nat := 429410178537694899204053

theorem tailTrace_1254410 : CollatzResearch.WordTrace tailWord_1254410 prefixEnd_1254410 429410178537694899204053 := by
  unfold tailWord_1254410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438022846373570254224171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30501394256996187344597789 11438022846373570254224171)
  ·
    refine ⟨17157034269560355381336257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11438022846373570254224171 17157034269560355381336257)
    ·
      refine ⟨12867775702170266536002193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17157034269560355381336257 12867775702170266536002193)
      ·
        refine ⟨9650831776627699902001645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12867775702170266536002193 9650831776627699902001645)
        ·
          refine ⟨3619061916235387463250617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9650831776627699902001645 3619061916235387463250617)
          ·
            refine ⟨2714296437176540597437963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619061916235387463250617 2714296437176540597437963)
            ·
              refine ⟨4071444655764810896156945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714296437176540597437963 4071444655764810896156945)
              ·
                refine ⟨3053583491823608172117709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4071444655764810896156945 3053583491823608172117709)
                ·
                  refine ⟨1145093809433853064544141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3053583491823608172117709 1145093809433853064544141)
                  ·
                    refine ⟨429410178537694899204053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145093809433853064544141 429410178537694899204053)
                    ·
                      rfl

theorem cell22_1254410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_1254410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254410 prefixEnd_1254410 := by exact prefixLift 1254410
  have htrace : WordTrace (prefixWord ++ tailWord_1254410) baseStart_1254410 baseEnd_1254410 := by
    simpa [prefixWord, tailWord_1254410, baseEnd_1254410] using wordTrace_append hprefix tailTrace_1254410
  have hstable : (prefixWord ++ tailWord_1254410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254410).length < 2 ^ (prefixWord ++ tailWord_1254410).sum := by decide
  have hdescent : baseEnd_1254410 < baseStart_1254410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254483 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 4, 3]
def baseStart_1254483 : Nat := 118140960795 + 1254483 * 2 ^ 59
def prefixEnd_1254483 : Nat := 4983230072969 + 3 ^ 40 * 1254483 * 2
def baseEnd_1254483 : Nat := 429435167929547042128829

theorem tailTrace_1254483 : CollatzResearch.WordTrace tailWord_1254483 prefixEnd_1254483 429435167929547042128829 := by
  unfold tailWord_1254483
  simp only [CollatzResearch.WordTrace]
  refine ⟨45754753914229814484304103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30503169276153209656202735 45754753914229814484304103)
  ·
    refine ⟨68632130871344721726456155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45754753914229814484304103 68632130871344721726456155)
    ·
      refine ⟨102948196307017082589684233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68632130871344721726456155 102948196307017082589684233)
      ·
        refine ⟨77211147230262811942263175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102948196307017082589684233 77211147230262811942263175)
        ·
          refine ⟨115816720845394217913394763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77211147230262811942263175 115816720845394217913394763)
          ·
            refine ⟨173725081268091326870092145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115816720845394217913394763 173725081268091326870092145)
            ·
              refine ⟨130293810951068495152569109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173725081268091326870092145 130293810951068495152569109)
              ·
                refine ⟨6107522388331335710276677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130293810951068495152569109 6107522388331335710276677)
                ·
                  refine ⟨1145160447812125445676877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6107522388331335710276677 1145160447812125445676877)
                  ·
                    refine ⟨429435167929547042128829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145160447812125445676877 429435167929547042128829)
                    ·
                      rfl

theorem cell22_1254483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 3].length) (baseStart_1254483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254483 prefixEnd_1254483 := by exact prefixLift 1254483
  have htrace : WordTrace (prefixWord ++ tailWord_1254483) baseStart_1254483 baseEnd_1254483 := by
    simpa [prefixWord, tailWord_1254483, baseEnd_1254483] using wordTrace_append hprefix tailTrace_1254483
  have hstable : (prefixWord ++ tailWord_1254483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254483).length < 2 ^ (prefixWord ++ tailWord_1254483).sum := by decide
  have hdescent : baseEnd_1254483 < baseStart_1254483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254500 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_1254500 : Nat := 118140960795 + 1254500 * 2 ^ 59
def prefixEnd_1254500 : Nat := 4983230072969 + 3 ^ 40 * 1254500 * 2
def baseEnd_1254500 : Nat := 429440987376964664453777

theorem tailTrace_1254500 : CollatzResearch.WordTrace tailWord_1254500 prefixEnd_1254500 429440987376964664453777 := by
  unfold tailWord_1254500
  simp only [CollatzResearch.WordTrace]
  refine ⟨22877686977584113193836477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30503582636778817591781969 22877686977584113193836477)
  ·
    refine ⟨8579132616594042447688679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22877686977584113193836477 8579132616594042447688679)
    ·
      refine ⟨12868698924891063671533019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8579132616594042447688679 12868698924891063671533019)
      ·
        refine ⟨19303048387336595507299529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12868698924891063671533019 19303048387336595507299529)
        ·
          refine ⟨14477286290502446630474647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19303048387336595507299529 14477286290502446630474647)
          ·
            refine ⟨21715929435753669945711971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14477286290502446630474647 21715929435753669945711971)
            ·
              refine ⟨32573894153630504918567957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21715929435753669945711971 32573894153630504918567957)
              ·
                refine ⟨1526901288451429918057873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32573894153630504918567957 1526901288451429918057873)
                ·
                  refine ⟨1145175966338572438543405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1526901288451429918057873 1145175966338572438543405)
                  ·
                    refine ⟨429440987376964664453777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145175966338572438543405 429440987376964664453777)
                    ·
                      rfl

theorem cell22_1254500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_1254500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254500 prefixEnd_1254500 := by exact prefixLift 1254500
  have htrace : WordTrace (prefixWord ++ tailWord_1254500) baseStart_1254500 baseEnd_1254500 := by
    simpa [prefixWord, tailWord_1254500, baseEnd_1254500] using wordTrace_append hprefix tailTrace_1254500
  have hstable : (prefixWord ++ tailWord_1254500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254500).length < 2 ^ (prefixWord ++ tailWord_1254500).sum := by decide
  have hdescent : baseEnd_1254500 < baseStart_1254500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254596 : List Nat := [2, 3, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1254596 : Nat := 118140960795 + 1254596 * 2 ^ 59
def prefixEnd_1254596 : Nat := 4983230072969 + 3 ^ 40 * 1254596 * 2
def baseEnd_1254596 : Nat := 429473850138852414053483

theorem tailTrace_1254596 : CollatzResearch.WordTrace tailWord_1254596 prefixEnd_1254596 429473850138852414053483 := by
  unfold tailWord_1254596
  simp only [CollatzResearch.WordTrace]
  refine ⟨22879437681410217391583821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30505916908546956522111761 22879437681410217391583821)
  ·
    refine ⟨8579789130528831521843933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22879437681410217391583821 8579789130528831521843933)
    ·
      refine ⟨3217420923948311820691475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8579789130528831521843933 3217420923948311820691475)
      ·
        refine ⟨4826131385922467731037213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217420923948311820691475 4826131385922467731037213)
        ·
          refine ⟨1809799269720925399138955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4826131385922467731037213 1809799269720925399138955)
          ·
            refine ⟨2714698904581388098708433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809799269720925399138955 2714698904581388098708433)
            ·
              refine ⟨2036024178436041074031325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2714698904581388098708433 2036024178436041074031325)
              ·
                refine ⟨763509066913515402761747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036024178436041074031325 763509066913515402761747)
                ·
                  refine ⟨1145263600370273104142621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763509066913515402761747 1145263600370273104142621)
                  ·
                    refine ⟨429473850138852414053483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145263600370273104142621 429473850138852414053483)
                    ·
                      rfl

theorem cell22_1254596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1254596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254596 prefixEnd_1254596 := by exact prefixLift 1254596
  have htrace : WordTrace (prefixWord ++ tailWord_1254596) baseStart_1254596 baseEnd_1254596 := by
    simpa [prefixWord, tailWord_1254596, baseEnd_1254596] using wordTrace_append hprefix tailTrace_1254596
  have hstable : (prefixWord ++ tailWord_1254596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254596).length < 2 ^ (prefixWord ++ tailWord_1254596).sum := by decide
  have hdescent : baseEnd_1254596 < baseStart_1254596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254635 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 1, 5]
def baseStart_1254635 : Nat := 118140960795 + 1254635 * 2 ^ 59
def prefixEnd_1254635 : Nat := 4983230072969 + 3 ^ 40 * 1254635 * 2
def baseEnd_1254635 : Nat := 429487200635869312328363

theorem tailTrace_1254635 : CollatzResearch.WordTrace tailWord_1254635 prefixEnd_1254635 429487200635869312328363 := by
  unfold tailWord_1254635
  simp only [CollatzResearch.WordTrace]
  refine ⟨45760297809679144443837359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30506865206452762962558239 45760297809679144443837359)
  ·
    refine ⟨68640446714518716665756039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45760297809679144443837359 68640446714518716665756039)
    ·
      refine ⟨102960670071778074998634059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68640446714518716665756039 102960670071778074998634059)
      ·
        refine ⟨154441005107667112497951089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102960670071778074998634059 154441005107667112497951089)
        ·
          refine ⟨115830753830750334373463317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154441005107667112497951089 115830753830750334373463317)
          ·
            refine ⟨5429566585816421923756093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115830753830750334373463317 5429566585816421923756093)
            ·
              refine ⟨2036087469681158221408535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5429566585816421923756093 2036087469681158221408535)
              ·
                refine ⟨3054131204521737332112803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036087469681158221408535 3054131204521737332112803)
                ·
                  refine ⟨4581196806782605998169205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054131204521737332112803 4581196806782605998169205)
                  ·
                    refine ⟨429487200635869312328363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4581196806782605998169205 429487200635869312328363)
                    ·
                      rfl

theorem cell22_1254635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5].length) (baseStart_1254635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254635 prefixEnd_1254635 := by exact prefixLift 1254635
  have htrace : WordTrace (prefixWord ++ tailWord_1254635) baseStart_1254635 baseEnd_1254635 := by
    simpa [prefixWord, tailWord_1254635, baseEnd_1254635] using wordTrace_append hprefix tailTrace_1254635
  have hstable : (prefixWord ++ tailWord_1254635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254635).length < 2 ^ (prefixWord ++ tailWord_1254635).sum := by decide
  have hdescent : baseEnd_1254635 < baseStart_1254635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254650 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_1254650 : Nat := 118140960795 + 1254650 * 2 ^ 59
def prefixEnd_1254650 : Nat := 4983230072969 + 3 ^ 40 * 1254650 * 2
def baseEnd_1254650 : Nat := 429492335442414273203317

theorem tailTrace_1254650 : CollatzResearch.WordTrace tailWord_1254650 prefixEnd_1254650 429492335442414273203317 := by
  unfold tailWord_1254650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11440211226156200501408351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30507229936416534670422269 11440211226156200501408351)
  ·
    refine ⟨17160316839234300752112527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11440211226156200501408351 17160316839234300752112527)
    ·
      refine ⟨25740475258851451128168791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17160316839234300752112527 25740475258851451128168791)
      ·
        refine ⟨38610712888277176692253187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25740475258851451128168791 38610712888277176692253187)
        ·
          refine ⟨57916069332415765038379781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38610712888277176692253187 57916069332415765038379781)
          ·
            refine ⟨10859262999827955944696209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57916069332415765038379781 10859262999827955944696209)
            ·
              refine ⟨8144447249870966958522157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10859262999827955944696209 8144447249870966958522157)
              ·
                refine ⟨3054167718701612609445809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8144447249870966958522157 3054167718701612609445809)
                ·
                  refine ⟨2290625789026209457084357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3054167718701612609445809 2290625789026209457084357)
                  ·
                    refine ⟨429492335442414273203317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2290625789026209457084357 429492335442414273203317)
                    ·
                      rfl

theorem cell22_1254650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_1254650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254650 prefixEnd_1254650 := by exact prefixLift 1254650
  have htrace : WordTrace (prefixWord ++ tailWord_1254650) baseStart_1254650 baseEnd_1254650 := by
    simpa [prefixWord, tailWord_1254650, baseEnd_1254650] using wordTrace_append hprefix tailTrace_1254650
  have hstable : (prefixWord ++ tailWord_1254650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254650).length < 2 ^ (prefixWord ++ tailWord_1254650).sum := by decide
  have hdescent : baseEnd_1254650 < baseStart_1254650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254654 : List Nat := [4, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_1254654 : Nat := 118140960795 + 1254654 * 2 ^ 59
def prefixEnd_1254654 : Nat := 4983230072969 + 3 ^ 40 * 1254654 * 2
def baseEnd_1254654 : Nat := 143164568241386532034435

theorem tailTrace_1254654 : CollatzResearch.WordTrace tailWord_1254654 prefixEnd_1254654 143164568241386532034435 := by
  unfold tailWord_1254654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720123849576288836097377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30507327197740207125852677 5720123849576288836097377)
  ·
    refine ⟨4290092887182216627073033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5720123849576288836097377 4290092887182216627073033)
    ·
      refine ⟨3217569665386662470304775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4290092887182216627073033 3217569665386662470304775)
      ·
        refine ⟨4826354498079993705457163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217569665386662470304775 4826354498079993705457163)
        ·
          refine ⟨7239531747119990558185745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826354498079993705457163 7239531747119990558185745)
          ·
            refine ⟨5429648810339992918639309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239531747119990558185745 5429648810339992918639309)
            ·
              refine ⟨2036118303877497344489741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5429648810339992918639309 2036118303877497344489741)
              ·
                refine ⟨763544363954061504183653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036118303877497344489741 763544363954061504183653)
                ·
                  refine ⟨143164568241386532034435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763544363954061504183653 143164568241386532034435)
                  ·
                    rfl

theorem cell22_1254654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_1254654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254654 prefixEnd_1254654 := by exact prefixLift 1254654
  have htrace : WordTrace (prefixWord ++ tailWord_1254654) baseStart_1254654 baseEnd_1254654 := by
    simpa [prefixWord, tailWord_1254654, baseEnd_1254654] using wordTrace_append hprefix tailTrace_1254654
  have hstable : (prefixWord ++ tailWord_1254654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254654).length < 2 ^ (prefixWord ++ tailWord_1254654).sum := by decide
  have hdescent : baseEnd_1254654 < baseStart_1254654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254714 : List Nat := [3, 1, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_1254714 : Nat := 118140960795 + 1254714 * 2 ^ 59
def prefixEnd_1254714 : Nat := 4983230072969 + 3 ^ 40 * 1254714 * 2
def baseEnd_1254714 : Nat := 429514243950339439603121

theorem tailTrace_1254714 : CollatzResearch.WordTrace tailWord_1254714 prefixEnd_1254714 429514243950339439603121 := by
  unfold tailWord_1254714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11440794794098235233990799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30508786117595293957308797 11440794794098235233990799)
  ·
    refine ⟨17161192191147352850986199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11440794794098235233990799 17161192191147352850986199)
    ·
      refine ⟨25741788286721029276479299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17161192191147352850986199 25741788286721029276479299)
      ·
        refine ⟨38612682430081543914718949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25741788286721029276479299 38612682430081543914718949)
        ·
          refine ⟨7239877955640289484009803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38612682430081543914718949 7239877955640289484009803)
          ·
            refine ⟨10859816933460434226014705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239877955640289484009803 10859816933460434226014705)
            ·
              refine ⟨8144862700095325669511029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10859816933460434226014705 8144862700095325669511029)
              ·
                refine ⟨763580878133936781516659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8144862700095325669511029 763580878133936781516659)
                ·
                  refine ⟨1145371317200905172274989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763580878133936781516659 1145371317200905172274989)
                  ·
                    refine ⟨429514243950339439603121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145371317200905172274989 429514243950339439603121)
                    ·
                      rfl

theorem cell22_1254714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_1254714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254714 prefixEnd_1254714 := by exact prefixLift 1254714
  have htrace : WordTrace (prefixWord ++ tailWord_1254714) baseStart_1254714 baseEnd_1254714 := by
    simpa [prefixWord, tailWord_1254714, baseEnd_1254714] using wordTrace_append hprefix tailTrace_1254714
  have hstable : (prefixWord ++ tailWord_1254714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254714).length < 2 ^ (prefixWord ++ tailWord_1254714).sum := by decide
  have hdescent : baseEnd_1254714 < baseStart_1254714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254727 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 5]
def baseStart_1254727 : Nat := 118140960795 + 1254727 * 2 ^ 59
def prefixEnd_1254727 : Nat := 4983230072969 + 3 ^ 40 * 1254727 * 2
def baseEnd_1254727 : Nat := 143172898038670579676027

theorem tailTrace_1254727 : CollatzResearch.WordTrace tailWord_1254727 prefixEnd_1254727 143172898038670579676027 := by
  unfold tailWord_1254727
  simp only [CollatzResearch.WordTrace]
  refine ⟨45763653325345844156186435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30509102216897229437457623 45763653325345844156186435)
  ·
    refine ⟨68645479988018766234279653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45763653325345844156186435 68645479988018766234279653)
    ·
      refine ⟨12871027497753518668927435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68645479988018766234279653 12871027497753518668927435)
      ·
        refine ⟨19306541246630278003391153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12871027497753518668927435 19306541246630278003391153)
        ·
          refine ⟨14479905934972708502543365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19306541246630278003391153 14479905934972708502543365)
          ·
            refine ⟨2714982362807382844226881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14479905934972708502543365 2714982362807382844226881)
            ·
              refine ⟨2036236772105537133170161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2714982362807382844226881 2036236772105537133170161)
              ·
                refine ⟨1527177579079152849877621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036236772105537133170161 1527177579079152849877621)
                ·
                  refine ⟨143172898038670579676027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1527177579079152849877621 143172898038670579676027)
                  ·
                    rfl

theorem cell22_1254727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 5].length) (baseStart_1254727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254727 prefixEnd_1254727 := by exact prefixLift 1254727
  have htrace : WordTrace (prefixWord ++ tailWord_1254727) baseStart_1254727 baseEnd_1254727 := by
    simpa [prefixWord, tailWord_1254727, baseEnd_1254727] using wordTrace_append hprefix tailTrace_1254727
  have hstable : (prefixWord ++ tailWord_1254727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254727).length < 2 ^ (prefixWord ++ tailWord_1254727).sum := by decide
  have hdescent : baseEnd_1254727 < baseStart_1254727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254755 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 8]
def baseStart_1254755 : Nat := 118140960795 + 1254755 * 2 ^ 59
def prefixEnd_1254755 : Nat := 4983230072969 + 3 ^ 40 * 1254755 * 2
def baseEnd_1254755 : Nat := 143176093029409666442665

theorem tailTrace_1254755 : CollatzResearch.WordTrace tailWord_1254755 prefixEnd_1254755 143176093029409666442665 := by
  unfold tailWord_1254755
  simp only [CollatzResearch.WordTrace]
  refine ⟨45764674569244404938205719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30509783046162936625470479 45764674569244404938205719)
  ·
    refine ⟨68647011853866607407308579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45764674569244404938205719 68647011853866607407308579)
    ·
      refine ⟨102970517780799911110962869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68647011853866607407308579 102970517780799911110962869)
      ·
        refine ⟨9653486041949991666652769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102970517780799911110962869 9653486041949991666652769)
        ·
          refine ⟨7240114531462493749989577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9653486041949991666652769 7240114531462493749989577)
          ·
            refine ⟨5430085898596870312492183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240114531462493749989577 5430085898596870312492183)
            ·
              refine ⟨8145128847895305468738275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430085898596870312492183 8145128847895305468738275)
              ·
                refine ⟨12217693271842958203107413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8145128847895305468738275 12217693271842958203107413)
                ·
                  refine ⟨143176093029409666442665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12217693271842958203107413 143176093029409666442665)
                  ·
                    rfl

theorem cell22_1254755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_1254755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254755 prefixEnd_1254755 := by exact prefixLift 1254755
  have htrace : WordTrace (prefixWord ++ tailWord_1254755) baseStart_1254755 baseEnd_1254755 := by
    simpa [prefixWord, tailWord_1254755, baseEnd_1254755] using wordTrace_append hprefix tailTrace_1254755
  have hstable : (prefixWord ++ tailWord_1254755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254755).length < 2 ^ (prefixWord ++ tailWord_1254755).sum := by decide
  have hdescent : baseEnd_1254755 < baseStart_1254755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254757 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_1254757 : Nat := 118140960795 + 1254757 * 2 ^ 59
def prefixEnd_1254757 : Nat := 4983230072969 + 3 ^ 40 * 1254757 * 2
def baseEnd_1254757 : Nat := 429528963729101660777989

theorem tailTrace_1254757 : CollatzResearch.WordTrace tailWord_1254757 prefixEnd_1254757 429528963729101660777989 := by
  unfold tailWord_1254757
  simp only [CollatzResearch.WordTrace]
  refine ⟨45764747515237159279778525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30509831676824772853185683 45764747515237159279778525)
  ·
    refine ⟨17161780318213934729916947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45764747515237159279778525 17161780318213934729916947)
    ·
      refine ⟨25742670477320902094875421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17161780318213934729916947 25742670477320902094875421)
      ·
        refine ⟨9653501428995338285578283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25742670477320902094875421 9653501428995338285578283)
        ·
          refine ⟨14480252143493007428367425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9653501428995338285578283 14480252143493007428367425)
          ·
            refine ⟨10860189107619755571275569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14480252143493007428367425 10860189107619755571275569)
            ·
              refine ⟨8145141830714816678456677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10860189107619755571275569 8145141830714816678456677)
              ·
                refine ⟨1527214093259028127210627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8145141830714816678456677 1527214093259028127210627)
                ·
                  refine ⟨2290821139888542190815941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527214093259028127210627 2290821139888542190815941)
                  ·
                    refine ⟨429528963729101660777989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2290821139888542190815941 429528963729101660777989)
                    ·
                      rfl

theorem cell22_1254757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_1254757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254757 prefixEnd_1254757 := by exact prefixLift 1254757
  have htrace : WordTrace (prefixWord ++ tailWord_1254757) baseStart_1254757 baseEnd_1254757 := by
    simpa [prefixWord, tailWord_1254757, baseEnd_1254757] using wordTrace_append hprefix tailTrace_1254757
  have hstable : (prefixWord ++ tailWord_1254757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254757).length < 2 ^ (prefixWord ++ tailWord_1254757).sum := by decide
  have hdescent : baseEnd_1254757 < baseStart_1254757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254804 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1254804 : Nat := 118140960795 + 1254804 * 2 ^ 59
def prefixEnd_1254804 : Nat := 4983230072969 + 3 ^ 40 * 1254804 * 2
def baseEnd_1254804 : Nat := 429545052789609204852845

theorem tailTrace_1254804 : CollatzResearch.WordTrace tailWord_1254804 prefixEnd_1254804 429545052789609204852845 := by
  unfold tailWord_1254804
  simp only [CollatzResearch.WordTrace]
  refine ⟨22883230873033443153369733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30510974497377924204492977 22883230873033443153369733)
  ·
    refine ⟨4290605788693770591256825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22883230873033443153369733 4290605788693770591256825)
    ·
      refine ⟨3217954341520327943442619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4290605788693770591256825 3217954341520327943442619)
      ·
        refine ⟨4826931512280491915163929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217954341520327943442619 4826931512280491915163929)
        ·
          refine ⟨3620198634210368936372947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4826931512280491915163929 3620198634210368936372947)
          ·
            refine ⟨5430297951315553404559421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620198634210368936372947 5430297951315553404559421)
            ·
              refine ⟨2036361731743332526709783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5430297951315553404559421 2036361731743332526709783)
              ·
                refine ⟨3054542597614998790064675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036361731743332526709783 3054542597614998790064675)
                ·
                  refine ⟨4581813896422498185097013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054542597614998790064675 4581813896422498185097013)
                  ·
                    refine ⟨429545052789609204852845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4581813896422498185097013 429545052789609204852845)
                    ·
                      rfl

theorem cell22_1254804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1254804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254804 prefixEnd_1254804 := by exact prefixLift 1254804
  have htrace : WordTrace (prefixWord ++ tailWord_1254804) baseStart_1254804 baseEnd_1254804 := by
    simpa [prefixWord, tailWord_1254804, baseEnd_1254804] using wordTrace_append hprefix tailTrace_1254804
  have hstable : (prefixWord ++ tailWord_1254804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254804).length < 2 ^ (prefixWord ++ tailWord_1254804).sum := by decide
  have hdescent : baseEnd_1254804 < baseStart_1254804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254875 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]
def baseStart_1254875 : Nat := 118140960795 + 1254875 * 2 ^ 59
def prefixEnd_1254875 : Nat := 4983230072969 + 3 ^ 40 * 1254875 * 2
def baseEnd_1254875 : Nat := 429569357540588686327627

theorem tailTrace_1254875 : CollatzResearch.WordTrace tailWord_1254875 prefixEnd_1254875 429569357540588686327627 := by
  unfold tailWord_1254875
  simp only [CollatzResearch.WordTrace]
  refine ⟨45769051328809665432574079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30512700885873110288382719 45769051328809665432574079)
  ·
    refine ⟨68653576993214498148861119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45769051328809665432574079 68653576993214498148861119)
    ·
      refine ⟨102980365489821747223291679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68653576993214498148861119 102980365489821747223291679)
      ·
        refine ⟨154470548234732620834937519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102980365489821747223291679 154470548234732620834937519)
        ·
          refine ⟨231705822352098931252406279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154470548234732620834937519 231705822352098931252406279)
          ·
            refine ⟨347558733528148396878609419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231705822352098931252406279 347558733528148396878609419)
            ·
              refine ⟨521338100292222595317914129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347558733528148396878609419 521338100292222595317914129)
              ·
                refine ⟨391003575219166946488435597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521338100292222595317914129 391003575219166946488435597)
                ·
                  refine ⟨146626340707187604933163349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391003575219166946488435597 146626340707187604933163349)
                  ·
                    refine ⟨429569357540588686327627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 146626340707187604933163349 429569357540588686327627)
                    ·
                      rfl

theorem cell22_1254875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_1254875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254875 prefixEnd_1254875 := by exact prefixLift 1254875
  have htrace : WordTrace (prefixWord ++ tailWord_1254875) baseStart_1254875 baseEnd_1254875 := by
    simpa [prefixWord, tailWord_1254875, baseEnd_1254875] using wordTrace_append hprefix tailTrace_1254875
  have hstable : (prefixWord ++ tailWord_1254875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254875).length < 2 ^ (prefixWord ++ tailWord_1254875).sum := by decide
  have hdescent : baseEnd_1254875 < baseStart_1254875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254924 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 6]
def baseStart_1254924 : Nat := 118140960795 + 1254924 * 2 ^ 59
def prefixEnd_1254924 : Nat := 4983230072969 + 3 ^ 40 * 1254924 * 2
def baseEnd_1254924 : Nat := 143195377080656297284159

theorem tailTrace_1254924 : CollatzResearch.WordTrace tailWord_1254924 prefixEnd_1254924 143195377080656297284159 := by
  unfold tailWord_1254924
  simp only [CollatzResearch.WordTrace]
  refine ⟨22885419252816073400553913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30513892337088097867405217 22885419252816073400553913)
  ·
    refine ⟨17164064439612055050415435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22885419252816073400553913 17164064439612055050415435)
    ·
      refine ⟨25746096659418082575623153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17164064439612055050415435 25746096659418082575623153)
      ·
        refine ⟨19309572494563561931717365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25746096659418082575623153 19309572494563561931717365)
        ·
          refine ⟨1810272421365333931098503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19309572494563561931717365 1810272421365333931098503)
          ·
            refine ⟨2715408632048000896647755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810272421365333931098503 2715408632048000896647755)
            ·
              refine ⟨4073112948072001344971633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715408632048000896647755 4073112948072001344971633)
              ·
                refine ⟨3054834711054001008728725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4073112948072001344971633 3054834711054001008728725)
                ·
                  refine ⟨143195377080656297284159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3054834711054001008728725 143195377080656297284159)
                  ·
                    rfl

theorem cell22_1254924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_1254924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254924 prefixEnd_1254924 := by exact prefixLift 1254924
  have htrace : WordTrace (prefixWord ++ tailWord_1254924) baseStart_1254924 baseEnd_1254924 := by
    simpa [prefixWord, tailWord_1254924, baseEnd_1254924] using wordTrace_append hprefix tailTrace_1254924
  have hstable : (prefixWord ++ tailWord_1254924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254924).length < 2 ^ (prefixWord ++ tailWord_1254924).sum := by decide
  have hdescent : baseEnd_1254924 < baseStart_1254924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254941 : List Nat := [1, 4, 2, 2, 1, 1, 4, 3, 4]
def baseStart_1254941 : Nat := 118140960795 + 1254941 * 2 ^ 59
def prefixEnd_1254941 : Nat := 4983230072969 + 3 ^ 40 * 1254941 * 2
def baseEnd_1254941 : Nat := 143197316896462171392475

theorem tailTrace_1254941 : CollatzResearch.WordTrace tailWord_1254941 prefixEnd_1254941 143197316896462171392475 := by
  unfold tailWord_1254941
  simp only [CollatzResearch.WordTrace]
  refine ⟨45771458546570558704476677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30514305697713705802984451 45771458546570558704476677)
  ·
    refine ⟨8582148477481979757089377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45771458546570558704476677 8582148477481979757089377)
    ·
      refine ⟨6436611358111484817817033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8582148477481979757089377 6436611358111484817817033)
      ·
        refine ⟨4827458518583613613362775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6436611358111484817817033 4827458518583613613362775)
        ·
          refine ⟨7241187777875420420044163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827458518583613613362775 7241187777875420420044163)
          ·
            refine ⟨10861781666813130630066245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7241187777875420420044163 10861781666813130630066245)
            ·
              refine ⟨2036584062527461993137421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10861781666813130630066245 2036584062527461993137421)
              ·
                refine ⟨763719023447798247426533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036584062527461993137421 763719023447798247426533)
                ·
                  refine ⟨143197316896462171392475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763719023447798247426533 143197316896462171392475)
                  ·
                    rfl

theorem cell22_1254941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_1254941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254941 prefixEnd_1254941 := by exact prefixLift 1254941
  have htrace : WordTrace (prefixWord ++ tailWord_1254941) baseStart_1254941 baseEnd_1254941 := by
    simpa [prefixWord, tailWord_1254941, baseEnd_1254941] using wordTrace_append hprefix tailTrace_1254941
  have hstable : (prefixWord ++ tailWord_1254941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254941).length < 2 ^ (prefixWord ++ tailWord_1254941).sum := by decide
  have hdescent : baseEnd_1254941 < baseStart_1254941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254954 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1254954 : Nat := 118140960795 + 1254954 * 2 ^ 59
def prefixEnd_1254954 : Nat := 4983230072969 + 3 ^ 40 * 1254954 * 2
def baseEnd_1254954 : Nat := 429596400855058813602385

theorem tailTrace_1254954 : CollatzResearch.WordTrace tailWord_1254954 prefixEnd_1254954 429596400855058813602385 := by
  unfold tailWord_1254954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442983173880865481174979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30514621797015641283133277 11442983173880865481174979)
  ·
    refine ⟨17164474760821298221762469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11442983173880865481174979 17164474760821298221762469)
    ·
      refine ⟨3218339017653993416580463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17164474760821298221762469 3218339017653993416580463)
      ·
        refine ⟨4827508526480990124870695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218339017653993416580463 4827508526480990124870695)
        ·
          refine ⟨7241262789721485187306043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827508526480990124870695 7241262789721485187306043)
          ·
            refine ⟨10861894184582227780959065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7241262789721485187306043 10861894184582227780959065)
            ·
              refine ⟨8146420638436670835719299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10861894184582227780959065 8146420638436670835719299)
              ·
                refine ⟨12219630957655006253578949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8146420638436670835719299 12219630957655006253578949)
                ·
                  refine ⟨2291180804560313672546053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12219630957655006253578949 2291180804560313672546053)
                  ·
                    refine ⟨429596400855058813602385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291180804560313672546053 429596400855058813602385)
                    ·
                      rfl

theorem cell22_1254954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1254954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254954 prefixEnd_1254954 := by exact prefixLift 1254954
  have htrace : WordTrace (prefixWord ++ tailWord_1254954) baseStart_1254954 baseEnd_1254954 := by
    simpa [prefixWord, tailWord_1254954, baseEnd_1254954] using wordTrace_append hprefix tailTrace_1254954
  have hstable : (prefixWord ++ tailWord_1254954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254954).length < 2 ^ (prefixWord ++ tailWord_1254954).sum := by decide
  have hdescent : baseEnd_1254954 < baseStart_1254954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254973 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_1254973 : Nat := 118140960795 + 1254973 * 2 ^ 59
def prefixEnd_1254973 : Nat := 4983230072969 + 3 ^ 40 * 1254973 * 2
def baseEnd_1254973 : Nat := 429602904943349097377327

theorem tailTrace_1254973 : CollatzResearch.WordTrace tailWord_1254973 prefixEnd_1254973 429602904943349097377327 := by
  unfold tailWord_1254973
  simp only [CollatzResearch.WordTrace]
  refine ⟨45772625682454628169641573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30515083788303085446427715 45772625682454628169641573)
  ·
    refine ⟨8582367315460242781807795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45772625682454628169641573 8582367315460242781807795)
    ·
      refine ⟨12873550973190364172711693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8582367315460242781807795 12873550973190364172711693)
      ·
        refine ⟨4827581614946386564766885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12873550973190364172711693 4827581614946386564766885)
        ·
          refine ⟨905171552802447480893791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4827581614946386564766885 905171552802447480893791)
          ·
            refine ⟨1357757329203671221340687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905171552802447480893791 1357757329203671221340687)
            ·
              refine ⟨2036635993805506832011031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357757329203671221340687 2036635993805506832011031)
              ·
                refine ⟨3054953990708260248016547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036635993805506832011031 3054953990708260248016547)
                ·
                  refine ⟨4582430986062390372024821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054953990708260248016547 4582430986062390372024821)
                  ·
                    refine ⟨429602904943349097377327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4582430986062390372024821 429602904943349097377327)
                    ·
                      rfl

theorem cell22_1254973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_1254973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1254973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1254973 prefixEnd_1254973 := by exact prefixLift 1254973
  have htrace : WordTrace (prefixWord ++ tailWord_1254973) baseStart_1254973 baseEnd_1254973 := by
    simpa [prefixWord, tailWord_1254973, baseEnd_1254973] using wordTrace_append hprefix tailTrace_1254973
  have hstable : (prefixWord ++ tailWord_1254973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254973).length < 2 ^ (prefixWord ++ tailWord_1254973).sum := by decide
  have hdescent : baseEnd_1254973 < baseStart_1254973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255018 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_1255018 : Nat := 118140960795 + 1255018 * 2 ^ 59
def prefixEnd_1255018 : Nat := 4983230072969 + 3 ^ 40 * 1255018 * 2
def baseEnd_1255018 : Nat := 429618309362983980002189

theorem tailTrace_1255018 : CollatzResearch.WordTrace tailWord_1255018 prefixEnd_1255018 429618309362983980002189 := by
  unfold tailWord_1255018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443566741822900213757427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30516177978194400570019805 11443566741822900213757427)
  ·
    refine ⟨17165350112734350320636141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11443566741822900213757427 17165350112734350320636141)
    ·
      refine ⟨6437006292275381370238553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17165350112734350320636141 6437006292275381370238553)
      ·
        refine ⟨4827754719206536027678915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6437006292275381370238553 4827754719206536027678915)
        ·
          refine ⟨7241632078809804041518373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827754719206536027678915 7241632078809804041518373)
          ·
            refine ⟨1357806014776838257784695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7241632078809804041518373 1357806014776838257784695)
            ·
              refine ⟨2036709022165257386677043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357806014776838257784695 2036709022165257386677043)
              ·
                refine ⟨3055063533247886080015565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036709022165257386677043 3055063533247886080015565)
                ·
                  refine ⟨1145648824967957280005837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3055063533247886080015565 1145648824967957280005837)
                  ·
                    refine ⟨429618309362983980002189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145648824967957280005837 429618309362983980002189)
                    ·
                      rfl

theorem cell22_1255018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_1255018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255018 prefixEnd_1255018 := by exact prefixLift 1255018
  have htrace : WordTrace (prefixWord ++ tailWord_1255018) baseStart_1255018 baseEnd_1255018 := by
    simpa [prefixWord, tailWord_1255018, baseEnd_1255018] using wordTrace_append hprefix tailTrace_1255018
  have hstable : (prefixWord ++ tailWord_1255018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255018).length < 2 ^ (prefixWord ++ tailWord_1255018).sum := by decide
  have hdescent : baseEnd_1255018 < baseStart_1255018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255080 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1255080 : Nat := 118140960795 + 1255080 * 2 ^ 59
def prefixEnd_1255080 : Nat := 4983230072969 + 3 ^ 40 * 1255080 * 2
def baseEnd_1255080 : Nat := 429639533230036484951999

theorem tailTrace_1255080 : CollatzResearch.WordTrace tailWord_1255080 prefixEnd_1255080 429639533230036484951999 := by
  unfold tailWord_1255080
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888264146533492721893347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30517685528711323629191129 22888264146533492721893347)
  ·
    refine ⟨34332396219800239082840021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22888264146533492721893347 34332396219800239082840021)
    ·
      refine ⟨804665536401568103504063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34332396219800239082840021 804665536401568103504063)
      ·
        refine ⟨1206998304602352155256095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804665536401568103504063 1206998304602352155256095)
        ·
          refine ⟨1810497456903528232884143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206998304602352155256095 1810497456903528232884143)
          ·
            refine ⟨2715746185355292349326215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810497456903528232884143 2715746185355292349326215)
            ·
              refine ⟨4073619278032938523989323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715746185355292349326215 4073619278032938523989323)
              ·
                refine ⟨6110428917049407785983985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073619278032938523989323 6110428917049407785983985)
                ·
                  refine ⟨4582821687787055839487989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6110428917049407785983985 4582821687787055839487989)
                  ·
                    refine ⟨429639533230036484951999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4582821687787055839487989 429639533230036484951999)
                    ·
                      rfl

theorem cell22_1255080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1255080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255080 prefixEnd_1255080 := by exact prefixLift 1255080
  have htrace : WordTrace (prefixWord ++ tailWord_1255080) baseStart_1255080 baseEnd_1255080 := by
    simpa [prefixWord, tailWord_1255080, baseEnd_1255080] using wordTrace_append hprefix tailTrace_1255080
  have hstable : (prefixWord ++ tailWord_1255080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255080).length < 2 ^ (prefixWord ++ tailWord_1255080).sum := by decide
  have hdescent : baseEnd_1255080 < baseStart_1255080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255091 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 2, 3]
def baseStart_1255091 : Nat := 118140960795 + 1255091 * 2 ^ 59
def prefixEnd_1255091 : Nat := 4983230072969 + 3 ^ 40 * 1255091 * 2
def baseEnd_1255091 : Nat := 429643298754836122926965

theorem tailTrace_1255091 : CollatzResearch.WordTrace tailWord_1255091 prefixEnd_1255091 429643298754836122926965 := by
  unfold tailWord_1255091
  simp only [CollatzResearch.WordTrace]
  refine ⟨45776929496027134322437127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30517952997351422881624751 45776929496027134322437127)
  ·
    refine ⟨68665394244040701483655691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45776929496027134322437127 68665394244040701483655691)
    ·
      refine ⟨102998091366061052225483537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68665394244040701483655691 102998091366061052225483537)
      ·
        refine ⟨77248568524545789169112653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102998091366061052225483537 77248568524545789169112653)
        ·
          refine ⟨28968213196704670938417245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77248568524545789169112653 28968213196704670938417245)
          ·
            refine ⟨10863079948764251601906467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28968213196704670938417245 10863079948764251601906467)
            ·
              refine ⟨16294619923146377402859701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10863079948764251601906467 16294619923146377402859701)
              ·
                refine ⟨1527620617794972881518097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16294619923146377402859701 1527620617794972881518097)
                ·
                  refine ⟨1145715463346229661138573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1527620617794972881518097 1145715463346229661138573)
                  ·
                    refine ⟨429643298754836122926965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145715463346229661138573 429643298754836122926965)
                    ·
                      rfl

theorem cell22_1255091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 3].length) (baseStart_1255091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255091 prefixEnd_1255091 := by exact prefixLift 1255091
  have htrace : WordTrace (prefixWord ++ tailWord_1255091) baseStart_1255091 baseEnd_1255091 := by
    simpa [prefixWord, tailWord_1255091, baseEnd_1255091] using wordTrace_append hprefix tailTrace_1255091
  have hstable : (prefixWord ++ tailWord_1255091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255091).length < 2 ^ (prefixWord ++ tailWord_1255091).sum := by decide
  have hdescent : baseEnd_1255091 < baseStart_1255091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255136 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 3, 3]
def baseStart_1255136 : Nat := 118140960795 + 1255136 * 2 ^ 59
def prefixEnd_1255136 : Nat := 4983230072969 + 3 ^ 40 * 1255136 * 2
def baseEnd_1255136 : Nat := 429658703174471005551827

theorem tailTrace_1255136 : CollatzResearch.WordTrace tailWord_1255136 prefixEnd_1255136 429658703174471005551827 := by
  unfold tailWord_1255136
  simp only [CollatzResearch.WordTrace]
  refine ⟨22889285390432053503912631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30519047187242738005216841 22889285390432053503912631)
  ·
    refine ⟨34333928085648080255868947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22889285390432053503912631 34333928085648080255868947)
    ·
      refine ⟨51500892128472120383803421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34333928085648080255868947 51500892128472120383803421)
      ·
        refine ⟨19312834548177045143926283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51500892128472120383803421 19312834548177045143926283)
        ·
          refine ⟨28969251822265567715889425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19312834548177045143926283 28969251822265567715889425)
          ·
            refine ⟨21726938866699175786917069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28969251822265567715889425 21726938866699175786917069)
            ·
              refine ⟨8147602075012190920093901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21726938866699175786917069 8147602075012190920093901)
              ·
                refine ⟨3055350778129571595035213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8147602075012190920093901 3055350778129571595035213)
                ·
                  refine ⟨1145756541798589348138205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3055350778129571595035213 1145756541798589348138205)
                  ·
                    refine ⟨429658703174471005551827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145756541798589348138205 429658703174471005551827)
                    ·
                      rfl

theorem cell22_1255136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_1255136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255136 prefixEnd_1255136 := by exact prefixLift 1255136
  have htrace : WordTrace (prefixWord ++ tailWord_1255136) baseStart_1255136 baseEnd_1255136 := by
    simpa [prefixWord, tailWord_1255136, baseEnd_1255136] using wordTrace_append hprefix tailTrace_1255136
  have hstable : (prefixWord ++ tailWord_1255136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255136).length < 2 ^ (prefixWord ++ tailWord_1255136).sum := by decide
  have hdescent : baseEnd_1255136 < baseStart_1255136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255196 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1255196 : Nat := 118140960795 + 1255196 * 2 ^ 59
def prefixEnd_1255196 : Nat := 4983230072969 + 3 ^ 40 * 1255196 * 2
def baseEnd_1255196 : Nat := 429679242400650849051643

theorem tailTrace_1255196 : CollatzResearch.WordTrace tailWord_1255196 prefixEnd_1255196 429679242400650849051643 := by
  unfold tailWord_1255196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22890379580323368627504721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30520506107097824836672961 22890379580323368627504721)
  ·
    refine ⟨17167784685242526470628541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22890379580323368627504721 17167784685242526470628541)
    ·
      refine ⟨6437919256965947426485703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17167784685242526470628541 6437919256965947426485703)
      ·
        refine ⟨9656878885448921139728555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437919256965947426485703 9656878885448921139728555)
        ·
          refine ⟨14485318328173381709592833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9656878885448921139728555 14485318328173381709592833)
          ·
            refine ⟨10863988746130036282194625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14485318328173381709592833 10863988746130036282194625)
            ·
              refine ⟨8147991559597527211645969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10863988746130036282194625 8147991559597527211645969)
              ·
                refine ⟨6110993669698145408734477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8147991559597527211645969 6110993669698145408734477)
                ·
                  refine ⟨2291622626136804528275429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6110993669698145408734477 2291622626136804528275429)
                  ·
                    refine ⟨429679242400650849051643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291622626136804528275429 429679242400650849051643)
                    ·
                      rfl

theorem cell22_1255196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1255196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255196 prefixEnd_1255196 := by exact prefixLift 1255196
  have htrace : WordTrace (prefixWord ++ tailWord_1255196) baseStart_1255196 baseEnd_1255196 := by
    simpa [prefixWord, tailWord_1255196, baseEnd_1255196] using wordTrace_append hprefix tailTrace_1255196
  have hstable : (prefixWord ++ tailWord_1255196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255196).length < 2 ^ (prefixWord ++ tailWord_1255196).sum := by decide
  have hdescent : baseEnd_1255196 < baseStart_1255196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255226 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_1255226 : Nat := 118140960795 + 1255226 * 2 ^ 59
def prefixEnd_1255226 : Nat := 4983230072969 + 3 ^ 40 * 1255226 * 2
def baseEnd_1255226 : Nat := 429689512013740770801551

theorem tailTrace_1255226 : CollatzResearch.WordTrace tailWord_1255226 prefixEnd_1255226 429689512013740770801551 := by
  unfold tailWord_1255226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445463337634513094650383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30521235567025368252401021 11445463337634513094650383)
  ·
    refine ⟨17168195006451769641975575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11445463337634513094650383 17168195006451769641975575)
    ·
      refine ⟨25752292509677654462963363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17168195006451769641975575 25752292509677654462963363)
      ·
        refine ⟨38628438764516481694445045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25752292509677654462963363 38628438764516481694445045)
        ·
          refine ⟨3621416134173420158854223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38628438764516481694445045 3621416134173420158854223)
          ·
            refine ⟨5432124201260130238281335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621416134173420158854223 5432124201260130238281335)
            ·
              refine ⟨8148186301890195357422003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5432124201260130238281335 8148186301890195357422003)
              ·
                refine ⟨12222279452835293036133005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8148186301890195357422003 12222279452835293036133005)
                ·
                  refine ⟨4583354794813234888549877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12222279452835293036133005 4583354794813234888549877)
                  ·
                    refine ⟨429689512013740770801551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4583354794813234888549877 429689512013740770801551)
                    ·
                      rfl

theorem cell22_1255226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_1255226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255226 prefixEnd_1255226 := by exact prefixLift 1255226
  have htrace : WordTrace (prefixWord ++ tailWord_1255226) baseStart_1255226 baseEnd_1255226 := by
    simpa [prefixWord, tailWord_1255226, baseEnd_1255226] using wordTrace_append hprefix tailTrace_1255226
  have hstable : (prefixWord ++ tailWord_1255226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255226).length < 2 ^ (prefixWord ++ tailWord_1255226).sum := by decide
  have hdescent : baseEnd_1255226 < baseStart_1255226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255241 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_1255241 : Nat := 118140960795 + 1255241 * 2 ^ 59
def prefixEnd_1255241 : Nat := 4983230072969 + 3 ^ 40 * 1255241 * 2
def baseEnd_1255241 : Nat := 429694646820285731676505

theorem tailTrace_1255241 : CollatzResearch.WordTrace tailWord_1255241 prefixEnd_1255241 429694646820285731676505 := by
  unfold tailWord_1255241
  simp only [CollatzResearch.WordTrace]
  refine ⟨45782400445483709940397577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30521600296989139960265051 45782400445483709940397577)
  ·
    refine ⟨34336800334112782455298183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45782400445483709940397577 34336800334112782455298183)
    ·
      refine ⟨51505200501169173682947275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34336800334112782455298183 51505200501169173682947275)
      ·
        refine ⟨77257800751753760524420913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51505200501169173682947275 77257800751753760524420913)
        ·
          refine ⟨57943350563815320393315685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77257800751753760524420913 57943350563815320393315685)
          ·
            refine ⟨10864378230715372573746691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57943350563815320393315685 10864378230715372573746691)
            ·
              refine ⟨16296567346073058860620037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864378230715372573746691 16296567346073058860620037)
              ·
                refine ⟨3055606377388698536366257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16296567346073058860620037 3055606377388698536366257)
                ·
                  refine ⟨2291704783041523902274693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055606377388698536366257 2291704783041523902274693)
                  ·
                    refine ⟨429694646820285731676505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291704783041523902274693 429694646820285731676505)
                    ·
                      rfl

theorem cell22_1255241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_1255241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255241 prefixEnd_1255241 := by exact prefixLift 1255241
  have htrace : WordTrace (prefixWord ++ tailWord_1255241) baseStart_1255241 baseEnd_1255241 := by
    simpa [prefixWord, tailWord_1255241, baseEnd_1255241] using wordTrace_append hprefix tailTrace_1255241
  have hstable : (prefixWord ++ tailWord_1255241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255241).length < 2 ^ (prefixWord ++ tailWord_1255241).sum := by decide
  have hdescent : baseEnd_1255241 < baseStart_1255241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255260 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1255260 : Nat := 118140960795 + 1255260 * 2 ^ 59
def prefixEnd_1255260 : Nat := 4983230072969 + 3 ^ 40 * 1255260 * 2
def baseEnd_1255260 : Nat := 429701150908576015451447

theorem tailTrace_1255260 : CollatzResearch.WordTrace tailWord_1255260 prefixEnd_1255260 429701150908576015451447 := by
  unfold tailWord_1255260
  simp only [CollatzResearch.WordTrace]
  refine ⟨22891546716207438092669617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30522062288276584123559489 22891546716207438092669617)
  ·
    refine ⟨17168660037155578569502213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22891546716207438092669617 17168660037155578569502213)
    ·
      refine ⟨3219123756966670981781665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17168660037155578569502213 3219123756966670981781665)
      ·
        refine ⟨2414342817725003236336249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3219123756966670981781665 2414342817725003236336249)
        ·
          refine ⟨1810757113293752427252187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2414342817725003236336249 1810757113293752427252187)
          ·
            refine ⟨2716135669940628640878281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810757113293752427252187 2716135669940628640878281)
            ·
              refine ⟨2037101752455471480658711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2716135669940628640878281 2037101752455471480658711)
              ·
                refine ⟨3055652628683207220988067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037101752455471480658711 3055652628683207220988067)
                ·
                  refine ⟨4583478943024810831482101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055652628683207220988067 4583478943024810831482101)
                  ·
                    refine ⟨429701150908576015451447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4583478943024810831482101 429701150908576015451447)
                    ·
                      rfl

theorem cell22_1255260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1255260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255260 prefixEnd_1255260 := by exact prefixLift 1255260
  have htrace : WordTrace (prefixWord ++ tailWord_1255260) baseStart_1255260 baseEnd_1255260 := by
    simpa [prefixWord, tailWord_1255260, baseEnd_1255260] using wordTrace_append hprefix tailTrace_1255260
  have hstable : (prefixWord ++ tailWord_1255260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255260).length < 2 ^ (prefixWord ++ tailWord_1255260).sum := by decide
  have hdescent : baseEnd_1255260 < baseStart_1255260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255294 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1255294 : Nat := 118140960795 + 1255294 * 2 ^ 59
def prefixEnd_1255294 : Nat := 4983230072969 + 3 ^ 40 * 1255294 * 2
def baseEnd_1255294 : Nat := 429712789803411260101343

theorem tailTrace_1255294 : CollatzResearch.WordTrace tailWord_1255294 prefixEnd_1255294 429712789803411260101343 := by
  unfold tailWord_1255294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723041689286462499009617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30522889009527799994717957 5723041689286462499009617)
  ·
    refine ⟨4292281266964846874257213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5723041689286462499009617 4292281266964846874257213)
    ·
      refine ⟨1609605475111817577846455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4292281266964846874257213 1609605475111817577846455)
      ·
        refine ⟨2414408212667726366769683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609605475111817577846455 2414408212667726366769683)
        ·
          refine ⟨3621612319001589550154525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414408212667726366769683 3621612319001589550154525)
          ·
            refine ⟨1358104619625596081307947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3621612319001589550154525 1358104619625596081307947)
            ·
              refine ⟨2037156929438394121961921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358104619625596081307947 2037156929438394121961921)
              ·
                refine ⟨1527867697078795591471441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037156929438394121961921 1527867697078795591471441)
                ·
                  refine ⟨1145900772809096693603581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1527867697078795591471441 1145900772809096693603581)
                  ·
                    refine ⟨429712789803411260101343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145900772809096693603581 429712789803411260101343)
                    ·
                      rfl

theorem cell22_1255294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1255294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255294 prefixEnd_1255294 := by exact prefixLift 1255294
  have htrace : WordTrace (prefixWord ++ tailWord_1255294) baseStart_1255294 baseEnd_1255294 := by
    simpa [prefixWord, tailWord_1255294, baseEnd_1255294] using wordTrace_append hprefix tailTrace_1255294
  have hstable : (prefixWord ++ tailWord_1255294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255294).length < 2 ^ (prefixWord ++ tailWord_1255294).sum := by decide
  have hdescent : baseEnd_1255294 < baseStart_1255294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255301 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 7]
def baseStart_1255301 : Nat := 118140960795 + 1255301 * 2 ^ 59
def prefixEnd_1255301 : Nat := 4983230072969 + 3 ^ 40 * 1255301 * 2
def baseEnd_1255301 : Nat := 143238395348821858392107

theorem tailTrace_1255301 : CollatzResearch.WordTrace tailWord_1255301 prefixEnd_1255301 143238395348821858392107 := by
  unfold tailWord_1255301
  simp only [CollatzResearch.WordTrace]
  refine ⟨45784588825266340187581757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30523059216844226791721171 45784588825266340187581757)
  ·
    refine ⟨17169220809474877570343159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45784588825266340187581757 17169220809474877570343159)
    ·
      refine ⟨25753831214212316355514739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17169220809474877570343159 25753831214212316355514739)
      ·
        refine ⟨38630746821318474533272109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25753831214212316355514739 38630746821318474533272109)
        ·
          refine ⟨14486530057994427949977041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38630746821318474533272109 14486530057994427949977041)
          ·
            refine ⟨10864897543495820962482781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14486530057994427949977041 10864897543495820962482781)
            ·
              refine ⟨4074336578810932860931043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10864897543495820962482781 4074336578810932860931043)
              ·
                refine ⟨6111504868216399291396565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074336578810932860931043 6111504868216399291396565)
                ·
                  refine ⟨143238395348821858392107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6111504868216399291396565 143238395348821858392107)
                  ·
                    rfl

theorem cell22_1255301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_1255301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255301 prefixEnd_1255301 := by exact prefixLift 1255301
  have htrace : WordTrace (prefixWord ++ tailWord_1255301) baseStart_1255301 baseEnd_1255301 := by
    simpa [prefixWord, tailWord_1255301, baseEnd_1255301] using wordTrace_append hprefix tailTrace_1255301
  have hstable : (prefixWord ++ tailWord_1255301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255301).length < 2 ^ (prefixWord ++ tailWord_1255301).sum := by decide
  have hdescent : baseEnd_1255301 < baseStart_1255301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255305 : List Nat := [1, 2, 1, 1, 5, 1, 1, 6, 1, 3]
def baseStart_1255305 : Nat := 118140960795 + 1255305 * 2 ^ 59
def prefixEnd_1255305 : Nat := 4983230072969 + 3 ^ 40 * 1255305 * 2
def baseEnd_1255305 : Nat := 429716555328210898076309

theorem tailTrace_1255305 : CollatzResearch.WordTrace tailWord_1255305 prefixEnd_1255305 429716555328210898076309 := by
  unfold tailWord_1255305
  simp only [CollatzResearch.WordTrace]
  refine ⟨45784734717251848870727369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30523156478167899247151579 45784734717251848870727369)
  ·
    refine ⟨34338551037938886653045527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45784734717251848870727369 34338551037938886653045527)
    ·
      refine ⟨51507826556908329979568291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34338551037938886653045527 51507826556908329979568291)
      ·
        refine ⟨77261739835362494969352437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51507826556908329979568291 77261739835362494969352437)
        ·
          refine ⟨7243288109565233903376791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77261739835362494969352437 7243288109565233903376791)
          ·
            refine ⟨10864932164347850855065187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243288109565233903376791 10864932164347850855065187)
            ·
              refine ⟨16297398246521776282597781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864932164347850855065187 16297398246521776282597781)
              ·
                refine ⟨763940542805708263246771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16297398246521776282597781 763940542805708263246771)
                ·
                  refine ⟨1145910814208562394870157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763940542805708263246771 1145910814208562394870157)
                  ·
                    refine ⟨429716555328210898076309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145910814208562394870157 429716555328210898076309)
                    ·
                      rfl

theorem cell22_1255305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 3].length) (baseStart_1255305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255305 prefixEnd_1255305 := by exact prefixLift 1255305
  have htrace : WordTrace (prefixWord ++ tailWord_1255305) baseStart_1255305 baseEnd_1255305 := by
    simpa [prefixWord, tailWord_1255305, baseEnd_1255305] using wordTrace_append hprefix tailTrace_1255305
  have hstable : (prefixWord ++ tailWord_1255305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255305).length < 2 ^ (prefixWord ++ tailWord_1255305).sum := by decide
  have hdescent : baseEnd_1255305 < baseStart_1255305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255346 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1255346 : Nat := 118140960795 + 1255346 * 2 ^ 59
def prefixEnd_1255346 : Nat := 4983230072969 + 3 ^ 40 * 1255346 * 2
def baseEnd_1255346 : Nat := 143243530155366819267061

theorem tailTrace_1255346 : CollatzResearch.WordTrace tailWord_1255346 prefixEnd_1255346 143243530155366819267061 := by
  unfold tailWord_1255346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11446557527525828218242473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30524153406735541915313261 11446557527525828218242473)
  ·
    refine ⟨8584918145644371163681855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11446557527525828218242473 8584918145644371163681855)
    ·
      refine ⟨12877377218466556745522783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8584918145644371163681855 12877377218466556745522783)
      ·
        refine ⟨19316065827699835118284175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12877377218466556745522783 19316065827699835118284175)
        ·
          refine ⟨28974098741549752677426263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19316065827699835118284175 28974098741549752677426263)
          ·
            refine ⟨43461148112324629016139395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28974098741549752677426263 43461148112324629016139395)
            ·
              refine ⟨65191722168486943524209093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43461148112324629016139395 65191722168486943524209093)
              ·
                refine ⟨12223447906591301910789205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65191722168486943524209093 12223447906591301910789205)
                ·
                  refine ⟨143243530155366819267061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12223447906591301910789205 143243530155366819267061)
                  ·
                    rfl

theorem cell22_1255346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1255346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255346 prefixEnd_1255346 := by exact prefixLift 1255346
  have htrace : WordTrace (prefixWord ++ tailWord_1255346) baseStart_1255346 baseEnd_1255346 := by
    simpa [prefixWord, tailWord_1255346, baseEnd_1255346] using wordTrace_append hprefix tailTrace_1255346
  have hstable : (prefixWord ++ tailWord_1255346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255346).length < 2 ^ (prefixWord ++ tailWord_1255346).sum := by decide
  have hdescent : baseEnd_1255346 < baseStart_1255346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255356 : List Nat := [2, 2, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_1255356 : Nat := 118140960795 + 1255356 * 2 ^ 59
def prefixEnd_1255356 : Nat := 4983230072969 + 3 ^ 40 * 1255356 * 2
def baseEnd_1255356 : Nat := 429734013670463765051153

theorem tailTrace_1255356 : CollatzResearch.WordTrace tailWord_1255356 prefixEnd_1255356 429734013670463765051153 := by
  unfold tailWord_1255356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893297420033542290416961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30524396560044723053889281 22893297420033542290416961)
  ·
    refine ⟨17169973065025156717812721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22893297420033542290416961 17169973065025156717812721)
    ·
      refine ⟨12877479798768867538359541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17169973065025156717812721 12877479798768867538359541)
      ·
        refine ⟨1207263731134581331721207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12877479798768867538359541 1207263731134581331721207)
        ·
          refine ⟨1810895596701871997581811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207263731134581331721207 1810895596701871997581811)
          ·
            refine ⟨2716343395052807996372717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810895596701871997581811 2716343395052807996372717)
            ·
              refine ⟨1018628773144802998639769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2716343395052807996372717 1018628773144802998639769)
              ·
                refine ⟨763971579858602248979827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018628773144802998639769 763971579858602248979827)
                ·
                  refine ⟨1145957369787903373469741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763971579858602248979827 1145957369787903373469741)
                  ·
                    refine ⟨429734013670463765051153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145957369787903373469741 429734013670463765051153)
                    ·
                      rfl

theorem cell22_1255356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_1255356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255356 prefixEnd_1255356 := by exact prefixLift 1255356
  have htrace : WordTrace (prefixWord ++ tailWord_1255356) baseStart_1255356 baseEnd_1255356 := by
    simpa [prefixWord, tailWord_1255356, baseEnd_1255356] using wordTrace_append hprefix tailTrace_1255356
  have hstable : (prefixWord ++ tailWord_1255356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255356).length < 2 ^ (prefixWord ++ tailWord_1255356).sum := by decide
  have hdescent : baseEnd_1255356 < baseStart_1255356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255376 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_1255376 : Nat := 118140960795 + 1255376 * 2 ^ 59
def prefixEnd_1255376 : Nat := 4983230072969 + 3 ^ 40 * 1255376 * 2
def baseEnd_1255376 : Nat := 429740860079190379551091

theorem tailTrace_1255376 : CollatzResearch.WordTrace tailWord_1255376 prefixEnd_1255376 429740860079190379551091 := by
  unfold tailWord_1255376
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893662149997313998280991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30524882866663085331041321 22893662149997313998280991)
  ·
    refine ⟨34340493224995970997421487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22893662149997313998280991 34340493224995970997421487)
    ·
      refine ⟨51510739837493956496132231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34340493224995970997421487 51510739837493956496132231)
      ·
        refine ⟨77266109756240934744198347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51510739837493956496132231 77266109756240934744198347)
        ·
          refine ⟨115899164634361402116297521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77266109756240934744198347 115899164634361402116297521)
          ·
            refine ⟨86924373475771051587223141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115899164634361402116297521 86924373475771051587223141)
            ·
              refine ⟨16298320026707072172604339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86924373475771051587223141 16298320026707072172604339)
              ·
                refine ⟨24447480040060608258906509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16298320026707072172604339 24447480040060608258906509)
                ·
                  refine ⟨9167805015022728097089941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24447480040060608258906509 9167805015022728097089941)
                  ·
                    refine ⟨429740860079190379551091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9167805015022728097089941 429740860079190379551091)
                    ·
                      rfl

theorem cell22_1255376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_1255376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255376 prefixEnd_1255376 := by exact prefixLift 1255376
  have htrace : WordTrace (prefixWord ++ tailWord_1255376) baseStart_1255376 baseEnd_1255376 := by
    simpa [prefixWord, tailWord_1255376, baseEnd_1255376] using wordTrace_append hprefix tailTrace_1255376
  have hstable : (prefixWord ++ tailWord_1255376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255376).length < 2 ^ (prefixWord ++ tailWord_1255376).sum := by decide
  have hdescent : baseEnd_1255376 < baseStart_1255376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255382 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1255382 : Nat := 118140960795 + 1255382 * 2 ^ 59
def prefixEnd_1255382 : Nat := 4983230072969 + 3 ^ 40 * 1255382 * 2
def baseEnd_1255382 : Nat := 429742914001808363901073

theorem tailTrace_1255382 : CollatzResearch.WordTrace tailWord_1255382 prefixEnd_1255382 429742914001808363901073 := by
  unfold tailWord_1255382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861721446123305688830025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30525028758648594014186933 2861721446123305688830025)
  ·
    refine ⟨2146291084592479266622519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2861721446123305688830025 2146291084592479266622519)
    ·
      refine ⟨3219436626888718899933779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146291084592479266622519 3219436626888718899933779)
      ·
        refine ⟨4829154940333078349900669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219436626888718899933779 4829154940333078349900669)
        ·
          refine ⟨1810933102624904381212751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4829154940333078349900669 1810933102624904381212751)
          ·
            refine ⟨2716399653937356571819127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810933102624904381212751 2716399653937356571819127)
            ·
              refine ⟨4074599480906034857728691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716399653937356571819127 4074599480906034857728691)
              ·
                refine ⟨6111899221359052286593037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074599480906034857728691 6111899221359052286593037)
                ·
                  refine ⟨2291962208009644607472389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6111899221359052286593037 2291962208009644607472389)
                  ·
                    refine ⟨429742914001808363901073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291962208009644607472389 429742914001808363901073)
                    ·
                      rfl

theorem cell22_1255382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1255382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255382 prefixEnd_1255382 := by exact prefixLift 1255382
  have htrace : WordTrace (prefixWord ++ tailWord_1255382) baseStart_1255382 baseEnd_1255382 := by
    simpa [prefixWord, tailWord_1255382, baseEnd_1255382] using wordTrace_append hprefix tailTrace_1255382
  have hstable : (prefixWord ++ tailWord_1255382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255382).length < 2 ^ (prefixWord ++ tailWord_1255382).sum := by decide
  have hdescent : baseEnd_1255382 < baseStart_1255382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255393 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1255393 : Nat := 118140960795 + 1255393 * 2 ^ 59
def prefixEnd_1255393 : Nat := 4983230072969 + 3 ^ 40 * 1255393 * 2
def baseEnd_1255393 : Nat := 429746679526608001876039

theorem tailTrace_1255393 : CollatzResearch.WordTrace tailWord_1255393 prefixEnd_1255393 429746679526608001876039 := by
  unfold tailWord_1255393
  simp only [CollatzResearch.WordTrace]
  refine ⟨45787944340933039899930833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30525296227288693266620555 45787944340933039899930833)
  ·
    refine ⟨34340958255699779924948125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45787944340933039899930833 34340958255699779924948125)
    ·
      refine ⟨12877859345887417471855547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34340958255699779924948125 12877859345887417471855547)
      ·
        refine ⟨19316789018831126207783321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12877859345887417471855547 19316789018831126207783321)
        ·
          refine ⟨14487591764123344655837491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19316789018831126207783321 14487591764123344655837491)
          ·
            refine ⟨21731387646185016983756237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14487591764123344655837491 21731387646185016983756237)
            ·
              refine ⟨8149270367319381368908589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21731387646185016983756237 8149270367319381368908589)
              ·
                refine ⟨3055976387744768013340721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8149270367319381368908589 3055976387744768013340721)
                ·
                  refine ⟨2291982290808576010005541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055976387744768013340721 2291982290808576010005541)
                  ·
                    refine ⟨429746679526608001876039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291982290808576010005541 429746679526608001876039)
                    ·
                      rfl

theorem cell22_1255393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1255393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255393 prefixEnd_1255393 := by exact prefixLift 1255393
  have htrace : WordTrace (prefixWord ++ tailWord_1255393) baseStart_1255393 baseEnd_1255393 := by
    simpa [prefixWord, tailWord_1255393, baseEnd_1255393] using wordTrace_append hprefix tailTrace_1255393
  have hstable : (prefixWord ++ tailWord_1255393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255393).length < 2 ^ (prefixWord ++ tailWord_1255393).sum := by decide
  have hdescent : baseEnd_1255393 < baseStart_1255393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255423 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 7, 3]
def baseStart_1255423 : Nat := 118140960795 + 1255423 * 2 ^ 59
def prefixEnd_1255423 : Nat := 4983230072969 + 3 ^ 40 * 1255423 * 2
def baseEnd_1255423 : Nat := 429756949139697923625947

theorem tailTrace_1255423 : CollatzResearch.WordTrace tailWord_1255423 prefixEnd_1255423 429756949139697923625947 := by
  unfold tailWord_1255423
  simp only [CollatzResearch.WordTrace]
  refine ⟨45789038530824355023522923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30526025687216236682348615 45789038530824355023522923)
  ·
    refine ⟨68683557796236532535284385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45789038530824355023522923 68683557796236532535284385)
    ·
      refine ⟨51512668347177399401463289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68683557796236532535284385 51512668347177399401463289)
      ·
        refine ⟨38634501260383049551097467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51512668347177399401463289 38634501260383049551097467)
        ·
          refine ⟨57951751890574574326646201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38634501260383049551097467 57951751890574574326646201)
          ·
            refine ⟨43463813917930930744984651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57951751890574574326646201 43463813917930930744984651)
            ·
              refine ⟨65195720876896396117476977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43463813917930930744984651 65195720876896396117476977)
              ·
                refine ⟨48896790657672297088107733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65195720876896396117476977 48896790657672297088107733)
                ·
                  refine ⟨1146018531039194463002525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48896790657672297088107733 1146018531039194463002525)
                  ·
                    refine ⟨429756949139697923625947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1146018531039194463002525 429756949139697923625947)
                    ·
                      rfl

theorem cell22_1255423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_1255423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255423 prefixEnd_1255423 := by exact prefixLift 1255423
  have htrace : WordTrace (prefixWord ++ tailWord_1255423) baseStart_1255423 baseEnd_1255423 := by
    simpa [prefixWord, tailWord_1255423, baseEnd_1255423] using wordTrace_append hprefix tailTrace_1255423
  have hstable : (prefixWord ++ tailWord_1255423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255423).length < 2 ^ (prefixWord ++ tailWord_1255423).sum := by decide
  have hdescent : baseEnd_1255423 < baseStart_1255423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255438 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1255438 : Nat := 118140960795 + 1255438 * 2 ^ 59
def prefixEnd_1255438 : Nat := 4983230072969 + 3 ^ 40 * 1255438 * 2
def baseEnd_1255438 : Nat := 429762083946242884500901

theorem tailTrace_1255438 : CollatzResearch.WordTrace tailWord_1255438 prefixEnd_1255438 429762083946242884500901 := by
  unfold tailWord_1255438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723698203221251573164871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30526390417180008390212645 5723698203221251573164871)
  ·
    refine ⟨8585547304831877359747307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5723698203221251573164871 8585547304831877359747307)
    ·
      refine ⟨12878320957247816039620961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8585547304831877359747307 12878320957247816039620961)
      ·
        refine ⟨9658740717935862029715721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12878320957247816039620961 9658740717935862029715721)
        ·
          refine ⟨7244055538451896522286791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9658740717935862029715721 7244055538451896522286791)
          ·
            refine ⟨10866083307677844783430187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244055538451896522286791 10866083307677844783430187)
            ·
              refine ⟨16299124961516767175145281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10866083307677844783430187 16299124961516767175145281)
              ·
                refine ⟨12224343721137575381358961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16299124961516767175145281 12224343721137575381358961)
                ·
                  refine ⟨9168257790853181536019221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12224343721137575381358961 9168257790853181536019221)
                  ·
                    refine ⟨429762083946242884500901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9168257790853181536019221 429762083946242884500901)
                    ·
                      rfl

theorem cell22_1255438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1255438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255438 prefixEnd_1255438 := by exact prefixLift 1255438
  have htrace : WordTrace (prefixWord ++ tailWord_1255438) baseStart_1255438 baseEnd_1255438 := by
    simpa [prefixWord, tailWord_1255438, baseEnd_1255438] using wordTrace_append hprefix tailTrace_1255438
  have hstable : (prefixWord ++ tailWord_1255438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255438).length < 2 ^ (prefixWord ++ tailWord_1255438).sum := by decide
  have hdescent : baseEnd_1255438 < baseStart_1255438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255470 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_1255470 : Nat := 118140960795 + 1255470 * 2 ^ 59
def prefixEnd_1255470 : Nat := 4983230072969 + 3 ^ 40 * 1255470 * 2
def baseEnd_1255470 : Nat := 143257679400068489233601

theorem tailTrace_1255470 : CollatzResearch.WordTrace tailWord_1255470 prefixEnd_1255470 143257679400068489233601 := by
  unfold tailWord_1255470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723844095206760256310483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30527168507769388033655909 5723844095206760256310483)
  ·
    refine ⟨8585766142810140384465725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5723844095206760256310483 8585766142810140384465725)
    ·
      refine ⟨3219662303553802644174647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8585766142810140384465725 3219662303553802644174647)
      ·
        refine ⟨4829493455330703966261971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219662303553802644174647 4829493455330703966261971)
        ·
          refine ⟨7244240182996055949392957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829493455330703966261971 7244240182996055949392957)
          ·
            refine ⟨2716590068623520981022359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7244240182996055949392957 2716590068623520981022359)
            ·
              refine ⟨4074885102935281471533539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716590068623520981022359 4074885102935281471533539)
              ·
                refine ⟨6112327654402922207300309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074885102935281471533539 6112327654402922207300309)
                ·
                  refine ⟨143257679400068489233601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6112327654402922207300309 143257679400068489233601)
                  ·
                    rfl

theorem cell22_1255470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_1255470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255470 prefixEnd_1255470 := by exact prefixLift 1255470
  have htrace : WordTrace (prefixWord ++ tailWord_1255470) baseStart_1255470 baseEnd_1255470 := by
    simpa [prefixWord, tailWord_1255470, baseEnd_1255470] using wordTrace_append hprefix tailTrace_1255470
  have hstable : (prefixWord ++ tailWord_1255470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255470).length < 2 ^ (prefixWord ++ tailWord_1255470).sum := by decide
  have hdescent : baseEnd_1255470 < baseStart_1255470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255500 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_1255500 : Nat := 118140960795 + 1255500 * 2 ^ 59
def prefixEnd_1255500 : Nat := 4983230072969 + 3 ^ 40 * 1255500 * 2
def baseEnd_1255500 : Nat := 429783307813295389450711

theorem tailTrace_1255500 : CollatzResearch.WordTrace tailWord_1255500 prefixEnd_1255500 429783307813295389450711 := by
  unfold tailWord_1255500
  simp only [CollatzResearch.WordTrace]
  refine ⟨22895923475772698587037977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30527897967696931449383969 22895923475772698587037977)
  ·
    refine ⟨17171942606829523940278483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22895923475772698587037977 17171942606829523940278483)
    ·
      refine ⟨25757913910244285910417725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17171942606829523940278483 25757913910244285910417725)
      ·
        refine ⟨9659217716341607216406647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25757913910244285910417725 9659217716341607216406647)
        ·
          refine ⟨14488826574512410824609971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9659217716341607216406647 14488826574512410824609971)
          ·
            refine ⟨21733239861768616236914957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14488826574512410824609971 21733239861768616236914957)
            ·
              refine ⟨8149964948163231088843109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21733239861768616236914957 8149964948163231088843109)
              ·
                refine ⟨1528118427780605829158083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8149964948163231088843109 1528118427780605829158083)
                ·
                  refine ⟨2292177641670908743737125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528118427780605829158083 2292177641670908743737125)
                  ·
                    refine ⟨429783307813295389450711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292177641670908743737125 429783307813295389450711)
                    ·
                      rfl

theorem cell22_1255500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_1255500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255500 prefixEnd_1255500 := by exact prefixLift 1255500
  have htrace : WordTrace (prefixWord ++ tailWord_1255500) baseStart_1255500 baseEnd_1255500 := by
    simpa [prefixWord, tailWord_1255500, baseEnd_1255500] using wordTrace_append hprefix tailTrace_1255500
  have hstable : (prefixWord ++ tailWord_1255500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255500).length < 2 ^ (prefixWord ++ tailWord_1255500).sum := by decide
  have hdescent : baseEnd_1255500 < baseStart_1255500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255513 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_1255513 : Nat := 118140960795 + 1255513 * 2 ^ 59
def prefixEnd_1255513 : Nat := 4983230072969 + 3 ^ 40 * 1255513 * 2
def baseEnd_1255513 : Nat := 429787757978967688875671

theorem tailTrace_1255513 : CollatzResearch.WordTrace tailWord_1255513 prefixEnd_1255513 429787757978967688875671 := by
  unfold tailWord_1255513
  simp only [CollatzResearch.WordTrace]
  refine ⟨45792321100498300394299193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30528214066998866929532795 45792321100498300394299193)
  ·
    refine ⟨34344240825373725295724395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45792321100498300394299193 34344240825373725295724395)
    ·
      refine ⟨51516361238060587943586593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34344240825373725295724395 51516361238060587943586593)
      ·
        refine ⟨38637270928545440957689945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51516361238060587943586593 38637270928545440957689945)
        ·
          refine ⟨28977953196409080718267459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38637270928545440957689945 28977953196409080718267459)
          ·
            refine ⟨43466929794613621077401189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28977953196409080718267459 43466929794613621077401189)
            ·
              refine ⟨8150049336490053952012723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43466929794613621077401189 8150049336490053952012723)
              ·
                refine ⟨12225074004735080928019085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8150049336490053952012723 12225074004735080928019085)
                ·
                  refine ⟨4584402751775655348007157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12225074004735080928019085 4584402751775655348007157)
                  ·
                    refine ⟨429787757978967688875671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4584402751775655348007157 429787757978967688875671)
                    ·
                      rfl

theorem cell22_1255513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_1255513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255513 prefixEnd_1255513 := by exact prefixLift 1255513
  have htrace : WordTrace (prefixWord ++ tailWord_1255513) baseStart_1255513 baseEnd_1255513 := by
    simpa [prefixWord, tailWord_1255513, baseEnd_1255513] using wordTrace_append hprefix tailTrace_1255513
  have hstable : (prefixWord ++ tailWord_1255513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255513).length < 2 ^ (prefixWord ++ tailWord_1255513).sum := by decide
  have hdescent : baseEnd_1255513 < baseStart_1255513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255543 : List Nat := [1, 1, 3, 1, 1, 5, 1, 9]
def baseStart_1255543 : Nat := 118140960795 + 1255543 * 2 ^ 59
def prefixEnd_1255543 : Nat := 4983230072969 + 3 ^ 40 * 1255543 * 2
def baseEnd_1255543 : Nat := 47755336399117512291731

theorem tailTrace_1255543 : CollatzResearch.WordTrace tailWord_1255543 prefixEnd_1255543 47755336399117512291731 := by
  unfold tailWord_1255543
  simp only [CollatzResearch.WordTrace]
  refine ⟨45793415290389615517891283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30528943526926410345260855 45793415290389615517891283)
  ·
    refine ⟨68690122935584423276836925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45793415290389615517891283 68690122935584423276836925)
    ·
      refine ⟨25758796100844158728813847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68690122935584423276836925 25758796100844158728813847)
      ·
        refine ⟨38638194151266238093220771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25758796100844158728813847 38638194151266238093220771)
        ·
          refine ⟨57957291226899357139831157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38638194151266238093220771 57957291226899357139831157)
          ·
            refine ⟨5433496052521814731859171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57957291226899357139831157 5433496052521814731859171)
            ·
              refine ⟨8150244078782722097788757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433496052521814731859171 8150244078782722097788757)
              ·
                refine ⟨47755336399117512291731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8150244078782722097788757 47755336399117512291731)
                ·
                  rfl

theorem cell22_1255543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 9].length) (baseStart_1255543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255543 prefixEnd_1255543 := by exact prefixLift 1255543
  have htrace : WordTrace (prefixWord ++ tailWord_1255543) baseStart_1255543 baseEnd_1255543 := by
    simpa [prefixWord, tailWord_1255543, baseEnd_1255543] using wordTrace_append hprefix tailTrace_1255543
  have hstable : (prefixWord ++ tailWord_1255543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255543).length < 2 ^ (prefixWord ++ tailWord_1255543).sum := by decide
  have hdescent : baseEnd_1255543 < baseStart_1255543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255560 : List Nat := [2, 1, 3, 4, 1, 1, 2, 8]
def baseStart_1255560 : Nat := 118140960795 + 1255560 * 2 ^ 59
def prefixEnd_1255560 : Nat := 4983230072969 + 3 ^ 40 * 1255560 * 2
def baseEnd_1255560 : Nat := 47755983004386136994503

theorem tailTrace_1255560 : CollatzResearch.WordTrace tailWord_1255560 prefixEnd_1255560 47755983004386136994503 := by
  unfold tailWord_1255560
  simp only [CollatzResearch.WordTrace]
  refine ⟨22897017665664013710630067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30529356887552018280840089 22897017665664013710630067)
  ·
    refine ⟨34345526498496020565945101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22897017665664013710630067 34345526498496020565945101)
    ·
      refine ⟨12879572436936007712229413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34345526498496020565945101 12879572436936007712229413)
      ·
        refine ⟨2414919831925501446043015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12879572436936007712229413 2414919831925501446043015)
        ·
          refine ⟨3622379747888252169064523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414919831925501446043015 3622379747888252169064523)
          ·
            refine ⟨5433569621832378253596785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622379747888252169064523 5433569621832378253596785)
            ·
              refine ⟨4075177216374283690197589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5433569621832378253596785 4075177216374283690197589)
              ·
                refine ⟨47755983004386136994503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4075177216374283690197589 47755983004386136994503)
                ·
                  rfl

theorem cell22_1255560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_1255560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255560 prefixEnd_1255560 := by exact prefixLift 1255560
  have htrace : WordTrace (prefixWord ++ tailWord_1255560) baseStart_1255560 baseEnd_1255560 := by
    simpa [prefixWord, tailWord_1255560, baseEnd_1255560] using wordTrace_append hprefix tailTrace_1255560
  have hstable : (prefixWord ++ tailWord_1255560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255560).length < 2 ^ (prefixWord ++ tailWord_1255560).sum := by decide
  have hdescent : baseEnd_1255560 < baseStart_1255560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255562 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_1255562 : Nat := 118140960795 + 1255562 * 2 ^ 59
def prefixEnd_1255562 : Nat := 4983230072969 + 3 ^ 40 * 1255562 * 2
def baseEnd_1255562 : Nat := 429804531680347894400521

theorem tailTrace_1255562 : CollatzResearch.WordTrace tailWord_1255562 prefixEnd_1255562 429804531680347894400521 := by
  unfold tailWord_1255562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448527069330195440708235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30529405518213854508555293 11448527069330195440708235)
  ·
    refine ⟨17172790603995293161062353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11448527069330195440708235 17172790603995293161062353)
    ·
      refine ⟨12879592952996469870796765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17172790603995293161062353 12879592952996469870796765)
      ·
        refine ⟨4829847357373676201548787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12879592952996469870796765 4829847357373676201548787)
        ·
          refine ⟨7244771036060514302323181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829847357373676201548787 7244771036060514302323181)
          ·
            refine ⟨2716789138522692863371193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7244771036060514302323181 2716789138522692863371193)
            ·
              refine ⟨2037591853892019647528395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2716789138522692863371193 2037591853892019647528395)
              ·
                refine ⟨3056387780838029471292593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037591853892019647528395 3056387780838029471292593)
                ·
                  refine ⟨2292290835628522103469445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3056387780838029471292593 2292290835628522103469445)
                  ·
                    refine ⟨429804531680347894400521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292290835628522103469445 429804531680347894400521)
                    ·
                      rfl

theorem cell22_1255562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_1255562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255562 prefixEnd_1255562 := by exact prefixLift 1255562
  have htrace : WordTrace (prefixWord ++ tailWord_1255562) baseStart_1255562 baseEnd_1255562 := by
    simpa [prefixWord, tailWord_1255562, baseEnd_1255562] using wordTrace_append hprefix tailTrace_1255562
  have hstable : (prefixWord ++ tailWord_1255562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255562).length < 2 ^ (prefixWord ++ tailWord_1255562).sum := by decide
  have hdescent : baseEnd_1255562 < baseStart_1255562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255594 : List Nat := [3, 1, 5, 1, 2, 2, 1, 7]
def baseStart_1255594 : Nat := 118140960795 + 1255594 * 2 ^ 59
def prefixEnd_1255594 : Nat := 4983230072969 + 3 ^ 40 * 1255594 * 2
def baseEnd_1255594 : Nat := 47757276214923386400047

theorem tailTrace_1255594 : CollatzResearch.WordTrace tailWord_1255594 prefixEnd_1255594 47757276214923386400047 := by
  unfold tailWord_1255594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448818853301212806999459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30530183608803234151998557 11448818853301212806999459)
  ·
    refine ⟨17173228279951819210499189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11448818853301212806999459 17173228279951819210499189)
    ·
      refine ⟨1609990151245483050984299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17173228279951819210499189 1609990151245483050984299)
      ·
        refine ⟨2414985226868224576476449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609990151245483050984299 2414985226868224576476449)
        ·
          refine ⟨1811238920151168432357337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2414985226868224576476449 1811238920151168432357337)
          ·
            refine ⟨1358429190113376324268003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1811238920151168432357337 1358429190113376324268003)
            ·
              refine ⟨2037643785170064486402005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358429190113376324268003 2037643785170064486402005)
              ·
                refine ⟨47757276214923386400047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2037643785170064486402005 47757276214923386400047)
                ·
                  rfl

theorem cell22_1255594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_1255594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255594 prefixEnd_1255594 := by exact prefixLift 1255594
  have htrace : WordTrace (prefixWord ++ tailWord_1255594) baseStart_1255594 baseEnd_1255594 := by
    simpa [prefixWord, tailWord_1255594, baseEnd_1255594] using wordTrace_append hprefix tailTrace_1255594
  have hstable : (prefixWord ++ tailWord_1255594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255594).length < 2 ^ (prefixWord ++ tailWord_1255594).sum := by decide
  have hdescent : baseEnd_1255594 < baseStart_1255594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255680 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_1255680 : Nat := 118140960795 + 1255680 * 2 ^ 59
def prefixEnd_1255680 : Nat := 4983230072969 + 3 ^ 40 * 1255680 * 2
def baseEnd_1255680 : Nat := 429844925491834919950159

theorem tailTrace_1255680 : CollatzResearch.WordTrace tailWord_1255680 prefixEnd_1255680 429844925491834919950159 := by
  unfold tailWord_1255680
  simp only [CollatzResearch.WordTrace]
  refine ⟨22899206045446643957814247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30532274727262191943752329 22899206045446643957814247)
  ·
    refine ⟨34348809068169965936721371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22899206045446643957814247 34348809068169965936721371)
    ·
      refine ⟨51523213602254948905082057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34348809068169965936721371 51523213602254948905082057)
      ·
        refine ⟨38642410201691211678811543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51523213602254948905082057 38642410201691211678811543)
        ·
          refine ⟨57963615302536817518217315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38642410201691211678811543 57963615302536817518217315)
          ·
            refine ⟨86945422953805226277325973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57963615302536817518217315 86945422953805226277325973)
            ·
              refine ⟨4075566700959619981749655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86945422953805226277325973 4075566700959619981749655)
              ·
                refine ⟨6113350051439429972624483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4075566700959619981749655 6113350051439429972624483)
                ·
                  refine ⟨9170025077159144958936725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6113350051439429972624483 9170025077159144958936725)
                  ·
                    refine ⟨429844925491834919950159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9170025077159144958936725 429844925491834919950159)
                    ·
                      rfl

theorem cell22_1255680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_1255680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255680 prefixEnd_1255680 := by exact prefixLift 1255680
  have htrace : WordTrace (prefixWord ++ tailWord_1255680) baseStart_1255680 baseEnd_1255680 := by
    simpa [prefixWord, tailWord_1255680, baseEnd_1255680] using wordTrace_append hprefix tailTrace_1255680
  have hstable : (prefixWord ++ tailWord_1255680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255680).length < 2 ^ (prefixWord ++ tailWord_1255680).sum := by decide
  have hdescent : baseEnd_1255680 < baseStart_1255680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255697 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_1255697 : Nat := 118140960795 + 1255697 * 2 ^ 59
def prefixEnd_1255697 : Nat := 4983230072969 + 3 ^ 40 * 1255697 * 2
def baseEnd_1255697 : Nat := 429850744939252542275107

theorem tailTrace_1255697 : CollatzResearch.WordTrace tailWord_1255697 prefixEnd_1255697 429850744939252542275107 := by
  unfold tailWord_1255697
  simp only [CollatzResearch.WordTrace]
  refine ⟨45799032131831699818997345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30532688087887799879331563 45799032131831699818997345)
  ·
    refine ⟨34349274098873774864248009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45799032131831699818997345 34349274098873774864248009)
    ·
      refine ⟨25761955574155331148186007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34349274098873774864248009 25761955574155331148186007)
      ·
        refine ⟨38642933361232996722279011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25761955574155331148186007 38642933361232996722279011)
        ·
          refine ⟨57964400041849495083418517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38642933361232996722279011 57964400041849495083418517)
          ·
            refine ⟨2717081251961695082035243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57964400041849495083418517 2717081251961695082035243)
            ·
              refine ⟨4075621877942542623052865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717081251961695082035243 4075621877942542623052865)
              ·
                refine ⟨3056716408456906967289649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4075621877942542623052865 3056716408456906967289649)
                ·
                  refine ⟨2292537306342680225467237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3056716408456906967289649 2292537306342680225467237)
                  ·
                    refine ⟨429850744939252542275107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292537306342680225467237 429850744939252542275107)
                    ·
                      rfl

theorem cell22_1255697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_1255697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255697 prefixEnd_1255697 := by exact prefixLift 1255697
  have htrace : WordTrace (prefixWord ++ tailWord_1255697) baseStart_1255697 baseEnd_1255697 := by
    simpa [prefixWord, tailWord_1255697, baseEnd_1255697] using wordTrace_append hprefix tailTrace_1255697
  have hstable : (prefixWord ++ tailWord_1255697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255697).length < 2 ^ (prefixWord ++ tailWord_1255697).sum := by decide
  have hdescent : baseEnd_1255697 < baseStart_1255697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255712 : List Nat := [2, 1, 1, 5, 2, 2, 2, 7]
def baseStart_1255712 : Nat := 118140960795 + 1255712 * 2 ^ 59
def prefixEnd_1255712 : Nat := 4983230072969 + 3 ^ 40 * 1255712 * 2
def baseEnd_1255712 : Nat := 47761764416199722572229

theorem tailTrace_1255712 : CollatzResearch.WordTrace tailWord_1255712 prefixEnd_1255712 47761764416199722572229 := by
  unfold tailWord_1255712
  simp only [CollatzResearch.WordTrace]
  refine ⟨22899789613388678690396695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30533052817851571587195593 22899789613388678690396695)
  ·
    refine ⟨34349684420083018035595043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22899789613388678690396695 34349684420083018035595043)
    ·
      refine ⟨51524526630124527053392565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34349684420083018035595043 51524526630124527053392565)
      ·
        refine ⟨4830424371574174411255553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51524526630124527053392565 4830424371574174411255553)
        ·
          refine ⟨3622818278680630808441665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4830424371574174411255553 3622818278680630808441665)
          ·
            refine ⟨2717113709010473106331249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3622818278680630808441665 2717113709010473106331249)
            ·
              refine ⟨2037835281757854829748437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717113709010473106331249 2037835281757854829748437)
              ·
                refine ⟨47761764416199722572229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2037835281757854829748437 47761764416199722572229)
                ·
                  rfl

theorem cell22_1255712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_1255712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255712 prefixEnd_1255712 := by exact prefixLift 1255712
  have htrace : WordTrace (prefixWord ++ tailWord_1255712) baseStart_1255712 baseEnd_1255712 := by
    simpa [prefixWord, tailWord_1255712, baseEnd_1255712] using wordTrace_append hprefix tailTrace_1255712
  have hstable : (prefixWord ++ tailWord_1255712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255712).length < 2 ^ (prefixWord ++ tailWord_1255712).sum := by decide
  have hdescent : baseEnd_1255712 < baseStart_1255712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255716 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_1255716 : Nat := 118140960795 + 1255716 * 2 ^ 59
def prefixEnd_1255716 : Nat := 4983230072969 + 3 ^ 40 * 1255716 * 2
def baseEnd_1255716 : Nat := 429857249027542826050049

theorem tailTrace_1255716 : CollatzResearch.WordTrace tailWord_1255716 prefixEnd_1255716 429857249027542826050049 := by
  unfold tailWord_1255716
  simp only [CollatzResearch.WordTrace]
  refine ⟨22899862559381433031969501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30533150079175244042626001 22899862559381433031969501)
  ·
    refine ⟨8587448459768037386988563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22899862559381433031969501 8587448459768037386988563)
    ·
      refine ⟨12881172689652056080482845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8587448459768037386988563 12881172689652056080482845)
      ·
        refine ⟨4830439758619521030181067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12881172689652056080482845 4830439758619521030181067)
        ·
          refine ⟨7245659637929281545271601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4830439758619521030181067 7245659637929281545271601)
          ·
            refine ⟨5434244728446961158953701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7245659637929281545271601 5434244728446961158953701)
            ·
              refine ⟨1018920886583805217303819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5434244728446961158953701 1018920886583805217303819)
              ·
                refine ⟨1528381329875707825955729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018920886583805217303819 1528381329875707825955729)
                ·
                  refine ⟨1146285997406780869466797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528381329875707825955729 1146285997406780869466797)
                  ·
                    refine ⟨429857249027542826050049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1146285997406780869466797 429857249027542826050049)
                    ·
                      rfl

theorem cell22_1255716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_1255716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255716 prefixEnd_1255716 := by exact prefixLift 1255716
  have htrace : WordTrace (prefixWord ++ tailWord_1255716) baseStart_1255716 baseEnd_1255716 := by
    simpa [prefixWord, tailWord_1255716, baseEnd_1255716] using wordTrace_append hprefix tailTrace_1255716
  have hstable : (prefixWord ++ tailWord_1255716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255716).length < 2 ^ (prefixWord ++ tailWord_1255716).sum := by decide
  have hdescent : baseEnd_1255716 < baseStart_1255716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255727 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 3, 3]
def baseStart_1255727 : Nat := 118140960795 + 1255727 * 2 ^ 59
def prefixEnd_1255727 : Nat := 4983230072969 + 3 ^ 40 * 1255727 * 2
def baseEnd_1255727 : Nat := 429861014552342464025015

theorem tailTrace_1255727 : CollatzResearch.WordTrace tailWord_1255727 prefixEnd_1255727 429861014552342464025015 := by
  unfold tailWord_1255727
  simp only [CollatzResearch.WordTrace]
  refine ⟨45800126321723014942589435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30533417547815343295059623 45800126321723014942589435)
  ·
    refine ⟨68700189482584522413884153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45800126321723014942589435 68700189482584522413884153)
    ·
      refine ⟨51525142111938391810413115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68700189482584522413884153 51525142111938391810413115)
      ·
        refine ⟨77287713167907587715619673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51525142111938391810413115 77287713167907587715619673)
        ·
          refine ⟨57965784875930690786714755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77287713167907587715619673 57965784875930690786714755)
          ·
            refine ⟨86948677313896036180072133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57965784875930690786714755 86948677313896036180072133)
            ·
              refine ⟨16302876996355506783763525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86948677313896036180072133 16302876996355506783763525)
              ·
                refine ⟨3056789436816657521955661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16302876996355506783763525 3056789436816657521955661)
                ·
                  refine ⟨1146296038806246570733373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3056789436816657521955661 1146296038806246570733373)
                  ·
                    refine ⟨429861014552342464025015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1146296038806246570733373 429861014552342464025015)
                    ·
                      rfl

theorem cell22_1255727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_1255727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255727 prefixEnd_1255727 := by exact prefixLift 1255727
  have htrace : WordTrace (prefixWord ++ tailWord_1255727) baseStart_1255727 baseEnd_1255727 := by
    simpa [prefixWord, tailWord_1255727, baseEnd_1255727] using wordTrace_append hprefix tailTrace_1255727
  have hstable : (prefixWord ++ tailWord_1255727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255727).length < 2 ^ (prefixWord ++ tailWord_1255727).sum := by decide
  have hdescent : baseEnd_1255727 < baseStart_1255727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255761 : List Nat := [1, 2, 2, 1, 4, 3, 1, 4, 1, 3]
def baseStart_1255761 : Nat := 118140960795 + 1255761 * 2 ^ 59
def prefixEnd_1255761 : Nat := 4983230072969 + 3 ^ 40 * 1255761 * 2
def baseEnd_1255761 : Nat := 429872653447177708674911

theorem tailTrace_1255761 : CollatzResearch.WordTrace tailWord_1255761 prefixEnd_1255761 429872653447177708674911 := by
  unfold tailWord_1255761
  simp only [CollatzResearch.WordTrace]
  refine ⟨45801366403599838749327137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30534244269066559166218091 45801366403599838749327137)
  ·
    refine ⟨34351024802699879061995353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45801366403599838749327137 34351024802699879061995353)
    ·
      refine ⟨25763268602024909296496515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34351024802699879061995353 25763268602024909296496515)
      ·
        refine ⟨38644902903037363944744773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25763268602024909296496515 38644902903037363944744773)
        ·
          refine ⟨7245919294319505739639645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38644902903037363944744773 7245919294319505739639645)
          ·
            refine ⟨2717219735369814652364867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7245919294319505739639645 2717219735369814652364867)
            ·
              refine ⟨4075829603054721978547301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717219735369814652364867 4075829603054721978547301)
              ·
                refine ⟨764218050572760370977619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4075829603054721978547301 764218050572760370977619)
                ·
                  refine ⟨1146327075859140556466429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764218050572760370977619 1146327075859140556466429)
                  ·
                    refine ⟨429872653447177708674911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1146327075859140556466429 429872653447177708674911)
                    ·
                      rfl

theorem cell22_1255761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_1255761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255761 prefixEnd_1255761 := by exact prefixLift 1255761
  have htrace : WordTrace (prefixWord ++ tailWord_1255761) baseStart_1255761 baseEnd_1255761 := by
    simpa [prefixWord, tailWord_1255761, baseEnd_1255761] using wordTrace_append hprefix tailTrace_1255761
  have hstable : (prefixWord ++ tailWord_1255761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255761).length < 2 ^ (prefixWord ++ tailWord_1255761).sum := by decide
  have hdescent : baseEnd_1255761 < baseStart_1255761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255819 : List Nat := [1, 1, 1, 1, 4, 4, 2, 4, 4]
def baseStart_1255819 : Nat := 118140960795 + 1255819 * 2 ^ 59
def prefixEnd_1255819 : Nat := 4983230072969 + 3 ^ 40 * 1255819 * 2
def baseEnd_1255819 : Nat := 143297502677494963574911

theorem tailTrace_1255819 : CollatzResearch.WordTrace tailWord_1255819 prefixEnd_1255819 143297502677494963574911 := by
  unfold tailWord_1255819
  simp only [CollatzResearch.WordTrace]
  refine ⟨45803481837389714654938511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30535654558259809769959007 45803481837389714654938511)
  ·
    refine ⟨68705222756084571982407767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45803481837389714654938511 68705222756084571982407767)
    ·
      refine ⟨103057834134126857973611651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68705222756084571982407767 103057834134126857973611651)
      ·
        refine ⟨154586751201190286960417477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103057834134126857973611651 154586751201190286960417477)
        ·
          refine ⟨28985015850223178805078277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154586751201190286960417477 28985015850223178805078277)
          ·
            refine ⟨5434690471916846025952177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28985015850223178805078277 5434690471916846025952177)
            ·
              refine ⟨4076017853937634519464133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5434690471916846025952177 4076017853937634519464133)
              ·
                refine ⟨764253347613306472399525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4076017853937634519464133 764253347613306472399525)
                ·
                  refine ⟨143297502677494963574911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 764253347613306472399525 143297502677494963574911)
                  ·
                    rfl

theorem cell22_1255819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 4].length) (baseStart_1255819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255819 prefixEnd_1255819 := by exact prefixLift 1255819
  have htrace : WordTrace (prefixWord ++ tailWord_1255819) baseStart_1255819 baseEnd_1255819 := by
    simpa [prefixWord, tailWord_1255819, baseEnd_1255819] using wordTrace_append hprefix tailTrace_1255819
  have hstable : (prefixWord ++ tailWord_1255819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255819).length < 2 ^ (prefixWord ++ tailWord_1255819).sum := by decide
  have hdescent : baseEnd_1255819 < baseStart_1255819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255834 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_1255834 : Nat := 118140960795 + 1255834 * 2 ^ 59
def prefixEnd_1255834 : Nat := 4983230072969 + 3 ^ 40 * 1255834 * 2
def baseEnd_1255834 : Nat := 429897642839029851599687

theorem tailTrace_1255834 : CollatzResearch.WordTrace tailWord_1255834 prefixEnd_1255834 429897642839029851599687 := by
  unfold tailWord_1255834
  simp only [CollatzResearch.WordTrace]
  refine ⟨11451007233083843054183639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30536019288223581477823037 11451007233083843054183639)
  ·
    refine ⟨17176510849625764581275459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11451007233083843054183639 17176510849625764581275459)
    ·
      refine ⟨25764766274438646871913189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17176510849625764581275459 25764766274438646871913189)
      ·
        refine ⟨4830893676457246288483723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25764766274438646871913189 4830893676457246288483723)
        ·
          refine ⟨7246340514685869432725585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4830893676457246288483723 7246340514685869432725585)
          ·
            refine ⟨5434755386014402074544189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7246340514685869432725585 5434755386014402074544189)
            ·
              refine ⟨2038033269755400777954071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5434755386014402074544189 2038033269755400777954071)
              ·
                refine ⟨3057049904633101166931107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038033269755400777954071 3057049904633101166931107)
                ·
                  refine ⟨4585574856949651750396661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057049904633101166931107 4585574856949651750396661)
                  ·
                    refine ⟨429897642839029851599687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4585574856949651750396661 429897642839029851599687)
                    ·
                      rfl

theorem cell22_1255834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_1255834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255834 prefixEnd_1255834 := by exact prefixLift 1255834
  have htrace : WordTrace (prefixWord ++ tailWord_1255834) baseStart_1255834 baseEnd_1255834 := by
    simpa [prefixWord, tailWord_1255834, baseEnd_1255834] using wordTrace_append hprefix tailTrace_1255834
  have hstable : (prefixWord ++ tailWord_1255834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255834).length < 2 ^ (prefixWord ++ tailWord_1255834).sum := by decide
  have hdescent : baseEnd_1255834 < baseStart_1255834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255838 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1255838 : Nat := 118140960795 + 1255838 * 2 ^ 59
def prefixEnd_1255838 : Nat := 4983230072969 + 3 ^ 40 * 1255838 * 2
def baseEnd_1255838 : Nat := 429899012120775174499675

theorem tailTrace_1255838 : CollatzResearch.WordTrace tailWord_1255838 prefixEnd_1255838 429899012120775174499675 := by
  unfold tailWord_1255838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725521853040110112485021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30536116549547253933253445 5725521853040110112485021)
  ·
    refine ⟨2147070694890041292181883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5725521853040110112485021 2147070694890041292181883)
    ·
      refine ⟨3220606042335061938272825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147070694890041292181883 3220606042335061938272825)
      ·
        refine ⟨2415454531751296453704619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3220606042335061938272825 2415454531751296453704619)
        ·
          refine ⟨3623181797626944680556929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415454531751296453704619 3623181797626944680556929)
          ·
            refine ⟨2717386348220208510417697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3623181797626944680556929 2717386348220208510417697)
            ·
              refine ⟨2038039761165156382813273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717386348220208510417697 2038039761165156382813273)
              ·
                refine ⟨1528529820873867287109955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038039761165156382813273 1528529820873867287109955)
                ·
                  refine ⟨2292794731310800930664933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528529820873867287109955 2292794731310800930664933)
                  ·
                    refine ⟨429899012120775174499675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292794731310800930664933 429899012120775174499675)
                    ·
                      rfl

theorem cell22_1255838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1255838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255838 prefixEnd_1255838 := by exact prefixLift 1255838
  have htrace : WordTrace (prefixWord ++ tailWord_1255838) baseStart_1255838 baseEnd_1255838 := by
    simpa [prefixWord, tailWord_1255838, baseEnd_1255838] using wordTrace_append hprefix tailTrace_1255838
  have hstable : (prefixWord ++ tailWord_1255838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255838).length < 2 ^ (prefixWord ++ tailWord_1255838).sum := by decide
  have hdescent : baseEnd_1255838 < baseStart_1255838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255926 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_1255926 : Nat := 118140960795 + 1255926 * 2 ^ 59
def prefixEnd_1255926 : Nat := 4983230072969 + 3 ^ 40 * 1255926 * 2
def baseEnd_1255926 : Nat := 143309712106390759433135

theorem tailTrace_1255926 : CollatzResearch.WordTrace tailWord_1255926 prefixEnd_1255926 143309712106390759433135 := by
  unfold tailWord_1255926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862961528000129495567727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30538256298668047952722421 2862961528000129495567727)
  ·
    refine ⟨4294442292000194243351591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2862961528000129495567727 4294442292000194243351591)
    ·
      refine ⟨6441663438000291365027387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4294442292000194243351591 6441663438000291365027387)
      ·
        refine ⟨9662495157000437047541081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6441663438000291365027387 9662495157000437047541081)
        ·
          refine ⟨7246871367750327785655811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9662495157000437047541081 7246871367750327785655811)
          ·
            refine ⟨10870307051625491678483717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7246871367750327785655811 10870307051625491678483717)
            ·
              refine ⟨2038182572179779689715697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10870307051625491678483717 2038182572179779689715697)
              ·
                refine ⟨1528636929134834767286773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038182572179779689715697 1528636929134834767286773)
                ·
                  refine ⟨143309712106390759433135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1528636929134834767286773 143309712106390759433135)
                  ·
                    rfl

theorem cell22_1255926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_1255926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255926 prefixEnd_1255926 := by exact prefixLift 1255926
  have htrace : WordTrace (prefixWord ++ tailWord_1255926) baseStart_1255926 baseEnd_1255926 := by
    simpa [prefixWord, tailWord_1255926, baseEnd_1255926] using wordTrace_append hprefix tailTrace_1255926
  have hstable : (prefixWord ++ tailWord_1255926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255926).length < 2 ^ (prefixWord ++ tailWord_1255926).sum := by decide
  have hdescent : baseEnd_1255926 < baseStart_1255926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255969 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1255969 : Nat := 118140960795 + 1255969 * 2 ^ 59
def prefixEnd_1255969 : Nat := 4983230072969 + 3 ^ 40 * 1255969 * 2
def baseEnd_1255969 : Nat := 429943856097934499474273

theorem tailTrace_1255969 : CollatzResearch.WordTrace tailWord_1255969 prefixEnd_1255969 429943856097934499474273 := by
  unfold tailWord_1255969
  simp only [CollatzResearch.WordTrace]
  refine ⟨45808952786846290272898961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30539301857897526848599307 45808952786846290272898961)
  ·
    refine ⟨34356714590134717704674221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45808952786846290272898961 34356714590134717704674221)
    ·
      refine ⟨12883767971300519139252833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34356714590134717704674221 12883767971300519139252833)
      ·
        refine ⟨9662825978475389354439625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12883767971300519139252833 9662825978475389354439625)
        ·
          refine ⟨7247119483856542015829719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9662825978475389354439625 7247119483856542015829719)
          ·
            refine ⟨10870679225784813023744579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7247119483856542015829719 10870679225784813023744579)
            ·
              refine ⟨16306018838677219535616869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10870679225784813023744579 16306018838677219535616869)
              ·
                refine ⟨3057378532251978662928163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16306018838677219535616869 3057378532251978662928163)
                ·
                  refine ⟨4586067798377967994392245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057378532251978662928163 4586067798377967994392245)
                  ·
                    refine ⟨429943856097934499474273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4586067798377967994392245 429943856097934499474273)
                    ·
                      rfl

theorem cell22_1255969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1255969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255969 prefixEnd_1255969 := by exact prefixLift 1255969
  have htrace : WordTrace (prefixWord ++ tailWord_1255969) baseStart_1255969 baseEnd_1255969 := by
    simpa [prefixWord, tailWord_1255969, baseEnd_1255969] using wordTrace_append hprefix tailTrace_1255969
  have hstable : (prefixWord ++ tailWord_1255969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255969).length < 2 ^ (prefixWord ++ tailWord_1255969).sum := by decide
  have hdescent : baseEnd_1255969 < baseStart_1255969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255971 : List Nat := [1, 1, 1, 4, 4, 1, 1, 5, 4]
def baseStart_1255971 : Nat := 118140960795 + 1255971 * 2 ^ 59
def prefixEnd_1255971 : Nat := 4983230072969 + 3 ^ 40 * 1255971 * 2
def baseEnd_1255971 : Nat := 143314846912935720308089

theorem tailTrace_1255971 : CollatzResearch.WordTrace tailWord_1255971 prefixEnd_1255971 143314846912935720308089 := by
  unfold tailWord_1255971
  simp only [CollatzResearch.WordTrace]
  refine ⟨45809025732839044614471767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30539350488559363076314511 45809025732839044614471767)
  ·
    refine ⟨68713538599258566921707651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45809025732839044614471767 68713538599258566921707651)
    ·
      refine ⟨103070307898887850382561477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68713538599258566921707651 103070307898887850382561477)
      ·
        refine ⟨19325682731041471946730277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103070307898887850382561477 19325682731041471946730277)
        ·
          refine ⟨3623565512070275990011927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19325682731041471946730277 3623565512070275990011927)
          ·
            refine ⟨5435348268105413985017891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623565512070275990011927 5435348268105413985017891)
            ·
              refine ⟨8153022402158120977526837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435348268105413985017891 8153022402158120977526837)
              ·
                refine ⟨764345850202323841643141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8153022402158120977526837 764345850202323841643141)
                ·
                  refine ⟨143314846912935720308089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 764345850202323841643141 143314846912935720308089)
                  ·
                    rfl

theorem cell22_1255971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 4].length) (baseStart_1255971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255971 prefixEnd_1255971 := by exact prefixLift 1255971
  have htrace : WordTrace (prefixWord ++ tailWord_1255971) baseStart_1255971 baseEnd_1255971 := by
    simpa [prefixWord, tailWord_1255971, baseEnd_1255971] using wordTrace_append hprefix tailTrace_1255971
  have hstable : (prefixWord ++ tailWord_1255971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255971).length < 2 ^ (prefixWord ++ tailWord_1255971).sum := by decide
  have hdescent : baseEnd_1255971 < baseStart_1255971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255984 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_1255984 : Nat := 118140960795 + 1255984 * 2 ^ 59
def prefixEnd_1255984 : Nat := 4983230072969 + 3 ^ 40 * 1255984 * 2
def baseEnd_1255984 : Nat := 429948990904479460349227

theorem tailTrace_1255984 : CollatzResearch.WordTrace tailWord_1255984 prefixEnd_1255984 429948990904479460349227 := by
  unfold tailWord_1255984
  simp only [CollatzResearch.WordTrace]
  refine ⟨22904749940895973917347503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30539666587861298556463337 22904749940895973917347503)
  ·
    refine ⟨34357124911343960876021255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22904749940895973917347503 34357124911343960876021255)
    ·
      refine ⟨51535687367015941314031883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34357124911343960876021255 51535687367015941314031883)
      ·
        refine ⟨77303531050523911971047825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51535687367015941314031883 77303531050523911971047825)
        ·
          refine ⟨57977648287892933978285869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77303531050523911971047825 57977648287892933978285869)
          ·
            refine ⟨21741618107959850241857201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57977648287892933978285869 21741618107959850241857201)
            ·
              refine ⟨16306213580969887681392901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21741618107959850241857201 16306213580969887681392901)
              ·
                refine ⟨3057415046431853940261169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16306213580969887681392901 3057415046431853940261169)
                ·
                  refine ⟨2293061284823890455195877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3057415046431853940261169 2293061284823890455195877)
                  ·
                    refine ⟨429948990904479460349227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293061284823890455195877 429948990904479460349227)
                    ·
                      rfl

theorem cell22_1255984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_1255984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1255984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1255984 prefixEnd_1255984 := by exact prefixLift 1255984
  have htrace : WordTrace (prefixWord ++ tailWord_1255984) baseStart_1255984 baseEnd_1255984 := by
    simpa [prefixWord, tailWord_1255984, baseEnd_1255984] using wordTrace_append hprefix tailTrace_1255984
  have hstable : (prefixWord ++ tailWord_1255984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255984).length < 2 ^ (prefixWord ++ tailWord_1255984).sum := by decide
  have hdescent : baseEnd_1255984 < baseStart_1255984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256044 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 7]
def baseStart_1256044 : Nat := 118140960795 + 1256044 * 2 ^ 59
def prefixEnd_1256044 : Nat := 4983230072969 + 3 ^ 40 * 1256044 * 2
def baseEnd_1256044 : Nat := 143323176710219767949681

theorem tailTrace_1256044 : CollatzResearch.WordTrace tailWord_1256044 prefixEnd_1256044 143323176710219767949681 := by
  unfold tailWord_1256044
  simp only [CollatzResearch.WordTrace]
  refine ⟨22905844130787289040939593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30541125507716385387919457 22905844130787289040939593)
  ·
    refine ⟨17179383098090466780704695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22905844130787289040939593 17179383098090466780704695)
    ·
      refine ⟨25769074647135700171057043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17179383098090466780704695 25769074647135700171057043)
      ·
        refine ⟨38653611970703550256585565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25769074647135700171057043 38653611970703550256585565)
        ·
          refine ⟨14495104489013831346219587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38653611970703550256585565 14495104489013831346219587)
          ·
            refine ⟨21742656733520747019329381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14495104489013831346219587 21742656733520747019329381)
            ·
              refine ⟨4076748137535140066124259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21742656733520747019329381 4076748137535140066124259)
              ·
                refine ⟨6115122206302710099186389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4076748137535140066124259 6115122206302710099186389)
                ·
                  refine ⟨143323176710219767949681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6115122206302710099186389 143323176710219767949681)
                  ·
                    rfl

theorem cell22_1256044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_1256044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256044 prefixEnd_1256044 := by exact prefixLift 1256044
  have htrace : WordTrace (prefixWord ++ tailWord_1256044) baseStart_1256044 baseEnd_1256044 := by
    simpa [prefixWord, tailWord_1256044, baseEnd_1256044] using wordTrace_append hprefix tailTrace_1256044
  have hstable : (prefixWord ++ tailWord_1256044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256044).length < 2 ^ (prefixWord ++ tailWord_1256044).sum := by decide
  have hdescent : baseEnd_1256044 < baseStart_1256044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256054 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1256054 : Nat := 118140960795 + 1256054 * 2 ^ 59
def prefixEnd_1256054 : Nat := 4983230072969 + 3 ^ 40 * 1256054 * 2
def baseEnd_1256054 : Nat := 429972953335022611099013

theorem tailTrace_1256054 : CollatzResearch.WordTrace tailWord_1256054 prefixEnd_1256054 429972953335022611099013 := by
  unfold tailWord_1256054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863253311971146861858951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30541368661025566526495477 2863253311971146861858951)
  ·
    refine ⟨4294879967956720292788427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2863253311971146861858951 4294879967956720292788427)
    ·
      refine ⟨6442319951935080439182641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4294879967956720292788427 6442319951935080439182641)
      ·
        refine ⟨4831739963951310329386981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6442319951935080439182641 4831739963951310329386981)
        ·
          refine ⟨905951243240870686760059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4831739963951310329386981 905951243240870686760059)
          ·
            refine ⟨1358926864861306030140089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905951243240870686760059 1358926864861306030140089)
            ·
              refine ⟨1019195148645979522605067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358926864861306030140089 1019195148645979522605067)
              ·
                refine ⟨1528792722968969283907601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019195148645979522605067 1528792722968969283907601)
                ·
                  refine ⟨1146594542226726962930701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528792722968969283907601 1146594542226726962930701)
                  ·
                    refine ⟨429972953335022611099013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1146594542226726962930701 429972953335022611099013)
                    ·
                      rfl

theorem cell22_1256054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1256054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256054 prefixEnd_1256054 := by exact prefixLift 1256054
  have htrace : WordTrace (prefixWord ++ tailWord_1256054) baseStart_1256054 baseEnd_1256054 := by
    simpa [prefixWord, tailWord_1256054, baseEnd_1256054] using wordTrace_append hprefix tailTrace_1256054
  have hstable : (prefixWord ++ tailWord_1256054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256054).length < 2 ^ (prefixWord ++ tailWord_1256054).sum := by decide
  have hdescent : baseEnd_1256054 < baseStart_1256054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256121 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 6, 3]
def baseStart_1256121 : Nat := 118140960795 + 1256121 * 2 ^ 59
def prefixEnd_1256121 : Nat := 4983230072969 + 3 ^ 40 * 1256121 * 2
def baseEnd_1256121 : Nat := 429995888804256769673807

theorem tailTrace_1256121 : CollatzResearch.WordTrace tailWord_1256121 prefixEnd_1256121 429995888804256769673807 := by
  unfold tailWord_1256121
  simp only [CollatzResearch.WordTrace]
  refine ⟨45814496682295620232432217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30542997788197080154954811 45814496682295620232432217)
  ·
    refine ⟨34360872511721715174324163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45814496682295620232432217 34360872511721715174324163)
    ·
      refine ⟨51541308767582572761486245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34360872511721715174324163 51541308767582572761486245)
      ·
        refine ⟨9663995393921732392778671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51541308767582572761486245 9663995393921732392778671)
        ·
          refine ⟨14495993090882598589168007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663995393921732392778671 14495993090882598589168007)
          ·
            refine ⟨21743989636323897883752011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14495993090882598589168007 21743989636323897883752011)
            ·
              refine ⟨32615984454485846825628017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21743989636323897883752011 32615984454485846825628017)
              ·
                refine ⟨24461988340864385119221013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32615984454485846825628017 24461988340864385119221013)
                ·
                  refine ⟨1146655703478018052463485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24461988340864385119221013 1146655703478018052463485)
                  ·
                    refine ⟨429995888804256769673807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1146655703478018052463485 429995888804256769673807)
                    ·
                      rfl

theorem cell22_1256121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_1256121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256121 prefixEnd_1256121 := by exact prefixLift 1256121
  have htrace : WordTrace (prefixWord ++ tailWord_1256121) baseStart_1256121 baseEnd_1256121 := by
    simpa [prefixWord, tailWord_1256121, baseEnd_1256121] using wordTrace_append hprefix tailTrace_1256121
  have hstable : (prefixWord ++ tailWord_1256121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256121).length < 2 ^ (prefixWord ++ tailWord_1256121).sum := by decide
  have hdescent : baseEnd_1256121 < baseStart_1256121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256136 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1256136 : Nat := 118140960795 + 1256136 * 2 ^ 59
def prefixEnd_1256136 : Nat := 4983230072969 + 3 ^ 40 * 1256136 * 2
def baseEnd_1256136 : Nat := 430001023610801730548761

theorem tailTrace_1256136 : CollatzResearch.WordTrace tailWord_1256136 prefixEnd_1256136 430001023610801730548761 := by
  unfold tailWord_1256136
  simp only [CollatzResearch.WordTrace]
  refine ⟨22907521888620638897114131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30543362518160851862818841 22907521888620638897114131)
  ·
    refine ⟨34361282832930958345671197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22907521888620638897114131 34361282832930958345671197)
    ·
      refine ⟨12885481062349109379626699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34361282832930958345671197 12885481062349109379626699)
      ·
        refine ⟨19328221593523664069440049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12885481062349109379626699 19328221593523664069440049)
        ·
          refine ⟨14496166195142748052080037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19328221593523664069440049 14496166195142748052080037)
          ·
            refine ⟨2718031161589265259765007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14496166195142748052080037 2718031161589265259765007)
            ·
              refine ⟨4077046742383897889647511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718031161589265259765007 4077046742383897889647511)
              ·
                refine ⟨6115570113575846834471267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077046742383897889647511 6115570113575846834471267)
                ·
                  refine ⟨9173355170363770251706901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6115570113575846834471267 9173355170363770251706901)
                  ·
                    refine ⟨430001023610801730548761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9173355170363770251706901 430001023610801730548761)
                    ·
                      rfl

theorem cell22_1256136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1256136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256136 prefixEnd_1256136 := by exact prefixLift 1256136
  have htrace : WordTrace (prefixWord ++ tailWord_1256136) baseStart_1256136 baseEnd_1256136 := by
    simpa [prefixWord, tailWord_1256136, baseEnd_1256136] using wordTrace_append hprefix tailTrace_1256136
  have hstable : (prefixWord ++ tailWord_1256136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256136).length < 2 ^ (prefixWord ++ tailWord_1256136).sum := by decide
  have hdescent : baseEnd_1256136 < baseStart_1256136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256140 : List Nat := [2, 2, 1, 5, 1, 2, 2, 3, 4]
def baseStart_1256140 : Nat := 118140960795 + 1256140 * 2 ^ 59
def prefixEnd_1256140 : Nat := 4983230072969 + 3 ^ 40 * 1256140 * 2
def baseEnd_1256140 : Nat := 143334130964182351149583

theorem tailTrace_1256140 : CollatzResearch.WordTrace tailWord_1256140 prefixEnd_1256140 143334130964182351149583 := by
  unfold tailWord_1256140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22907594834613393238686937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30543459779484524318249249 22907594834613393238686937)
  ·
    refine ⟨17180696125960044929015203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22907594834613393238686937 17180696125960044929015203)
    ·
      refine ⟨25771044188940067393522805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17180696125960044929015203 25771044188940067393522805)
      ·
        refine ⟨2416035392713131318142763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25771044188940067393522805 2416035392713131318142763)
        ·
          refine ⟨3624053089069696977214145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416035392713131318142763 3624053089069696977214145)
          ·
            refine ⟨2718039816802272732910609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3624053089069696977214145 2718039816802272732910609)
            ·
              refine ⟨2038529862601704549682957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718039816802272732910609 2038529862601704549682957)
              ·
                refine ⟨764448698475639206131109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2038529862601704549682957 764448698475639206131109)
                ·
                  refine ⟨143334130964182351149583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 764448698475639206131109 143334130964182351149583)
                  ·
                    rfl

theorem cell22_1256140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_1256140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256140 prefixEnd_1256140 := by exact prefixLift 1256140
  have htrace : WordTrace (prefixWord ++ tailWord_1256140) baseStart_1256140 baseEnd_1256140 := by
    simpa [prefixWord, tailWord_1256140, baseEnd_1256140] using wordTrace_append hprefix tailTrace_1256140
  have hstable : (prefixWord ++ tailWord_1256140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256140).length < 2 ^ (prefixWord ++ tailWord_1256140).sum := by decide
  have hdescent : baseEnd_1256140 < baseStart_1256140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256196 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 9]
def baseStart_1256196 : Nat := 118140960795 + 1256196 * 2 ^ 59
def prefixEnd_1256196 : Nat := 4983230072969 + 3 ^ 40 * 1256196 * 2
def baseEnd_1256196 : Nat := 143340520945660524682859

theorem tailTrace_1256196 : CollatzResearch.WordTrace tailWord_1256196 prefixEnd_1256196 143340520945660524682859 := by
  unfold tailWord_1256196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22908616078511954020706221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30544821438015938694274961 22908616078511954020706221)
  ·
    refine ⟨8590731029441982757764833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22908616078511954020706221 8590731029441982757764833)
    ·
      refine ⟨6443048272081487068323625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8590731029441982757764833 6443048272081487068323625)
      ·
        refine ⟨4832286204061115301242719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6443048272081487068323625 4832286204061115301242719)
        ·
          refine ⟨7248429306091672951864079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4832286204061115301242719 7248429306091672951864079)
          ·
            refine ⟨10872643959137509427796119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248429306091672951864079 10872643959137509427796119)
            ·
              refine ⟨16308965938706264141694179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10872643959137509427796119 16308965938706264141694179)
              ·
                refine ⟨24463448908059396212541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16308965938706264141694179 24463448908059396212541269)
                ·
                  refine ⟨143340520945660524682859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24463448908059396212541269 143340520945660524682859)
                  ·
                    rfl

theorem cell22_1256196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_1256196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256196 prefixEnd_1256196 := by exact prefixLift 1256196
  have htrace : WordTrace (prefixWord ++ tailWord_1256196) baseStart_1256196 baseEnd_1256196 := by
    simpa [prefixWord, tailWord_1256196, baseEnd_1256196] using wordTrace_append hprefix tailTrace_1256196
  have hstable : (prefixWord ++ tailWord_1256196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256196).length < 2 ^ (prefixWord ++ tailWord_1256196).sum := by decide
  have hdescent : baseEnd_1256196 < baseStart_1256196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256241 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 8]
def baseStart_1256241 : Nat := 118140960795 + 1256241 * 2 ^ 59
def prefixEnd_1256241 : Nat := 4983230072969 + 3 ^ 40 * 1256241 * 2
def baseEnd_1256241 : Nat := 143345655752205485557813

theorem tailTrace_1256241 : CollatzResearch.WordTrace tailWord_1256241 prefixEnd_1256241 143345655752205485557813 := by
  unfold tailWord_1256241
  simp only [CollatzResearch.WordTrace]
  refine ⟨45818873441860880726800577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30545915627907253817867051 45818873441860880726800577)
  ·
    refine ⟨34364155081395660545100433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45818873441860880726800577 34364155081395660545100433)
    ·
      refine ⟨25773116311046745408825325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34364155081395660545100433 25773116311046745408825325)
      ·
        refine ⟨9664918616642529528309497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25773116311046745408825325 9664918616642529528309497)
        ·
          refine ⟨7248688962481897146232123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9664918616642529528309497 7248688962481897146232123)
          ·
            refine ⟨10873033443722845719348185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248688962481897146232123 10873033443722845719348185)
            ·
              refine ⟨8154775082792134289511139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10873033443722845719348185 8154775082792134289511139)
              ·
                refine ⟨12232162624188201434266709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8154775082792134289511139 12232162624188201434266709)
                ·
                  refine ⟨143345655752205485557813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12232162624188201434266709 143345655752205485557813)
                  ·
                    rfl

theorem cell22_1256241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_1256241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256241 prefixEnd_1256241 := by exact prefixLift 1256241
  have htrace : WordTrace (prefixWord ++ tailWord_1256241) baseStart_1256241 baseEnd_1256241 := by
    simpa [prefixWord, tailWord_1256241, baseEnd_1256241] using wordTrace_append hprefix tailTrace_1256241
  have hstable : (prefixWord ++ tailWord_1256241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256241).length < 2 ^ (prefixWord ++ tailWord_1256241).sum := by decide
  have hdescent : baseEnd_1256241 < baseStart_1256241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256243 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 3, 4]
def baseStart_1256243 : Nat := 118140960795 + 1256243 * 2 ^ 59
def prefixEnd_1256243 : Nat := 4983230072969 + 3 ^ 40 * 1256243 * 2
def baseEnd_1256243 : Nat := 430037651897489118123433

theorem tailTrace_1256243 : CollatzResearch.WordTrace tailWord_1256243 prefixEnd_1256243 430037651897489118123433 := by
  unfold tailWord_1256243
  simp only [CollatzResearch.WordTrace]
  refine ⟨45818946387853635068373383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30545964258569090045582255 45818946387853635068373383)
  ·
    refine ⟨68728419581780452602560075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45818946387853635068373383 68728419581780452602560075)
    ·
      refine ⟨103092629372670678903840113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68728419581780452602560075 103092629372670678903840113)
      ·
        refine ⟨77319472029503009177880085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103092629372670678903840113 77319472029503009177880085)
        ·
          refine ⟨3624350251382953555213129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77319472029503009177880085 3624350251382953555213129)
          ·
            refine ⟨2718262688537215166409847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3624350251382953555213129 2718262688537215166409847)
            ·
              refine ⟨4077394032805822749614771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718262688537215166409847 4077394032805822749614771)
              ·
                refine ⟨6116091049208734124422157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077394032805822749614771 6116091049208734124422157)
                ·
                  refine ⟨2293534143453275296658309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6116091049208734124422157 2293534143453275296658309)
                  ·
                    refine ⟨430037651897489118123433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293534143453275296658309 430037651897489118123433)
                    ·
                      rfl

theorem cell22_1256243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_1256243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256243 prefixEnd_1256243 := by exact prefixLift 1256243
  have htrace : WordTrace (prefixWord ++ tailWord_1256243) baseStart_1256243 baseEnd_1256243 := by
    simpa [prefixWord, tailWord_1256243, baseEnd_1256243] using wordTrace_append hprefix tailTrace_1256243
  have hstable : (prefixWord ++ tailWord_1256243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256243).length < 2 ^ (prefixWord ++ tailWord_1256243).sum := by decide
  have hdescent : baseEnd_1256243 < baseStart_1256243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256305 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 2, 4]
def baseStart_1256305 : Nat := 118140960795 + 1256305 * 2 ^ 59
def prefixEnd_1256305 : Nat := 4983230072969 + 3 ^ 40 * 1256305 * 2
def baseEnd_1256305 : Nat := 430058875764541623073243

theorem tailTrace_1256305 : CollatzResearch.WordTrace tailWord_1256305 prefixEnd_1256305 430058875764541623073243 := by
  unfold tailWord_1256305
  simp only [CollatzResearch.WordTrace]
  refine ⟨45821207713629019657130369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30547471809086013104753579 45821207713629019657130369)
  ·
    refine ⟨34365905785221764742847777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45821207713629019657130369 34365905785221764742847777)
    ·
      refine ⟨25774429338916323557135833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34365905785221764742847777 25774429338916323557135833)
      ·
        refine ⟨19330822004187242667851875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25774429338916323557135833 19330822004187242667851875)
        ·
          refine ⟨28996233006280864001777813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19330822004187242667851875 28996233006280864001777813)
          ·
            refine ⟨1359198422169415500083335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28996233006280864001777813 1359198422169415500083335)
            ·
              refine ⟨2038797633254123250125003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359198422169415500083335 2038797633254123250125003)
              ·
                refine ⟨3058196449881184875187505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038797633254123250125003 3058196449881184875187505)
                ·
                  refine ⟨2293647337410888656390629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058196449881184875187505 2293647337410888656390629)
                  ·
                    refine ⟨430058875764541623073243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293647337410888656390629 430058875764541623073243)
                    ·
                      rfl

theorem cell22_1256305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_1256305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256305 prefixEnd_1256305 := by exact prefixLift 1256305
  have htrace : WordTrace (prefixWord ++ tailWord_1256305) baseStart_1256305 baseEnd_1256305 := by
    simpa [prefixWord, tailWord_1256305, baseEnd_1256305] using wordTrace_append hprefix tailTrace_1256305
  have hstable : (prefixWord ++ tailWord_1256305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256305).length < 2 ^ (prefixWord ++ tailWord_1256305).sum := by decide
  have hdescent : baseEnd_1256305 < baseStart_1256305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256444 : List Nat := [2, 2, 2, 1, 2, 5, 2, 2, 4]
def baseStart_1256444 : Nat := 118140960795 + 1256444 * 2 ^ 59
def prefixEnd_1256444 : Nat := 4983230072969 + 3 ^ 40 * 1256444 * 2
def baseEnd_1256444 : Nat := 143368819435063864615939

theorem tailTrace_1256444 : CollatzResearch.WordTrace tailWord_1256444 prefixEnd_1256444 143368819435063864615939 := by
  unfold tailWord_1256444
  simp only [CollatzResearch.WordTrace]
  refine ⟨22913138730062723198220193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30550851640083630930960257 22913138730062723198220193)
  ·
    refine ⟨17184854047547042398665145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22913138730062723198220193 17184854047547042398665145)
    ·
      refine ⟨12888640535660281798998859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17184854047547042398665145 12888640535660281798998859)
      ·
        refine ⟨19332960803490422698498289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12888640535660281798998859 19332960803490422698498289)
        ·
          refine ⟨14499720602617817023873717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19332960803490422698498289 14499720602617817023873717)
          ·
            refine ⟨1359348806495420345988161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14499720602617817023873717 1359348806495420345988161)
            ·
              refine ⟨1019511604871565259491121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359348806495420345988161 1019511604871565259491121)
              ·
                refine ⟨764633703653673944618341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019511604871565259491121 764633703653673944618341)
                ·
                  refine ⟨143368819435063864615939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 764633703653673944618341 143368819435063864615939)
                  ·
                    rfl

theorem cell22_1256444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_1256444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256444 prefixEnd_1256444 := by exact prefixLift 1256444
  have htrace : WordTrace (prefixWord ++ tailWord_1256444) baseStart_1256444 baseEnd_1256444 := by
    simpa [prefixWord, tailWord_1256444, baseEnd_1256444] using wordTrace_append hprefix tailTrace_1256444
  have hstable : (prefixWord ++ tailWord_1256444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256444).length < 2 ^ (prefixWord ++ tailWord_1256444).sum := by decide
  have hdescent : baseEnd_1256444 < baseStart_1256444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256504 : List Nat := [2, 1, 2, 1, 5, 1, 2, 4, 1, 3]
def baseStart_1256504 : Nat := 118140960795 + 1256504 * 2 ^ 59
def prefixEnd_1256504 : Nat := 4983230072969 + 3 ^ 40 * 1256504 * 2
def baseEnd_1256504 : Nat := 430126997531371437347633

theorem tailTrace_1256504 : CollatzResearch.WordTrace tailWord_1256504 prefixEnd_1256504 430126997531371437347633 := by
  unfold tailWord_1256504
  simp only [CollatzResearch.WordTrace]
  refine ⟨22914232919954038321812283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30552310559938717762416377 22914232919954038321812283)
  ·
    refine ⟨34371349379931057482718425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22914232919954038321812283 34371349379931057482718425)
    ·
      refine ⟨25778512034948293112038819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34371349379931057482718425 25778512034948293112038819)
      ·
        refine ⟨38667768052422439668058229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25778512034948293112038819 38667768052422439668058229)
        ·
          refine ⟨3625103254914603718880459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38667768052422439668058229 3625103254914603718880459)
          ·
            refine ⟨5437654882371905578320689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625103254914603718880459 5437654882371905578320689)
            ·
              refine ⟨4078241161778929183740517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437654882371905578320689 4078241161778929183740517)
              ·
                refine ⟨764670217833549221951347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4078241161778929183740517 764670217833549221951347)
                ·
                  refine ⟨1147005326750323832927021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764670217833549221951347 1147005326750323832927021)
                  ·
                    refine ⟨430126997531371437347633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1147005326750323832927021 430126997531371437347633)
                    ·
                      rfl

theorem cell22_1256504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_1256504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256504 prefixEnd_1256504 := by exact prefixLift 1256504
  have htrace : WordTrace (prefixWord ++ tailWord_1256504) baseStart_1256504 baseEnd_1256504 := by
    simpa [prefixWord, tailWord_1256504, baseEnd_1256504] using wordTrace_append hprefix tailTrace_1256504
  have hstable : (prefixWord ++ tailWord_1256504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256504).length < 2 ^ (prefixWord ++ tailWord_1256504).sum := by decide
  have hdescent : baseEnd_1256504 < baseStart_1256504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256581 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_1256581 : Nat := 118140960795 + 1256581 * 2 ^ 59
def prefixEnd_1256581 : Nat := 4983230072969 + 3 ^ 40 * 1256581 * 2
def baseEnd_1256581 : Nat := 430153356204968903172397

theorem tailTrace_1256581 : CollatzResearch.WordTrace tailWord_1256581 prefixEnd_1256581 430153356204968903172397 := by
  unfold tailWord_1256581
  simp only [CollatzResearch.WordTrace]
  refine ⟨45831274260629118794177597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30554182840419412529451731 45831274260629118794177597)
  ·
    refine ⟨17186727847735919547816599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45831274260629118794177597 17186727847735919547816599)
    ·
      refine ⟨25780091771603879321724899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17186727847735919547816599 25780091771603879321724899)
      ·
        refine ⟨38670137657405818982587349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25780091771603879321724899 38670137657405818982587349)
        ·
          refine ⟨906331351345448882404391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38670137657405818982587349 906331351345448882404391)
          ·
            refine ⟨1359497027018173323606587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906331351345448882404391 1359497027018173323606587)
            ·
              refine ⟨2039245540527259985409881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359497027018173323606587 2039245540527259985409881)
              ·
                refine ⟨1529434155395444989057411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2039245540527259985409881 1529434155395444989057411)
                ·
                  refine ⟨2294151233093167483586117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529434155395444989057411 2294151233093167483586117)
                  ·
                    refine ⟨430153356204968903172397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2294151233093167483586117 430153356204968903172397)
                    ·
                      rfl

theorem cell22_1256581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_1256581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256581 prefixEnd_1256581 := by exact prefixLift 1256581
  have htrace : WordTrace (prefixWord ++ tailWord_1256581) baseStart_1256581 baseEnd_1256581 := by
    simpa [prefixWord, tailWord_1256581, baseEnd_1256581] using wordTrace_append hprefix tailTrace_1256581
  have hstable : (prefixWord ++ tailWord_1256581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256581).length < 2 ^ (prefixWord ++ tailWord_1256581).sum := by decide
  have hdescent : baseEnd_1256581 < baseStart_1256581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256607 : List Nat := [1, 1, 2, 6, 3, 9]
def baseStart_1256607 : Nat := 118140960795 + 1256607 * 2 ^ 59
def prefixEnd_1256607 : Nat := 4983230072969 + 3 ^ 40 * 1256607 * 2
def baseEnd_1256607 : Nat := 5310645142423623481757

theorem tailTrace_1256607 : CollatzResearch.WordTrace tailWord_1256607 prefixEnd_1256607 5310645142423623481757 := by
  unfold tailWord_1256607
  simp only [CollatzResearch.WordTrace]
  refine ⟨45832222558534925234624075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30554815039023283489749383 45832222558534925234624075)
  ·
    refine ⟨68748333837802387851936113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45832222558534925234624075 68748333837802387851936113)
    ·
      refine ⟨51561250378351790888952085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68748333837802387851936113 51561250378351790888952085)
      ·
        refine ⟨2416933611485240197919629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51561250378351790888952085 2416933611485240197919629)
        ·
          refine ⟨906350104306965074219861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2416933611485240197919629 906350104306965074219861)
          ·
            refine ⟨5310645142423623481757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 906350104306965074219861 5310645142423623481757)
            ·
              rfl

theorem cell22_1256607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 9].length) (baseStart_1256607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256607 prefixEnd_1256607 := by exact prefixLift 1256607
  have htrace : WordTrace (prefixWord ++ tailWord_1256607) baseStart_1256607 baseEnd_1256607 := by
    simpa [prefixWord, tailWord_1256607, baseEnd_1256607] using wordTrace_append hprefix tailTrace_1256607
  have hstable : (prefixWord ++ tailWord_1256607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256607).length < 2 ^ (prefixWord ++ tailWord_1256607).sum := by decide
  have hdescent : baseEnd_1256607 < baseStart_1256607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256669 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 7]
def baseStart_1256669 : Nat := 118140960795 + 1256669 * 2 ^ 59
def prefixEnd_1256669 : Nat := 4983230072969 + 3 ^ 40 * 1256669 * 2
def baseEnd_1256669 : Nat := 143394493467788668990709

theorem tailTrace_1256669 : CollatzResearch.WordTrace tailWord_1256669 prefixEnd_1256669 143394493467788668990709 := by
  unfold tailWord_1256669
  simp only [CollatzResearch.WordTrace]
  refine ⟨45834483884310309823381061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30556322589540206548920707 45834483884310309823381061)
  ·
    refine ⟨8593965728308183091883949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45834483884310309823381061 8593965728308183091883949)
    ·
      refine ⟨3222737148115568659456481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8593965728308183091883949 3222737148115568659456481)
      ·
        refine ⟨2417052861086676494592361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3222737148115568659456481 2417052861086676494592361)
        ·
          refine ⟨1812789645815007370944271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417052861086676494592361 1812789645815007370944271)
          ·
            refine ⟨2719184468722511056416407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812789645815007370944271 2719184468722511056416407)
            ·
              refine ⟨4078776703083766584624611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719184468722511056416407 4078776703083766584624611)
              ·
                refine ⟨6118165054625649876936917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4078776703083766584624611 6118165054625649876936917)
                ·
                  refine ⟨143394493467788668990709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6118165054625649876936917 143394493467788668990709)
                  ·
                    rfl

theorem cell22_1256669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_1256669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256669 prefixEnd_1256669 := by exact prefixLift 1256669
  have htrace : WordTrace (prefixWord ++ tailWord_1256669) baseStart_1256669 baseEnd_1256669 := by
    simpa [prefixWord, tailWord_1256669, baseEnd_1256669] using wordTrace_append hprefix tailTrace_1256669
  have hstable : (prefixWord ++ tailWord_1256669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256669).length < 2 ^ (prefixWord ++ tailWord_1256669).sum := by decide
  have hdescent : baseEnd_1256669 < baseStart_1256669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256761 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_1256761 : Nat := 118140960795 + 1256761 * 2 ^ 59
def prefixEnd_1256761 : Nat := 4983230072969 + 3 ^ 40 * 1256761 * 2
def baseEnd_1256761 : Nat := 430214973883508433671845

theorem tailTrace_1256761 : CollatzResearch.WordTrace tailWord_1256761 prefixEnd_1256761 430214973883508433671845 := by
  unfold tailWord_1256761
  simp only [CollatzResearch.WordTrace]
  refine ⟨45837839399977009535730137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30558559599984673023820091 45837839399977009535730137)
  ·
    refine ⟨34378379549982757151797603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45837839399977009535730137 34378379549982757151797603)
    ·
      refine ⟨51567569324974135727696405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34378379549982757151797603 51567569324974135727696405)
      ·
        refine ⟨2417229812108162612235769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51567569324974135727696405 2417229812108162612235769)
        ·
          refine ⟨1812922359081121959176827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417229812108162612235769 1812922359081121959176827)
          ·
            refine ⟨2719383538621682938765241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812922359081121959176827 2719383538621682938765241)
            ·
              refine ⟨2039537653966262204073931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2719383538621682938765241 2039537653966262204073931)
              ·
                refine ⟨3059306480949393306110897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039537653966262204073931 3059306480949393306110897)
                ·
                  refine ⟨2294479860712044979583173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059306480949393306110897 2294479860712044979583173)
                  ·
                    refine ⟨430214973883508433671845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2294479860712044979583173 430214973883508433671845)
                    ·
                      rfl

theorem cell22_1256761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_1256761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256761 prefixEnd_1256761 := by exact prefixLift 1256761
  have htrace : WordTrace (prefixWord ++ tailWord_1256761) baseStart_1256761 baseEnd_1256761 := by
    simpa [prefixWord, tailWord_1256761, baseEnd_1256761] using wordTrace_append hprefix tailTrace_1256761
  have hstable : (prefixWord ++ tailWord_1256761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256761).length < 2 ^ (prefixWord ++ tailWord_1256761).sum := by decide
  have hdescent : baseEnd_1256761 < baseStart_1256761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256804 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 5]
def baseStart_1256804 : Nat := 118140960795 + 1256804 * 2 ^ 59
def prefixEnd_1256804 : Nat := 4983230072969 + 3 ^ 40 * 1256804 * 2
def baseEnd_1256804 : Nat := 143409897887423551615571

theorem tailTrace_1256804 : CollatzResearch.WordTrace tailWord_1256804 prefixEnd_1256804 143409897887423551615571 := by
  unfold tailWord_1256804
  simp only [CollatzResearch.WordTrace]
  refine ⟨22919703869410613939772733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30559605159214151919696977 22919703869410613939772733)
  ·
    refine ⟨8594888951028980227414775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22919703869410613939772733 8594888951028980227414775)
    ·
      refine ⟨12892333426543470341122163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8594888951028980227414775 12892333426543470341122163)
      ·
        refine ⟨19338500139815205511683245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12892333426543470341122163 19338500139815205511683245)
        ·
          refine ⟨7251937552430702066881217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19338500139815205511683245 7251937552430702066881217)
          ·
            refine ⟨5438953164323026550160913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7251937552430702066881217 5438953164323026550160913)
            ·
              refine ⟨4079214873242269912620685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5438953164323026550160913 4079214873242269912620685)
              ·
                refine ⟨1529705577465851217232757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4079214873242269912620685 1529705577465851217232757)
                ·
                  refine ⟨143409897887423551615571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1529705577465851217232757 143409897887423551615571)
                  ·
                    rfl

theorem cell22_1256804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_1256804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256804 prefixEnd_1256804 := by exact prefixLift 1256804
  have htrace : WordTrace (prefixWord ++ tailWord_1256804) baseStart_1256804 baseEnd_1256804 := by
    simpa [prefixWord, tailWord_1256804, baseEnd_1256804] using wordTrace_append hprefix tailTrace_1256804
  have hstable : (prefixWord ++ tailWord_1256804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256804).length < 2 ^ (prefixWord ++ tailWord_1256804).sum := by decide
  have hdescent : baseEnd_1256804 < baseStart_1256804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256900 : List Nat := [2, 3, 3, 2, 1, 2, 3, 2, 4]
def baseStart_1256900 : Nat := 118140960795 + 1256900 * 2 ^ 59
def prefixEnd_1256900 : Nat := 4983230072969 + 3 ^ 40 * 1256900 * 2
def baseEnd_1256900 : Nat := 143420852141386134815473

theorem tailTrace_1256900 : CollatzResearch.WordTrace tailWord_1256900 prefixEnd_1256900 143420852141386134815473 := by
  unfold tailWord_1256900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22921454573236718137520077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30561939430982290850026769 22921454573236718137520077)
  ·
    refine ⟨8595545464963769301570029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22921454573236718137520077 8595545464963769301570029)
    ·
      refine ⟨3223329549361413488088761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8595545464963769301570029 3223329549361413488088761)
      ·
        refine ⟨2417497162021060116066571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3223329549361413488088761 2417497162021060116066571)
        ·
          refine ⟨3626245743031590174099857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417497162021060116066571 3626245743031590174099857)
          ·
            refine ⟨2719684307273692630574893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3626245743031590174099857 2719684307273692630574893)
            ·
              refine ⟨1019881615227634736465585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2719684307273692630574893 1019881615227634736465585)
              ·
                refine ⟨764911211420726052349189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019881615227634736465585 764911211420726052349189)
                ·
                  refine ⟨143420852141386134815473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 764911211420726052349189 143420852141386134815473)
                  ·
                    rfl

theorem cell22_1256900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_1256900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256900 prefixEnd_1256900 := by exact prefixLift 1256900
  have htrace : WordTrace (prefixWord ++ tailWord_1256900) baseStart_1256900 baseEnd_1256900 := by
    simpa [prefixWord, tailWord_1256900, baseEnd_1256900] using wordTrace_append hprefix tailTrace_1256900
  have hstable : (prefixWord ++ tailWord_1256900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256900).length < 2 ^ (prefixWord ++ tailWord_1256900).sum := by decide
  have hdescent : baseEnd_1256900 < baseStart_1256900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256954 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_1256954 : Nat := 118140960795 + 1256954 * 2 ^ 59
def prefixEnd_1256954 : Nat := 4983230072969 + 3 ^ 40 * 1256954 * 2
def baseEnd_1256954 : Nat := 430281041727720263596253

theorem tailTrace_1256954 : CollatzResearch.WordTrace tailWord_1256954 prefixEnd_1256954 430281041727720263596253 := by
  unfold tailWord_1256954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11461219672069450874376479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30563252458851868998337277 11461219672069450874376479)
  ·
    refine ⟨17191829508104176311564719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11461219672069450874376479 17191829508104176311564719)
    ·
      refine ⟨25787744262156264467347079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17191829508104176311564719 25787744262156264467347079)
      ·
        refine ⟨38681616393234396701020619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25787744262156264467347079 38681616393234396701020619)
        ·
          refine ⟨58022424589851595051530929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38681616393234396701020619 58022424589851595051530929)
          ·
            refine ⟨43516818442388696288648197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58022424589851595051530929 43516818442388696288648197)
            ·
              refine ⟨8159403457947880554121537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43516818442388696288648197 8159403457947880554121537)
              ·
                refine ⟨6119552593460910415591153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8159403457947880554121537 6119552593460910415591153)
                ·
                  refine ⟨4589664445095682811693365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6119552593460910415591153 4589664445095682811693365)
                  ·
                    refine ⟨430281041727720263596253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4589664445095682811693365 430281041727720263596253)
                    ·
                      rfl

theorem cell22_1256954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_1256954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256954 prefixEnd_1256954 := by exact prefixLift 1256954
  have htrace : WordTrace (prefixWord ++ tailWord_1256954) baseStart_1256954 baseEnd_1256954 := by
    simpa [prefixWord, tailWord_1256954, baseEnd_1256954] using wordTrace_append hprefix tailTrace_1256954
  have hstable : (prefixWord ++ tailWord_1256954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256954).length < 2 ^ (prefixWord ++ tailWord_1256954).sum := by decide
  have hdescent : baseEnd_1256954 < baseStart_1256954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256969 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_1256969 : Nat := 118140960795 + 1256969 * 2 ^ 59
def prefixEnd_1256969 : Nat := 4983230072969 + 3 ^ 40 * 1256969 * 2
def baseEnd_1256969 : Nat := 430286176534265224471207

theorem tailTrace_1256969 : CollatzResearch.WordTrace tailWord_1256969 prefixEnd_1256969 430286176534265224471207 := by
  unfold tailWord_1256969
  simp only [CollatzResearch.WordTrace]
  refine ⟨45845425783223461059301961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30563617188815640706201307 45845425783223461059301961)
  ·
    refine ⟨34384069337417595794476471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45845425783223461059301961 34384069337417595794476471)
    ·
      refine ⟨51576104006126393691714707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34384069337417595794476471 51576104006126393691714707)
      ·
        refine ⟨77364156009189590537572061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51576104006126393691714707 77364156009189590537572061)
        ·
          refine ⟨29011558503446096451589523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77364156009189590537572061 29011558503446096451589523)
          ·
            refine ⟨43517337755169144677384285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29011558503446096451589523 43517337755169144677384285)
            ·
              refine ⟨16319001658188429254019107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43517337755169144677384285 16319001658188429254019107)
              ·
                refine ⟨24478502487282643881028661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16319001658188429254019107 24478502487282643881028661)
                ·
                  refine ⟨2294859608182747863846437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24478502487282643881028661 2294859608182747863846437)
                  ·
                    refine ⟨430286176534265224471207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2294859608182747863846437 430286176534265224471207)
                    ·
                      rfl

theorem cell22_1256969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_1256969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256969 prefixEnd_1256969 := by exact prefixLift 1256969
  have htrace : WordTrace (prefixWord ++ tailWord_1256969) baseStart_1256969 baseEnd_1256969 := by
    simpa [prefixWord, tailWord_1256969, baseEnd_1256969] using wordTrace_append hprefix tailTrace_1256969
  have hstable : (prefixWord ++ tailWord_1256969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256969).length < 2 ^ (prefixWord ++ tailWord_1256969).sum := by decide
  have hdescent : baseEnd_1256969 < baseStart_1256969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256971 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 2, 5]
def baseStart_1256971 : Nat := 118140960795 + 1256971 * 2 ^ 59
def prefixEnd_1256971 : Nat := 4983230072969 + 3 ^ 40 * 1256971 * 2
def baseEnd_1256971 : Nat := 430286861175137885921201

theorem tailTrace_1256971 : CollatzResearch.WordTrace tailWord_1256971 prefixEnd_1256971 430286861175137885921201 := by
  unfold tailWord_1256971
  simp only [CollatzResearch.WordTrace]
  refine ⟨45845498729216215400874767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30563665819477476933916511 45845498729216215400874767)
  ·
    refine ⟨68768248093824323101312151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45845498729216215400874767 68768248093824323101312151)
    ·
      refine ⟨103152372140736484651968227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68768248093824323101312151 103152372140736484651968227)
      ·
        refine ⟨154728558211104726977952341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103152372140736484651968227 154728558211104726977952341)
        ·
          refine ⟨1813225291536383519272879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 154728558211104726977952341 1813225291536383519272879)
          ·
            refine ⟨2719837937304575278909319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813225291536383519272879 2719837937304575278909319)
            ·
              refine ⟨4079756905956862918363979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719837937304575278909319 4079756905956862918363979)
              ·
                refine ⟨6119635358935294377545969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079756905956862918363979 6119635358935294377545969)
                ·
                  refine ⟨4589726519201470783159477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6119635358935294377545969 4589726519201470783159477)
                  ·
                    refine ⟨430286861175137885921201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4589726519201470783159477 430286861175137885921201)
                    ·
                      rfl

theorem cell22_1256971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5].length) (baseStart_1256971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256971 prefixEnd_1256971 := by exact prefixLift 1256971
  have htrace : WordTrace (prefixWord ++ tailWord_1256971) baseStart_1256971 baseEnd_1256971 := by
    simpa [prefixWord, tailWord_1256971, baseEnd_1256971] using wordTrace_append hprefix tailTrace_1256971
  have hstable : (prefixWord ++ tailWord_1256971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256971).length < 2 ^ (prefixWord ++ tailWord_1256971).sum := by decide
  have hdescent : baseEnd_1256971 < baseStart_1256971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256986 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_1256986 : Nat := 118140960795 + 1256986 * 2 ^ 59
def prefixEnd_1256986 : Nat := 4983230072969 + 3 ^ 40 * 1256986 * 2
def baseEnd_1256986 : Nat := 430291995981682846796155

theorem tailTrace_1256986 : CollatzResearch.WordTrace tailWord_1256986 prefixEnd_1256986 430291995981682846796155 := by
  unfold tailWord_1256986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11461511456040468240667703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30564030549441248641780541 11461511456040468240667703)
  ·
    refine ⟨17192267184060702361001555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11461511456040468240667703 17192267184060702361001555)
    ·
      refine ⟨25788400776091053541502333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17192267184060702361001555 25788400776091053541502333)
      ·
        refine ⟨9670650291034145078063375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25788400776091053541502333 9670650291034145078063375)
        ·
          refine ⟨14505975436551217617095063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9670650291034145078063375 14505975436551217617095063)
          ·
            refine ⟨21758963154826826425642595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14505975436551217617095063 21758963154826826425642595)
            ·
              refine ⟨32638444732240239638463893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21758963154826826425642595 32638444732240239638463893)
              ·
                refine ⟨1529927096823761233052995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32638444732240239638463893 1529927096823761233052995)
                ·
                  refine ⟨2294890645235641849579493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529927096823761233052995 2294890645235641849579493)
                  ·
                    refine ⟨430291995981682846796155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2294890645235641849579493 430291995981682846796155)
                    ·
                      rfl

theorem cell22_1256986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_1256986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1256986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1256986 prefixEnd_1256986 := by exact prefixLift 1256986
  have htrace : WordTrace (prefixWord ++ tailWord_1256986) baseStart_1256986 baseEnd_1256986 := by
    simpa [prefixWord, tailWord_1256986, baseEnd_1256986] using wordTrace_append hprefix tailTrace_1256986
  have hstable : (prefixWord ++ tailWord_1256986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256986).length < 2 ^ (prefixWord ++ tailWord_1256986).sum := by decide
  have hdescent : baseEnd_1256986 < baseStart_1256986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257029 : List Nat := [1, 3, 1, 1, 1, 4, 2, 9]
def baseStart_1257029 : Nat := 118140960795 + 1257029 * 2 ^ 59
def prefixEnd_1257029 : Nat := 4983230072969 + 3 ^ 40 * 1257029 * 2
def baseEnd_1257029 : Nat := 47811857306716118663447

theorem tailTrace_1257029 : CollatzResearch.WordTrace tailWord_1257029 prefixEnd_1257029 47811857306716118663447 := by
  unfold tailWord_1257029
  simp only [CollatzResearch.WordTrace]
  refine ⟨45847614163006091306486141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30565076108670727537657427 45847614163006091306486141)
  ·
    refine ⟨17192855311127284239932303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45847614163006091306486141 17192855311127284239932303)
    ·
      refine ⟨25789282966690926359898455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17192855311127284239932303 25789282966690926359898455)
      ·
        refine ⟨38683924450036389539847683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25789282966690926359898455 38683924450036389539847683)
        ·
          refine ⟨58025886675054584309771525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38683924450036389539847683 58025886675054584309771525)
          ·
            refine ⟨10879853751572734558082161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58025886675054584309771525 10879853751572734558082161)
            ·
              refine ⟨8159890313679550918561621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10879853751572734558082161 8159890313679550918561621)
              ·
                refine ⟨47811857306716118663447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8159890313679550918561621 47811857306716118663447)
                ·
                  rfl

theorem cell22_1257029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 9].length) (baseStart_1257029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257029 prefixEnd_1257029 := by exact prefixLift 1257029
  have htrace : WordTrace (prefixWord ++ tailWord_1257029) baseStart_1257029 baseEnd_1257029 := by
    simpa [prefixWord, tailWord_1257029, baseEnd_1257029] using wordTrace_append hprefix tailTrace_1257029
  have hstable : (prefixWord ++ tailWord_1257029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257029).length < 2 ^ (prefixWord ++ tailWord_1257029).sum := by decide
  have hdescent : baseEnd_1257029 < baseStart_1257029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257170 : List Nat := [3, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_1257170 : Nat := 118140960795 + 1257170 * 2 ^ 59
def prefixEnd_1257170 : Nat := 4983230072969 + 3 ^ 40 * 1257170 * 2
def baseEnd_1257170 : Nat := 143451660980655900065197

theorem tailTrace_1257170 : CollatzResearch.WordTrace tailWord_1257170 prefixEnd_1257170 143451660980655900065197 := by
  unfold tailWord_1257170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11463189213873818096842241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30568504570330181591579309 11463189213873818096842241)
  ·
    refine ⟨8597391910405363572631681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11463189213873818096842241 8597391910405363572631681)
    ·
      refine ⟨6448043932804022679473761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8597391910405363572631681 6448043932804022679473761)
      ·
        refine ⟨4836032949603017009605321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6448043932804022679473761 4836032949603017009605321)
        ·
          refine ⟨3627024712202262757203991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4836032949603017009605321 3627024712202262757203991)
          ·
            refine ⟨5440537068303394135805987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3627024712202262757203991 5440537068303394135805987)
            ·
              refine ⟨8160805602455091203708981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440537068303394135805987 8160805602455091203708981)
              ·
                refine ⟨765075525230164800347717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8160805602455091203708981 765075525230164800347717)
                ·
                  refine ⟨143451660980655900065197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765075525230164800347717 143451660980655900065197)
                  ·
                    rfl

theorem cell22_1257170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_1257170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257170 prefixEnd_1257170 := by exact prefixLift 1257170
  have htrace : WordTrace (prefixWord ++ tailWord_1257170) baseStart_1257170 baseEnd_1257170 := by
    simpa [prefixWord, tailWord_1257170, baseEnd_1257170] using wordTrace_append hprefix tailTrace_1257170
  have hstable : (prefixWord ++ tailWord_1257170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257170).length < 2 ^ (prefixWord ++ tailWord_1257170).sum := by decide
  have hdescent : baseEnd_1257170 < baseStart_1257170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257172 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_1257172 : Nat := 118140960795 + 1257172 * 2 ^ 59
def prefixEnd_1257172 : Nat := 4983230072969 + 3 ^ 40 * 1257172 * 2
def baseEnd_1257172 : Nat := 430355667582840361645585

theorem tailTrace_1257172 : CollatzResearch.WordTrace tailWord_1257172 prefixEnd_1257172 430355667582840361645585 := by
  unfold tailWord_1257172
  simp only [CollatzResearch.WordTrace]
  refine ⟨22926414900744013364470885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30568553200992017819294513 22926414900744013364470885)
  ·
    refine ⟨4298702793889502505838291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22926414900744013364470885 4298702793889502505838291)
    ·
      refine ⟨6448054190834253758757437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4298702793889502505838291 6448054190834253758757437)
      ·
        refine ⟨2418020321562845159534039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6448054190834253758757437 2418020321562845159534039)
        ·
          refine ⟨3627030482344267739301059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418020321562845159534039 3627030482344267739301059)
          ·
            refine ⟨5440545723516401608951589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3627030482344267739301059 5440545723516401608951589)
            ·
              refine ⟨1020102323159325301678423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5440545723516401608951589 1020102323159325301678423)
              ·
                refine ⟨1530153484738987952517635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020102323159325301678423 1530153484738987952517635)
                ·
                  refine ⟨2295230227108481928776453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530153484738987952517635 2295230227108481928776453)
                  ·
                    refine ⟨430355667582840361645585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2295230227108481928776453 430355667582840361645585)
                    ·
                      rfl

theorem cell22_1257172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_1257172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257172 prefixEnd_1257172 := by exact prefixLift 1257172
  have htrace : WordTrace (prefixWord ++ tailWord_1257172) baseStart_1257172 baseEnd_1257172 := by
    simpa [prefixWord, tailWord_1257172, baseEnd_1257172] using wordTrace_append hprefix tailTrace_1257172
  have hstable : (prefixWord ++ tailWord_1257172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257172).length < 2 ^ (prefixWord ++ tailWord_1257172).sum := by decide
  have hdescent : baseEnd_1257172 < baseStart_1257172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257185 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 4, 3]
def baseStart_1257185 : Nat := 118140960795 + 1257185 * 2 ^ 59
def prefixEnd_1257185 : Nat := 4983230072969 + 3 ^ 40 * 1257185 * 2
def baseEnd_1257185 : Nat := 430360117748512661070545

theorem tailTrace_1257185 : CollatzResearch.WordTrace tailWord_1257185 prefixEnd_1257185 430360117748512661070545 := by
  unfold tailWord_1257185
  simp only [CollatzResearch.WordTrace]
  refine ⟨45853303950440929949165009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30568869300293953299443339 45853303950440929949165009)
  ·
    refine ⟨34389977962830697461873757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45853303950440929949165009 34389977962830697461873757)
    ·
      refine ⟨12896241736061511548202659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34389977962830697461873757 12896241736061511548202659)
      ·
        refine ⟨19344362604092267322303989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12896241736061511548202659 19344362604092267322303989)
        ·
          refine ⟨1813533994133650061465999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19344362604092267322303989 1813533994133650061465999)
          ·
            refine ⟨2720300991200475092198999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813533994133650061465999 2720300991200475092198999)
            ·
              refine ⟨4080451486800712638298499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720300991200475092198999 4080451486800712638298499)
              ·
                refine ⟨6120677230201068957447749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4080451486800712638298499 6120677230201068957447749)
                ·
                  refine ⟨1147626980662700429521453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6120677230201068957447749 1147626980662700429521453)
                  ·
                    refine ⟨430360117748512661070545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1147626980662700429521453 430360117748512661070545)
                    ·
                      rfl

theorem cell22_1257185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_1257185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257185 prefixEnd_1257185 := by exact prefixLift 1257185
  have htrace : WordTrace (prefixWord ++ tailWord_1257185) baseStart_1257185 baseEnd_1257185 := by
    simpa [prefixWord, tailWord_1257185, baseEnd_1257185] using wordTrace_append hprefix tailTrace_1257185
  have hstable : (prefixWord ++ tailWord_1257185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257185).length < 2 ^ (prefixWord ++ tailWord_1257185).sum := by decide
  have hdescent : baseEnd_1257185 < baseStart_1257185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257202 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_1257202 : Nat := 118140960795 + 1257202 * 2 ^ 59
def prefixEnd_1257202 : Nat := 4983230072969 + 3 ^ 40 * 1257202 * 2
def baseEnd_1257202 : Nat := 430365937195930283395493

theorem tailTrace_1257202 : CollatzResearch.WordTrace tailWord_1257202 prefixEnd_1257202 430365937195930283395493 := by
  unfold tailWord_1257202
  simp only [CollatzResearch.WordTrace]
  refine ⟨11463480997844835463133465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30569282660919561235022573 11463480997844835463133465)
  ·
    refine ⟨8597610748383626597350099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11463480997844835463133465 8597610748383626597350099)
    ·
      refine ⟨12896416122575439896025149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597610748383626597350099 12896416122575439896025149)
      ·
        refine ⟨4836156045965789961009431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12896416122575439896025149 4836156045965789961009431)
        ·
          refine ⟨7254234068948684941514147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4836156045965789961009431 7254234068948684941514147)
          ·
            refine ⟨10881351103423027412271221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254234068948684941514147 10881351103423027412271221)
            ·
              refine ⟨1020126665945908819900427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10881351103423027412271221 1020126665945908819900427)
              ·
                refine ⟨1530189998918863229850641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020126665945908819900427 1530189998918863229850641)
                ·
                  refine ⟨1147642499189147422387981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1530189998918863229850641 1147642499189147422387981)
                  ·
                    refine ⟨430365937195930283395493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1147642499189147422387981 430365937195930283395493)
                    ·
                      rfl

theorem cell22_1257202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_1257202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257202 prefixEnd_1257202 := by exact prefixLift 1257202
  have htrace : WordTrace (prefixWord ++ tailWord_1257202) baseStart_1257202 baseEnd_1257202 := by
    simpa [prefixWord, tailWord_1257202, baseEnd_1257202] using wordTrace_append hprefix tailTrace_1257202
  have hstable : (prefixWord ++ tailWord_1257202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257202).length < 2 ^ (prefixWord ++ tailWord_1257202).sum := by decide
  have hdescent : baseEnd_1257202 < baseStart_1257202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257213 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1257213 : Nat := 118140960795 + 1257213 * 2 ^ 59
def prefixEnd_1257213 : Nat := 4983230072969 + 3 ^ 40 * 1257213 * 2
def baseEnd_1257213 : Nat := 430369702720729921370459

theorem tailTrace_1257213 : CollatzResearch.WordTrace tailWord_1257213 prefixEnd_1257213 430369702720729921370459 := by
  unfold tailWord_1257213
  simp only [CollatzResearch.WordTrace]
  refine ⟨45854325194339490731184293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30569550129559660487456195 45854325194339490731184293)
  ·
    refine ⟨8597685973938654512097055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45854325194339490731184293 8597685973938654512097055)
    ·
      refine ⟨12896528960907981768145583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597685973938654512097055 12896528960907981768145583)
      ·
        refine ⟨19344793441361972652218375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12896528960907981768145583 19344793441361972652218375)
        ·
          refine ⟨29017190162042958978327563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19344793441361972652218375 29017190162042958978327563)
          ·
            refine ⟨43525785243064438467491345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29017190162042958978327563 43525785243064438467491345)
            ·
              refine ⟨32644338932298328850618509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43525785243064438467491345 32644338932298328850618509)
              ·
                refine ⟨12241627099611873318981941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32644338932298328850618509 12241627099611873318981941)
                ·
                  refine ⟨1147652540588613123654557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12241627099611873318981941 1147652540588613123654557)
                  ·
                    refine ⟨430369702720729921370459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1147652540588613123654557 430369702720729921370459)
                    ·
                      rfl

theorem cell22_1257213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1257213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257213 prefixEnd_1257213 := by exact prefixLift 1257213
  have htrace : WordTrace (prefixWord ++ tailWord_1257213) baseStart_1257213 baseEnd_1257213 := by
    simpa [prefixWord, tailWord_1257213, baseEnd_1257213] using wordTrace_append hprefix tailTrace_1257213
  have hstable : (prefixWord ++ tailWord_1257213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257213).length < 2 ^ (prefixWord ++ tailWord_1257213).sum := by decide
  have hdescent : baseEnd_1257213 < baseStart_1257213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257260 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 5]
def baseStart_1257260 : Nat := 118140960795 + 1257260 * 2 ^ 59
def prefixEnd_1257260 : Nat := 4983230072969 + 3 ^ 40 * 1257260 * 2
def baseEnd_1257260 : Nat := 143461930593745821815105

theorem tailTrace_1257260 : CollatzResearch.WordTrace tailWord_1257260 prefixEnd_1257260 143461930593745821815105 := by
  unfold tailWord_1257260
  simp only [CollatzResearch.WordTrace]
  refine ⟨22928019712584608879072617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30570692950112811838763489 22928019712584608879072617)
  ·
    refine ⟨17196014784438456659304463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22928019712584608879072617 17196014784438456659304463)
    ·
      refine ⟨25794022176657684988956695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17196014784438456659304463 25794022176657684988956695)
      ·
        refine ⟨38691033264986527483435043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25794022176657684988956695 38691033264986527483435043)
        ·
          refine ⟨58036549897479791225152565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38691033264986527483435043 58036549897479791225152565)
          ·
            refine ⟨5440926552888730427358053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58036549897479791225152565 5440926552888730427358053)
            ·
              refine ⟨1020173728666636955129635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5440926552888730427358053 1020173728666636955129635)
              ·
                refine ⟨1530260592999955432694453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020173728666636955129635 1530260592999955432694453)
                ·
                  refine ⟨143461930593745821815105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1530260592999955432694453 143461930593745821815105)
                  ·
                    rfl

theorem cell22_1257260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_1257260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257260 prefixEnd_1257260 := by exact prefixLift 1257260
  have htrace : WordTrace (prefixWord ++ tailWord_1257260) baseStart_1257260 baseEnd_1257260 := by
    simpa [prefixWord, tailWord_1257260, baseEnd_1257260] using wordTrace_append hprefix tailTrace_1257260
  have hstable : (prefixWord ++ tailWord_1257260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257260).length < 2 ^ (prefixWord ++ tailWord_1257260).sum := by decide
  have hdescent : baseEnd_1257260 < baseStart_1257260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257305 : List Nat := [1, 2, 1, 2, 2, 3, 3, 4, 4]
def baseStart_1257305 : Nat := 118140960795 + 1257305 * 2 ^ 59
def prefixEnd_1257305 : Nat := 4983230072969 + 3 ^ 40 * 1257305 * 2
def baseEnd_1257305 : Nat := 143467065400290782690059

theorem tailTrace_1257305 : CollatzResearch.WordTrace tailWord_1257305 prefixEnd_1257305 143467065400290782690059 := by
  unfold tailWord_1257305
  simp only [CollatzResearch.WordTrace]
  refine ⟨45857680710006190443533369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30571787140004126962355579 45857680710006190443533369)
  ·
    refine ⟨34393260532504642832650027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45857680710006190443533369 34393260532504642832650027)
    ·
      refine ⟨51589890798756964248975041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34393260532504642832650027 51589890798756964248975041)
      ·
        refine ⟨38692418099067723186731281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51589890798756964248975041 38692418099067723186731281)
        ·
          refine ⟨29019313574300792390048461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38692418099067723186731281 29019313574300792390048461)
          ·
            refine ⟨10882242590362797146268173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29019313574300792390048461 10882242590362797146268173)
            ·
              refine ⟨4080840971386048929850565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10882242590362797146268173 4080840971386048929850565)
              ·
                refine ⟨765157682134884174346981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4080840971386048929850565 765157682134884174346981)
                ·
                  refine ⟨143467065400290782690059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765157682134884174346981 143467065400290782690059)
                  ·
                    rfl

theorem cell22_1257305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_1257305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257305 prefixEnd_1257305 := by exact prefixLift 1257305
  have htrace : WordTrace (prefixWord ++ tailWord_1257305) baseStart_1257305 baseEnd_1257305 := by
    simpa [prefixWord, tailWord_1257305, baseEnd_1257305] using wordTrace_append hprefix tailTrace_1257305
  have hstable : (prefixWord ++ tailWord_1257305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257305).length < 2 ^ (prefixWord ++ tailWord_1257305).sum := by decide
  have hdescent : baseEnd_1257305 < baseStart_1257305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257320 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1257320 : Nat := 118140960795 + 1257320 * 2 ^ 59
def prefixEnd_1257320 : Nat := 4983230072969 + 3 ^ 40 * 1257320 * 2
def baseEnd_1257320 : Nat := 430406331007417308945131

theorem tailTrace_1257320 : CollatzResearch.WordTrace tailWord_1257320 prefixEnd_1257320 430406331007417308945131 := by
  unfold tailWord_1257320
  simp only [CollatzResearch.WordTrace]
  refine ⟨22929113902475924002664707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30572151869967898670219609 22929113902475924002664707)
  ·
    refine ⟨34393670853713886003997061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22929113902475924002664707 34393670853713886003997061)
    ·
      refine ⟨6448813285071353625749449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34393670853713886003997061 6448813285071353625749449)
      ·
        refine ⟨4836609963803515219312087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6448813285071353625749449 4836609963803515219312087)
        ·
          refine ⟨7254914945705272828968131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4836609963803515219312087 7254914945705272828968131)
          ·
            refine ⟨10882372418557909243452197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254914945705272828968131 10882372418557909243452197)
            ·
              refine ⟨2040444828479607983147287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10882372418557909243452197 2040444828479607983147287)
              ·
                refine ⟨3060667242719411974720931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040444828479607983147287 3060667242719411974720931)
                ·
                  refine ⟨4591000864079117962081397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060667242719411974720931 4591000864079117962081397)
                  ·
                    refine ⟨430406331007417308945131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4591000864079117962081397 430406331007417308945131)
                    ·
                      rfl

theorem cell22_1257320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1257320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257320 prefixEnd_1257320 := by exact prefixLift 1257320
  have htrace : WordTrace (prefixWord ++ tailWord_1257320) baseStart_1257320 baseEnd_1257320 := by
    simpa [prefixWord, tailWord_1257320, baseEnd_1257320] using wordTrace_append hprefix tailTrace_1257320
  have hstable : (prefixWord ++ tailWord_1257320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257320).length < 2 ^ (prefixWord ++ tailWord_1257320).sum := by decide
  have hdescent : baseEnd_1257320 < baseStart_1257320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257322 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_1257322 : Nat := 118140960795 + 1257322 * 2 ^ 59
def prefixEnd_1257322 : Nat := 4983230072969 + 3 ^ 40 * 1257322 * 2
def baseEnd_1257322 : Nat := 143469005216096656798375

theorem tailTrace_1257322 : CollatzResearch.WordTrace tailWord_1257322 prefixEnd_1257322 143469005216096656798375 := by
  unfold tailWord_1257322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464575187736150586725555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30572200500629734897934813 11464575187736150586725555)
  ·
    refine ⟨17196862781604225880088333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11464575187736150586725555 17196862781604225880088333)
    ·
      refine ⟨6448823543101584705033125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17196862781604225880088333 6448823543101584705033125)
      ·
        refine ⟨1209154414331547132193711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6448823543101584705033125 1209154414331547132193711)
        ·
          refine ⟨1813731621497320698290567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209154414331547132193711 1813731621497320698290567)
          ·
            refine ⟨2720597432245981047435851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813731621497320698290567 2720597432245981047435851)
            ·
              refine ⟨4080896148368971571153777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720597432245981047435851 4080896148368971571153777)
              ·
                refine ⟨3060672111276728678365333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4080896148368971571153777 3060672111276728678365333)
                ·
                  refine ⟨143469005216096656798375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3060672111276728678365333 143469005216096656798375)
                  ·
                    rfl

theorem cell22_1257322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_1257322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257322 prefixEnd_1257322 := by exact prefixLift 1257322
  have htrace : WordTrace (prefixWord ++ tailWord_1257322) baseStart_1257322 baseEnd_1257322 := by
    simpa [prefixWord, tailWord_1257322, baseEnd_1257322] using wordTrace_append hprefix tailTrace_1257322
  have hstable : (prefixWord ++ tailWord_1257322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257322).length < 2 ^ (prefixWord ++ tailWord_1257322).sum := by decide
  have hdescent : baseEnd_1257322 < baseStart_1257322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257390 : List Nat := [4, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_1257390 : Nat := 118140960795 + 1257390 * 2 ^ 59
def prefixEnd_1257390 : Nat := 4983230072969 + 3 ^ 40 * 1257390 * 2
def baseEnd_1257390 : Nat := 143476764479320153231639

theorem tailTrace_1257390 : CollatzResearch.WordTrace tailWord_1257390 prefixEnd_1257390 143476764479320153231639 := by
  unfold tailWord_1257390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5732597614337281245047203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30573853943132166640251749 5732597614337281245047203)
  ·
    refine ⟨8598896421505921867570805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5732597614337281245047203 8598896421505921867570805)
    ·
      refine ⟨806146539516180175084763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8598896421505921867570805 806146539516180175084763)
      ·
        refine ⟨1209219809274270262627145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806146539516180175084763 1209219809274270262627145)
        ·
          refine ⟨906914856955702696970359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209219809274270262627145 906914856955702696970359)
          ·
            refine ⟨1360372285433554045455539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906914856955702696970359 1360372285433554045455539)
            ·
              refine ⟨2040558428150331068183309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360372285433554045455539 2040558428150331068183309)
              ·
                refine ⟨765209410556374150568741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2040558428150331068183309 765209410556374150568741)
                ·
                  refine ⟨143476764479320153231639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765209410556374150568741 143476764479320153231639)
                  ·
                    rfl

theorem cell22_1257390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_1257390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257390 prefixEnd_1257390 := by exact prefixLift 1257390
  have htrace : WordTrace (prefixWord ++ tailWord_1257390) baseStart_1257390 baseEnd_1257390 := by
    simpa [prefixWord, tailWord_1257390, baseEnd_1257390] using wordTrace_append hprefix tailTrace_1257390
  have hstable : (prefixWord ++ tailWord_1257390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257390).length < 2 ^ (prefixWord ++ tailWord_1257390).sum := by decide
  have hdescent : baseEnd_1257390 < baseStart_1257390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257416 : List Nat := [2, 1, 3, 1, 4, 2, 3, 2, 1, 3]
def baseStart_1257416 : Nat := 118140960795 + 1257416 * 2 ^ 59
def prefixEnd_1257416 : Nat := 4983230072969 + 3 ^ 40 * 1257416 * 2
def baseEnd_1257416 : Nat := 430439193769305058544837

theorem tailTrace_1257416 : CollatzResearch.WordTrace tailWord_1257416 prefixEnd_1257416 430439193769305058544837 := by
  unfold tailWord_1257416
  simp only [CollatzResearch.WordTrace]
  refine ⟨22930864606302028200412051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30574486141736037600549401 22930864606302028200412051)
  ·
    refine ⟨34396296909453042300618077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22930864606302028200412051 34396296909453042300618077)
    ·
      refine ⟨12898611341044890862731779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34396296909453042300618077 12898611341044890862731779)
      ·
        refine ⟨19347917011567336294097669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12898611341044890862731779 19347917011567336294097669)
        ·
          refine ⟨3627734439668875555143313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19347917011567336294097669 3627734439668875555143313)
          ·
            refine ⟨2720800829751656666357485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3627734439668875555143313 2720800829751656666357485)
            ·
              refine ⟨1020300311156871249884057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2720800829751656666357485 1020300311156871249884057)
              ·
                refine ⟨765225233367653437413043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020300311156871249884057 765225233367653437413043)
                ·
                  refine ⟨1147837850051480156119565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765225233367653437413043 1147837850051480156119565)
                  ·
                    refine ⟨430439193769305058544837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1147837850051480156119565 430439193769305058544837)
                    ·
                      rfl

theorem cell22_1257416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_1257416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257416 prefixEnd_1257416 := by exact prefixLift 1257416
  have htrace : WordTrace (prefixWord ++ tailWord_1257416) baseStart_1257416 baseEnd_1257416 := by
    simpa [prefixWord, tailWord_1257416, baseEnd_1257416] using wordTrace_append hprefix tailTrace_1257416
  have hstable : (prefixWord ++ tailWord_1257416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257416).length < 2 ^ (prefixWord ++ tailWord_1257416).sum := by decide
  have hdescent : baseEnd_1257416 < baseStart_1257416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257429 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 5]
def baseStart_1257429 : Nat := 118140960795 + 1257429 * 2 ^ 59
def prefixEnd_1257429 : Nat := 4983230072969 + 3 ^ 40 * 1257429 * 2
def baseEnd_1257429 : Nat := 143481214644992452656599

theorem tailTrace_1257429 : CollatzResearch.WordTrace tailWord_1257429 prefixEnd_1257429 143481214644992452656599 := by
  unfold tailWord_1257429
  simp only [CollatzResearch.WordTrace]
  refine ⟨45862203361556959621047341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30574802241037973080698227 45862203361556959621047341)
  ·
    refine ⟨17198326260583859857892753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45862203361556959621047341 17198326260583859857892753)
    ·
      refine ⟨12898744695437894893419565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17198326260583859857892753 12898744695437894893419565)
      ·
        refine ⟨4837029260789210585032337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12898744695437894893419565 4837029260789210585032337)
        ·
          refine ⟨3627771945591907938774253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4837029260789210585032337 3627771945591907938774253)
          ·
            refine ⟨1360414479596965477040345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3627771945591907938774253 1360414479596965477040345)
            ·
              refine ⟨1020310859697724107780259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360414479596965477040345 1020310859697724107780259)
              ·
                refine ⟨1530466289546586161670389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020310859697724107780259 1530466289546586161670389)
                ·
                  refine ⟨143481214644992452656599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1530466289546586161670389 143481214644992452656599)
                  ·
                    rfl

theorem cell22_1257429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_1257429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257429 prefixEnd_1257429 := by exact prefixLift 1257429
  have htrace : WordTrace (prefixWord ++ tailWord_1257429) baseStart_1257429 baseEnd_1257429 := by
    simpa [prefixWord, tailWord_1257429, baseEnd_1257429] using wordTrace_append hprefix tailTrace_1257429
  have hstable : (prefixWord ++ tailWord_1257429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257429).length < 2 ^ (prefixWord ++ tailWord_1257429).sum := by decide
  have hdescent : baseEnd_1257429 < baseStart_1257429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257455 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 1, 5]
def baseStart_1257455 : Nat := 118140960795 + 1257455 * 2 ^ 59
def prefixEnd_1257455 : Nat := 4983230072969 + 3 ^ 40 * 1257455 * 2
def baseEnd_1257455 : Nat := 430452544266321956819717

theorem tailTrace_1257455 : CollatzResearch.WordTrace tailWord_1257455 prefixEnd_1257455 430452544266321956819717 := by
  unfold tailWord_1257455
  simp only [CollatzResearch.WordTrace]
  refine ⟨45863151659462766061493819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30575434439641844040995879 45863151659462766061493819)
  ·
    refine ⟨68794727489194149092240729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45863151659462766061493819 68794727489194149092240729)
    ·
      refine ⟨51596045616895611819180547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68794727489194149092240729 51596045616895611819180547)
      ·
        refine ⟨77394068425343417728770821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51596045616895611819180547 77394068425343417728770821)
        ·
          refine ⟨14511387829751890824144529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77394068425343417728770821 14511387829751890824144529)
          ·
            refine ⟨10883540872313918118108397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14511387829751890824144529 10883540872313918118108397)
            ·
              refine ⟨4081327827117719294290649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10883540872313918118108397 4081327827117719294290649)
              ·
                refine ⟨3060995870338289470717987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081327827117719294290649 3060995870338289470717987)
                ·
                  refine ⟨4591493805507434206076981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060995870338289470717987 4591493805507434206076981)
                  ·
                    refine ⟨430452544266321956819717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4591493805507434206076981 430452544266321956819717)
                    ·
                      rfl

theorem cell22_1257455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_1257455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257455 prefixEnd_1257455 := by exact prefixLift 1257455
  have htrace : WordTrace (prefixWord ++ tailWord_1257455) baseStart_1257455 baseEnd_1257455 := by
    simpa [prefixWord, tailWord_1257455, baseEnd_1257455] using wordTrace_append hprefix tailTrace_1257455
  have hstable : (prefixWord ++ tailWord_1257455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257455).length < 2 ^ (prefixWord ++ tailWord_1257455).sum := by decide
  have hdescent : baseEnd_1257455 < baseStart_1257455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257478 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1257478 : Nat := 118140960795 + 1257478 * 2 ^ 59
def prefixEnd_1257478 : Nat := 4983230072969 + 3 ^ 40 * 1257478 * 2
def baseEnd_1257478 : Nat := 430460417636357563494647

theorem tailTrace_1257478 : CollatzResearch.WordTrace tailWord_1257478 prefixEnd_1257478 430460417636357563494647 := by
  unfold tailWord_1257478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433249704324357530924409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30575993692252960659720725 1433249704324357530924409)
  ·
    refine ⟨1074937278243268148193307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1433249704324357530924409 1074937278243268148193307)
    ·
      refine ⟨1612405917364902222289961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1074937278243268148193307 1612405917364902222289961)
      ·
        refine ⟨1209304438023676666717471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1612405917364902222289961 1209304438023676666717471)
        ·
          refine ⟨1813956657035515000076207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209304438023676666717471 1813956657035515000076207)
          ·
            refine ⟨2720934985553272500114311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813956657035515000076207 2720934985553272500114311)
            ·
              refine ⟨4081402478329908750171467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720934985553272500114311 4081402478329908750171467)
              ·
                refine ⟨6122103717494863125257201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4081402478329908750171467 6122103717494863125257201)
                ·
                  refine ⟨4591577788121147343942901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122103717494863125257201 4591577788121147343942901)
                  ·
                    refine ⟨430460417636357563494647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4591577788121147343942901 430460417636357563494647)
                    ·
                      rfl

theorem cell22_1257478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1257478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257478 prefixEnd_1257478 := by exact prefixLift 1257478
  have htrace : WordTrace (prefixWord ++ tailWord_1257478) baseStart_1257478 baseEnd_1257478 := by
    simpa [prefixWord, tailWord_1257478, baseEnd_1257478] using wordTrace_append hprefix tailTrace_1257478
  have hstable : (prefixWord ++ tailWord_1257478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257478).length < 2 ^ (prefixWord ++ tailWord_1257478).sum := by decide
  have hdescent : baseEnd_1257478 < baseStart_1257478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257545 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_1257545 : Nat := 118140960795 + 1257545 * 2 ^ 59
def prefixEnd_1257545 : Nat := 4983230072969 + 3 ^ 40 * 1257545 * 2
def baseEnd_1257545 : Nat := 430483353105591722069441

theorem tailTrace_1257545 : CollatzResearch.WordTrace tailWord_1257545 prefixEnd_1257545 430483353105591722069441 := by
  unfold tailWord_1257545
  simp only [CollatzResearch.WordTrace]
  refine ⟨45866434229136711432270089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30577622819424474288180059 45866434229136711432270089)
  ·
    refine ⟨34399825671852533574202567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45866434229136711432270089 34399825671852533574202567)
    ·
      refine ⟨51599738507778800361303851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34399825671852533574202567 51599738507778800361303851)
      ·
        refine ⟨77399607761668200541955777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51599738507778800361303851 77399607761668200541955777)
        ·
          refine ⟨58049705821251150406466833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77399607761668200541955777 58049705821251150406466833)
          ·
            refine ⟨43537279365938362804850125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58049705821251150406466833 43537279365938362804850125)
            ·
              refine ⟨16326479762226886051818797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43537279365938362804850125 16326479762226886051818797)
              ·
                refine ⟨6122429910835082269432049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16326479762226886051818797 6122429910835082269432049)
                ·
                  refine ⟨4591822433126311702074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122429910835082269432049 4591822433126311702074037)
                  ·
                    refine ⟨430483353105591722069441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4591822433126311702074037 430483353105591722069441)
                    ·
                      rfl

theorem cell22_1257545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_1257545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257545 prefixEnd_1257545 := by exact prefixLift 1257545
  have htrace : WordTrace (prefixWord ++ tailWord_1257545) baseStart_1257545 baseEnd_1257545 := by
    simpa [prefixWord, tailWord_1257545, baseEnd_1257545] using wordTrace_append hprefix tailTrace_1257545
  have hstable : (prefixWord ++ tailWord_1257545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257545).length < 2 ^ (prefixWord ++ tailWord_1257545).sum := by decide
  have hdescent : baseEnd_1257545 < baseStart_1257545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257577 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_1257577 : Nat := 118140960795 + 1257577 * 2 ^ 59
def prefixEnd_1257577 : Nat := 4983230072969 + 3 ^ 40 * 1257577 * 2
def baseEnd_1257577 : Nat := 430494307359554305269343

theorem tailTrace_1257577 : CollatzResearch.WordTrace tailWord_1257577 prefixEnd_1257577 430494307359554305269343 := by
  unfold tailWord_1257577
  simp only [CollatzResearch.WordTrace]
  refine ⟨45867601365020780897434985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30578400910013853931623323 45867601365020780897434985)
  ·
    refine ⟨34400701023765585673076239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45867601365020780897434985 34400701023765585673076239)
    ·
      refine ⟨51601051535648378509614359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34400701023765585673076239 51601051535648378509614359)
      ·
        refine ⟨77401577303472567764421539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51601051535648378509614359 77401577303472567764421539)
        ·
          refine ⟨116102365955208851646632309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77401577303472567764421539 116102365955208851646632309)
          ·
            refine ⟨10884596808300829841871779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116102365955208851646632309 10884596808300829841871779)
            ·
              refine ⟨16326895212451244762807669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10884596808300829841871779 16326895212451244762807669)
              ·
                refine ⟨1530646426167304196513219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16326895212451244762807669 1530646426167304196513219)
                ·
                  refine ⟨2295969639250956294769829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530646426167304196513219 2295969639250956294769829)
                  ·
                    refine ⟨430494307359554305269343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2295969639250956294769829 430494307359554305269343)
                    ·
                      rfl

theorem cell22_1257577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_1257577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257577 prefixEnd_1257577 := by exact prefixLift 1257577
  have htrace : WordTrace (prefixWord ++ tailWord_1257577) baseStart_1257577 baseEnd_1257577 := by
    simpa [prefixWord, tailWord_1257577, baseEnd_1257577] using wordTrace_append hprefix tailTrace_1257577
  have hstable : (prefixWord ++ tailWord_1257577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257577).length < 2 ^ (prefixWord ++ tailWord_1257577).sum := by decide
  have hdescent : baseEnd_1257577 < baseStart_1257577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257624 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_1257624 : Nat := 118140960795 + 1257624 * 2 ^ 59
def prefixEnd_1257624 : Nat := 4983230072969 + 3 ^ 40 * 1257624 * 2
def baseEnd_1257624 : Nat := 430510396420061849344199

theorem tailTrace_1257624 : CollatzResearch.WordTrace tailWord_1257624 prefixEnd_1257624 430510396420061849344199 := by
  unfold tailWord_1257624
  simp only [CollatzResearch.WordTrace]
  refine ⟨22934657797925253962197963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30579543730567005282930617 22934657797925253962197963)
  ·
    refine ⟨34401986696887880943296945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22934657797925253962197963 34401986696887880943296945)
    ·
      refine ⟨25801490022665910707472709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34401986696887880943296945 25801490022665910707472709)
      ·
        refine ⟨4837779379249858257651133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25801490022665910707472709 4837779379249858257651133)
        ·
          refine ⟨1814167267218696846619175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4837779379249858257651133 1814167267218696846619175)
          ·
            refine ⟨2721250900828045269928763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814167267218696846619175 2721250900828045269928763)
            ·
              refine ⟨4081876351242067904893145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721250900828045269928763 4081876351242067904893145)
              ·
                refine ⟨3061407263431550928669859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081876351242067904893145 3061407263431550928669859)
                ·
                  refine ⟨4592110895147326393004789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061407263431550928669859 4592110895147326393004789)
                  ·
                    refine ⟨430510396420061849344199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4592110895147326393004789 430510396420061849344199)
                    ·
                      rfl

theorem cell22_1257624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_1257624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257624 prefixEnd_1257624 := by exact prefixLift 1257624
  have htrace : WordTrace (prefixWord ++ tailWord_1257624) baseStart_1257624 baseEnd_1257624 := by
    simpa [prefixWord, tailWord_1257624, baseEnd_1257624] using wordTrace_append hprefix tailTrace_1257624
  have hstable : (prefixWord ++ tailWord_1257624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257624).length < 2 ^ (prefixWord ++ tailWord_1257624).sum := by decide
  have hdescent : baseEnd_1257624 < baseStart_1257624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257692 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1257692 : Nat := 118140960795 + 1257692 * 2 ^ 59
def prefixEnd_1257692 : Nat := 4983230072969 + 3 ^ 40 * 1257692 * 2
def baseEnd_1257692 : Nat := 430533674209732338643991

theorem tailTrace_1257692 : CollatzResearch.WordTrace tailWord_1257692 prefixEnd_1257692 430533674209732338643991 := by
  unfold tailWord_1257692
  simp only [CollatzResearch.WordTrace]
  refine ⟨22935897879802077768935665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30581197173069437025247553 22935897879802077768935665)
  ·
    refine ⟨17201923409851558326701749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22935897879802077768935665 17201923409851558326701749)
    ·
      refine ⟨1612680319673583593128289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17201923409851558326701749 1612680319673583593128289)
      ·
        refine ⟨1209510239755187694846217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1612680319673583593128289 1209510239755187694846217)
        ·
          refine ⟨907132679816390771134663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209510239755187694846217 907132679816390771134663)
          ·
            refine ⟨1360699019724586156701995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907132679816390771134663 1360699019724586156701995)
            ·
              refine ⟨2041048529586879235052993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360699019724586156701995 2041048529586879235052993)
              ·
                refine ⟨1530786397190159426289745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041048529586879235052993 1530786397190159426289745)
                ·
                  refine ⟨1148089797892619569717309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1530786397190159426289745 1148089797892619569717309)
                  ·
                    refine ⟨430533674209732338643991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148089797892619569717309 430533674209732338643991)
                    ·
                      rfl

theorem cell22_1257692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1257692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257692 prefixEnd_1257692 := by exact prefixLift 1257692
  have htrace : WordTrace (prefixWord ++ tailWord_1257692) baseStart_1257692 baseEnd_1257692 := by
    simpa [prefixWord, tailWord_1257692, baseEnd_1257692] using wordTrace_append hprefix tailTrace_1257692
  have hstable : (prefixWord ++ tailWord_1257692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257692).length < 2 ^ (prefixWord ++ tailWord_1257692).sum := by decide
  have hdescent : baseEnd_1257692 < baseStart_1257692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257697 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1257697 : Nat := 118140960795 + 1257697 * 2 ^ 59
def prefixEnd_1257697 : Nat := 4983230072969 + 3 ^ 40 * 1257697 * 2
def baseEnd_1257697 : Nat := 430535385811913992268975

theorem tailTrace_1257697 : CollatzResearch.WordTrace tailWord_1257697 prefixEnd_1257697 430535385811913992268975 := by
  unfold tailWord_1257697
  simp only [CollatzResearch.WordTrace]
  refine ⟨45871978124586041391803345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30581318749724027594535563 45871978124586041391803345)
  ·
    refine ⟨34403983593439531043852509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45871978124586041391803345 34403983593439531043852509)
    ·
      refine ⟨12901493847539824141444691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34403983593439531043852509 12901493847539824141444691)
      ·
        refine ⟨19352240771309736212167037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12901493847539824141444691 19352240771309736212167037)
        ·
          refine ⟨7257090289241151079562639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19352240771309736212167037 7257090289241151079562639)
          ·
            refine ⟨10885635433861726619343959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7257090289241151079562639 10885635433861726619343959)
            ·
              refine ⟨16328453150792589929015939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10885635433861726619343959 16328453150792589929015939)
              ·
                refine ⟨24492679726188884893523909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16328453150792589929015939 24492679726188884893523909)
                ·
                  refine ⟨4592377448660415917535733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24492679726188884893523909 4592377448660415917535733)
                  ·
                    refine ⟨430535385811913992268975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4592377448660415917535733 430535385811913992268975)
                    ·
                      rfl

theorem cell22_1257697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1257697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257697 prefixEnd_1257697 := by exact prefixLift 1257697
  have htrace : WordTrace (prefixWord ++ tailWord_1257697) baseStart_1257697 baseEnd_1257697 := by
    simpa [prefixWord, tailWord_1257697, baseEnd_1257697] using wordTrace_append hprefix tailTrace_1257697
  have hstable : (prefixWord ++ tailWord_1257697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257697).length < 2 ^ (prefixWord ++ tailWord_1257697).sum := by decide
  have hdescent : baseEnd_1257697 < baseStart_1257697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257703 : List Nat := [1, 1, 5, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1257703 : Nat := 118140960795 + 1257703 * 2 ^ 59
def prefixEnd_1257703 : Nat := 4983230072969 + 3 ^ 40 * 1257703 * 2
def baseEnd_1257703 : Nat := 430537439734531976618957

theorem tailTrace_1257703 : CollatzResearch.WordTrace tailWord_1257703 prefixEnd_1257703 430537439734531976618957 := by
  unfold tailWord_1257703
  simp only [CollatzResearch.WordTrace]
  refine ⟨45872196962564304416521763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30581464641709536277681175 45872196962564304416521763)
  ·
    refine ⟨68808295443846456624782645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45872196962564304416521763 68808295443846456624782645)
    ·
      refine ⟨6450777697860605308573373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68808295443846456624782645 6450777697860605308573373)
      ·
        refine ⟨2419041636697726990715015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6450777697860605308573373 2419041636697726990715015)
        ·
          refine ⟨3628562455046590486072523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419041636697726990715015 3628562455046590486072523)
          ·
            refine ⟨5442843682569885729108785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628562455046590486072523 5442843682569885729108785)
            ·
              refine ⟨4082132761927414296831589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5442843682569885729108785 4082132761927414296831589)
              ·
                refine ⟨765399892861390180655923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4082132761927414296831589 765399892861390180655923)
                ·
                  refine ⟨1148099839292085270983885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765399892861390180655923 1148099839292085270983885)
                  ·
                    refine ⟨430537439734531976618957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148099839292085270983885 430537439734531976618957)
                    ·
                      rfl

theorem cell22_1257703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1257703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257703 prefixEnd_1257703 := by exact prefixLift 1257703
  have htrace : WordTrace (prefixWord ++ tailWord_1257703) baseStart_1257703 baseEnd_1257703 := by
    simpa [prefixWord, tailWord_1257703, baseEnd_1257703] using wordTrace_append hprefix tailTrace_1257703
  have hstable : (prefixWord ++ tailWord_1257703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257703).length < 2 ^ (prefixWord ++ tailWord_1257703).sum := by decide
  have hdescent : baseEnd_1257703 < baseStart_1257703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257712 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_1257712 : Nat := 118140960795 + 1257712 * 2 ^ 59
def prefixEnd_1257712 : Nat := 4983230072969 + 3 ^ 40 * 1257712 * 2
def baseEnd_1257712 : Nat := 430540520618458953143929

theorem tailTrace_1257712 : CollatzResearch.WordTrace tailWord_1257712 prefixEnd_1257712 430540520618458953143929 := by
  unfold tailWord_1257712
  simp only [CollatzResearch.WordTrace]
  refine ⟨22936262609765849476799695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30581683479687799302399593 22936262609765849476799695)
  ·
    refine ⟨34404393914648774215199543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22936262609765849476799695 34404393914648774215199543)
    ·
      refine ⟨51606590871973161322799315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34404393914648774215199543 51606590871973161322799315)
      ·
        refine ⟨77409886307959741984198973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51606590871973161322799315 77409886307959741984198973)
        ·
          refine ⟨29028707365484903244074615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77409886307959741984198973 29028707365484903244074615)
          ·
            refine ⟨43543061048227354866111923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29028707365484903244074615 43543061048227354866111923)
            ·
              refine ⟨65314591572341032299167885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43543061048227354866111923 65314591572341032299167885)
              ·
                refine ⟨24492971839627887112187957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65314591572341032299167885 24492971839627887112187957)
                ·
                  refine ⟨2296216109965114416767621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24492971839627887112187957 2296216109965114416767621)
                  ·
                    refine ⟨430540520618458953143929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296216109965114416767621 430540520618458953143929)
                    ·
                      rfl

theorem cell22_1257712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_1257712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257712 prefixEnd_1257712 := by exact prefixLift 1257712
  have htrace : WordTrace (prefixWord ++ tailWord_1257712) baseStart_1257712 baseEnd_1257712 := by
    simpa [prefixWord, tailWord_1257712, baseEnd_1257712] using wordTrace_append hprefix tailTrace_1257712
  have hstable : (prefixWord ++ tailWord_1257712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257712).length < 2 ^ (prefixWord ++ tailWord_1257712).sum := by decide
  have hdescent : baseEnd_1257712 < baseStart_1257712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257714 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1257714 : Nat := 118140960795 + 1257714 * 2 ^ 59
def prefixEnd_1257714 : Nat := 4983230072969 + 3 ^ 40 * 1257714 * 2
def baseEnd_1257714 : Nat := 430541205259331614593923

theorem tailTrace_1257714 : CollatzResearch.WordTrace tailWord_1257714 prefixEnd_1257714 430541205259331614593923 := by
  unfold tailWord_1257714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11468149541381113323793049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30581732110349635530114797 11468149541381113323793049)
  ·
    refine ⟨8601112156035834992844787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11468149541381113323793049 8601112156035834992844787)
    ·
      refine ⟨12901668234053752489267181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8601112156035834992844787 12901668234053752489267181)
      ·
        refine ⟨4838125587770157183475193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12901668234053752489267181 4838125587770157183475193)
        ·
          refine ⟨3628594190827617887606395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838125587770157183475193 3628594190827617887606395)
          ·
            refine ⟨5442891286241426831409593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628594190827617887606395 5442891286241426831409593)
            ·
              refine ⟨4082168464681070123557195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5442891286241426831409593 4082168464681070123557195)
              ·
                refine ⟨6123252697021605185335793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4082168464681070123557195 6123252697021605185335793)
                ·
                  refine ⟨4592439522766203889001845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6123252697021605185335793 4592439522766203889001845)
                  ·
                    refine ⟨430541205259331614593923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4592439522766203889001845 430541205259331614593923)
                    ·
                      rfl

theorem cell22_1257714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1257714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257714 prefixEnd_1257714 := by exact prefixLift 1257714
  have htrace : WordTrace (prefixWord ++ tailWord_1257714) baseStart_1257714 baseEnd_1257714 := by
    simpa [prefixWord, tailWord_1257714, baseEnd_1257714] using wordTrace_append hprefix tailTrace_1257714
  have hstable : (prefixWord ++ tailWord_1257714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257714).length < 2 ^ (prefixWord ++ tailWord_1257714).sum := by decide
  have hdescent : baseEnd_1257714 < baseStart_1257714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257727 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 6]
def baseStart_1257727 : Nat := 118140960795 + 1257727 * 2 ^ 59
def prefixEnd_1257727 : Nat := 4983230072969 + 3 ^ 40 * 1257727 * 2
def baseEnd_1257727 : Nat := 143515218475001304672961

theorem tailTrace_1257727 : CollatzResearch.WordTrace tailWord_1257727 prefixEnd_1257727 143515218475001304672961 := by
  unfold tailWord_1257727
  simp only [CollatzResearch.WordTrace]
  refine ⟨45873072314477356515395435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30582048209651571010263623 45873072314477356515395435)
  ·
    refine ⟨68809608471716034773093153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45873072314477356515395435 68809608471716034773093153)
    ·
      refine ⟨51607206353787026079819865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68809608471716034773093153 51607206353787026079819865)
      ·
        refine ⟨38705404765340269559864899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51607206353787026079819865 38705404765340269559864899)
        ·
          refine ⟨58058107148010404339797349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38705404765340269559864899 58058107148010404339797349)
          ·
            refine ⟨10885895090251950813712003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58058107148010404339797349 10885895090251950813712003)
            ·
              refine ⟨16328842635377926220568005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10885895090251950813712003 16328842635377926220568005)
              ·
                refine ⟨3061657994133361166356501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16328842635377926220568005 3061657994133361166356501)
                ·
                  refine ⟨143515218475001304672961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3061657994133361166356501 143515218475001304672961)
                  ·
                    rfl

theorem cell22_1257727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 6].length) (baseStart_1257727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257727 prefixEnd_1257727 := by exact prefixLift 1257727
  have htrace : WordTrace (prefixWord ++ tailWord_1257727) baseStart_1257727 baseEnd_1257727 := by
    simpa [prefixWord, tailWord_1257727, baseEnd_1257727] using wordTrace_append hprefix tailTrace_1257727
  have hstable : (prefixWord ++ tailWord_1257727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257727).length < 2 ^ (prefixWord ++ tailWord_1257727).sum := by decide
  have hdescent : baseEnd_1257727 < baseStart_1257727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257767 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 5]
def baseStart_1257767 : Nat := 118140960795 + 1257767 * 2 ^ 59
def prefixEnd_1257767 : Nat := 4983230072969 + 3 ^ 40 * 1257767 * 2
def baseEnd_1257767 : Nat := 143519782747485714339587

theorem tailTrace_1257767 : CollatzResearch.WordTrace tailWord_1257767 prefixEnd_1257767 143519782747485714339587 := by
  unfold tailWord_1257767
  simp only [CollatzResearch.WordTrace]
  refine ⟨45874531234332443346851555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30583020822888295564567703 45874531234332443346851555)
  ·
    refine ⟨68811796851498665020277333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45874531234332443346851555 68811796851498665020277333)
    ·
      refine ⟨806388244353499980706375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 68811796851498665020277333 806388244353499980706375)
      ·
        refine ⟨1209582366530249971059563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806388244353499980706375 1209582366530249971059563)
        ·
          refine ⟨1814373549795374956589345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209582366530249971059563 1814373549795374956589345)
          ·
            refine ⟨1360780162346531217442009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1814373549795374956589345 1360780162346531217442009)
            ·
              refine ⟨1020585121759898413081507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360780162346531217442009 1020585121759898413081507)
              ·
                refine ⟨1530877682639847619622261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020585121759898413081507 1530877682639847619622261)
                ·
                  refine ⟨143519782747485714339587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1530877682639847619622261 143519782747485714339587)
                  ·
                    rfl

theorem cell22_1257767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 5].length) (baseStart_1257767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257767 prefixEnd_1257767 := by exact prefixLift 1257767
  have htrace : WordTrace (prefixWord ++ tailWord_1257767) baseStart_1257767 baseEnd_1257767 := by
    simpa [prefixWord, tailWord_1257767, baseEnd_1257767] using wordTrace_append hprefix tailTrace_1257767
  have hstable : (prefixWord ++ tailWord_1257767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257767).length < 2 ^ (prefixWord ++ tailWord_1257767).sum := by decide
  have hdescent : baseEnd_1257767 < baseStart_1257767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257772 : List Nat := [2, 2, 1, 1, 1, 3, 3, 9]
def baseStart_1257772 : Nat := 118140960795 + 1257772 * 2 ^ 59
def prefixEnd_1257772 : Nat := 4983230072969 + 3 ^ 40 * 1257772 * 2
def baseEnd_1257772 : Nat := 47840117760515421849305

theorem tailTrace_1257772 : CollatzResearch.WordTrace tailWord_1257772 prefixEnd_1257772 47840117760515421849305 := by
  unfold tailWord_1257772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22937356799657164600391785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30583142399542886133855713 22937356799657164600391785)
  ·
    refine ⟨17203017599742873450293839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22937356799657164600391785 17203017599742873450293839)
    ·
      refine ⟨25804526399614310175440759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17203017599742873450293839 25804526399614310175440759)
      ·
        refine ⟨38706789599421465263161139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25804526399614310175440759 38706789599421465263161139)
        ·
          refine ⟨58060184399132197894741709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38706789599421465263161139 58060184399132197894741709)
          ·
            refine ⟨21772569149674574210528141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58060184399132197894741709 21772569149674574210528141)
            ·
              refine ⟨8164713431127965328948053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21772569149674574210528141 8164713431127965328948053)
              ·
                refine ⟨47840117760515421849305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8164713431127965328948053 47840117760515421849305)
                ·
                  rfl

theorem cell22_1257772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 9].length) (baseStart_1257772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257772 prefixEnd_1257772 := by exact prefixLift 1257772
  have htrace : WordTrace (prefixWord ++ tailWord_1257772) baseStart_1257772 baseEnd_1257772 := by
    simpa [prefixWord, tailWord_1257772, baseEnd_1257772] using wordTrace_append hprefix tailTrace_1257772
  have hstable : (prefixWord ++ tailWord_1257772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257772).length < 2 ^ (prefixWord ++ tailWord_1257772).sum := by decide
  have hdescent : baseEnd_1257772 < baseStart_1257772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257879 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 6]
def baseStart_1257879 : Nat := 118140960795 + 1257879 * 2 ^ 59
def prefixEnd_1257879 : Nat := 4983230072969 + 3 ^ 40 * 1257879 * 2
def baseEnd_1257879 : Nat := 143532562710442061406139

theorem tailTrace_1257879 : CollatzResearch.WordTrace tailWord_1257879 prefixEnd_1257879 143532562710442061406139 := by
  unfold tailWord_1257879
  simp only [CollatzResearch.WordTrace]
  refine ⟨45878616209926686474928691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30585744139951124316619127 45878616209926686474928691)
  ·
    refine ⟨68817924314890029712393037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45878616209926686474928691 68817924314890029712393037)
    ·
      refine ⟨25806721618083761142147389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68817924314890029712393037 25806721618083761142147389)
      ·
        refine ⟨9677520606781410428305271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25806721618083761142147389 9677520606781410428305271)
        ·
          refine ⟨14516280910172115642457907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677520606781410428305271 14516280910172115642457907)
          ·
            refine ⟨21774421365258173463686861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14516280910172115642457907 21774421365258173463686861)
            ·
              refine ⟨8165408011971815048882573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21774421365258173463686861 8165408011971815048882573)
              ·
                refine ⟨3062028004489430643330965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8165408011971815048882573 3062028004489430643330965)
                ·
                  refine ⟨143532562710442061406139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3062028004489430643330965 143532562710442061406139)
                  ·
                    rfl

theorem cell22_1257879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 6].length) (baseStart_1257879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257879 prefixEnd_1257879 := by exact prefixLift 1257879
  have htrace : WordTrace (prefixWord ++ tailWord_1257879) baseStart_1257879 baseEnd_1257879 := by
    simpa [prefixWord, tailWord_1257879, baseEnd_1257879] using wordTrace_append hprefix tailTrace_1257879
  have hstable : (prefixWord ++ tailWord_1257879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257879).length < 2 ^ (prefixWord ++ tailWord_1257879).sum := by decide
  have hdescent : baseEnd_1257879 < baseStart_1257879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257911 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 4, 3]
def baseStart_1257911 : Nat := 118140960795 + 1257911 * 2 ^ 59
def prefixEnd_1257911 : Nat := 4983230072969 + 3 ^ 40 * 1257911 * 2
def baseEnd_1257911 : Nat := 430608642385288767418319

theorem tailTrace_1257911 : CollatzResearch.WordTrace tailWord_1257911 prefixEnd_1257911 430608642385288767418319 := by
  unfold tailWord_1257911
  simp only [CollatzResearch.WordTrace]
  refine ⟨45879783345810755940093587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30586522230540503960062391 45879783345810755940093587)
  ·
    refine ⟨68819675018716133910140381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45879783345810755940093587 68819675018716133910140381)
    ·
      refine ⟨25807378132018550216302643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68819675018716133910140381 25807378132018550216302643)
      ·
        refine ⟨38711067198027825324453965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25807378132018550216302643 38711067198027825324453965)
        ·
          refine ⟨14516650199260434496670237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38711067198027825324453965 14516650199260434496670237)
          ·
            refine ⟨5443743824722662936251339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14516650199260434496670237 5443743824722662936251339)
            ·
              refine ⟨8165615737083994404377009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443743824722662936251339 8165615737083994404377009)
              ·
                refine ⟨6124211802812995803282757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8165615737083994404377009 6124211802812995803282757)
                ·
                  refine ⟨1148289713027436713115517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6124211802812995803282757 1148289713027436713115517)
                  ·
                    refine ⟨430608642385288767418319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148289713027436713115517 430608642385288767418319)
                    ·
                      rfl

theorem cell22_1257911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_1257911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257911 prefixEnd_1257911 := by exact prefixLift 1257911
  have htrace : WordTrace (prefixWord ++ tailWord_1257911) baseStart_1257911 baseEnd_1257911 := by
    simpa [prefixWord, tailWord_1257911, baseEnd_1257911] using wordTrace_append hprefix tailTrace_1257911
  have hstable : (prefixWord ++ tailWord_1257911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257911).length < 2 ^ (prefixWord ++ tailWord_1257911).sum := by decide
  have hdescent : baseEnd_1257911 < baseStart_1257911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257913 : List Nat := [1, 2, 1, 4, 3, 1, 3, 3, 4]
def baseStart_1257913 : Nat := 118140960795 + 1257913 * 2 ^ 59
def prefixEnd_1257913 : Nat := 4983230072969 + 3 ^ 40 * 1257913 * 2
def baseEnd_1257913 : Nat := 143536442342053809622771

theorem tailTrace_1257913 : CollatzResearch.WordTrace tailWord_1257913 prefixEnd_1257913 143536442342053809622771 := by
  unfold tailWord_1257913
  simp only [CollatzResearch.WordTrace]
  refine ⟨45879856291803510281666393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30586570861202340187777595 45879856291803510281666393)
  ·
    refine ⟨34409892218852632711249795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45879856291803510281666393 34409892218852632711249795)
    ·
      refine ⟨51614838328278949066874693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34409892218852632711249795 51614838328278949066874693)
      ·
        refine ⟨9677782186552302950039005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51614838328278949066874693 9677782186552302950039005)
        ·
          refine ⟨3629168319957113606264627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9677782186552302950039005 3629168319957113606264627)
          ·
            refine ⟨5443752479935670409396941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629168319957113606264627 5443752479935670409396941)
            ·
              refine ⟨2041407179975876403523853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5443752479935670409396941 2041407179975876403523853)
              ·
                refine ⟨765527692490953651321445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2041407179975876403523853 765527692490953651321445)
                ·
                  refine ⟨143536442342053809622771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765527692490953651321445 143536442342053809622771)
                  ·
                    rfl

theorem cell22_1257913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_1257913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257913 prefixEnd_1257913 := by exact prefixLift 1257913
  have htrace : WordTrace (prefixWord ++ tailWord_1257913) baseStart_1257913 baseEnd_1257913 := by
    simpa [prefixWord, tailWord_1257913, baseEnd_1257913] using wordTrace_append hprefix tailTrace_1257913
  have hstable : (prefixWord ++ tailWord_1257913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257913).length < 2 ^ (prefixWord ++ tailWord_1257913).sum := by decide
  have hdescent : baseEnd_1257913 < baseStart_1257913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257941 : List Nat := [1, 3, 2, 3, 1, 3, 2, 7]
def baseStart_1257941 : Nat := 118140960795 + 1257941 * 2 ^ 59
def prefixEnd_1257941 : Nat := 4983230072969 + 3 ^ 40 * 1257941 * 2
def baseEnd_1257941 : Nat := 47846545777597632129803

theorem tailTrace_1257941 : CollatzResearch.WordTrace tailWord_1257941 prefixEnd_1257941 47846545777597632129803 := by
  unfold tailWord_1257941
  simp only [CollatzResearch.WordTrace]
  refine ⟨45880877535702071063685677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30587251690468047375790451 45880877535702071063685677)
  ·
    refine ⟨17205329075888276648882129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45880877535702071063685677 17205329075888276648882129)
    ·
      refine ⟨12903996806916207486661597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17205329075888276648882129 12903996806916207486661597)
      ·
        refine ⟨4838998802593577807498099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12903996806916207486661597 4838998802593577807498099)
        ·
          refine ⟨7258498203890366711247149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838998802593577807498099 7258498203890366711247149)
          ·
            refine ⟨2721936826458887516717681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7258498203890366711247149 2721936826458887516717681)
            ·
              refine ⟨2041452619844165637538261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721936826458887516717681 2041452619844165637538261)
              ·
                refine ⟨47846545777597632129803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2041452619844165637538261 47846545777597632129803)
                ·
                  rfl

theorem cell22_1257941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 7].length) (baseStart_1257941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257941 prefixEnd_1257941 := by exact prefixLift 1257941
  have htrace : WordTrace (prefixWord ++ tailWord_1257941) baseStart_1257941 baseEnd_1257941 := by
    simpa [prefixWord, tailWord_1257941, baseEnd_1257941] using wordTrace_append hprefix tailTrace_1257941
  have hstable : (prefixWord ++ tailWord_1257941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257941).length < 2 ^ (prefixWord ++ tailWord_1257941).sum := by decide
  have hdescent : baseEnd_1257941 < baseStart_1257941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257984 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_1257984 : Nat := 118140960795 + 1257984 * 2 ^ 59
def prefixEnd_1257984 : Nat := 4983230072969 + 3 ^ 40 * 1257984 * 2
def baseEnd_1257984 : Nat := 430633631777140910343095

theorem tailTrace_1257984 : CollatzResearch.WordTrace tailWord_1257984 prefixEnd_1257984 430633631777140910343095 := by
  unfold tailWord_1257984
  simp only [CollatzResearch.WordTrace]
  refine ⟨22941222937273144703750503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30588297249697526271667337 22941222937273144703750503)
  ·
    refine ⟨34411834405909717055625755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22941222937273144703750503 34411834405909717055625755)
    ·
      refine ⟨51617751608864575583438633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34411834405909717055625755 51617751608864575583438633)
      ·
        refine ⟨38713313706648431687578975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51617751608864575583438633 38713313706648431687578975)
        ·
          refine ⟨58069970559972647531368463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38713313706648431687578975 58069970559972647531368463)
          ·
            refine ⟨87104955839958971297052695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58069970559972647531368463 87104955839958971297052695)
            ·
              refine ⟨130657433759938456945579043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87104955839958971297052695 130657433759938456945579043)
              ·
                refine ⟨195986150639907685418368565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130657433759938456945579043 195986150639907685418368565)
                ·
                  refine ⟨18373701622491345507972053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195986150639907685418368565 18373701622491345507972053)
                  ·
                    refine ⟨430633631777140910343095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18373701622491345507972053 430633631777140910343095)
                    ·
                      rfl

theorem cell22_1257984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_1257984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257984 prefixEnd_1257984 := by exact prefixLift 1257984
  have htrace : WordTrace (prefixWord ++ tailWord_1257984) baseStart_1257984 baseEnd_1257984 := by
    simpa [prefixWord, tailWord_1257984, baseEnd_1257984] using wordTrace_append hprefix tailTrace_1257984
  have hstable : (prefixWord ++ tailWord_1257984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257984).length < 2 ^ (prefixWord ++ tailWord_1257984).sum := by decide
  have hdescent : baseEnd_1257984 < baseStart_1257984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257999 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 8]
def baseStart_1257999 : Nat := 118140960795 + 1257999 * 2 ^ 59
def prefixEnd_1257999 : Nat := 4983230072969 + 3 ^ 40 * 1257999 * 2
def baseEnd_1257999 : Nat := 430638766583685871218049

theorem tailTrace_1257999 : CollatzResearch.WordTrace tailWord_1257999 prefixEnd_1257999 430638766583685871218049 := by
  unfold tailWord_1257999
  simp only [CollatzResearch.WordTrace]
  refine ⟨45882992969491946969297051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30588661979661297979531367 45882992969491946969297051)
  ·
    refine ⟨68824489454237920453945577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45882992969491946969297051 68824489454237920453945577)
    ·
      refine ⟨51618367090678440340459183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68824489454237920453945577 51618367090678440340459183)
      ·
        refine ⟨77427550636017660510688775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51618367090678440340459183 77427550636017660510688775)
        ·
          refine ⟨116141325954026490766033163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77427550636017660510688775 116141325954026490766033163)
          ·
            refine ⟨174211988931039736149049745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116141325954026490766033163 174211988931039736149049745)
            ·
              refine ⟨130658991698279802111787309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174211988931039736149049745 130658991698279802111787309)
              ·
                refine ⟨48997121886854925791920241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130658991698279802111787309 48997121886854925791920241)
                ·
                  refine ⟨36747841415141194343940181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48997121886854925791920241 36747841415141194343940181)
                  ·
                    refine ⟨430638766583685871218049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36747841415141194343940181 430638766583685871218049)
                    ·
                      rfl

theorem cell22_1257999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_1257999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1257999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1257999 prefixEnd_1257999 := by exact prefixLift 1257999
  have htrace : WordTrace (prefixWord ++ tailWord_1257999) baseStart_1257999 baseEnd_1257999 := by
    simpa [prefixWord, tailWord_1257999, baseEnd_1257999] using wordTrace_append hprefix tailTrace_1257999
  have hstable : (prefixWord ++ tailWord_1257999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257999).length < 2 ^ (prefixWord ++ tailWord_1257999).sum := by decide
  have hdescent : baseEnd_1257999 < baseStart_1257999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258048 : List Nat := [2, 1, 1, 2, 2, 2, 4, 4, 4]
def baseStart_1258048 : Nat := 118140960795 + 1258048 * 2 ^ 59
def prefixEnd_1258048 : Nat := 4983230072969 + 3 ^ 40 * 1258048 * 2
def baseEnd_1258048 : Nat := 143551846761688692247633

theorem tailTrace_1258048 : CollatzResearch.WordTrace tailWord_1258048 prefixEnd_1258048 143551846761688692247633 := by
  unfold tailWord_1258048
  simp only [CollatzResearch.WordTrace]
  refine ⟨22942390073157214168915399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30589853430876285558553865 22942390073157214168915399)
  ·
    refine ⟨34413585109735821253373099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22942390073157214168915399 34413585109735821253373099)
    ·
      refine ⟨51620377664603731880059649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34413585109735821253373099 51620377664603731880059649)
      ·
        refine ⟨38715283248452798910044737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51620377664603731880059649 38715283248452798910044737)
        ·
          refine ⟨29036462436339599182533553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38715283248452798910044737 29036462436339599182533553)
          ·
            refine ⟨21777346827254699386900165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29036462436339599182533553 21777346827254699386900165)
            ·
              refine ⟨4083252530110256135043781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21777346827254699386900165 4083252530110256135043781)
              ·
                refine ⟨765609849395673025320709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4083252530110256135043781 765609849395673025320709)
                ·
                  refine ⟨143551846761688692247633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765609849395673025320709 143551846761688692247633)
                  ·
                    rfl

theorem cell22_1258048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_1258048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258048 prefixEnd_1258048 := by exact prefixLift 1258048
  have htrace : WordTrace (prefixWord ++ tailWord_1258048) baseStart_1258048 baseEnd_1258048 := by
    simpa [prefixWord, tailWord_1258048, baseEnd_1258048] using wordTrace_append hprefix tailTrace_1258048
  have hstable : (prefixWord ++ tailWord_1258048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258048).length < 2 ^ (prefixWord ++ tailWord_1258048).sum := by decide
  have hdescent : baseEnd_1258048 < baseStart_1258048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258063 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 2, 3]
def baseStart_1258063 : Nat := 118140960795 + 1258063 * 2 ^ 59
def prefixEnd_1258063 : Nat := 4983230072969 + 3 ^ 40 * 1258063 * 2
def baseEnd_1258063 : Nat := 430660675091611037617853

theorem tailTrace_1258063 : CollatzResearch.WordTrace tailWord_1258063 prefixEnd_1258063 430660675091611037617853 := by
  unfold tailWord_1258063
  simp only [CollatzResearch.WordTrace]
  refine ⟨45885327241260085899626843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30590218160840057266417895 45885327241260085899626843)
  ·
    refine ⟨68827990861890128849440265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45885327241260085899626843 68827990861890128849440265)
    ·
      refine ⟨51620993146417596637080199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68827990861890128849440265 51620993146417596637080199)
      ·
        refine ⟨77431489719626394955620299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51620993146417596637080199 77431489719626394955620299)
        ·
          refine ⟨116147234579439592433430449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77431489719626394955620299 116147234579439592433430449)
          ·
            refine ⟨87110425934579694325072837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116147234579439592433430449 87110425934579694325072837)
            ·
              refine ⟨16333204862733692685951157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87110425934579694325072837 16333204862733692685951157)
              ·
                refine ⟨1531237955881283689307921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16333204862733692685951157 1531237955881283689307921)
                ·
                  refine ⟨1148428466910962766980941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531237955881283689307921 1148428466910962766980941)
                  ·
                    refine ⟨430660675091611037617853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148428466910962766980941 430660675091611037617853)
                    ·
                      rfl

theorem cell22_1258063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_1258063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258063 prefixEnd_1258063 := by exact prefixLift 1258063
  have htrace : WordTrace (prefixWord ++ tailWord_1258063) baseStart_1258063 baseEnd_1258063 := by
    simpa [prefixWord, tailWord_1258063, baseEnd_1258063] using wordTrace_append hprefix tailTrace_1258063
  have hstable : (prefixWord ++ tailWord_1258063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258063).length < 2 ^ (prefixWord ++ tailWord_1258063).sum := by decide
  have hdescent : baseEnd_1258063 < baseStart_1258063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258093 : List Nat := [1, 5, 1, 1, 3, 3, 8]
def baseStart_1258093 : Nat := 118140960795 + 1258093 * 2 ^ 59
def prefixEnd_1258093 : Nat := 4983230072969 + 3 ^ 40 * 1258093 * 2
def baseEnd_1258093 : Nat := 15950775729803739235843

theorem tailTrace_1258093 : CollatzResearch.WordTrace tailWord_1258093 prefixEnd_1258093 15950775729803739235843 := by
  unfold tailWord_1258093
  simp only [CollatzResearch.WordTrace]
  refine ⟨45886421431151401023218933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30590947620767600682145955 45886421431151401023218933)
  ·
    refine ⟨4301852009170443845926775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45886421431151401023218933 4301852009170443845926775)
    ·
      refine ⟨6452778013755665768890163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301852009170443845926775 6452778013755665768890163)
      ·
        refine ⟨9679167020633498653335245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6452778013755665768890163 9679167020633498653335245)
        ·
          refine ⟨3629687632737561995000717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9679167020633498653335245 3629687632737561995000717)
          ·
            refine ⟨1361132862276585748125269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3629687632737561995000717 1361132862276585748125269)
            ·
              refine ⟨15950775729803739235843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1361132862276585748125269 15950775729803739235843)
              ·
                rfl

theorem cell22_1258093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 8].length) (baseStart_1258093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258093 prefixEnd_1258093 := by exact prefixLift 1258093
  have htrace : WordTrace (prefixWord ++ tailWord_1258093) baseStart_1258093 baseEnd_1258093 := by
    simpa [prefixWord, tailWord_1258093, baseEnd_1258093] using wordTrace_append hprefix tailTrace_1258093
  have hstable : (prefixWord ++ tailWord_1258093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258093).length < 2 ^ (prefixWord ++ tailWord_1258093).sum := by decide
  have hdescent : baseEnd_1258093 < baseStart_1258093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258159 : List Nat := [1, 1, 2, 1, 2, 7, 2, 2, 1, 3]
def baseStart_1258159 : Nat := 118140960795 + 1258159 * 2 ^ 59
def prefixEnd_1258159 : Nat := 4983230072969 + 3 ^ 40 * 1258159 * 2
def baseEnd_1258159 : Nat := 430693537853498787217559

theorem tailTrace_1258159 : CollatzResearch.WordTrace tailWord_1258159 prefixEnd_1258159 430693537853498787217559 := by
  unfold tailWord_1258159
  simp only [CollatzResearch.WordTrace]
  refine ⟨45888828648912294295121531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30592552432608196196747687 45888828648912294295121531)
  ·
    refine ⟨68833242973368441442682297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45888828648912294295121531 68833242973368441442682297)
    ·
      refine ⟨51624932230026331082011723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68833242973368441442682297 51624932230026331082011723)
      ·
        refine ⟨77437398345039496623017585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51624932230026331082011723 77437398345039496623017585)
        ·
          refine ⟨58078048758779622467263189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77437398345039496623017585 58078048758779622467263189)
          ·
            refine ⟨1361204267783897401576481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 58078048758779622467263189 1361204267783897401576481)
            ·
              refine ⟨1020903200837923051182361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361204267783897401576481 1020903200837923051182361)
              ·
                refine ⟨765677400628442288386771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020903200837923051182361 765677400628442288386771)
                ·
                  refine ⟨1148516100942663432580157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765677400628442288386771 1148516100942663432580157)
                  ·
                    refine ⟨430693537853498787217559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148516100942663432580157 430693537853498787217559)
                    ·
                      rfl

theorem cell22_1258159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 3].length) (baseStart_1258159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258159 prefixEnd_1258159 := by exact prefixLift 1258159
  have htrace : WordTrace (prefixWord ++ tailWord_1258159) baseStart_1258159 baseEnd_1258159 := by
    simpa [prefixWord, tailWord_1258159, baseEnd_1258159] using wordTrace_append hprefix tailTrace_1258159
  have hstable : (prefixWord ++ tailWord_1258159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258159).length < 2 ^ (prefixWord ++ tailWord_1258159).sum := by decide
  have hdescent : baseEnd_1258159 < baseStart_1258159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258200 : List Nat := [2, 1, 2, 2, 3, 2, 1, 5, 4]
def baseStart_1258200 : Nat := 118140960795 + 1258200 * 2 ^ 59
def prefixEnd_1258200 : Nat := 4983230072969 + 3 ^ 40 * 1258200 * 2
def baseEnd_1258200 : Nat := 143569190997129448980811

theorem tailTrace_1258200 : CollatzResearch.WordTrace tailWord_1258200 prefixEnd_1258200 143569190997129448980811 := by
  unfold tailWord_1258200
  simp only [CollatzResearch.WordTrace]
  refine ⟨22945162020881879148682027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30593549361175838864909369 22945162020881879148682027)
  ·
    refine ⟨34417743031322818723023041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22945162020881879148682027 34417743031322818723023041)
    ·
      refine ⟨25813307273492114042267281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34417743031322818723023041 25813307273492114042267281)
      ·
        refine ⟨19359980455119085531700461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25813307273492114042267281 19359980455119085531700461)
        ·
          refine ⟨7259992670669657074387673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19359980455119085531700461 7259992670669657074387673)
          ·
            refine ⟨5444994503002242805790755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7259992670669657074387673 5444994503002242805790755)
            ·
              refine ⟨8167491754503364208686133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444994503002242805790755 8167491754503364208686133)
              ·
                refine ⟨765702351984690394564325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8167491754503364208686133 765702351984690394564325)
                ·
                  refine ⟨143569190997129448980811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765702351984690394564325 143569190997129448980811)
                  ·
                    rfl

theorem cell22_1258200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_1258200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258200 prefixEnd_1258200 := by exact prefixLift 1258200
  have htrace : WordTrace (prefixWord ++ tailWord_1258200) baseStart_1258200 baseEnd_1258200 := by
    simpa [prefixWord, tailWord_1258200, baseEnd_1258200] using wordTrace_append hprefix tailTrace_1258200
  have hstable : (prefixWord ++ tailWord_1258200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258200).length < 2 ^ (prefixWord ++ tailWord_1258200).sum := by decide
  have hdescent : baseEnd_1258200 < baseStart_1258200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258232 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 2, 3]
def baseStart_1258232 : Nat := 118140960795 + 1258232 * 2 ^ 59
def prefixEnd_1258232 : Nat := 4983230072969 + 3 ^ 40 * 1258232 * 2
def baseEnd_1258232 : Nat := 430718527245350930142335

theorem tailTrace_1258232 : CollatzResearch.WordTrace tailWord_1258232 prefixEnd_1258232 430718527245350930142335 := by
  unfold tailWord_1258232
  simp only [CollatzResearch.WordTrace]
  refine ⟨22945745588823913881264475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30594327451765218508352633 22945745588823913881264475)
  ·
    refine ⟨34418618383235870821896713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22945745588823913881264475 34418618383235870821896713)
    ·
      refine ⟨25813963787426903116422535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34418618383235870821896713 25813963787426903116422535)
      ·
        refine ⟨38720945681140354674633803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25813963787426903116422535 38720945681140354674633803)
        ·
          refine ⟨58081418521710532011950705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38720945681140354674633803 58081418521710532011950705)
          ·
            refine ⟨43561063891282899008963029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58081418521710532011950705 43561063891282899008963029)
            ·
              refine ⟨1020962434951942945522571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43561063891282899008963029 1020962434951942945522571)
              ·
                refine ⟨1531443652427914418283857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020962434951942945522571 1531443652427914418283857)
                ·
                  refine ⟨1148582739320935813712893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531443652427914418283857 1148582739320935813712893)
                  ·
                    refine ⟨430718527245350930142335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148582739320935813712893 430718527245350930142335)
                    ·
                      rfl

theorem cell22_1258232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_1258232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258232 prefixEnd_1258232 := by exact prefixLift 1258232
  have htrace : WordTrace (prefixWord ++ tailWord_1258232) baseStart_1258232 baseEnd_1258232 := by
    simpa [prefixWord, tailWord_1258232, baseEnd_1258232] using wordTrace_append hprefix tailTrace_1258232
  have hstable : (prefixWord ++ tailWord_1258232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258232).length < 2 ^ (prefixWord ++ tailWord_1258232).sum := by decide
  have hdescent : baseEnd_1258232 < baseStart_1258232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258273 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 7]
def baseStart_1258273 : Nat := 118140960795 + 1258273 * 2 ^ 59
def prefixEnd_1258273 : Nat := 4983230072969 + 3 ^ 40 * 1258273 * 2
def baseEnd_1258273 : Nat := 143577520794413496622403

theorem tailTrace_1258273 : CollatzResearch.WordTrace tailWord_1258273 prefixEnd_1258273 143577520794413496622403 := by
  unfold tailWord_1258273
  simp only [CollatzResearch.WordTrace]
  refine ⟨45892986570499291764771473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30595324380332861176514315 45892986570499291764771473)
  ·
    refine ⟨34419739927874468823578605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45892986570499291764771473 34419739927874468823578605)
    ·
      refine ⟨12907402472952925808841977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34419739927874468823578605 12907402472952925808841977)
      ·
        refine ⟨9680551854714694356631483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12907402472952925808841977 9680551854714694356631483)
        ·
          refine ⟨14520827782072041534947225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9680551854714694356631483 14520827782072041534947225)
          ·
            refine ⟨10890620836554031151210419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14520827782072041534947225 10890620836554031151210419)
            ·
              refine ⟨16335931254831046726815629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10890620836554031151210419 16335931254831046726815629)
              ·
                refine ⟨6125974220561642522555861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16335931254831046726815629 6125974220561642522555861)
                ·
                  refine ⟨143577520794413496622403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6125974220561642522555861 143577520794413496622403)
                  ·
                    rfl

theorem cell22_1258273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_1258273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258273 prefixEnd_1258273 := by exact prefixLift 1258273
  have htrace : WordTrace (prefixWord ++ tailWord_1258273) baseStart_1258273 baseEnd_1258273 := by
    simpa [prefixWord, tailWord_1258273, baseEnd_1258273] using wordTrace_append hprefix tailTrace_1258273
  have hstable : (prefixWord ++ tailWord_1258273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258273).length < 2 ^ (prefixWord ++ tailWord_1258273).sum := by decide
  have hdescent : baseEnd_1258273 < baseStart_1258273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258288 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_1258288 : Nat := 118140960795 + 1258288 * 2 ^ 59
def prefixEnd_1258288 : Nat := 4983230072969 + 3 ^ 40 * 1258288 * 2
def baseEnd_1258288 : Nat := 430737697189785450742163

theorem tailTrace_1258288 : CollatzResearch.WordTrace tailWord_1258288 prefixEnd_1258288 430737697189785450742163 := by
  unfold tailWord_1258288
  simp only [CollatzResearch.WordTrace]
  refine ⟨22946766832722474663283759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30595689110296632884378345 22946766832722474663283759)
  ·
    refine ⟨34420150249083711994925639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22946766832722474663283759 34420150249083711994925639)
    ·
      refine ⟨51630225373625567992388459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34420150249083711994925639 51630225373625567992388459)
      ·
        refine ⟨77445338060438351988582689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51630225373625567992388459 77445338060438351988582689)
        ·
          refine ⟨58084003545328763991437017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77445338060438351988582689 58084003545328763991437017)
          ·
            refine ⟨43563002658996572993577763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58084003545328763991437017 43563002658996572993577763)
            ·
              refine ⟨65344503988494859490366645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43563002658996572993577763 65344503988494859490366645)
              ·
                refine ⟨6126047248921393077221873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65344503988494859490366645 6126047248921393077221873)
                ·
                  refine ⟨4594535436691044807916405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6126047248921393077221873 4594535436691044807916405)
                  ·
                    refine ⟨430737697189785450742163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4594535436691044807916405 430737697189785450742163)
                    ·
                      rfl

theorem cell22_1258288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_1258288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258288 prefixEnd_1258288 := by exact prefixLift 1258288
  have htrace : WordTrace (prefixWord ++ tailWord_1258288) baseStart_1258288 baseEnd_1258288 := by
    simpa [prefixWord, tailWord_1258288, baseEnd_1258288] using wordTrace_append hprefix tailTrace_1258288
  have hstable : (prefixWord ++ tailWord_1258288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258288).length < 2 ^ (prefixWord ++ tailWord_1258288).sum := by decide
  have hdescent : baseEnd_1258288 < baseStart_1258288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258290 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_1258290 : Nat := 118140960795 + 1258290 * 2 ^ 59
def prefixEnd_1258290 : Nat := 4983230072969 + 3 ^ 40 * 1258290 * 2
def baseEnd_1258290 : Nat := 143579460610219370730719

theorem tailTrace_1258290 : CollatzResearch.WordTrace tailWord_1258290 prefixEnd_1258290 143579460610219370730719 := by
  unfold tailWord_1258290
  simp only [CollatzResearch.WordTrace]
  refine ⟨11473401652859425917035081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30595737740958469112093549 11473401652859425917035081)
  ·
    refine ⟨8605051239644569437776311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11473401652859425917035081 8605051239644569437776311)
    ·
      refine ⟨12907576859466854156664467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8605051239644569437776311 12907576859466854156664467)
      ·
        refine ⟨19361365289200281234996701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12907576859466854156664467 19361365289200281234996701)
        ·
          refine ⟨7260511983450105463123763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19361365289200281234996701 7260511983450105463123763)
          ·
            refine ⟨10890767975175158194685645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7260511983450105463123763 10890767975175158194685645)
            ·
              refine ⟨4084037990690684323007117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10890767975175158194685645 4084037990690684323007117)
              ·
                refine ⟨1531514246509006621127669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4084037990690684323007117 1531514246509006621127669)
                ·
                  refine ⟨143579460610219370730719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1531514246509006621127669 143579460610219370730719)
                  ·
                    rfl

theorem cell22_1258290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_1258290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258290 prefixEnd_1258290 := by exact prefixLift 1258290
  have htrace : WordTrace (prefixWord ++ tailWord_1258290) baseStart_1258290 baseEnd_1258290 := by
    simpa [prefixWord, tailWord_1258290, baseEnd_1258290] using wordTrace_append hprefix tailTrace_1258290
  have hstable : (prefixWord ++ tailWord_1258290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258290).length < 2 ^ (prefixWord ++ tailWord_1258290).sum := by decide
  have hdescent : baseEnd_1258290 < baseStart_1258290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258320 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_1258320 : Nat := 118140960795 + 1258320 * 2 ^ 59
def prefixEnd_1258320 : Nat := 4983230072969 + 3 ^ 40 * 1258320 * 2
def baseEnd_1258320 : Nat := 430748651443748033942065

theorem tailTrace_1258320 : CollatzResearch.WordTrace tailWord_1258320 prefixEnd_1258320 430748651443748033942065 := by
  unfold tailWord_1258320
  simp only [CollatzResearch.WordTrace]
  refine ⟨22947350400664509395866207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30596467200886012527821609 22947350400664509395866207)
  ·
    refine ⟨34421025600996764093799311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22947350400664509395866207 34421025600996764093799311)
    ·
      refine ⟨51631538401495146140698967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34421025600996764093799311 51631538401495146140698967)
      ·
        refine ⟨77447307602242719211048451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51631538401495146140698967 77447307602242719211048451)
        ·
          refine ⟨116170961403364078816572677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77447307602242719211048451 116170961403364078816572677)
          ·
            refine ⟨21782055263130764778107377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116170961403364078816572677 21782055263130764778107377)
            ·
              refine ⟨16336541447348073583580533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21782055263130764778107377 16336541447348073583580533)
              ·
                refine ⟨1531550760688881898460675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16336541447348073583580533 1531550760688881898460675)
                ·
                  refine ⟨2297326141033322847691013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531550760688881898460675 2297326141033322847691013)
                  ·
                    refine ⟨430748651443748033942065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2297326141033322847691013 430748651443748033942065)
                    ·
                      rfl

theorem cell22_1258320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_1258320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258320 prefixEnd_1258320 := by exact prefixLift 1258320
  have htrace : WordTrace (prefixWord ++ tailWord_1258320) baseStart_1258320 baseEnd_1258320 := by
    simpa [prefixWord, tailWord_1258320, baseEnd_1258320] using wordTrace_append hprefix tailTrace_1258320
  have hstable : (prefixWord ++ tailWord_1258320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258320).length < 2 ^ (prefixWord ++ tailWord_1258320).sum := by decide
  have hdescent : baseEnd_1258320 < baseStart_1258320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258363 : List Nat := [1, 1, 1, 1, 1, 5, 2, 10]
def baseStart_1258363 : Nat := 118140960795 + 1258363 * 2 ^ 59
def prefixEnd_1258363 : Nat := 4983230072969 + 3 ^ 40 * 1258363 * 2
def baseEnd_1258363 : Nat := 47862596802501139457437

theorem tailTrace_1258363 : CollatzResearch.WordTrace tailWord_1258363 prefixEnd_1258363 47862596802501139457437 := by
  unfold tailWord_1258363
  simp only [CollatzResearch.WordTrace]
  refine ⟨45896269140173237135547743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30597512760115491423698495 45896269140173237135547743)
  ·
    refine ⟨68844403710259855703321615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45896269140173237135547743 68844403710259855703321615)
    ·
      refine ⟨103266605565389783554982423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68844403710259855703321615 103266605565389783554982423)
      ·
        refine ⟨154899908348084675332473635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103266605565389783554982423 154899908348084675332473635)
        ·
          refine ⟨232349862522127012998710453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154899908348084675332473635 232349862522127012998710453)
          ·
            refine ⟨21782799611449407468629105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232349862522127012998710453 21782799611449407468629105)
            ·
              refine ⟨16337099708587055601471829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21782799611449407468629105 16337099708587055601471829)
              ·
                refine ⟨47862596802501139457437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16337099708587055601471829 47862596802501139457437)
                ·
                  rfl

theorem cell22_1258363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 10].length) (baseStart_1258363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258363 prefixEnd_1258363 := by exact prefixLift 1258363
  have htrace : WordTrace (prefixWord ++ tailWord_1258363) baseStart_1258363 baseEnd_1258363 := by
    simpa [prefixWord, tailWord_1258363, baseEnd_1258363] using wordTrace_append hprefix tailTrace_1258363
  have hstable : (prefixWord ++ tailWord_1258363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258363).length < 2 ^ (prefixWord ++ tailWord_1258363).sum := by decide
  have hdescent : baseEnd_1258363 < baseStart_1258363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258401 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 2, 3]
def baseStart_1258401 : Nat := 118140960795 + 1258401 * 2 ^ 59
def prefixEnd_1258401 : Nat := 4983230072969 + 3 ^ 40 * 1258401 * 2
def baseEnd_1258401 : Nat := 430776379399090822666817

theorem tailTrace_1258401 : CollatzResearch.WordTrace tailWord_1258401 prefixEnd_1258401 430776379399090822666817 := by
  unfold tailWord_1258401
  simp only [CollatzResearch.WordTrace]
  refine ⟨45897655114035569625431057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30598436742690379750287371 45897655114035569625431057)
  ·
    refine ⟨34423241335526677219073293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45897655114035569625431057 34423241335526677219073293)
    ·
      refine ⟨12908715500822503957152485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34423241335526677219073293 12908715500822503957152485)
      ·
        refine ⟨2420384156404219491966091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12908715500822503957152485 2420384156404219491966091)
        ·
          refine ⟨3630576234606329237949137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420384156404219491966091 3630576234606329237949137)
          ·
            refine ⟨2722932175954746928461853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3630576234606329237949137 2722932175954746928461853)
            ·
              refine ⟨1021099565983030098173195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2722932175954746928461853 1021099565983030098173195)
              ·
                refine ⟨1531649348974545147259793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021099565983030098173195 1531649348974545147259793)
                ·
                  refine ⟨1148737011730908860444845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531649348974545147259793 1148737011730908860444845)
                  ·
                    refine ⟨430776379399090822666817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148737011730908860444845 430776379399090822666817)
                    ·
                      rfl

theorem cell22_1258401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_1258401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258401 prefixEnd_1258401 := by exact prefixLift 1258401
  have htrace : WordTrace (prefixWord ++ tailWord_1258401) baseStart_1258401 baseEnd_1258401 := by
    simpa [prefixWord, tailWord_1258401, baseEnd_1258401] using wordTrace_append hprefix tailTrace_1258401
  have hstable : (prefixWord ++ tailWord_1258401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258401).length < 2 ^ (prefixWord ++ tailWord_1258401).sum := by decide
  have hdescent : baseEnd_1258401 < baseStart_1258401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258425 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 7]
def baseStart_1258425 : Nat := 118140960795 + 1258425 * 2 ^ 59
def prefixEnd_1258425 : Nat := 4983230072969 + 3 ^ 40 * 1258425 * 2
def baseEnd_1258425 : Nat := 143594865029854253355581

theorem tailTrace_1258425 : CollatzResearch.WordTrace tailWord_1258425 prefixEnd_1258425 143594865029854253355581 := by
  unfold tailWord_1258425
  simp only [CollatzResearch.WordTrace]
  refine ⟨45898530465948621724304729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30599020310632414482869819 45898530465948621724304729)
  ·
    refine ⟨34423897849461466293228547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45898530465948621724304729 34423897849461466293228547)
    ·
      refine ⟨51635846774192199439842821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34423897849461466293228547 51635846774192199439842821)
      ·
        refine ⟨9681721270161037394970529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51635846774192199439842821 9681721270161037394970529)
        ·
          refine ⟨7261290952620778046227897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9681721270161037394970529 7261290952620778046227897)
          ·
            refine ⟨5445968214465583534670923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7261290952620778046227897 5445968214465583534670923)
            ·
              refine ⟨8168952321698375302006385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445968214465583534670923 8168952321698375302006385)
              ·
                refine ⟨6126714241273781476504789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8168952321698375302006385 6126714241273781476504789)
                ·
                  refine ⟨143594865029854253355581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6126714241273781476504789 143594865029854253355581)
                  ·
                    rfl

theorem cell22_1258425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_1258425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258425 prefixEnd_1258425 := by exact prefixLift 1258425
  have htrace : WordTrace (prefixWord ++ tailWord_1258425) baseStart_1258425 baseEnd_1258425 := by
    simpa [prefixWord, tailWord_1258425, baseEnd_1258425] using wordTrace_append hprefix tailTrace_1258425
  have hstable : (prefixWord ++ tailWord_1258425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258425).length < 2 ^ (prefixWord ++ tailWord_1258425).sum := by decide
  have hdescent : baseEnd_1258425 < baseStart_1258425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258489 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 1, 4]
def baseStart_1258489 : Nat := 118140960795 + 1258489 * 2 ^ 59
def prefixEnd_1258489 : Nat := 4983230072969 + 3 ^ 40 * 1258489 * 2
def baseEnd_1258489 : Nat := 430806503597487926466547

theorem tailTrace_1258489 : CollatzResearch.WordTrace tailWord_1258489 prefixEnd_1258489 430806503597487926466547 := by
  unfold tailWord_1258489
  simp only [CollatzResearch.WordTrace]
  refine ⟨45900864737716760654634521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30600576491811173769756347 45900864737716760654634521)
  ·
    refine ⟨34425648553287570490975891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45900864737716760654634521 34425648553287570490975891)
    ·
      refine ⟨51638472829931355736463837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34425648553287570490975891 51638472829931355736463837)
      ·
        refine ⟨19364427311224258401173939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51638472829931355736463837 19364427311224258401173939)
        ·
          refine ⟨29046640966836387601760909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19364427311224258401173939 29046640966836387601760909)
          ·
            refine ⟨10892490362563645350660341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29046640966836387601760909 10892490362563645350660341)
            ·
              refine ⟨1021170971490341751624407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10892490362563645350660341 1021170971490341751624407)
              ·
                refine ⟨1531756457235512627436611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021170971490341751624407 1531756457235512627436611)
                ·
                  refine ⟨2297634685853268941154917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531756457235512627436611 2297634685853268941154917)
                  ·
                    refine ⟨430806503597487926466547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2297634685853268941154917 430806503597487926466547)
                    ·
                      rfl

theorem cell22_1258489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_1258489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258489 prefixEnd_1258489 := by exact prefixLift 1258489
  have htrace : WordTrace (prefixWord ++ tailWord_1258489) baseStart_1258489 baseEnd_1258489 := by
    simpa [prefixWord, tailWord_1258489, baseEnd_1258489] using wordTrace_append hprefix tailTrace_1258489
  have hstable : (prefixWord ++ tailWord_1258489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258489).length < 2 ^ (prefixWord ++ tailWord_1258489).sum := by decide
  have hdescent : baseEnd_1258489 < baseStart_1258489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258504 : List Nat := [2, 1, 3, 2, 1, 4, 1, 4, 4]
def baseStart_1258504 : Nat := 118140960795 + 1258504 * 2 ^ 59
def prefixEnd_1258504 : Nat := 4983230072969 + 3 ^ 40 * 1258504 * 2
def baseEnd_1258504 : Nat := 143603879468010962447167

theorem tailTrace_1258504 : CollatzResearch.WordTrace tailWord_1258504 prefixEnd_1258504 143603879468010962447167 := by
  unfold tailWord_1258504
  simp only [CollatzResearch.WordTrace]
  refine ⟨22950705916331209108215283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30600941221774945477620377 22950705916331209108215283)
  ·
    refine ⟨34426058874496813662322925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22950705916331209108215283 34426058874496813662322925)
    ·
      refine ⟨12909772077936305123371097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34426058874496813662322925 12909772077936305123371097)
      ·
        refine ⟨9682329058452228842528323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12909772077936305123371097 9682329058452228842528323)
        ·
          refine ⟨14523493587678343263792485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9682329058452228842528323 14523493587678343263792485)
          ·
            refine ⟨2723155047689689361961091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14523493587678343263792485 2723155047689689361961091)
            ·
              refine ⟨4084732571534534042941637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723155047689689361961091 4084732571534534042941637)
              ·
                refine ⟨765887357162725133051557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4084732571534534042941637 765887357162725133051557)
                ·
                  refine ⟨143603879468010962447167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765887357162725133051557 143603879468010962447167)
                  ·
                    rfl

theorem cell22_1258504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_1258504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258504 prefixEnd_1258504 := by exact prefixLift 1258504
  have htrace : WordTrace (prefixWord ++ tailWord_1258504) baseStart_1258504 baseEnd_1258504 := by
    simpa [prefixWord, tailWord_1258504, baseEnd_1258504] using wordTrace_append hprefix tailTrace_1258504
  have hstable : (prefixWord ++ tailWord_1258504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258504).length < 2 ^ (prefixWord ++ tailWord_1258504).sum := by decide
  have hdescent : baseEnd_1258504 < baseStart_1258504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258519 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 1, 5]
def baseStart_1258519 : Nat := 118140960795 + 1258519 * 2 ^ 59
def prefixEnd_1258519 : Nat := 4983230072969 + 3 ^ 40 * 1258519 * 2
def baseEnd_1258519 : Nat := 430816773210577848216455

theorem tailTrace_1258519 : CollatzResearch.WordTrace tailWord_1258519 prefixEnd_1258519 430816773210577848216455 := by
  unfold tailWord_1258519
  simp only [CollatzResearch.WordTrace]
  refine ⟨45901958927608075778226611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30601305951738717185484407 45901958927608075778226611)
  ·
    refine ⟨68852938391412113667339917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45901958927608075778226611 68852938391412113667339917)
    ·
      refine ⟨25819851896779542625252469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68852938391412113667339917 25819851896779542625252469)
      ·
        refine ⟨2420611115323082121117419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25819851896779542625252469 2420611115323082121117419)
        ·
          refine ⟨3630916672984623181676129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420611115323082121117419 3630916672984623181676129)
          ·
            refine ⟨2723187504738467386257097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3630916672984623181676129 2723187504738467386257097)
            ·
              refine ⟨2042390628553850539692823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2723187504738467386257097 2042390628553850539692823)
              ·
                refine ⟨3063585942830775809539235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042390628553850539692823 3063585942830775809539235)
                ·
                  refine ⟨4595378914246163714308853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063585942830775809539235 4595378914246163714308853)
                  ·
                    refine ⟨430816773210577848216455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4595378914246163714308853 430816773210577848216455)
                    ·
                      rfl

theorem cell22_1258519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_1258519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258519 prefixEnd_1258519 := by exact prefixLift 1258519
  have htrace : WordTrace (prefixWord ++ tailWord_1258519) baseStart_1258519 baseEnd_1258519 := by
    simpa [prefixWord, tailWord_1258519, baseEnd_1258519] using wordTrace_append hprefix tailTrace_1258519
  have hstable : (prefixWord ++ tailWord_1258519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258519).length < 2 ^ (prefixWord ++ tailWord_1258519).sum := by decide
  have hdescent : baseEnd_1258519 < baseStart_1258519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258547 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 7, 3]
def baseStart_1258547 : Nat := 118140960795 + 1258547 * 2 ^ 59
def prefixEnd_1258547 : Nat := 4983230072969 + 3 ^ 40 * 1258547 * 2
def baseEnd_1258547 : Nat := 430826358182795108516369

theorem tailTrace_1258547 : CollatzResearch.WordTrace tailWord_1258547 prefixEnd_1258547 430826358182795108516369 := by
  unfold tailWord_1258547
  simp only [CollatzResearch.WordTrace]
  refine ⟨45902980171506636560245895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30601986781004424373497263 45902980171506636560245895)
  ·
    refine ⟨68854470257259954840368843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45902980171506636560245895 68854470257259954840368843)
    ·
      refine ⟨103281705385889932260553265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68854470257259954840368843 103281705385889932260553265)
      ·
        refine ⟨77461279039417449195414949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103281705385889932260553265 77461279039417449195414949)
        ·
          refine ⟨14523989819890771724140303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77461279039417449195414949 14523989819890771724140303)
          ·
            refine ⟨21785984729836157586210455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14523989819890771724140303 21785984729836157586210455)
            ·
              refine ⟨32678977094754236379315683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21785984729836157586210455 32678977094754236379315683)
              ·
                refine ⟨49018465642131354568973525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32678977094754236379315683 49018465642131354568973525)
                ·
                  refine ⟨1148870288487453622710317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 49018465642131354568973525 1148870288487453622710317)
                  ·
                    refine ⟨430826358182795108516369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148870288487453622710317 430826358182795108516369)
                    ·
                      rfl

theorem cell22_1258547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 3].length) (baseStart_1258547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258547 prefixEnd_1258547 := by exact prefixLift 1258547
  have htrace : WordTrace (prefixWord ++ tailWord_1258547) baseStart_1258547 baseEnd_1258547 := by
    simpa [prefixWord, tailWord_1258547, baseEnd_1258547] using wordTrace_append hprefix tailTrace_1258547
  have hstable : (prefixWord ++ tailWord_1258547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258547).length < 2 ^ (prefixWord ++ tailWord_1258547).sum := by decide
  have hdescent : baseEnd_1258547 < baseStart_1258547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258577 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 5]
def baseStart_1258577 : Nat := 118140960795 + 1258577 * 2 ^ 59
def prefixEnd_1258577 : Nat := 4983230072969 + 3 ^ 40 * 1258577 * 2
def baseEnd_1258577 : Nat := 143612209265295010088759

theorem tailTrace_1258577 : CollatzResearch.WordTrace tailWord_1258577 prefixEnd_1258577 143612209265295010088759 := by
  unfold tailWord_1258577
  simp only [CollatzResearch.WordTrace]
  refine ⟨45904074361397951683837985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30602716240931967789225323 45904074361397951683837985)
  ·
    refine ⟨34428055771048463762878489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45904074361397951683837985 34428055771048463762878489)
    ·
      refine ⟨25821041828286347822158867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34428055771048463762878489 25821041828286347822158867)
      ·
        refine ⟨38731562742429521733238301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25821041828286347822158867 38731562742429521733238301)
        ·
          refine ⟨14524336028411070649964363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38731562742429521733238301 14524336028411070649964363)
          ·
            refine ⟨21786504042616605974946545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14524336028411070649964363 21786504042616605974946545)
            ·
              refine ⟨16339878031962454481209909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21786504042616605974946545 16339878031962454481209909)
              ·
                refine ⟨1531863565496480107613429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16339878031962454481209909 1531863565496480107613429)
                ·
                  refine ⟨143612209265295010088759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1531863565496480107613429 143612209265295010088759)
                  ·
                    rfl

theorem cell22_1258577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_1258577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258577 prefixEnd_1258577 := by exact prefixLift 1258577
  have htrace : WordTrace (prefixWord ++ tailWord_1258577) baseStart_1258577 baseEnd_1258577 := by
    simpa [prefixWord, tailWord_1258577, baseEnd_1258577] using wordTrace_append hprefix tailTrace_1258577
  have hstable : (prefixWord ++ tailWord_1258577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258577).length < 2 ^ (prefixWord ++ tailWord_1258577).sum := by decide
  have hdescent : baseEnd_1258577 < baseStart_1258577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258594 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1258594 : Nat := 118140960795 + 1258594 * 2 ^ 59
def prefixEnd_1258594 : Nat := 4983230072969 + 3 ^ 40 * 1258594 * 2
def baseEnd_1258594 : Nat := 143614149081100884197075

theorem tailTrace_1258594 : CollatzResearch.WordTrace tailWord_1258594 prefixEnd_1258594 143614149081100884197075 := by
  unfold tailWord_1258594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476173600584090896801709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30603129601557575724804557 11476173600584090896801709)
  ·
    refine ⟨4303565100219034086300641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11476173600584090896801709 4303565100219034086300641)
    ·
      refine ⟨3227673825164275564725481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4303565100219034086300641 3227673825164275564725481)
      ·
        refine ⟨2420755368873206673544111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3227673825164275564725481 2420755368873206673544111)
        ·
          refine ⟨3631133053309810010316167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420755368873206673544111 3631133053309810010316167)
          ·
            refine ⟨5446699579964715015474251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631133053309810010316167 5446699579964715015474251)
            ·
              refine ⟨8170049369947072523211377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446699579964715015474251 8170049369947072523211377)
              ·
                refine ⟨6127537027460304392408533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8170049369947072523211377 6127537027460304392408533)
                ·
                  refine ⟨143614149081100884197075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6127537027460304392408533 143614149081100884197075)
                  ·
                    rfl

theorem cell22_1258594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1258594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258594 prefixEnd_1258594 := by exact prefixLift 1258594
  have htrace : WordTrace (prefixWord ++ tailWord_1258594) baseStart_1258594 baseEnd_1258594 := by
    simpa [prefixWord, tailWord_1258594, baseEnd_1258594] using wordTrace_append hprefix tailTrace_1258594
  have hstable : (prefixWord ++ tailWord_1258594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258594).length < 2 ^ (prefixWord ++ tailWord_1258594).sum := by decide
  have hdescent : baseEnd_1258594 < baseStart_1258594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258673 : List Nat := [1, 2, 2, 5, 1, 1, 4, 2, 4]
def baseStart_1258673 : Nat := 118140960795 + 1258673 * 2 ^ 59
def prefixEnd_1258673 : Nat := 4983230072969 + 3 ^ 40 * 1258673 * 2
def baseEnd_1258673 : Nat := 143623163519257593288661

theorem tailTrace_1258673 : CollatzResearch.WordTrace tailWord_1258673 prefixEnd_1258673 143623163519257593288661 := by
  unfold tailWord_1258673
  simp only [CollatzResearch.WordTrace]
  refine ⟨45907575769050160079332673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30605050512700106719555115 45907575769050160079332673)
  ·
    refine ⟨34430681826787620059499505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45907575769050160079332673 34430681826787620059499505)
    ·
      refine ⟨25823011370090715044624629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34430681826787620059499505 25823011370090715044624629)
      ·
        refine ⟨2420907315946004535433559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25823011370090715044624629 2420907315946004535433559)
        ·
          refine ⟨3631360973919006803150339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420907315946004535433559 3631360973919006803150339)
          ·
            refine ⟨5447041460878510204725509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631360973919006803150339 5447041460878510204725509)
            ·
              refine ⟨1021320273914720663386033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5447041460878510204725509 1021320273914720663386033)
              ·
                refine ⟨765990205436040497539525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021320273914720663386033 765990205436040497539525)
                ·
                  refine ⟨143623163519257593288661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765990205436040497539525 143623163519257593288661)
                  ·
                    rfl

theorem cell22_1258673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_1258673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258673 prefixEnd_1258673 := by exact prefixLift 1258673
  have htrace : WordTrace (prefixWord ++ tailWord_1258673) baseStart_1258673 baseEnd_1258673 := by
    simpa [prefixWord, tailWord_1258673, baseEnd_1258673] using wordTrace_append hprefix tailTrace_1258673
  have hstable : (prefixWord ++ tailWord_1258673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258673).length < 2 ^ (prefixWord ++ tailWord_1258673).sum := by decide
  have hdescent : baseEnd_1258673 < baseStart_1258673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258682 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_1258682 : Nat := 118140960795 + 1258682 * 2 ^ 59
def prefixEnd_1258682 : Nat := 4983230072969 + 3 ^ 40 * 1258682 * 2
def baseEnd_1258682 : Nat := 430872571441699756390955

theorem tailTrace_1258682 : CollatzResearch.WordTrace tailWord_1258682 prefixEnd_1258682 430872571441699756390955 := by
  unfold tailWord_1258682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476976006504388654102575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30605269350678369744273533 11476976006504388654102575)
  ·
    refine ⟨17215464009756582981153863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11476976006504388654102575 17215464009756582981153863)
    ·
      refine ⟨25823196014634874471730795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17215464009756582981153863 25823196014634874471730795)
      ·
        refine ⟨38734794021952311707596193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25823196014634874471730795 38734794021952311707596193)
        ·
          refine ⟨29051095516464233780697145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38734794021952311707596193 29051095516464233780697145)
          ·
            refine ⟨21788321637348175335522859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29051095516464233780697145 21788321637348175335522859)
            ·
              refine ⟨32682482456022263003284289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21788321637348175335522859 32682482456022263003284289)
              ·
                refine ⟨24511861842016697252463217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32682482456022263003284289 24511861842016697252463217)
                ·
                  refine ⟨18383896381512522939347413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24511861842016697252463217 18383896381512522939347413)
                  ·
                    refine ⟨430872571441699756390955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18383896381512522939347413 430872571441699756390955)
                    ·
                      rfl

theorem cell22_1258682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_1258682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258682 prefixEnd_1258682 := by exact prefixLift 1258682
  have htrace : WordTrace (prefixWord ++ tailWord_1258682) baseStart_1258682 baseEnd_1258682 := by
    simpa [prefixWord, tailWord_1258682, baseEnd_1258682] using wordTrace_append hprefix tailTrace_1258682
  have hstable : (prefixWord ++ tailWord_1258682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258682).length < 2 ^ (prefixWord ++ tailWord_1258682).sum := by decide
  have hdescent : baseEnd_1258682 < baseStart_1258682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258684 : List Nat := [2, 2, 2, 3, 2, 1, 3, 7]
def baseStart_1258684 : Nat := 118140960795 + 1258684 * 2 ^ 59
def prefixEnd_1258684 : Nat := 4983230072969 + 3 ^ 40 * 1258684 * 2
def baseEnd_1258684 : Nat := 47874806231396935315661

theorem tailTrace_1258684 : CollatzResearch.WordTrace tailWord_1258684 prefixEnd_1258684 47874806231396935315661 := by
  unfold tailWord_1258684
  simp only [CollatzResearch.WordTrace]
  refine ⟨22953988486005154478991553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30605317981340205971988737 22953988486005154478991553)
  ·
    refine ⟨17215491364503865859243665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22953988486005154478991553 17215491364503865859243665)
    ·
      refine ⟨12911618523377899394432749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17215491364503865859243665 12911618523377899394432749)
      ·
        refine ⟨4841856946266712272912281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12911618523377899394432749 4841856946266712272912281)
        ·
          refine ⟨3631392709700034204684211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4841856946266712272912281 3631392709700034204684211)
          ·
            refine ⟨5447089064550051307026317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631392709700034204684211 5447089064550051307026317)
            ·
              refine ⟨2042658399206269240134869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5447089064550051307026317 2042658399206269240134869)
              ·
                refine ⟨47874806231396935315661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2042658399206269240134869 47874806231396935315661)
                ·
                  rfl

theorem cell22_1258684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 7].length) (baseStart_1258684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258684 prefixEnd_1258684 := by exact prefixLift 1258684
  have htrace : WordTrace (prefixWord ++ tailWord_1258684) baseStart_1258684 baseEnd_1258684 := by
    simpa [prefixWord, tailWord_1258684, baseEnd_1258684] using wordTrace_append hprefix tailTrace_1258684
  have hstable : (prefixWord ++ tailWord_1258684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258684).length < 2 ^ (prefixWord ++ tailWord_1258684).sum := by decide
  have hdescent : baseEnd_1258684 < baseStart_1258684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258733 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_1258733 : Nat := 118140960795 + 1258733 * 2 ^ 59
def prefixEnd_1258733 : Nat := 4983230072969 + 3 ^ 40 * 1258733 * 2
def baseEnd_1258733 : Nat := 430890029783952623365799

theorem tailTrace_1258733 : CollatzResearch.WordTrace tailWord_1258733 prefixEnd_1258733 430890029783952623365799 := by
  unfold tailWord_1258733
  simp only [CollatzResearch.WordTrace]
  refine ⟨45909764148832790326516853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30606509432555193551011235 45909764148832790326516853)
  ·
    refine ⟨4304040388953074093110955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45909764148832790326516853 4304040388953074093110955)
    ·
      refine ⟨6456060583429611139666433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4304040388953074093110955 6456060583429611139666433)
      ·
        refine ⟨4842045437572208354749825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6456060583429611139666433 4842045437572208354749825)
        ·
          refine ⟨3631534078179156266062369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4842045437572208354749825 3631534078179156266062369)
          ·
            refine ⟨2723650558634367199546777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3631534078179156266062369 2723650558634367199546777)
            ·
              refine ⟨2042737918975775399660083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2723650558634367199546777 2042737918975775399660083)
              ·
                refine ⟨3064106878463663099490125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042737918975775399660083 3064106878463663099490125)
                ·
                  refine ⟨1149040079423873662308797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3064106878463663099490125 1149040079423873662308797)
                  ·
                    refine ⟨430890029783952623365799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149040079423873662308797 430890029783952623365799)
                    ·
                      rfl

theorem cell22_1258733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_1258733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258733 prefixEnd_1258733 := by exact prefixLift 1258733
  have htrace : WordTrace (prefixWord ++ tailWord_1258733) baseStart_1258733 baseEnd_1258733 := by
    simpa [prefixWord, tailWord_1258733, baseEnd_1258733] using wordTrace_append hprefix tailTrace_1258733
  have hstable : (prefixWord ++ tailWord_1258733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258733).length < 2 ^ (prefixWord ++ tailWord_1258733).sum := by decide
  have hdescent : baseEnd_1258733 < baseStart_1258733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258746 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_1258746 : Nat := 118140960795 + 1258746 * 2 ^ 59
def prefixEnd_1258746 : Nat := 4983230072969 + 3 ^ 40 * 1258746 * 2
def baseEnd_1258746 : Nat := 143631493316541640930253

theorem tailTrace_1258746 : CollatzResearch.WordTrace tailWord_1258746 prefixEnd_1258746 143631493316541640930253 := by
  unfold tailWord_1258746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477559574446423386685023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30606825531857129031160061 11477559574446423386685023)
  ·
    refine ⟨17216339361669635080027535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11477559574446423386685023 17216339361669635080027535)
    ·
      refine ⟨25824509042504452620041303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17216339361669635080027535 25824509042504452620041303)
      ·
        refine ⟨38736763563756678930061955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25824509042504452620041303 38736763563756678930061955)
        ·
          refine ⟨58105145345635018395092933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38736763563756678930061955 58105145345635018395092933)
          ·
            refine ⟨10894714752306565949079925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58105145345635018395092933 10894714752306565949079925)
            ·
              refine ⟨1021379508028740557726243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10894714752306565949079925 1021379508028740557726243)
              ·
                refine ⟨1532069262043110836589365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021379508028740557726243 1532069262043110836589365)
                ·
                  refine ⟨143631493316541640930253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1532069262043110836589365 143631493316541640930253)
                  ·
                    rfl

theorem cell22_1258746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_1258746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258746 prefixEnd_1258746 := by exact prefixLift 1258746
  have htrace : WordTrace (prefixWord ++ tailWord_1258746) baseStart_1258746 baseEnd_1258746 := by
    simpa [prefixWord, tailWord_1258746, baseEnd_1258746] using wordTrace_append hprefix tailTrace_1258746
  have hstable : (prefixWord ++ tailWord_1258746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258746).length < 2 ^ (prefixWord ++ tailWord_1258746).sum := by decide
  have hdescent : baseEnd_1258746 < baseStart_1258746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258776 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_1258776 : Nat := 118140960795 + 1258776 * 2 ^ 59
def prefixEnd_1258776 : Nat := 4983230072969 + 3 ^ 40 * 1258776 * 2
def baseEnd_1258776 : Nat := 430904749562714844540667

theorem tailTrace_1258776 : CollatzResearch.WordTrace tailWord_1258776 prefixEnd_1258776 430904749562714844540667 := by
  unfold tailWord_1258776
  simp only [CollatzResearch.WordTrace]
  refine ⟨22955666243838504335166091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30607554991784672446888121 22955666243838504335166091)
  ·
    refine ⟨34433499365757756502749137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22955666243838504335166091 34433499365757756502749137)
    ·
      refine ⟨25825124524318317377061853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34433499365757756502749137 25825124524318317377061853)
      ·
        refine ⟨9684421696619369016398195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25825124524318317377061853 9684421696619369016398195)
        ·
          refine ⟨14526632544929053524597293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9684421696619369016398195 14526632544929053524597293)
          ·
            refine ⟨5447487204348395071723985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14526632544929053524597293 5447487204348395071723985)
            ·
              refine ⟨4085615403261296303792989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5447487204348395071723985 4085615403261296303792989)
              ·
                refine ⟨1532105776222986113922371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4085615403261296303792989 1532105776222986113922371)
                ·
                  refine ⟨2298158664334479170883557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532105776222986113922371 2298158664334479170883557)
                  ·
                    refine ⟨430904749562714844540667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298158664334479170883557 430904749562714844540667)
                    ·
                      rfl

theorem cell22_1258776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_1258776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258776 prefixEnd_1258776 := by exact prefixLift 1258776
  have htrace : WordTrace (prefixWord ++ tailWord_1258776) baseStart_1258776 baseEnd_1258776 := by
    simpa [prefixWord, tailWord_1258776, baseEnd_1258776] using wordTrace_append hprefix tailTrace_1258776
  have hstable : (prefixWord ++ tailWord_1258776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258776).length < 2 ^ (prefixWord ++ tailWord_1258776).sum := by decide
  have hdescent : baseEnd_1258776 < baseStart_1258776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258879 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 6, 5]
def baseStart_1258879 : Nat := 118140960795 + 1258879 * 2 ^ 59
def prefixEnd_1258879 : Nat := 4983230072969 + 3 ^ 40 * 1258879 * 2
def baseEnd_1258879 : Nat := 430940008567656909215351

theorem tailTrace_1258879 : CollatzResearch.WordTrace tailWord_1258879 prefixEnd_1258879 430940008567656909215351 := by
  unfold tailWord_1258879
  simp only [CollatzResearch.WordTrace]
  refine ⟨45915089206303857261331691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30610059470869238174221127 45915089206303857261331691)
  ·
    refine ⟨68872633809455785891997537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45915089206303857261331691 68872633809455785891997537)
    ·
      refine ⟨51654475357091839418998153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68872633809455785891997537 51654475357091839418998153)
      ·
        refine ⟨38740856517818879564248615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51654475357091839418998153 38740856517818879564248615)
        ·
          refine ⟨58111284776728319346372923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38740856517818879564248615 58111284776728319346372923)
          ·
            refine ⟨87166927165092479019559385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58111284776728319346372923 87166927165092479019559385)
            ·
              refine ⟨65375195373819359264669539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87166927165092479019559385 65375195373819359264669539)
              ·
                refine ⟨98062793060729038897004309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65375195373819359264669539 98062793060729038897004309)
                ·
                  refine ⟨4596693424721673698297077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98062793060729038897004309 4596693424721673698297077)
                  ·
                    refine ⟨430940008567656909215351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4596693424721673698297077 430940008567656909215351)
                    ·
                      rfl

theorem cell22_1258879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_1258879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258879 prefixEnd_1258879 := by exact prefixLift 1258879
  have htrace : WordTrace (prefixWord ++ tailWord_1258879) baseStart_1258879 baseEnd_1258879 := by
    simpa [prefixWord, tailWord_1258879, baseEnd_1258879] using wordTrace_append hprefix tailTrace_1258879
  have hstable : (prefixWord ++ tailWord_1258879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258879).length < 2 ^ (prefixWord ++ tailWord_1258879).sum := by decide
  have hdescent : baseEnd_1258879 < baseStart_1258879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258941 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1258941 : Nat := 118140960795 + 1258941 * 2 ^ 59
def prefixEnd_1258941 : Nat := 4983230072969 + 3 ^ 40 * 1258941 * 2
def baseEnd_1258941 : Nat := 430961232434709414165161

theorem tailTrace_1258941 : CollatzResearch.WordTrace tailWord_1258941 prefixEnd_1258941 430961232434709414165161 := by
  unfold tailWord_1258941
  simp only [CollatzResearch.WordTrace]
  refine ⟨45917350532079241850088677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30611567021386161233392451 45917350532079241850088677)
  ·
    refine ⟨8609503224764857846891627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45917350532079241850088677 8609503224764857846891627)
    ·
      refine ⟨12914254837147286770337441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8609503224764857846891627 12914254837147286770337441)
      ·
        refine ⟨9685691127860465077753081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12914254837147286770337441 9685691127860465077753081)
        ·
          refine ⟨7264268345895348808314811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9685691127860465077753081 7264268345895348808314811)
          ·
            refine ⟨10896402518843023212472217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7264268345895348808314811 10896402518843023212472217)
            ·
              refine ⟨8172301889132267409354163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10896402518843023212472217 8172301889132267409354163)
              ·
                refine ⟨12258452833698401114031245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8172301889132267409354163 12258452833698401114031245)
                ·
                  refine ⟨4596919812636900417761717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12258452833698401114031245 4596919812636900417761717)
                  ·
                    refine ⟨430961232434709414165161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4596919812636900417761717 430961232434709414165161)
                    ·
                      rfl

theorem cell22_1258941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1258941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258941 prefixEnd_1258941 := by exact prefixLift 1258941
  have htrace : WordTrace (prefixWord ++ tailWord_1258941) baseStart_1258941 baseEnd_1258941 := by
    simpa [prefixWord, tailWord_1258941, baseEnd_1258941] using wordTrace_append hprefix tailTrace_1258941
  have hstable : (prefixWord ++ tailWord_1258941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258941).length < 2 ^ (prefixWord ++ tailWord_1258941).sum := by decide
  have hdescent : baseEnd_1258941 < baseStart_1258941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258958 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_1258958 : Nat := 118140960795 + 1258958 * 2 ^ 59
def prefixEnd_1258958 : Nat := 4983230072969 + 3 ^ 40 * 1258958 * 2
def baseEnd_1258958 : Nat := 430967051882127036490109

theorem tailTrace_1258958 : CollatzResearch.WordTrace tailWord_1258958 prefixEnd_1258958 430967051882127036490109 := by
  unfold tailWord_1258958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5739746321627206719182191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30611980382011769168971685 5739746321627206719182191)
  ·
    refine ⟨8609619482440810078773287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5739746321627206719182191 8609619482440810078773287)
    ·
      refine ⟨12914429223661215118159931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8609619482440810078773287 12914429223661215118159931)
      ·
        refine ⟨19371643835491822677239897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12914429223661215118159931 19371643835491822677239897)
        ·
          refine ⟨14528732876618867007929923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19371643835491822677239897 14528732876618867007929923)
          ·
            refine ⟨21793099314928300511894885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14528732876618867007929923 21793099314928300511894885)
            ·
              refine ⟨4086206121549056345980291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21793099314928300511894885 4086206121549056345980291)
              ·
                refine ⟨6129309182323584518970437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086206121549056345980291 6129309182323584518970437)
                ·
                  refine ⟨1149245471685672097306957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6129309182323584518970437 1149245471685672097306957)
                  ·
                    refine ⟨430967051882127036490109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149245471685672097306957 430967051882127036490109)
                    ·
                      rfl

theorem cell22_1258958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_1258958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1258958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1258958 prefixEnd_1258958 := by exact prefixLift 1258958
  have htrace : WordTrace (prefixWord ++ tailWord_1258958) baseStart_1258958 baseEnd_1258958 := by
    simpa [prefixWord, tailWord_1258958, baseEnd_1258958] using wordTrace_append hprefix tailTrace_1258958
  have hstable : (prefixWord ++ tailWord_1258958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258958).length < 2 ^ (prefixWord ++ tailWord_1258958).sum := by decide
  have hdescent : baseEnd_1258958 < baseStart_1258958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259016 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 7]
def baseStart_1259016 : Nat := 118140960795 + 1259016 * 2 ^ 59
def prefixEnd_1259016 : Nat := 4983230072969 + 3 ^ 40 * 1259016 * 2
def baseEnd_1259016 : Nat := 143662302155811406179977

theorem tailTrace_1259016 : CollatzResearch.WordTrace tailWord_1259016 prefixEnd_1259016 143662302155811406179977 := by
  unfold tailWord_1259016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22960043003403764829534451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30613390671205019772712601 22960043003403764829534451)
  ·
    refine ⟨34440064505105647244301677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22960043003403764829534451 34440064505105647244301677)
    ·
      refine ⟨12915024189414617716613129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34440064505105647244301677 12915024189414617716613129)
      ·
        refine ⟨9686268142060963287459847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12915024189414617716613129 9686268142060963287459847)
        ·
          refine ⟨14529402213091444931189771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9686268142060963287459847 14529402213091444931189771)
          ·
            refine ⟨21794103319637167396784657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14529402213091444931189771 21794103319637167396784657)
            ·
              refine ⟨16345577489727875547588493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21794103319637167396784657 16345577489727875547588493)
              ·
                refine ⟨6129591558647953330345685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16345577489727875547588493 6129591558647953330345685)
                ·
                  refine ⟨143662302155811406179977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6129591558647953330345685 143662302155811406179977)
                  ·
                    rfl

theorem cell22_1259016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_1259016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259016 prefixEnd_1259016 := by exact prefixLift 1259016
  have htrace : WordTrace (prefixWord ++ tailWord_1259016) baseStart_1259016 baseEnd_1259016 := by
    simpa [prefixWord, tailWord_1259016, baseEnd_1259016] using wordTrace_append hprefix tailTrace_1259016
  have hstable : (prefixWord ++ tailWord_1259016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259016).length < 2 ^ (prefixWord ++ tailWord_1259016).sum := by decide
  have hdescent : baseEnd_1259016 < baseStart_1259016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259054 : List Nat := [4, 1, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1259054 : Nat := 118140960795 + 1259054 * 2 ^ 59
def prefixEnd_1259054 : Nat := 4983230072969 + 3 ^ 40 * 1259054 * 2
def baseEnd_1259054 : Nat := 430999914644014786089815

theorem tailTrace_1259054 : CollatzResearch.WordTrace tailWord_1259054 prefixEnd_1259054 430999914644014786089815 := by
  unfold tailWord_1259054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5740183997583732768619027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30614314653779908099301477 5740183997583732768619027)
  ·
    refine ⟨8610275996375599152928541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5740183997583732768619027 8610275996375599152928541)
    ·
      refine ⟨3228853498640849682348203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8610275996375599152928541 3228853498640849682348203)
      ·
        refine ⟨4843280247961274523522305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3228853498640849682348203 4843280247961274523522305)
        ·
          refine ⟨3632460185970955892641729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4843280247961274523522305 3632460185970955892641729)
          ·
            refine ⟨2724345139478216919481297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3632460185970955892641729 2724345139478216919481297)
            ·
              refine ⟨2043258854608662689610973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724345139478216919481297 2043258854608662689610973)
              ·
                refine ⟨766222070478248508604115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2043258854608662689610973 766222070478248508604115)
                ·
                  refine ⟨1149333105717372762906173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766222070478248508604115 1149333105717372762906173)
                  ·
                    refine ⟨430999914644014786089815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149333105717372762906173 430999914644014786089815)
                    ·
                      rfl

theorem cell22_1259054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1259054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259054 prefixEnd_1259054 := by exact prefixLift 1259054
  have htrace : WordTrace (prefixWord ++ tailWord_1259054) baseStart_1259054 baseEnd_1259054 := by
    simpa [prefixWord, tailWord_1259054, baseEnd_1259054] using wordTrace_append hprefix tailTrace_1259054
  have hstable : (prefixWord ++ tailWord_1259054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259054).length < 2 ^ (prefixWord ++ tailWord_1259054).sum := by decide
  have hdescent : baseEnd_1259054 < baseStart_1259054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259108 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1259108 : Nat := 118140960795 + 1259108 * 2 ^ 59
def prefixEnd_1259108 : Nat := 4983230072969 + 3 ^ 40 * 1259108 * 2
def baseEnd_1259108 : Nat := 431018399947576645239649

theorem tailTrace_1259108 : CollatzResearch.WordTrace tailWord_1259108 prefixEnd_1259108 431018399947576645239649 := by
  unfold tailWord_1259108
  simp only [CollatzResearch.WordTrace]
  refine ⟨22961720761237114685708989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30615627681649486247611985 22961720761237114685708989)
  ·
    refine ⟨8610645285463918007140871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22961720761237114685708989 8610645285463918007140871)
    ·
      refine ⟨12915967928195877010711307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8610645285463918007140871 12915967928195877010711307)
      ·
        refine ⟨19373951892293815516066961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12915967928195877010711307 19373951892293815516066961)
        ·
          refine ⟨14530463919220361637050221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19373951892293815516066961 14530463919220361637050221)
          ·
            refine ⟨5448923969707635613893833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14530463919220361637050221 5448923969707635613893833)
            ·
              refine ⟨4086692977280726710420375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5448923969707635613893833 4086692977280726710420375)
              ·
                refine ⟨6130039465921090065630563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086692977280726710420375 6130039465921090065630563)
                ·
                  refine ⟨9195059198881635098445845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6130039465921090065630563 9195059198881635098445845)
                  ·
                    refine ⟨431018399947576645239649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9195059198881635098445845 431018399947576645239649)
                    ·
                      rfl

theorem cell22_1259108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1259108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259108 prefixEnd_1259108 := by exact prefixLift 1259108
  have htrace : WordTrace (prefixWord ++ tailWord_1259108) baseStart_1259108 baseEnd_1259108 := by
    simpa [prefixWord, tailWord_1259108, baseEnd_1259108] using wordTrace_append hprefix tailTrace_1259108
  have hstable : (prefixWord ++ tailWord_1259108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259108).length < 2 ^ (prefixWord ++ tailWord_1259108).sum := by decide
  have hdescent : baseEnd_1259108 < baseStart_1259108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259112 : List Nat := [2, 1, 4, 3, 1, 1, 3, 3, 4]
def baseStart_1259112 : Nat := 118140960795 + 1259112 * 2 ^ 59
def prefixEnd_1259112 : Nat := 4983230072969 + 3 ^ 40 * 1259112 * 2
def baseEnd_1259112 : Nat := 143673256409773989379879

theorem tailTrace_1259112 : CollatzResearch.WordTrace tailWord_1259112 prefixEnd_1259112 143673256409773989379879 := by
  unfold tailWord_1259112
  simp only [CollatzResearch.WordTrace]
  refine ⟨22961793707229869027281795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30615724942973158703042393 22961793707229869027281795)
  ·
    refine ⟨34442690560844803540922693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22961793707229869027281795 34442690560844803540922693)
    ·
      refine ⟨6458004480158400663923005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34442690560844803540922693 6458004480158400663923005)
      ·
        refine ⟨2421751680059400248971127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6458004480158400663923005 2421751680059400248971127)
        ·
          refine ⟨3632627520089100373456691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2421751680059400248971127 3632627520089100373456691)
          ·
            refine ⟨5448941280133650560185037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632627520089100373456691 5448941280133650560185037)
            ·
              refine ⟨2043352980050118960069389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5448941280133650560185037 2043352980050118960069389)
              ·
                refine ⟨766257367518794610026021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2043352980050118960069389 766257367518794610026021)
                ·
                  refine ⟨143673256409773989379879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766257367518794610026021 143673256409773989379879)
                  ·
                    rfl

theorem cell22_1259112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_1259112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259112 prefixEnd_1259112 := by exact prefixLift 1259112
  have htrace : WordTrace (prefixWord ++ tailWord_1259112) baseStart_1259112 baseEnd_1259112 := by
    simpa [prefixWord, tailWord_1259112, baseEnd_1259112] using wordTrace_append hprefix tailTrace_1259112
  have hstable : (prefixWord ++ tailWord_1259112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259112).length < 2 ^ (prefixWord ++ tailWord_1259112).sum := by decide
  have hdescent : baseEnd_1259112 < baseStart_1259112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259125 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1259125 : Nat := 118140960795 + 1259125 * 2 ^ 59
def prefixEnd_1259125 : Nat := 4983230072969 + 3 ^ 40 * 1259125 * 2
def baseEnd_1259125 : Nat := 431024219394994267564597

theorem tailTrace_1259125 : CollatzResearch.WordTrace tailWord_1259125 prefixEnd_1259125 431024219394994267564597 := by
  unfold tailWord_1259125
  simp only [CollatzResearch.WordTrace]
  refine ⟨45924061563412641274786829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30616041042275094183191219 45924061563412641274786829)
  ·
    refine ⟨17221523086279740478045061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45924061563412641274786829 17221523086279740478045061)
    ·
      refine ⟨3229035578677451339633449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17221523086279740478045061 3229035578677451339633449)
      ·
        refine ⟨2421776684008088504725087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3229035578677451339633449 2421776684008088504725087)
        ·
          refine ⟨3632665026012132757087631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2421776684008088504725087 3632665026012132757087631)
          ·
            refine ⟨5448997539018199135631447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632665026012132757087631 5448997539018199135631447)
            ·
              refine ⟨8173496308527298703447171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448997539018199135631447 8173496308527298703447171)
              ·
                refine ⟨12260244462790948055170757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8173496308527298703447171 12260244462790948055170757)
                ·
                  refine ⟨2298795836773302760344517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12260244462790948055170757 2298795836773302760344517)
                  ·
                    refine ⟨431024219394994267564597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298795836773302760344517 431024219394994267564597)
                    ·
                      rfl

theorem cell22_1259125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1259125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259125 prefixEnd_1259125 := by exact prefixLift 1259125
  have htrace : WordTrace (prefixWord ++ tailWord_1259125) baseStart_1259125 baseEnd_1259125 := by
    simpa [prefixWord, tailWord_1259125, baseEnd_1259125] using wordTrace_append hprefix tailTrace_1259125
  have hstable : (prefixWord ++ tailWord_1259125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259125).length < 2 ^ (prefixWord ++ tailWord_1259125).sum := by decide
  have hdescent : baseEnd_1259125 < baseStart_1259125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259140 : List Nat := [2, 3, 2, 1, 4, 1, 2, 7]
def baseStart_1259140 : Nat := 118140960795 + 1259140 * 2 ^ 59
def prefixEnd_1259140 : Nat := 4983230072969 + 3 ^ 40 * 1259140 * 2
def baseEnd_1259140 : Nat := 47892150466837692048839

theorem tailTrace_1259140 : CollatzResearch.WordTrace tailWord_1259140 prefixEnd_1259140 47892150466837692048839 := by
  unfold tailWord_1259140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962304329179149418291437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30616405772238865891055249 22962304329179149418291437)
  ·
    refine ⟨8610864123442181031859289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22962304329179149418291437 8610864123442181031859289)
    ·
      refine ⟨6458148092581635773894467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8610864123442181031859289 6458148092581635773894467)
      ·
        refine ⟨9687222138872453660841701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458148092581635773894467 9687222138872453660841701)
        ·
          refine ⟨1816354151038585061407819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9687222138872453660841701 1816354151038585061407819)
          ·
            refine ⟨2724531226557877592111729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816354151038585061407819 2724531226557877592111729)
            ·
              refine ⟨2043398419918408194083797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724531226557877592111729 2043398419918408194083797)
              ·
                refine ⟨47892150466837692048839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2043398419918408194083797 47892150466837692048839)
                ·
                  rfl

theorem cell22_1259140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 7].length) (baseStart_1259140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259140 prefixEnd_1259140 := by exact prefixLift 1259140
  have htrace : WordTrace (prefixWord ++ tailWord_1259140) baseStart_1259140 baseEnd_1259140 := by
    simpa [prefixWord, tailWord_1259140, baseEnd_1259140] using wordTrace_append hprefix tailTrace_1259140
  have hstable : (prefixWord ++ tailWord_1259140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259140).length < 2 ^ (prefixWord ++ tailWord_1259140).sum := by decide
  have hdescent : baseEnd_1259140 < baseStart_1259140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259144 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1259144 : Nat := 118140960795 + 1259144 * 2 ^ 59
def prefixEnd_1259144 : Nat := 4983230072969 + 3 ^ 40 * 1259144 * 2
def baseEnd_1259144 : Nat := 431030723483284551339539

theorem tailTrace_1259144 : CollatzResearch.WordTrace tailWord_1259144 prefixEnd_1259144 431030723483284551339539 := by
  unfold tailWord_1259144
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962377275171903759864243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30616503033562538346485657 22962377275171903759864243)
  ·
    refine ⟨34443565912757855639796365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22962377275171903759864243 34443565912757855639796365)
    ·
      refine ⟨12916337217284195864923637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34443565912757855639796365 12916337217284195864923637)
      ·
        refine ⟨1210906614120393362336591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12916337217284195864923637 1210906614120393362336591)
        ·
          refine ⟨1816359921180590043504887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210906614120393362336591 1816359921180590043504887)
          ·
            refine ⟨2724539881770885065257331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816359921180590043504887 2724539881770885065257331)
            ·
              refine ⟨4086809822656327597885997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724539881770885065257331 4086809822656327597885997)
              ·
                refine ⟨1532553683496122849207249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4086809822656327597885997 1532553683496122849207249)
                ·
                  refine ⟨1149415262622092136905437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1532553683496122849207249 1149415262622092136905437)
                  ·
                    refine ⟨431030723483284551339539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149415262622092136905437 431030723483284551339539)
                    ·
                      rfl

theorem cell22_1259144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1259144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259144 prefixEnd_1259144 := by exact prefixLift 1259144
  have htrace : WordTrace (prefixWord ++ tailWord_1259144) baseStart_1259144 baseEnd_1259144 := by
    simpa [prefixWord, tailWord_1259144, baseEnd_1259144] using wordTrace_append hprefix tailTrace_1259144
  have hstable : (prefixWord ++ tailWord_1259144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259144).length < 2 ^ (prefixWord ++ tailWord_1259144).sum := by decide
  have hdescent : baseEnd_1259144 < baseStart_1259144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259183 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 2, 5]
def baseStart_1259183 : Nat := 118140960795 + 1259183 * 2 ^ 59
def prefixEnd_1259183 : Nat := 4983230072969 + 3 ^ 40 * 1259183 * 2
def baseEnd_1259183 : Nat := 431044073980301449614419

theorem tailTrace_1259183 : CollatzResearch.WordTrace tailWord_1259183 prefixEnd_1259183 431044073980301449614419 := by
  unfold tailWord_1259183
  simp only [CollatzResearch.WordTrace]
  refine ⟨45926176997202517180398203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30617451331468344786932135 45926176997202517180398203)
  ·
    refine ⟨68889265495803775770597305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45926176997202517180398203 68889265495803775770597305)
    ·
      refine ⟨51666949121852831827947979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68889265495803775770597305 51666949121852831827947979)
      ·
        refine ⟨77500423682779247741921969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51666949121852831827947979 77500423682779247741921969)
        ·
          refine ⟨58125317762084435806441477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77500423682779247741921969 58125317762084435806441477)
          ·
            refine ⟨10898497080390831713707777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58125317762084435806441477 10898497080390831713707777)
            ·
              refine ⟨8173872810293123785280833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10898497080390831713707777 8173872810293123785280833)
              ·
                refine ⟨6130404607719842838960625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8173872810293123785280833 6130404607719842838960625)
                ·
                  refine ⟨4597803455789882129220469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130404607719842838960625 4597803455789882129220469)
                  ·
                    refine ⟨431044073980301449614419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4597803455789882129220469 431044073980301449614419)
                    ·
                      rfl

theorem cell22_1259183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_1259183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259183 prefixEnd_1259183 := by exact prefixLift 1259183
  have htrace : WordTrace (prefixWord ++ tailWord_1259183) baseStart_1259183 baseEnd_1259183 := by
    simpa [prefixWord, tailWord_1259183, baseEnd_1259183] using wordTrace_append hprefix tailTrace_1259183
  have hstable : (prefixWord ++ tailWord_1259183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259183).length < 2 ^ (prefixWord ++ tailWord_1259183).sum := by decide
  have hdescent : baseEnd_1259183 < baseStart_1259183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259206 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1259206 : Nat := 118140960795 + 1259206 * 2 ^ 59
def prefixEnd_1259206 : Nat := 4983230072969 + 3 ^ 40 * 1259206 * 2
def baseEnd_1259206 : Nat := 431051947350337056289349

theorem tailTrace_1259206 : CollatzResearch.WordTrace tailWord_1259206 prefixEnd_1259206 431051947350337056289349 := by
  unfold tailWord_1259206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435219246128724753390171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30618010584079461405656981 1435219246128724753390171)
  ·
    refine ⟨2152828869193087130085257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1435219246128724753390171 2152828869193087130085257)
    ·
      refine ⟨1614621651894815347563943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2152828869193087130085257 1614621651894815347563943)
      ·
        refine ⟨2421932477842223021345915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1614621651894815347563943 2421932477842223021345915)
        ·
          refine ⟨3632898716763334532018873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2421932477842223021345915 3632898716763334532018873)
          ·
            refine ⟨2724674037572500899014155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3632898716763334532018873 2724674037572500899014155)
            ·
              refine ⟨4087011056358751348521233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724674037572500899014155 4087011056358751348521233)
              ·
                refine ⟨3065258292269063511390925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4087011056358751348521233 3065258292269063511390925)
                ·
                  refine ⟨1149471859600898816771597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3065258292269063511390925 1149471859600898816771597)
                  ·
                    refine ⟨431051947350337056289349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149471859600898816771597 431051947350337056289349)
                    ·
                      rfl

theorem cell22_1259206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1259206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259206 prefixEnd_1259206 := by exact prefixLift 1259206
  have htrace : WordTrace (prefixWord ++ tailWord_1259206) baseStart_1259206 baseEnd_1259206 := by
    simpa [prefixWord, tailWord_1259206, baseEnd_1259206] using wordTrace_append hprefix tailTrace_1259206
  have hstable : (prefixWord ++ tailWord_1259206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259206).length < 2 ^ (prefixWord ++ tailWord_1259206).sum := by decide
  have hdescent : baseEnd_1259206 < baseStart_1259206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259232 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 1, 4]
def baseStart_1259232 : Nat := 118140960795 + 1259232 * 2 ^ 59
def prefixEnd_1259232 : Nat := 4983230072969 + 3 ^ 40 * 1259232 * 2
def baseEnd_1259232 : Nat := 431060847681681655139269

theorem tailTrace_1259232 : CollatzResearch.WordTrace tailWord_1259232 prefixEnd_1259232 431060847681681655139269 := by
  unfold tailWord_1259232
  simp only [CollatzResearch.WordTrace]
  refine ⟨22963982087012499274465975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30618642782683332365954633 22963982087012499274465975)
  ·
    refine ⟨34445973130518748911698963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22963982087012499274465975 34445973130518748911698963)
    ·
      refine ⟨51668959695778123367548445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34445973130518748911698963 51668959695778123367548445)
      ·
        refine ⟨19375859885916796262830667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51668959695778123367548445 19375859885916796262830667)
        ·
          refine ⟨29063789828875194394246001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19375859885916796262830667 29063789828875194394246001)
          ·
            refine ⟨21797842371656395795684501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29063789828875194394246001 21797842371656395795684501)
            ·
              refine ⟨1021773861171393552922711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21797842371656395795684501 1021773861171393552922711)
              ·
                refine ⟨1532660791757090329384067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021773861171393552922711 1532660791757090329384067)
                ·
                  refine ⟨2298991187635635494076101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532660791757090329384067 2298991187635635494076101)
                  ·
                    refine ⟨431060847681681655139269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298991187635635494076101 431060847681681655139269)
                    ·
                      rfl

theorem cell22_1259232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_1259232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259232 prefixEnd_1259232 := by exact prefixLift 1259232
  have htrace : WordTrace (prefixWord ++ tailWord_1259232) baseStart_1259232 baseEnd_1259232 := by
    simpa [prefixWord, tailWord_1259232, baseEnd_1259232] using wordTrace_append hprefix tailTrace_1259232
  have hstable : (prefixWord ++ tailWord_1259232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259232).length < 2 ^ (prefixWord ++ tailWord_1259232).sum := by decide
  have hdescent : baseEnd_1259232 < baseStart_1259232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259258 : List Nat := [3, 1, 1, 1, 1, 3, 1, 11]
def baseStart_1259258 : Nat := 118140960795 + 1259258 * 2 ^ 59
def prefixEnd_1259258 : Nat := 4983230072969 + 3 ^ 40 * 1259258 * 2
def baseEnd_1259258 : Nat := 47896638668114028221021

theorem tailTrace_1259258 : CollatzResearch.WordTrace tailWord_1259258 prefixEnd_1259258 47896638668114028221021 := by
  unfold tailWord_1259258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11482228117982701247344607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30619274981287203326252285 11482228117982701247344607)
  ·
    refine ⟨17223342176974051871016911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11482228117982701247344607 17223342176974051871016911)
    ·
      refine ⟨25835013265461077806525367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17223342176974051871016911 25835013265461077806525367)
      ·
        refine ⟨38752519898191616709788051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25835013265461077806525367 38752519898191616709788051)
        ·
          refine ⟨58128779847287425064682077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38752519898191616709788051 58128779847287425064682077)
          ·
            refine ⟨21798292442732784399255779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58128779847287425064682077 21798292442732784399255779)
            ·
              refine ⟨32697438664099176598883669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21798292442732784399255779 32697438664099176598883669)
              ·
                refine ⟨47896638668114028221021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32697438664099176598883669 47896638668114028221021)
                ·
                  rfl

theorem cell22_1259258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_1259258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259258 prefixEnd_1259258 := by exact prefixLift 1259258
  have htrace : WordTrace (prefixWord ++ tailWord_1259258) baseStart_1259258 baseEnd_1259258 := by
    simpa [prefixWord, tailWord_1259258, baseEnd_1259258] using wordTrace_append hprefix tailTrace_1259258
  have hstable : (prefixWord ++ tailWord_1259258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259258).length < 2 ^ (prefixWord ++ tailWord_1259258).sum := by decide
  have hdescent : baseEnd_1259258 < baseStart_1259258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259273 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_1259273 : Nat := 118140960795 + 1259273 * 2 ^ 59
def prefixEnd_1259273 : Nat := 4983230072969 + 3 ^ 40 * 1259273 * 2
def baseEnd_1259273 : Nat := 431074882819571214864143

theorem tailTrace_1259273 : CollatzResearch.WordTrace tailWord_1259273 prefixEnd_1259273 431074882819571214864143 := by
  unfold tailWord_1259273
  simp only [CollatzResearch.WordTrace]
  refine ⟨45929459566876462551174473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30619639711250975034116315 45929459566876462551174473)
  ·
    refine ⟨34447094675157346913380855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45929459566876462551174473 34447094675157346913380855)
    ·
      refine ⟨51670642012736020370071283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34447094675157346913380855 51670642012736020370071283)
      ·
        refine ⟨77505963019104030555106925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51670642012736020370071283 77505963019104030555106925)
        ·
          refine ⟨29064736132164011458165097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77505963019104030555106925 29064736132164011458165097)
          ·
            refine ⟨21798552099123008593623823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29064736132164011458165097 21798552099123008593623823)
            ·
              refine ⟨32697828148684512890435735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21798552099123008593623823 32697828148684512890435735)
              ·
                refine ⟨49046742223026769335653603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32697828148684512890435735 49046742223026769335653603)
                ·
                  refine ⟨73570113334540154003480405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49046742223026769335653603 73570113334540154003480405)
                  ·
                    refine ⟨431074882819571214864143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73570113334540154003480405 431074882819571214864143)
                    ·
                      rfl

theorem cell22_1259273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_1259273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259273 prefixEnd_1259273 := by exact prefixLift 1259273
  have htrace : WordTrace (prefixWord ++ tailWord_1259273) baseStart_1259273 baseEnd_1259273 := by
    simpa [prefixWord, tailWord_1259273, baseEnd_1259273] using wordTrace_append hprefix tailTrace_1259273
  have hstable : (prefixWord ++ tailWord_1259273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259273).length < 2 ^ (prefixWord ++ tailWord_1259273).sum := by decide
  have hdescent : baseEnd_1259273 < baseStart_1259273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259275 : List Nat := [1, 1, 1, 1, 5, 1, 6, 6]
def baseStart_1259275 : Nat := 118140960795 + 1259275 * 2 ^ 59
def prefixEnd_1259275 : Nat := 4983230072969 + 3 ^ 40 * 1259275 * 2
def baseEnd_1259275 : Nat := 47897285273382652923793

theorem tailTrace_1259275 : CollatzResearch.WordTrace tailWord_1259275 prefixEnd_1259275 47897285273382652923793 := by
  unfold tailWord_1259275
  simp only [CollatzResearch.WordTrace]
  refine ⟨45929532512869216892747279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30619688341912811261831519 45929532512869216892747279)
  ·
    refine ⟨68894298769303825339120919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45929532512869216892747279 68894298769303825339120919)
    ·
      refine ⟨103341448153955738008681379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68894298769303825339120919 103341448153955738008681379)
      ·
        refine ⟨155012172230933607013022069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103341448153955738008681379 155012172230933607013022069)
        ·
          refine ⟨14532391146650025657470819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155012172230933607013022069 14532391146650025657470819)
          ·
            refine ⟨21798586719975038486206229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14532391146650025657470819 21798586719975038486206229)
            ·
              refine ⟨1021808752498829929040917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21798586719975038486206229 1021808752498829929040917)
              ·
                refine ⟨47897285273382652923793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1021808752498829929040917 47897285273382652923793)
                ·
                  rfl

theorem cell22_1259275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 6].length) (baseStart_1259275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259275 prefixEnd_1259275 := by exact prefixLift 1259275
  have htrace : WordTrace (prefixWord ++ tailWord_1259275) baseStart_1259275 baseEnd_1259275 := by
    simpa [prefixWord, tailWord_1259275, baseEnd_1259275] using wordTrace_append hprefix tailTrace_1259275
  have hstable : (prefixWord ++ tailWord_1259275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259275).length < 2 ^ (prefixWord ++ tailWord_1259275).sum := by decide
  have hdescent : baseEnd_1259275 < baseStart_1259275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259365 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 6]
def baseStart_1259365 : Nat := 118140960795 + 1259365 * 2 ^ 59
def prefixEnd_1259365 : Nat := 4983230072969 + 3 ^ 40 * 1259365 * 2
def baseEnd_1259365 : Nat := 143702125433237880521287

theorem tailTrace_1259365 : CollatzResearch.WordTrace tailWord_1259365 prefixEnd_1259365 143702125433237880521287 := by
  unfold tailWord_1259365
  simp only [CollatzResearch.WordTrace]
  refine ⟨45932815082543162263523549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30621876721695441509015699 45932815082543162263523549)
  ·
    refine ⟨17224805655953685848821331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45932815082543162263523549 17224805655953685848821331)
    ·
      refine ⟨25837208483930528773231997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17224805655953685848821331 25837208483930528773231997)
      ·
        refine ⟨9688953181473948289961999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25837208483930528773231997 9688953181473948289961999)
        ·
          refine ⟨14533429772210922434942999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9688953181473948289961999 14533429772210922434942999)
          ·
            refine ⟨21800144658316383652414499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14533429772210922434942999 21800144658316383652414499)
            ·
              refine ⟨32700216987474575478621749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21800144658316383652414499 32700216987474575478621749)
              ·
                refine ⟨3065645342575741451120789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32700216987474575478621749 3065645342575741451120789)
                ·
                  refine ⟨143702125433237880521287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3065645342575741451120789 143702125433237880521287)
                  ·
                    rfl

theorem cell22_1259365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_1259365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259365 prefixEnd_1259365 := by exact prefixLift 1259365
  have htrace : WordTrace (prefixWord ++ tailWord_1259365) baseStart_1259365 baseEnd_1259365 := by
    simpa [prefixWord, tailWord_1259365, baseEnd_1259365] using wordTrace_append hprefix tailTrace_1259365
  have hstable : (prefixWord ++ tailWord_1259365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259365).length < 2 ^ (prefixWord ++ tailWord_1259365).sum := by decide
  have hdescent : baseEnd_1259365 < baseStart_1259365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259397 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_1259397 : Nat := 118140960795 + 1259397 * 2 ^ 59
def prefixEnd_1259397 : Nat := 4983230072969 + 3 ^ 40 * 1259397 * 2
def baseEnd_1259397 : Nat := 431117330553676224763763

theorem tailTrace_1259397 : CollatzResearch.WordTrace tailWord_1259397 prefixEnd_1259397 431117330553676224763763 := by
  unfold tailWord_1259397
  simp only [CollatzResearch.WordTrace]
  refine ⟨45933982218427231728688445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30622654812284821152458963 45933982218427231728688445)
  ·
    refine ⟨17225243331910211898258167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45933982218427231728688445 17225243331910211898258167)
    ·
      refine ⟨25837864997865317847387251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17225243331910211898258167 25837864997865317847387251)
      ·
        refine ⟨38756797496797976771080877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25837864997865317847387251 38756797496797976771080877)
        ·
          refine ⟨14533799061299241289155329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38756797496797976771080877 14533799061299241289155329)
          ·
            refine ⟨10900349295974430966866497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14533799061299241289155329 10900349295974430966866497)
            ·
              refine ⟨8175261971980823225149873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10900349295974430966866497 8175261971980823225149873)
              ·
                refine ⟨6131446478985617418862405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8175261971980823225149873 6131446478985617418862405)
                ·
                  refine ⟨1149646214809803266036701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6131446478985617418862405 1149646214809803266036701)
                  ·
                    refine ⟨431117330553676224763763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149646214809803266036701 431117330553676224763763)
                    ·
                      rfl

theorem cell22_1259397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_1259397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259397 prefixEnd_1259397 := by exact prefixLift 1259397
  have htrace : WordTrace (prefixWord ++ tailWord_1259397) baseStart_1259397 baseEnd_1259397 := by
    simpa [prefixWord, tailWord_1259397, baseEnd_1259397] using wordTrace_append hprefix tailTrace_1259397
  have hstable : (prefixWord ++ tailWord_1259397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259397).length < 2 ^ (prefixWord ++ tailWord_1259397).sum := by decide
  have hdescent : baseEnd_1259397 < baseStart_1259397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259455 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 9]
def baseStart_1259455 : Nat := 118140960795 + 1259455 * 2 ^ 59
def prefixEnd_1259455 : Nat := 4983230072969 + 3 ^ 40 * 1259455 * 2
def baseEnd_1259455 : Nat := 143712395046327802271195

theorem tailTrace_1259455 : CollatzResearch.WordTrace tailWord_1259455 prefixEnd_1259455 143712395046327802271195 := by
  unfold tailWord_1259455
  simp only [CollatzResearch.WordTrace]
  refine ⟨45936097652217107634299819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30624065101478071756199879 45936097652217107634299819)
  ·
    refine ⟨68904146478325661451449729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45936097652217107634299819 68904146478325661451449729)
    ·
      refine ⟨51678109858744246088587297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68904146478325661451449729 51678109858744246088587297)
      ·
        refine ⟨38758582394058184566440473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51678109858744246088587297 38758582394058184566440473)
        ·
          refine ⟨29068936795543638424830355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38758582394058184566440473 29068936795543638424830355)
          ·
            refine ⟨43603405193315457637245533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29068936795543638424830355 43603405193315457637245533)
            ·
              refine ⟨16351276947493296613967075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43603405193315457637245533 16351276947493296613967075)
              ·
                refine ⟨24526915421239944920950613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16351276947493296613967075 24526915421239944920950613)
                ·
                  refine ⟨143712395046327802271195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24526915421239944920950613 143712395046327802271195)
                  ·
                    rfl

theorem cell22_1259455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 9].length) (baseStart_1259455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259455 prefixEnd_1259455 := by exact prefixLift 1259455
  have htrace : WordTrace (prefixWord ++ tailWord_1259455) baseStart_1259455 baseEnd_1259455 := by
    simpa [prefixWord, tailWord_1259455, baseEnd_1259455] using wordTrace_append hprefix tailTrace_1259455
  have hstable : (prefixWord ++ tailWord_1259455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259455).length < 2 ^ (prefixWord ++ tailWord_1259455).sum := by decide
  have hdescent : baseEnd_1259455 < baseStart_1259455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259489 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 5]
def baseStart_1259489 : Nat := 118140960795 + 1259489 * 2 ^ 59
def prefixEnd_1259489 : Nat := 4983230072969 + 3 ^ 40 * 1259489 * 2
def baseEnd_1259489 : Nat := 143716274677939550487827

theorem tailTrace_1259489 : CollatzResearch.WordTrace tailWord_1259489 prefixEnd_1259489 143716274677939550487827 := by
  unfold tailWord_1259489
  simp only [CollatzResearch.WordTrace]
  refine ⟨45937337734093931441037521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30624891822729287627358347 45937337734093931441037521)
  ·
    refine ⟨34453003300570448580778141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45937337734093931441037521 34453003300570448580778141)
    ·
      refine ⟨12919876237713918217791803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34453003300570448580778141 12919876237713918217791803)
      ·
        refine ⟨19379814356570877326687705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12919876237713918217791803 19379814356570877326687705)
        ·
          refine ⟨14534860767428157995015779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19379814356570877326687705 14534860767428157995015779)
          ·
            refine ⟨21802291151142236992523669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14534860767428157995015779 21802291151142236992523669)
            ·
              refine ⟨1021982397709792359024547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21802291151142236992523669 1021982397709792359024547)
              ·
                refine ⟨1532973596564688538536821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021982397709792359024547 1532973596564688538536821)
                ·
                  refine ⟨143716274677939550487827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1532973596564688538536821 143716274677939550487827)
                  ·
                    rfl

theorem cell22_1259489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_1259489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259489 prefixEnd_1259489 := by exact prefixLift 1259489
  have htrace : WordTrace (prefixWord ++ tailWord_1259489) baseStart_1259489 baseEnd_1259489 := by
    simpa [prefixWord, tailWord_1259489, baseEnd_1259489] using wordTrace_append hprefix tailTrace_1259489
  have hstable : (prefixWord ++ tailWord_1259489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259489).length < 2 ^ (prefixWord ++ tailWord_1259489).sum := by decide
  have hdescent : baseEnd_1259489 < baseStart_1259489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259532 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1259532 : Nat := 118140960795 + 1259532 * 2 ^ 59
def prefixEnd_1259532 : Nat := 4983230072969 + 3 ^ 40 * 1259532 * 2
def baseEnd_1259532 : Nat := 431163543812580872638349

theorem tailTrace_1259532 : CollatzResearch.WordTrace tailWord_1259532 prefixEnd_1259532 431163543812580872638349 := by
  unfold tailWord_1259532
  simp only [CollatzResearch.WordTrace]
  refine ⟨22969453036469074892426425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30625937381958766523235233 22969453036469074892426425)
  ·
    refine ⟨17227089777351806169319819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22969453036469074892426425 17227089777351806169319819)
    ·
      refine ⟨25840634666027709253979729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17227089777351806169319819 25840634666027709253979729)
      ·
        refine ⟨19380475999520781940484797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25840634666027709253979729 19380475999520781940484797)
        ·
          refine ⟨7267678499820293227681799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19380475999520781940484797 7267678499820293227681799)
          ·
            refine ⟨10901517749730439841522699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7267678499820293227681799 10901517749730439841522699)
            ·
              refine ⟨16352276624595659762284049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10901517749730439841522699 16352276624595659762284049)
              ·
                refine ⟨12264207468446744821713037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16352276624595659762284049 12264207468446744821713037)
                ·
                  refine ⟨4599077800667529308142389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12264207468446744821713037 4599077800667529308142389)
                  ·
                    refine ⟨431163543812580872638349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4599077800667529308142389 431163543812580872638349)
                    ·
                      rfl

theorem cell22_1259532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1259532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259532 prefixEnd_1259532 := by exact prefixLift 1259532
  have htrace : WordTrace (prefixWord ++ tailWord_1259532) baseStart_1259532 baseEnd_1259532 := by
    simpa [prefixWord, tailWord_1259532, baseEnd_1259532] using wordTrace_append hprefix tailTrace_1259532
  have hstable : (prefixWord ++ tailWord_1259532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259532).length < 2 ^ (prefixWord ++ tailWord_1259532).sum := by decide
  have hdescent : baseEnd_1259532 < baseStart_1259532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259549 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1259549 : Nat := 118140960795 + 1259549 * 2 ^ 59
def prefixEnd_1259549 : Nat := 4983230072969 + 3 ^ 40 * 1259549 * 2
def baseEnd_1259549 : Nat := 431169363259998494963297

theorem tailTrace_1259549 : CollatzResearch.WordTrace tailWord_1259549 prefixEnd_1259549 431169363259998494963297 := by
  unfold tailWord_1259549
  simp only [CollatzResearch.WordTrace]
  refine ⟨45939526113876561688221701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30626350742584374458814467 45939526113876561688221701)
  ·
    refine ⟨8613661146351855316541569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45939526113876561688221701 8613661146351855316541569)
    ·
      refine ⟨6460245859763891487406177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8613661146351855316541569 6460245859763891487406177)
      ·
        refine ⟨4845184394822918615554633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6460245859763891487406177 4845184394822918615554633)
        ·
          refine ⟨3633888296117188961665975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4845184394822918615554633 3633888296117188961665975)
          ·
            refine ⟨5450832444175783442498963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633888296117188961665975 5450832444175783442498963)
            ·
              refine ⟨8176248666263675163748445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450832444175783442498963 8176248666263675163748445)
              ·
                refine ⟨3066093249848878186405667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8176248666263675163748445 3066093249848878186405667)
                ·
                  refine ⟨4599139874773317279608501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066093249848878186405667 4599139874773317279608501)
                  ·
                    refine ⟨431169363259998494963297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4599139874773317279608501 431169363259998494963297)
                    ·
                      rfl

theorem cell22_1259549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1259549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259549 prefixEnd_1259549 := by exact prefixLift 1259549
  have htrace : WordTrace (prefixWord ++ tailWord_1259549) baseStart_1259549 baseEnd_1259549 := by
    simpa [prefixWord, tailWord_1259549, baseEnd_1259549] using wordTrace_append hprefix tailTrace_1259549
  have hstable : (prefixWord ++ tailWord_1259549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259549).length < 2 ^ (prefixWord ++ tailWord_1259549).sum := by decide
  have hdescent : baseEnd_1259549 < baseStart_1259549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259592 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1259592 : Nat := 118140960795 + 1259592 * 2 ^ 59
def prefixEnd_1259592 : Nat := 4983230072969 + 3 ^ 40 * 1259592 * 2
def baseEnd_1259592 : Nat := 431184083038760716138165

theorem tailTrace_1259592 : CollatzResearch.WordTrace tailWord_1259592 prefixEnd_1259592 431184083038760716138165 := by
  unfold tailWord_1259592
  simp only [CollatzResearch.WordTrace]
  refine ⟨22970547226360390016018515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30627396301813853354691353 22970547226360390016018515)
  ·
    refine ⟨34455820839540585024027773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22970547226360390016018515 34455820839540585024027773)
    ·
      refine ⟨12920932814827719384010415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34455820839540585024027773 12920932814827719384010415)
      ·
        refine ⟨19381399222241579076015623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12920932814827719384010415 19381399222241579076015623)
        ·
          refine ⟨29072098833362368614023435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19381399222241579076015623 29072098833362368614023435)
          ·
            refine ⟨43608148250043552921035153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29072098833362368614023435 43608148250043552921035153)
            ·
              refine ⟨32706111187532664690776365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43608148250043552921035153 32706111187532664690776365)
              ·
                refine ⟨12264791695324749259041137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32706111187532664690776365 12264791695324749259041137)
                ·
                  refine ⟨9198593771493561944280853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12264791695324749259041137 9198593771493561944280853)
                  ·
                    refine ⟨431184083038760716138165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9198593771493561944280853 431184083038760716138165)
                    ·
                      rfl

theorem cell22_1259592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1259592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259592 prefixEnd_1259592 := by exact prefixLift 1259592
  have htrace : WordTrace (prefixWord ++ tailWord_1259592) baseStart_1259592 baseEnd_1259592 := by
    simpa [prefixWord, tailWord_1259592, baseEnd_1259592] using wordTrace_append hprefix tailTrace_1259592
  have hstable : (prefixWord ++ tailWord_1259592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259592).length < 2 ^ (prefixWord ++ tailWord_1259592).sum := by decide
  have hdescent : baseEnd_1259592 < baseStart_1259592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259613 : List Nat := [1, 4, 4, 1, 1, 3, 2, 6]
def baseStart_1259613 : Nat := 118140960795 + 1259613 * 2 ^ 59
def prefixEnd_1259613 : Nat := 4983230072969 + 3 ^ 40 * 1259613 * 2
def baseEnd_1259613 : Nat := 47910141307547073484789

theorem tailTrace_1259613 : CollatzResearch.WordTrace tailWord_1259613 prefixEnd_1259613 47910141307547073484789 := by
  unfold tailWord_1259613
  simp only [CollatzResearch.WordTrace]
  refine ⟨45941860385644700618551493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30627906923763133745700995 45941860385644700618551493)
  ·
    refine ⟨8614098822308381365978405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45941860385644700618551493 8614098822308381365978405)
    ·
      refine ⟨1615143529182821506120951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8614098822308381365978405 1615143529182821506120951)
      ·
        refine ⟨2422715293774232259181427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615143529182821506120951 2422715293774232259181427)
        ·
          refine ⟨3634072940661348388772141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422715293774232259181427 3634072940661348388772141)
          ·
            refine ⟨1362777352748005645789553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3634072940661348388772141 1362777352748005645789553)
            ·
              refine ⟨1022083014561004234342165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362777352748005645789553 1022083014561004234342165)
              ·
                refine ⟨47910141307547073484789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1022083014561004234342165 47910141307547073484789)
                ·
                  rfl

theorem cell22_1259613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 6].length) (baseStart_1259613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259613 prefixEnd_1259613 := by exact prefixLift 1259613
  have htrace : WordTrace (prefixWord ++ tailWord_1259613) baseStart_1259613 baseEnd_1259613 := by
    simpa [prefixWord, tailWord_1259613, baseEnd_1259613] using wordTrace_append hprefix tailTrace_1259613
  have hstable : (prefixWord ++ tailWord_1259613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259613).length < 2 ^ (prefixWord ++ tailWord_1259613).sum := by decide
  have hdescent : baseEnd_1259613 < baseStart_1259613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259628 : List Nat := [2, 2, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_1259628 : Nat := 118140960795 + 1259628 * 2 ^ 59
def prefixEnd_1259628 : Nat := 4983230072969 + 3 ^ 40 * 1259628 * 2
def baseEnd_1259628 : Nat := 431196406574468622238055

theorem tailTrace_1259628 : CollatzResearch.WordTrace tailWord_1259628 prefixEnd_1259628 431196406574468622238055 := by
  unfold tailWord_1259628
  simp only [CollatzResearch.WordTrace]
  refine ⟨22971203740295179090173769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30628271653726905453565025 22971203740295179090173769)
  ·
    refine ⟨17228402805221384317630327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22971203740295179090173769 17228402805221384317630327)
    ·
      refine ⟨25842604207832076476445491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17228402805221384317630327 25842604207832076476445491)
      ·
        refine ⟨38763906311748114714668237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25842604207832076476445491 38763906311748114714668237)
        ·
          refine ⟨14536464866905543018000589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38763906311748114714668237 14536464866905543018000589)
          ·
            refine ⟨5451174325089578631750221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14536464866905543018000589 5451174325089578631750221)
            ·
              refine ⟨2044190371908591986906333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5451174325089578631750221 2044190371908591986906333)
              ·
                refine ⟨766571389465721995089875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2044190371908591986906333 766571389465721995089875)
                ·
                  refine ⟨1149857084198582992634813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766571389465721995089875 1149857084198582992634813)
                  ·
                    refine ⟨431196406574468622238055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149857084198582992634813 431196406574468622238055)
                    ·
                      rfl

theorem cell22_1259628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_1259628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259628 prefixEnd_1259628 := by exact prefixLift 1259628
  have htrace : WordTrace (prefixWord ++ tailWord_1259628) baseStart_1259628 baseEnd_1259628 := by
    simpa [prefixWord, tailWord_1259628, baseEnd_1259628] using wordTrace_append hprefix tailTrace_1259628
  have hstable : (prefixWord ++ tailWord_1259628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259628).length < 2 ^ (prefixWord ++ tailWord_1259628).sum := by decide
  have hdescent : baseEnd_1259628 < baseStart_1259628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259645 : List Nat := [1, 4, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_1259645 : Nat := 118140960795 + 1259645 * 2 ^ 59
def prefixEnd_1259645 : Nat := 4983230072969 + 3 ^ 40 * 1259645 * 2
def baseEnd_1259645 : Nat := 431202226021886244563003

theorem tailTrace_1259645 : CollatzResearch.WordTrace tailWord_1259645 prefixEnd_1259645 431202226021886244563003 := by
  unfold tailWord_1259645
  simp only [CollatzResearch.WordTrace]
  refine ⟨45943027521528770083716389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30628685014352513389144259 45943027521528770083716389)
  ·
    refine ⟨8614317660286644390696823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45943027521528770083716389 8614317660286644390696823)
    ·
      refine ⟨12921476490429966586045235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8614317660286644390696823 12921476490429966586045235)
      ·
        refine ⟨19382214735644949879067853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12921476490429966586045235 19382214735644949879067853)
        ·
          refine ⟨7268330525866856204650445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19382214735644949879067853 7268330525866856204650445)
          ·
            refine ⟨2725623947200071076743917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7268330525866856204650445 2725623947200071076743917)
            ·
              refine ⟨1022108980200026653778969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2725623947200071076743917 1022108980200026653778969)
              ·
                refine ⟨766581735150019990334227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022108980200026653778969 766581735150019990334227)
                ·
                  refine ⟨1149872602725029985501341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766581735150019990334227 1149872602725029985501341)
                  ·
                    refine ⟨431202226021886244563003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149872602725029985501341 431202226021886244563003)
                    ·
                      rfl

theorem cell22_1259645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_1259645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259645 prefixEnd_1259645 := by exact prefixLift 1259645
  have htrace : WordTrace (prefixWord ++ tailWord_1259645) baseStart_1259645 baseEnd_1259645 := by
    simpa [prefixWord, tailWord_1259645, baseEnd_1259645] using wordTrace_append hprefix tailTrace_1259645
  have hstable : (prefixWord ++ tailWord_1259645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259645).length < 2 ^ (prefixWord ++ tailWord_1259645).sum := by decide
  have hdescent : baseEnd_1259645 < baseStart_1259645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259658 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_1259658 : Nat := 118140960795 + 1259658 * 2 ^ 59
def prefixEnd_1259658 : Nat := 4983230072969 + 3 ^ 40 * 1259658 * 2
def baseEnd_1259658 : Nat := 143735558729186181329321

theorem tailTrace_1259658 : CollatzResearch.WordTrace tailWord_1259658 prefixEnd_1259658 143735558729186181329321 := by
  unfold tailWord_1259658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11485875417620418325984907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30629001113654448869293085 11485875417620418325984907)
  ·
    refine ⟨17228813126430627488977361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11485875417620418325984907 17228813126430627488977361)
    ·
      refine ⟨12921609844822970616733021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17228813126430627488977361 12921609844822970616733021)
      ·
        refine ⟨4845603691808613981274883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12921609844822970616733021 4845603691808613981274883)
        ·
          refine ⟨7268405537712920971912325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845603691808613981274883 7268405537712920971912325)
          ·
            refine ⟨1362826038321172682233561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7268405537712920971912325 1362826038321172682233561)
            ·
              refine ⟨1022119528740879511675171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362826038321172682233561 1022119528740879511675171)
              ·
                refine ⟨1533179293111319267512757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022119528740879511675171 1533179293111319267512757)
                ·
                  refine ⟨143735558729186181329321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1533179293111319267512757 143735558729186181329321)
                  ·
                    rfl

theorem cell22_1259658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_1259658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259658 prefixEnd_1259658 := by exact prefixLift 1259658
  have htrace : WordTrace (prefixWord ++ tailWord_1259658) baseStart_1259658 baseEnd_1259658 := by
    simpa [prefixWord, tailWord_1259658, baseEnd_1259658] using wordTrace_append hprefix tailTrace_1259658
  have hstable : (prefixWord ++ tailWord_1259658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259658).length < 2 ^ (prefixWord ++ tailWord_1259658).sum := by decide
  have hdescent : baseEnd_1259658 < baseStart_1259658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259671 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 3, 4]
def baseStart_1259671 : Nat := 118140960795 + 1259671 * 2 ^ 59
def prefixEnd_1259671 : Nat := 4983230072969 + 3 ^ 40 * 1259671 * 2
def baseEnd_1259671 : Nat := 431211126353230843412923

theorem tailTrace_1259671 : CollatzResearch.WordTrace tailWord_1259671 prefixEnd_1259671 431211126353230843412923 := by
  unfold tailWord_1259671
  simp only [CollatzResearch.WordTrace]
  refine ⟨45943975819434576524162867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30629317212956384349441911 45943975819434576524162867)
  ·
    refine ⟨68915963729151864786244301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45943975819434576524162867 68915963729151864786244301)
    ·
      refine ⟨25843486398431949294841613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68915963729151864786244301 25843486398431949294841613)
      ·
        refine ⟨9691307399411980985565605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25843486398431949294841613 9691307399411980985565605)
        ·
          refine ⟨1817120137389746434793551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9691307399411980985565605 1817120137389746434793551)
          ·
            refine ⟨2725680206084619652190327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817120137389746434793551 2725680206084619652190327)
            ·
              refine ⟨4088520309126929478285491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725680206084619652190327 4088520309126929478285491)
              ·
                refine ⟨6132780463690394217428237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088520309126929478285491 6132780463690394217428237)
                ·
                  refine ⟨2299792673883897831535589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6132780463690394217428237 2299792673883897831535589)
                  ·
                    refine ⟨431211126353230843412923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2299792673883897831535589 431211126353230843412923)
                    ·
                      rfl

theorem cell22_1259671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_1259671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259671 prefixEnd_1259671 := by exact prefixLift 1259671
  have htrace : WordTrace (prefixWord ++ tailWord_1259671) baseStart_1259671 baseEnd_1259671 := by
    simpa [prefixWord, tailWord_1259671, baseEnd_1259671] using wordTrace_append hprefix tailTrace_1259671
  have hstable : (prefixWord ++ tailWord_1259671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259671).length < 2 ^ (prefixWord ++ tailWord_1259671).sum := by decide
  have hdescent : baseEnd_1259671 < baseStart_1259671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259703 : List Nat := [1, 1, 3, 1, 4, 2, 4, 2, 4]
def baseStart_1259703 : Nat := 118140960795 + 1259703 * 2 ^ 59
def prefixEnd_1259703 : Nat := 4983230072969 + 3 ^ 40 * 1259703 * 2
def baseEnd_1259703 : Nat := 143740693535731142204275

theorem tailTrace_1259703 : CollatzResearch.WordTrace tailWord_1259703 prefixEnd_1259703 143740693535731142204275 := by
  unfold tailWord_1259703
  simp only [CollatzResearch.WordTrace]
  refine ⟨45945142955318645989327763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30630095303545763992885175 45945142955318645989327763)
  ·
    refine ⟨68917714432977968983991645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45945142955318645989327763 68917714432977968983991645)
    ·
      refine ⟨25844142912366738368996867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68917714432977968983991645 25844142912366738368996867)
      ·
        refine ⟨38766214368550107553495301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25844142912366738368996867 38766214368550107553495301)
        ·
          refine ⟨7268665194103145166280369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38766214368550107553495301 7268665194103145166280369)
          ·
            refine ⟨5451498895577358874710277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7268665194103145166280369 5451498895577358874710277)
            ·
              refine ⟨1022156042920754789008177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5451498895577358874710277 1022156042920754789008177)
              ·
                refine ⟨766617032190566091756133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022156042920754789008177 766617032190566091756133)
                ·
                  refine ⟨143740693535731142204275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766617032190566091756133 143740693535731142204275)
                  ·
                    rfl

theorem cell22_1259703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 4].length) (baseStart_1259703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259703 prefixEnd_1259703 := by exact prefixLift 1259703
  have htrace : WordTrace (prefixWord ++ tailWord_1259703) baseStart_1259703 baseEnd_1259703 := by
    simpa [prefixWord, tailWord_1259703, baseEnd_1259703] using wordTrace_append hprefix tailTrace_1259703
  have hstable : (prefixWord ++ tailWord_1259703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259703).length < 2 ^ (prefixWord ++ tailWord_1259703).sum := by decide
  have hdescent : baseEnd_1259703 < baseStart_1259703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259763 : List Nat := [1, 1, 1, 2, 2, 4, 1, 6, 1, 3]
def baseStart_1259763 : Nat := 118140960795 + 1259763 * 2 ^ 59
def prefixEnd_1259763 : Nat := 4983230072969 + 3 ^ 40 * 1259763 * 2
def baseEnd_1259763 : Nat := 431242619833373270112641

theorem tailTrace_1259763 : CollatzResearch.WordTrace tailWord_1259763 prefixEnd_1259763 431242619833373270112641 := by
  unfold tailWord_1259763
  simp only [CollatzResearch.WordTrace]
  refine ⟨45947331335101276236511943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30631554223400850824341295 45947331335101276236511943)
  ·
    refine ⟨68920997002651914354767915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45947331335101276236511943 68920997002651914354767915)
    ·
      refine ⟨103381495503977871532151873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68920997002651914354767915 103381495503977871532151873)
      ·
        refine ⟨77536121627983403649113905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103381495503977871532151873 77536121627983403649113905)
        ·
          refine ⟨58152091220987552736835429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77536121627983403649113905 58152091220987552736835429)
          ·
            refine ⟨10903517103935166138156643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58152091220987552736835429 10903517103935166138156643)
            ·
              refine ⟨16355275655902749207234965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10903517103935166138156643 16355275655902749207234965)
              ·
                refine ⟨766653546370441369089139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16355275655902749207234965 766653546370441369089139)
                ·
                  refine ⟨1149980319555662053633709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766653546370441369089139 1149980319555662053633709)
                  ·
                    refine ⟨431242619833373270112641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149980319555662053633709 431242619833373270112641)
                    ·
                      rfl

theorem cell22_1259763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 3].length) (baseStart_1259763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259763 prefixEnd_1259763 := by exact prefixLift 1259763
  have htrace : WordTrace (prefixWord ++ tailWord_1259763) baseStart_1259763 baseEnd_1259763 := by
    simpa [prefixWord, tailWord_1259763, baseEnd_1259763] using wordTrace_append hprefix tailTrace_1259763
  have hstable : (prefixWord ++ tailWord_1259763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259763).length < 2 ^ (prefixWord ++ tailWord_1259763).sum := by decide
  have hdescent : baseEnd_1259763 < baseStart_1259763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259836 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1259836 : Nat := 118140960795 + 1259836 * 2 ^ 59
def prefixEnd_1259836 : Nat := 4983230072969 + 3 ^ 40 * 1259836 * 2
def baseEnd_1259836 : Nat := 431267609225225413037417

theorem tailTrace_1259836 : CollatzResearch.WordTrace tailWord_1259836 prefixEnd_1259836 431267609225225413037417 := by
  unfold tailWord_1259836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22974996931918404851959681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30633329242557873135946241 22974996931918404851959681)
  ·
    refine ⟨17231247698938803638969761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22974996931918404851959681 17231247698938803638969761)
    ·
      refine ⟨12923435774204102729227321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17231247698938803638969761 12923435774204102729227321)
      ·
        refine ⟨9692576830653077046920491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12923435774204102729227321 9692576830653077046920491)
        ·
          refine ⟨14538865245979615570380737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9692576830653077046920491 14538865245979615570380737)
          ·
            refine ⟨10904148934484711677785553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14538865245979615570380737 10904148934484711677785553)
            ·
              refine ⟨8178111700863533758339165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10904148934484711677785553 8178111700863533758339165)
              ·
                refine ⟨3066791887823825159377187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8178111700863533758339165 3066791887823825159377187)
                ·
                  refine ⟨4600187831735737739065781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066791887823825159377187 4600187831735737739065781)
                  ·
                    refine ⟨431267609225225413037417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4600187831735737739065781 431267609225225413037417)
                    ·
                      rfl

theorem cell22_1259836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1259836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259836 prefixEnd_1259836 := by exact prefixLift 1259836
  have htrace : WordTrace (prefixWord ++ tailWord_1259836) baseStart_1259836 baseEnd_1259836 := by
    simpa [prefixWord, tailWord_1259836, baseEnd_1259836] using wordTrace_append hprefix tailTrace_1259836
  have hstable : (prefixWord ++ tailWord_1259836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259836).length < 2 ^ (prefixWord ++ tailWord_1259836).sum := by decide
  have hdescent : baseEnd_1259836 < baseStart_1259836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259872 : List Nat := [2, 1, 1, 3, 5, 2, 2, 2, 4]
def baseStart_1259872 : Nat := 118140960795 + 1259872 * 2 ^ 59
def prefixEnd_1259872 : Nat := 4983230072969 + 3 ^ 40 * 1259872 * 2
def baseEnd_1259872 : Nat := 143759977586977773045769

theorem tailTrace_1259872 : CollatzResearch.WordTrace tailWord_1259872 prefixEnd_1259872 143759977586977773045769 := by
  unfold tailWord_1259872
  simp only [CollatzResearch.WordTrace]
  refine ⟨22975653445853193926114935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30634204594470925234819913 22975653445853193926114935)
  ·
    refine ⟨34463480168779790889172403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22975653445853193926114935 34463480168779790889172403)
    ·
      refine ⟨51695220253169686333758605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34463480168779790889172403 51695220253169686333758605)
      ·
        refine ⟨19385707594938632375159477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51695220253169686333758605 19385707594938632375159477)
        ·
          refine ⟨1817410087025496785171201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19385707594938632375159477 1817410087025496785171201)
          ·
            refine ⟨1363057565269122588878401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1817410087025496785171201 1363057565269122588878401)
            ·
              refine ⟨1022293173951841941658801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363057565269122588878401 1022293173951841941658801)
              ·
                refine ⟨766719880463881456244101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022293173951841941658801 766719880463881456244101)
                ·
                  refine ⟨143759977586977773045769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766719880463881456244101 143759977586977773045769)
                  ·
                    rfl

theorem cell22_1259872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_1259872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259872 prefixEnd_1259872 := by exact prefixLift 1259872
  have htrace : WordTrace (prefixWord ++ tailWord_1259872) baseStart_1259872 baseEnd_1259872 := by
    simpa [prefixWord, tailWord_1259872, baseEnd_1259872] using wordTrace_append hprefix tailTrace_1259872
  have hstable : (prefixWord ++ tailWord_1259872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259872).length < 2 ^ (prefixWord ++ tailWord_1259872).sum := by decide
  have hdescent : baseEnd_1259872 < baseStart_1259872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259911 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 7]
def baseStart_1259911 : Nat := 118140960795 + 1259911 * 2 ^ 59
def prefixEnd_1259911 : Nat := 4983230072969 + 3 ^ 40 * 1259911 * 2
def baseEnd_1259911 : Nat := 143764427752650072470729

theorem tailTrace_1259911 : CollatzResearch.WordTrace tailWord_1259911 prefixEnd_1259911 143764427752650072470729 := by
  unfold tailWord_1259911
  simp only [CollatzResearch.WordTrace]
  refine ⟨45952729338565097512899587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30635152892376731675266391 45952729338565097512899587)
  ·
    refine ⟨68929094007847646269349381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45952729338565097512899587 68929094007847646269349381)
    ·
      refine ⟨12924205126471433675503009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68929094007847646269349381 12924205126471433675503009)
      ·
        refine ⟨9693153844853575256627257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12924205126471433675503009 9693153844853575256627257)
        ·
          refine ⟨7269865383640181442470443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9693153844853575256627257 7269865383640181442470443)
          ·
            refine ⟨10904798075460272163705665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269865383640181442470443 10904798075460272163705665)
            ·
              refine ⟨8178598556595204122779249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10904798075460272163705665 8178598556595204122779249)
              ·
                refine ⟨6133948917446403092084437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8178598556595204122779249 6133948917446403092084437)
                ·
                  refine ⟨143764427752650072470729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6133948917446403092084437 143764427752650072470729)
                  ·
                    rfl

theorem cell22_1259911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 7].length) (baseStart_1259911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259911 prefixEnd_1259911 := by exact prefixLift 1259911
  have htrace : WordTrace (prefixWord ++ tailWord_1259911) baseStart_1259911 baseEnd_1259911 := by
    simpa [prefixWord, tailWord_1259911, baseEnd_1259911] using wordTrace_append hprefix tailTrace_1259911
  have hstable : (prefixWord ++ tailWord_1259911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259911).length < 2 ^ (prefixWord ++ tailWord_1259911).sum := by decide
  have hdescent : baseEnd_1259911 < baseStart_1259911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259915 : List Nat := [1, 1, 1, 1, 4, 4, 1, 5, 1, 3]
def baseStart_1259915 : Nat := 118140960795 + 1259915 * 2 ^ 59
def prefixEnd_1259915 : Nat := 4983230072969 + 3 ^ 40 * 1259915 * 2
def baseEnd_1259915 : Nat := 431294652539695540312175

theorem tailTrace_1259915 : CollatzResearch.WordTrace tailWord_1259915 prefixEnd_1259915 431294652539695540312175 := by
  unfold tailWord_1259915
  simp only [CollatzResearch.WordTrace]
  refine ⟨45952875230550606196045199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30635250153700404130696799 45952875230550606196045199)
  ·
    refine ⟨68929312845825909294067799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45952875230550606196045199 68929312845825909294067799)
    ·
      refine ⟨103393969268738863941101699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68929312845825909294067799 103393969268738863941101699)
      ·
        refine ⟨155090953903108295911652549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103393969268738863941101699 155090953903108295911652549)
        ·
          refine ⟨29079553856832805483434853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155090953903108295911652549 29079553856832805483434853)
          ·
            refine ⟨5452416348156151028144035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29079553856832805483434853 5452416348156151028144035)
            ·
              refine ⟨8178624522234226542216053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452416348156151028144035 8178624522234226542216053)
              ·
                refine ⟨766746048959458738332755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8178624522234226542216053 766746048959458738332755)
                ·
                  refine ⟨1150119073439188107499133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766746048959458738332755 1150119073439188107499133)
                  ·
                    refine ⟨431294652539695540312175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150119073439188107499133 431294652539695540312175)
                    ·
                      rfl

theorem cell22_1259915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 3].length) (baseStart_1259915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259915 prefixEnd_1259915 := by exact prefixLift 1259915
  have htrace : WordTrace (prefixWord ++ tailWord_1259915) baseStart_1259915 baseEnd_1259915 := by
    simpa [prefixWord, tailWord_1259915, baseEnd_1259915] using wordTrace_append hprefix tailTrace_1259915
  have hstable : (prefixWord ++ tailWord_1259915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259915).length < 2 ^ (prefixWord ++ tailWord_1259915).sum := by decide
  have hdescent : baseEnd_1259915 < baseStart_1259915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259928 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 7]
def baseStart_1259928 : Nat := 118140960795 + 1259928 * 2 ^ 59
def prefixEnd_1259928 : Nat := 4983230072969 + 3 ^ 40 * 1259928 * 2
def baseEnd_1259928 : Nat := 143766367568455946579045

theorem tailTrace_1259928 : CollatzResearch.WordTrace tailWord_1259928 prefixEnd_1259928 143766367568455946579045 := by
  unfold tailWord_1259928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976674689751754708134219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30635566253002339610845625 22976674689751754708134219)
  ·
    refine ⟨34465012034627632062201329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22976674689751754708134219 34465012034627632062201329)
    ·
      refine ⟨25848759025970724046650997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34465012034627632062201329 25848759025970724046650997)
      ·
        refine ⟨2423321158684755379373531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25848759025970724046650997 2423321158684755379373531)
        ·
          refine ⟨3634981738027133069060297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423321158684755379373531 3634981738027133069060297)
          ·
            refine ⟨2726236303520349801795223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3634981738027133069060297 2726236303520349801795223)
            ·
              refine ⟨4089354455280524702692835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2726236303520349801795223 4089354455280524702692835)
              ·
                refine ⟨6134031682920787054039253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089354455280524702692835 6134031682920787054039253)
                ·
                  refine ⟨143766367568455946579045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6134031682920787054039253 143766367568455946579045)
                  ·
                    rfl

theorem cell22_1259928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_1259928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259928 prefixEnd_1259928 := by exact prefixLift 1259928
  have htrace : WordTrace (prefixWord ++ tailWord_1259928) baseStart_1259928 baseEnd_1259928 := by
    simpa [prefixWord, tailWord_1259928, baseEnd_1259928] using wordTrace_append hprefix tailTrace_1259928
  have hstable : (prefixWord ++ tailWord_1259928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259928).length < 2 ^ (prefixWord ++ tailWord_1259928).sum := by decide
  have hdescent : baseEnd_1259928 < baseStart_1259928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259943 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1259943 : Nat := 118140960795 + 1259943 * 2 ^ 59
def prefixEnd_1259943 : Nat := 4983230072969 + 3 ^ 40 * 1259943 * 2
def baseEnd_1259943 : Nat := 431304237511912800612089

theorem tailTrace_1259943 : CollatzResearch.WordTrace tailWord_1259943 prefixEnd_1259943 431304237511912800612089 := by
  unfold tailWord_1259943
  simp only [CollatzResearch.WordTrace]
  refine ⟨45953896474449166978064483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30635930982966111318709655 45953896474449166978064483)
  ·
    refine ⟨68930844711673750467096725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45953896474449166978064483 68930844711673750467096725)
    ·
      refine ⟨3231133345859707053145159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68930844711673750467096725 3231133345859707053145159)
      ·
        refine ⟨4846700018789560579717739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231133345859707053145159 4846700018789560579717739)
        ·
          refine ⟨7270050028184340869576609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846700018789560579717739 7270050028184340869576609)
          ·
            refine ⟨5452537521138255652182457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7270050028184340869576609 5452537521138255652182457)
            ·
              refine ⟨4089403140853691739136843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5452537521138255652182457 4089403140853691739136843)
              ·
                refine ⟨6134104711280537608705265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089403140853691739136843 6134104711280537608705265)
                ·
                  refine ⟨4600578533460403206528949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6134104711280537608705265 4600578533460403206528949)
                  ·
                    refine ⟨431304237511912800612089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4600578533460403206528949 431304237511912800612089)
                    ·
                      rfl

theorem cell22_1259943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1259943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259943 prefixEnd_1259943 := by exact prefixLift 1259943
  have htrace : WordTrace (prefixWord ++ tailWord_1259943) baseStart_1259943 baseEnd_1259943 := by
    simpa [prefixWord, tailWord_1259943, baseEnd_1259943] using wordTrace_append hprefix tailTrace_1259943
  have hstable : (prefixWord ++ tailWord_1259943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259943).length < 2 ^ (prefixWord ++ tailWord_1259943).sum := by decide
  have hdescent : baseEnd_1259943 < baseStart_1259943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259971 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 3, 5]
def baseStart_1259971 : Nat := 118140960795 + 1259971 * 2 ^ 59
def prefixEnd_1259971 : Nat := 4983230072969 + 3 ^ 40 * 1259971 * 2
def baseEnd_1259971 : Nat := 431313822484130060912003

theorem tailTrace_1259971 : CollatzResearch.WordTrace tailWord_1259971 prefixEnd_1259971 431313822484130060912003 := by
  unfold tailWord_1259971
  simp only [CollatzResearch.WordTrace]
  refine ⟨45954917718347727760083767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30636611812231818506722511 45954917718347727760083767)
  ·
    refine ⟨68932376577521591640125651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45954917718347727760083767 68932376577521591640125651)
    ·
      refine ⟨103398564866282387460188477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68932376577521591640125651 103398564866282387460188477)
      ·
        refine ⟨38774461824855895297570679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103398564866282387460188477 38774461824855895297570679)
        ·
          refine ⟨58161692737283842946356019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38774461824855895297570679 58161692737283842946356019)
          ·
            refine ⟨87242539105925764419534029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58161692737283842946356019 87242539105925764419534029)
            ·
              refine ⟨32715952164722161657325261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87242539105925764419534029 32715952164722161657325261)
              ·
                refine ⟨12268482061770810621496973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32715952164722161657325261 12268482061770810621496973)
                ·
                  refine ⟨4600680773164053983061365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12268482061770810621496973 4600680773164053983061365)
                  ·
                    refine ⟨431313822484130060912003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4600680773164053983061365 431313822484130060912003)
                    ·
                      rfl

theorem cell22_1259971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_1259971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1259971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1259971 prefixEnd_1259971 := by exact prefixLift 1259971
  have htrace : WordTrace (prefixWord ++ tailWord_1259971) baseStart_1259971 baseEnd_1259971 := by
    simpa [prefixWord, tailWord_1259971, baseEnd_1259971] using wordTrace_append hprefix tailTrace_1259971
  have hstable : (prefixWord ++ tailWord_1259971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259971).length < 2 ^ (prefixWord ++ tailWord_1259971).sum := by decide
  have hdescent : baseEnd_1259971 < baseStart_1259971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260052 : List Nat := [2, 4, 3, 1, 1, 3, 1, 7]
def baseStart_1260052 : Nat := 118140960795 + 1260052 * 2 ^ 59
def prefixEnd_1260052 : Nat := 4983230072969 + 3 ^ 40 * 1260052 * 2
def baseEnd_1260052 : Nat := 47926838937719205515195

theorem tailTrace_1260052 : CollatzResearch.WordTrace tailWord_1260052 prefixEnd_1260052 47926838937719205515195 := by
  unfold tailWord_1260052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22978936015527139296891205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30638581354036185729188273 22978936015527139296891205)
  ·
    refine ⟨4308550502911338618167101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22978936015527139296891205 4308550502911338618167101)
    ·
      refine ⟨1615706438591751981812663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4308550502911338618167101 1615706438591751981812663)
      ·
        refine ⟨2423559657887627972718995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615706438591751981812663 2423559657887627972718995)
        ·
          refine ⟨3635339486831441959078493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423559657887627972718995 3635339486831441959078493)
          ·
            refine ⟨1363252307561790734654435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3635339486831441959078493 1363252307561790734654435)
            ·
              refine ⟨2044878461342686101981653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363252307561790734654435 2044878461342686101981653)
              ·
                refine ⟨47926838937719205515195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2044878461342686101981653 47926838937719205515195)
                ·
                  rfl

theorem cell22_1260052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 7].length) (baseStart_1260052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260052 prefixEnd_1260052 := by exact prefixLift 1260052
  have htrace : WordTrace (prefixWord ++ tailWord_1260052) baseStart_1260052 baseEnd_1260052 := by
    simpa [prefixWord, tailWord_1260052, baseEnd_1260052] using wordTrace_append hprefix tailTrace_1260052
  have hstable : (prefixWord ++ tailWord_1260052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260052).length < 2 ^ (prefixWord ++ tailWord_1260052).sum := by decide
  have hdescent : baseEnd_1260052 < baseStart_1260052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260071 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1260071 : Nat := 118140960795 + 1260071 * 2 ^ 59
def prefixEnd_1260071 : Nat := 4983230072969 + 3 ^ 40 * 1260071 * 2
def baseEnd_1260071 : Nat := 431348054527763133411697

theorem tailTrace_1260071 : CollatzResearch.WordTrace tailWord_1260071 prefixEnd_1260071 431348054527763133411697 := by
  unfold tailWord_1260071
  simp only [CollatzResearch.WordTrace]
  refine ⟨45958565017985444838724067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30639043345323629892482711 45958565017985444838724067)
  ·
    refine ⟨68937847526978167258086101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45958565017985444838724067 68937847526978167258086101)
    ·
      refine ⟨1615730801413550795111393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 68937847526978167258086101 1615730801413550795111393)
      ·
        refine ⟨1211798101060163096333545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1615730801413550795111393 1211798101060163096333545)
        ·
          refine ⟨908848575795122322250159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211798101060163096333545 908848575795122322250159)
          ·
            refine ⟨1363272863692683483375239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908848575795122322250159 1363272863692683483375239)
            ·
              refine ⟨2044909295539025225062859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363272863692683483375239 2044909295539025225062859)
              ·
                refine ⟨3067363943308537837594289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044909295539025225062859 3067363943308537837594289)
                ·
                  refine ⟨2300522957481403378195717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067363943308537837594289 2300522957481403378195717)
                  ·
                    refine ⟨431348054527763133411697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2300522957481403378195717 431348054527763133411697)
                    ·
                      rfl

theorem cell22_1260071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1260071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260071 prefixEnd_1260071 := by exact prefixLift 1260071
  have htrace : WordTrace (prefixWord ++ tailWord_1260071) baseStart_1260071 baseEnd_1260071 := by
    simpa [prefixWord, tailWord_1260071, baseEnd_1260071] using wordTrace_append hprefix tailTrace_1260071
  have hstable : (prefixWord ++ tailWord_1260071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260071).length < 2 ^ (prefixWord ++ tailWord_1260071).sum := by decide
  have hdescent : baseEnd_1260071 < baseStart_1260071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260097 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 5]
def baseStart_1260097 : Nat := 118140960795 + 1260097 * 2 ^ 59
def prefixEnd_1260097 : Nat := 4983230072969 + 3 ^ 40 * 1260097 * 2
def baseEnd_1260097 : Nat := 143785651619702577420539

theorem tailTrace_1260097 : CollatzResearch.WordTrace tailWord_1260097 prefixEnd_1260097 143785651619702577420539 := by
  unfold tailWord_1260097
  simp only [CollatzResearch.WordTrace]
  refine ⟨45959513315891251279170545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30639675543927500852780363 45959513315891251279170545)
  ·
    refine ⟨34469634986918438459377909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45959513315891251279170545 34469634986918438459377909)
    ·
      refine ⟨3231528280023603605566679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34469634986918438459377909 3231528280023603605566679)
      ·
        refine ⟨4847292420035405408350019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231528280023603605566679 4847292420035405408350019)
        ·
          refine ⟨7270938630053108112525029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847292420035405408350019 7270938630053108112525029)
          ·
            refine ⟨1363300993134957771098443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7270938630053108112525029 1363300993134957771098443)
            ·
              refine ⟨2044951489702436656647665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363300993134957771098443 2044951489702436656647665)
              ·
                refine ⟨1533713617276827492485749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044951489702436656647665 1533713617276827492485749)
                ·
                  refine ⟨143785651619702577420539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1533713617276827492485749 143785651619702577420539)
                  ·
                    rfl

theorem cell22_1260097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_1260097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260097 prefixEnd_1260097 := by exact prefixLift 1260097
  have htrace : WordTrace (prefixWord ++ tailWord_1260097) baseStart_1260097 baseEnd_1260097 := by
    simpa [prefixWord, tailWord_1260097, baseEnd_1260097] using wordTrace_append hprefix tailTrace_1260097
  have hstable : (prefixWord ++ tailWord_1260097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260097).length < 2 ^ (prefixWord ++ tailWord_1260097).sum := by decide
  have hdescent : baseEnd_1260097 < baseStart_1260097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260140 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_1260140 : Nat := 118140960795 + 1260140 * 2 ^ 59
def prefixEnd_1260140 : Nat := 4983230072969 + 3 ^ 40 * 1260140 * 2
def baseEnd_1260140 : Nat := 431371674637869953436485

theorem tailTrace_1260140 : CollatzResearch.WordTrace tailWord_1260140 prefixEnd_1260140 431371674637869953436485 := by
  unfold tailWord_1260140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22980540827367734811492937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30640721103156979748657249 22980540827367734811492937)
  ·
    refine ⟨17235405620525801108619703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22980540827367734811492937 17235405620525801108619703)
    ·
      refine ⟨25853108430788701662929555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17235405620525801108619703 25853108430788701662929555)
      ·
        refine ⟨38779662646183052494394333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25853108430788701662929555 38779662646183052494394333)
        ·
          refine ⟨14542373492318644685397875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38779662646183052494394333 14542373492318644685397875)
          ·
            refine ⟨21813560238477967028096813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14542373492318644685397875 21813560238477967028096813)
            ·
              refine ⟨8180085089429237635536305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21813560238477967028096813 8180085089429237635536305)
              ·
                refine ⟨6135063817071928226652229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8180085089429237635536305 6135063817071928226652229)
                ·
                  refine ⟨1150324465700986542497293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6135063817071928226652229 1150324465700986542497293)
                  ·
                    refine ⟨431371674637869953436485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150324465700986542497293 431371674637869953436485)
                    ·
                      rfl

theorem cell22_1260140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_1260140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260140 prefixEnd_1260140 := by exact prefixLift 1260140
  have htrace : WordTrace (prefixWord ++ tailWord_1260140) baseStart_1260140 baseEnd_1260140 := by
    simpa [prefixWord, tailWord_1260140, baseEnd_1260140] using wordTrace_append hprefix tailTrace_1260140
  have hstable : (prefixWord ++ tailWord_1260140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260140).length < 2 ^ (prefixWord ++ tailWord_1260140).sum := by decide
  have hdescent : baseEnd_1260140 < baseStart_1260140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260153 : List Nat := [1, 2, 1, 3, 3, 2, 10]
def baseStart_1260153 : Nat := 118140960795 + 1260153 * 2 ^ 59
def prefixEnd_1260153 : Nat := 4983230072969 + 3 ^ 40 * 1260153 * 2
def baseEnd_1260153 : Nat := 15976893511242305661535

theorem tailTrace_1260153 : CollatzResearch.WordTrace tailWord_1260153 prefixEnd_1260153 15976893511242305661535 := by
  unfold tailWord_1260153
  simp only [CollatzResearch.WordTrace]
  refine ⟨45961555803688372843209113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30641037202458915228806075 45961555803688372843209113)
  ·
    refine ⟨34471166852766279632406835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45961555803688372843209113 34471166852766279632406835)
    ·
      refine ⟨51706750279149419448610253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34471166852766279632406835 51706750279149419448610253)
      ·
        refine ⟨19390031354681032293228845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51706750279149419448610253 19390031354681032293228845)
        ·
          refine ⟨7271261758005387109960817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19390031354681032293228845 7271261758005387109960817)
          ·
            refine ⟨5453446318504040332470613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7271261758005387109960817 5453446318504040332470613)
            ·
              refine ⟨15976893511242305661535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5453446318504040332470613 15976893511242305661535)
              ·
                rfl

theorem cell22_1260153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 10].length) (baseStart_1260153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260153 prefixEnd_1260153 := by exact prefixLift 1260153
  have htrace : WordTrace (prefixWord ++ tailWord_1260153) baseStart_1260153 baseEnd_1260153 := by
    simpa [prefixWord, tailWord_1260153, baseEnd_1260153] using wordTrace_append hprefix tailTrace_1260153
  have hstable : (prefixWord ++ tailWord_1260153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260153).length < 2 ^ (prefixWord ++ tailWord_1260153).sum := by decide
  have hdescent : baseEnd_1260153 < baseStart_1260153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260185 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 5, 3]
def baseStart_1260185 : Nat := 118140960795 + 1260185 * 2 ^ 59
def prefixEnd_1260185 : Nat := 4983230072969 + 3 ^ 40 * 1260185 * 2
def baseEnd_1260185 : Nat := 431387079057504836061347

theorem tailTrace_1260185 : CollatzResearch.WordTrace tailWord_1260185 prefixEnd_1260185 431387079057504836061347 := by
  unfold tailWord_1260185
  simp only [CollatzResearch.WordTrace]
  refine ⟨45962722939572442308374009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30641815293048294872249339 45962722939572442308374009)
  ·
    refine ⟨34472042204679331731280507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45962722939572442308374009 34472042204679331731280507)
    ·
      refine ⟨51708063307018997596920761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34472042204679331731280507 51708063307018997596920761)
      ·
        refine ⟨38781047480264248197690571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51708063307018997596920761 38781047480264248197690571)
        ·
          refine ⟨58171571220396372296535857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38781047480264248197690571 58171571220396372296535857)
          ·
            refine ⟨43628678415297279222401893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58171571220396372296535857 43628678415297279222401893)
            ·
              refine ⟨8180377202868239854200355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43628678415297279222401893 8180377202868239854200355)
              ·
                refine ⟨12270565804302359781300533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8180377202868239854200355 12270565804302359781300533)
                ·
                  refine ⟨1150365544153346229496925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12270565804302359781300533 1150365544153346229496925)
                  ·
                    refine ⟨431387079057504836061347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150365544153346229496925 431387079057504836061347)
                    ·
                      rfl

theorem cell22_1260185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_1260185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260185 prefixEnd_1260185 := by exact prefixLift 1260185
  have htrace : WordTrace (prefixWord ++ tailWord_1260185) baseStart_1260185 baseEnd_1260185 := by
    simpa [prefixWord, tailWord_1260185, baseEnd_1260185] using wordTrace_append hprefix tailTrace_1260185
  have hstable : (prefixWord ++ tailWord_1260185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260185).length < 2 ^ (prefixWord ++ tailWord_1260185).sum := by decide
  have hdescent : baseEnd_1260185 < baseStart_1260185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260311 : List Nat := [1, 1, 3, 4, 3, 2, 1, 3, 4]
def baseStart_1260311 : Nat := 118140960795 + 1260311 * 2 ^ 59
def prefixEnd_1260311 : Nat := 4983230072969 + 3 ^ 40 * 1260311 * 2
def baseEnd_1260311 : Nat := 143810070477494169136987

theorem tailTrace_1260311 : CollatzResearch.WordTrace tailWord_1260311 prefixEnd_1260311 143810070477494169136987 := by
  unfold tailWord_1260311
  simp only [CollatzResearch.WordTrace]
  refine ⟨45967318537115965827460787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30644879024743977218307191 45967318537115965827460787)
  ·
    refine ⟨68950977805673948741191181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45967318537115965827460787 68950977805673948741191181)
    ·
      refine ⟨25856616677127730777946693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68950977805673948741191181 25856616677127730777946693)
      ·
        refine ⟨4848115626961449520865005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25856616677127730777946693 4848115626961449520865005)
        ·
          refine ⟨1818043360110543570324377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4848115626961449520865005 1818043360110543570324377)
          ·
            refine ⟨1363532520082907677743283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1818043360110543570324377 1363532520082907677743283)
            ·
              refine ⟨2045298780124361516614925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363532520082907677743283 2045298780124361516614925)
              ·
                refine ⟨766987042546635568730597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2045298780124361516614925 766987042546635568730597)
                ·
                  refine ⟨143810070477494169136987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766987042546635568730597 143810070477494169136987)
                  ·
                    rfl

theorem cell22_1260311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 4].length) (baseStart_1260311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260311 prefixEnd_1260311 := by exact prefixLift 1260311
  have htrace : WordTrace (prefixWord ++ tailWord_1260311) baseStart_1260311 baseEnd_1260311 := by
    simpa [prefixWord, tailWord_1260311, baseEnd_1260311] using wordTrace_append hprefix tailTrace_1260311
  have hstable : (prefixWord ++ tailWord_1260311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260311).length < 2 ^ (prefixWord ++ tailWord_1260311).sum := by decide
  have hdescent : baseEnd_1260311 < baseStart_1260311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260322 : List Nat := [3, 3, 1, 1, 2, 4, 8]
def baseStart_1260322 : Nat := 118140960795 + 1260322 * 2 ^ 59
def prefixEnd_1260322 : Nat := 4983230072969 + 3 ^ 40 * 1260322 * 2
def baseEnd_1260322 : Nat := 15979036183603042421701

theorem tailTrace_1260322 : CollatzResearch.WordTrace tailWord_1260322 prefixEnd_1260322 15979036183603042421701 := by
  unfold tailWord_1260322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11491929935019028676527805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30645146493384076470740813 11491929935019028676527805)
  ·
    refine ⟨4309473725632135753697927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11491929935019028676527805 4309473725632135753697927)
    ·
      refine ⟨6464210588448203630546891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4309473725632135753697927 6464210588448203630546891)
      ·
        refine ⟨9696315882672305445820337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6464210588448203630546891 9696315882672305445820337)
        ·
          refine ⟨7272236912004229084365253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9696315882672305445820337 7272236912004229084365253)
          ·
            refine ⟨1363544421000792953318485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7272236912004229084365253 1363544421000792953318485)
            ·
              refine ⟨15979036183603042421701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1363544421000792953318485 15979036183603042421701)
              ·
                rfl

theorem cell22_1260322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 8].length) (baseStart_1260322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260322 prefixEnd_1260322 := by exact prefixLift 1260322
  have htrace : WordTrace (prefixWord ++ tailWord_1260322) baseStart_1260322 baseEnd_1260322 := by
    simpa [prefixWord, tailWord_1260322, baseEnd_1260322] using wordTrace_append hprefix tailTrace_1260322
  have hstable : (prefixWord ++ tailWord_1260322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260322).length < 2 ^ (prefixWord ++ tailWord_1260322).sum := by decide
  have hdescent : baseEnd_1260322 < baseStart_1260322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260324 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1260324 : Nat := 118140960795 + 1260324 * 2 ^ 59
def prefixEnd_1260324 : Nat := 4983230072969 + 3 ^ 40 * 1260324 * 2
def baseEnd_1260324 : Nat := 431434661598154806835921

theorem tailTrace_1260324 : CollatzResearch.WordTrace tailWord_1260324 prefixEnd_1260324 431434661598154806835921 := by
  unfold tailWord_1260324
  simp only [CollatzResearch.WordTrace]
  refine ⟨22983896343034434523842013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30645195124045912698456017 22983896343034434523842013)
  ·
    refine ⟨8618961128637912946440755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22983896343034434523842013 8618961128637912946440755)
    ·
      refine ⟨12928441692956869419661133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8618961128637912946440755 12928441692956869419661133)
      ·
        refine ⟨4848165634858826032372925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12928441692956869419661133 4848165634858826032372925)
        ·
          refine ⟨1818062113072059762139847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4848165634858826032372925 1818062113072059762139847)
          ·
            refine ⟨2727093169608089643209771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818062113072059762139847 2727093169608089643209771)
            ·
              refine ⟨4090639754412134464814657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727093169608089643209771 4090639754412134464814657)
              ·
                refine ⟨3067979815809100848610993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4090639754412134464814657 3067979815809100848610993)
                ·
                  refine ⟨2300984861856825636458245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067979815809100848610993 2300984861856825636458245)
                  ·
                    refine ⟨431434661598154806835921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2300984861856825636458245 431434661598154806835921)
                    ·
                      rfl

theorem cell22_1260324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1260324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260324 prefixEnd_1260324 := by exact prefixLift 1260324
  have htrace : WordTrace (prefixWord ++ tailWord_1260324) baseStart_1260324 baseEnd_1260324 := by
    simpa [prefixWord, tailWord_1260324, baseEnd_1260324] using wordTrace_append hprefix tailTrace_1260324
  have hstable : (prefixWord ++ tailWord_1260324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260324).length < 2 ^ (prefixWord ++ tailWord_1260324).sum := by decide
  have hdescent : baseEnd_1260324 < baseStart_1260324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260358 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1260358 : Nat := 118140960795 + 1260358 * 2 ^ 59
def prefixEnd_1260358 : Nat := 4983230072969 + 3 ^ 40 * 1260358 * 2
def baseEnd_1260358 : Nat := 431446300492990051485817

theorem tailTrace_1260358 : CollatzResearch.WordTrace tailWord_1260358 prefixEnd_1260358 431446300492990051485817 := by
  unfold tailWord_1260358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436532273998302901700679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30646021845297128569614485 1436532273998302901700679)
  ·
    refine ⟨2154798410997454352551019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1436532273998302901700679 2154798410997454352551019)
    ·
      refine ⟨3232197616496181528826529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154798410997454352551019 3232197616496181528826529)
      ·
        refine ⟨2424148212372136146619897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3232197616496181528826529 2424148212372136146619897)
        ·
          refine ⟨1818111159279102109964923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2424148212372136146619897 1818111159279102109964923)
          ·
            refine ⟨2727166738918653164947385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818111159279102109964923 2727166738918653164947385)
            ·
              refine ⟨2045375054188989873710539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2727166738918653164947385 2045375054188989873710539)
              ·
                refine ⟨3068062581283484810565809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045375054188989873710539 3068062581283484810565809)
                ·
                  refine ⟨2301046935962613607924357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068062581283484810565809 2301046935962613607924357)
                  ·
                    refine ⟨431446300492990051485817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2301046935962613607924357 431446300492990051485817)
                    ·
                      rfl

theorem cell22_1260358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1260358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260358 prefixEnd_1260358 := by exact prefixLift 1260358
  have htrace : WordTrace (prefixWord ++ tailWord_1260358) baseStart_1260358 baseEnd_1260358 := by
    simpa [prefixWord, tailWord_1260358, baseEnd_1260358] using wordTrace_append hprefix tailTrace_1260358
  have hstable : (prefixWord ++ tailWord_1260358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260358).length < 2 ^ (prefixWord ++ tailWord_1260358).sum := by decide
  have hdescent : baseEnd_1260358 < baseStart_1260358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260388 : List Nat := [2, 3, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_1260388 : Nat := 118140960795 + 1260388 * 2 ^ 59
def prefixEnd_1260388 : Nat := 4983230072969 + 3 ^ 40 * 1260388 * 2
def baseEnd_1260388 : Nat := 431456570106079973235725

theorem tailTrace_1260388 : CollatzResearch.WordTrace tailWord_1260388 prefixEnd_1260388 431456570106079973235725 := by
  unfold tailWord_1260388
  simp only [CollatzResearch.WordTrace]
  refine ⟨22985063478918503989006909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30646751305224671985342545 22985063478918503989006909)
  ·
    refine ⟨8619398804594438995877591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22985063478918503989006909 8619398804594438995877591)
    ·
      refine ⟨12929098206891658493816387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8619398804594438995877591 12929098206891658493816387)
      ·
        refine ⟨19393647310337487740724581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12929098206891658493816387 19393647310337487740724581)
        ·
          refine ⟨3636308870688278951385859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19393647310337487740724581 3636308870688278951385859)
          ·
            refine ⟨5454463306032418427078789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636308870688278951385859 5454463306032418427078789)
            ·
              refine ⟨1022711869881078455077273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5454463306032418427078789 1022711869881078455077273)
              ·
                refine ⟨767033902410808841307955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022711869881078455077273 767033902410808841307955)
                ·
                  refine ⟨1150550853616213261961933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767033902410808841307955 1150550853616213261961933)
                  ·
                    refine ⟨431456570106079973235725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150550853616213261961933 431456570106079973235725)
                    ·
                      rfl

theorem cell22_1260388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_1260388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260388 prefixEnd_1260388 := by exact prefixLift 1260388
  have htrace : WordTrace (prefixWord ++ tailWord_1260388) baseStart_1260388 baseEnd_1260388 := by
    simpa [prefixWord, tailWord_1260388, baseEnd_1260388] using wordTrace_append hprefix tailTrace_1260388
  have hstable : (prefixWord ++ tailWord_1260388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260388).length < 2 ^ (prefixWord ++ tailWord_1260388).sum := by decide
  have hdescent : baseEnd_1260388 < baseStart_1260388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260427 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 1, 5]
def baseStart_1260427 : Nat := 118140960795 + 1260427 * 2 ^ 59
def prefixEnd_1260427 : Nat := 4983230072969 + 3 ^ 40 * 1260427 * 2
def baseEnd_1260427 : Nat := 431469920603096871510605

theorem tailTrace_1260427 : CollatzResearch.WordTrace tailWord_1260427 prefixEnd_1260427 431469920603096871510605 := by
  unfold tailWord_1260427
  simp only [CollatzResearch.WordTrace]
  refine ⟨45971549404695717638683535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30647699603130478425789023 45971549404695717638683535)
  ·
    refine ⟨68957324107043576458025303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45971549404695717638683535 68957324107043576458025303)
    ·
      refine ⟨103435986160565364687037955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68957324107043576458025303 103435986160565364687037955)
      ·
        refine ⟨155153979240848047030556933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103435986160565364687037955 155153979240848047030556933)
        ·
          refine ⟨29091371107659008818229425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155153979240848047030556933 29091371107659008818229425)
          ·
            refine ⟨21818528330744256613672069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29091371107659008818229425 21818528330744256613672069)
            ·
              refine ⟨4090974062014548115063513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21818528330744256613672069 4090974062014548115063513)
              ·
                refine ⟨3068230546510911086297635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4090974062014548115063513 3068230546510911086297635)
                ·
                  refine ⟨4602345819766366629446453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068230546510911086297635 4602345819766366629446453)
                  ·
                    refine ⟨431469920603096871510605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4602345819766366629446453 431469920603096871510605)
                    ·
                      rfl

theorem cell22_1260427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_1260427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260427 prefixEnd_1260427 := by exact prefixLift 1260427
  have htrace : WordTrace (prefixWord ++ tailWord_1260427) baseStart_1260427 baseEnd_1260427 := by
    simpa [prefixWord, tailWord_1260427, baseEnd_1260427] using wordTrace_append hprefix tailTrace_1260427
  have hstable : (prefixWord ++ tailWord_1260427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260427).length < 2 ^ (prefixWord ++ tailWord_1260427).sum := by decide
  have hdescent : baseEnd_1260427 < baseStart_1260427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260506 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_1260506 : Nat := 118140960795 + 1260506 * 2 ^ 59
def prefixEnd_1260506 : Nat := 4983230072969 + 3 ^ 40 * 1260506 * 2
def baseEnd_1260506 : Nat := 431496963917566998785363

theorem tailTrace_1260506 : CollatzResearch.WordTrace tailWord_1260506 prefixEnd_1260506 431496963917566998785363 := by
  unfold tailWord_1260506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493607692852378532702343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30649620514273009420539581 11493607692852378532702343)
  ·
    refine ⟨17240411539278567799053515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11493607692852378532702343 17240411539278567799053515)
    ·
      refine ⟨25860617308917851698580273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17240411539278567799053515 25860617308917851698580273)
      ·
        refine ⟨19395462981688388773935205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25860617308917851698580273 19395462981688388773935205)
        ·
          refine ⟨3636649309066572895112851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19395462981688388773935205 3636649309066572895112851)
          ·
            refine ⟨5454973963599859342669277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636649309066572895112851 5454973963599859342669277)
            ·
              refine ⟨2045615236349947253500979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5454973963599859342669277 2045615236349947253500979)
              ·
                refine ⟨3068422854524920880251469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045615236349947253500979 3068422854524920880251469)
                ·
                  refine ⟨1150658570446845330094301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3068422854524920880251469 1150658570446845330094301)
                  ·
                    refine ⟨431496963917566998785363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150658570446845330094301 431496963917566998785363)
                    ·
                      rfl

theorem cell22_1260506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_1260506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260506 prefixEnd_1260506 := by exact prefixLift 1260506
  have htrace : WordTrace (prefixWord ++ tailWord_1260506) baseStart_1260506 baseEnd_1260506 := by
    simpa [prefixWord, tailWord_1260506, baseEnd_1260506] using wordTrace_append hprefix tailTrace_1260506
  have hstable : (prefixWord ++ tailWord_1260506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260506).length < 2 ^ (prefixWord ++ tailWord_1260506).sum := by decide
  have hdescent : baseEnd_1260506 < baseStart_1260506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260579 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 1, 5]
def baseStart_1260579 : Nat := 118140960795 + 1260579 * 2 ^ 59
def prefixEnd_1260579 : Nat := 4983230072969 + 3 ^ 40 * 1260579 * 2
def baseEnd_1260579 : Nat := 431521953309419141710139

theorem tailTrace_1260579 : CollatzResearch.WordTrace tailWord_1260579 prefixEnd_1260579 431521953309419141710139 := by
  unfold tailWord_1260579
  simp only [CollatzResearch.WordTrace]
  refine ⟨45977093300145047598216791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30651395533430031732144527 45977093300145047598216791)
  ·
    refine ⟨68965639950217571397325187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45977093300145047598216791 68965639950217571397325187)
    ·
      refine ⟨103448459925326357095987781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68965639950217571397325187 103448459925326357095987781)
      ·
        refine ⟨19396586235998691955497709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103448459925326357095987781 19396586235998691955497709)
        ·
          refine ⟨7273719838499509483311641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19396586235998691955497709 7273719838499509483311641)
          ·
            refine ⟨5455289878874632112483731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7273719838499509483311641 5455289878874632112483731)
            ·
              refine ⟨8182934818311948168725597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5455289878874632112483731 8182934818311948168725597)
              ·
                refine ⟨3068600556866980563272099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8182934818311948168725597 3068600556866980563272099)
                ·
                  refine ⟨4602900835300470844908149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068600556866980563272099 4602900835300470844908149)
                  ·
                    refine ⟨431521953309419141710139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4602900835300470844908149 431521953309419141710139)
                    ·
                      rfl

theorem cell22_1260579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_1260579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260579 prefixEnd_1260579 := by exact prefixLift 1260579
  have htrace : WordTrace (prefixWord ++ tailWord_1260579) baseStart_1260579 baseEnd_1260579 := by
    simpa [prefixWord, tailWord_1260579, baseEnd_1260579] using wordTrace_append hprefix tailTrace_1260579
  have hstable : (prefixWord ++ tailWord_1260579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260579).length < 2 ^ (prefixWord ++ tailWord_1260579).sum := by decide
  have hdescent : baseEnd_1260579 < baseStart_1260579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260594 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1260594 : Nat := 118140960795 + 1260594 * 2 ^ 59
def prefixEnd_1260594 : Nat := 4983230072969 + 3 ^ 40 * 1260594 * 2
def baseEnd_1260594 : Nat := 431527088115964102585093

theorem tailTrace_1260594 : CollatzResearch.WordTrace tailWord_1260594 prefixEnd_1260594 431527088115964102585093 := by
  unfold tailWord_1260594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11494410098772676290003209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30651760263393803440008557 11494410098772676290003209)
  ·
    refine ⟨8620807574079507217502407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11494410098772676290003209 8620807574079507217502407)
    ·
      refine ⟨12931211361119260826253611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8620807574079507217502407 12931211361119260826253611)
      ·
        refine ⟨19396817041678891239380417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12931211361119260826253611 19396817041678891239380417)
        ·
          refine ⟨14547612781259168429535313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19396817041678891239380417 14547612781259168429535313)
          ·
            refine ⟨10910709585944376322151485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14547612781259168429535313 10910709585944376322151485)
            ·
              refine ⟨4091516094729141120806807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10910709585944376322151485 4091516094729141120806807)
              ·
                refine ⟨6137274142093711681210211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091516094729141120806807 6137274142093711681210211)
                ·
                  refine ⟨9205911213140567521815317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6137274142093711681210211 9205911213140567521815317)
                  ·
                    refine ⟨431527088115964102585093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9205911213140567521815317 431527088115964102585093)
                    ·
                      rfl

theorem cell22_1260594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1260594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260594 prefixEnd_1260594 := by exact prefixLift 1260594
  have htrace : WordTrace (prefixWord ++ tailWord_1260594) baseStart_1260594 baseEnd_1260594 := by
    simpa [prefixWord, tailWord_1260594, baseEnd_1260594] using wordTrace_append hprefix tailTrace_1260594
  have hstable : (prefixWord ++ tailWord_1260594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260594).length < 2 ^ (prefixWord ++ tailWord_1260594).sum := by decide
  have hdescent : baseEnd_1260594 < baseStart_1260594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260598 : List Nat := [5, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1260598 : Nat := 118140960795 + 1260598 * 2 ^ 59
def prefixEnd_1260598 : Nat := 4983230072969 + 3 ^ 40 * 1260598 * 2
def baseEnd_1260598 : Nat := 143842819132569808495027

theorem tailTrace_1260598 : CollatzResearch.WordTrace tailWord_1260598 prefixEnd_1260598 143842819132569808495027 := by
  unfold tailWord_1260598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873611642942263365197403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30651857524717475895438965 2873611642942263365197403)
  ·
    refine ⟨4310417464413395047796105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2873611642942263365197403 4310417464413395047796105)
    ·
      refine ⟨3232813098310046285847079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4310417464413395047796105 3232813098310046285847079)
      ·
        refine ⟨4849219647465069428770619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3232813098310046285847079 4849219647465069428770619)
        ·
          refine ⟨7273829471197604143155929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4849219647465069428770619 7273829471197604143155929)
          ·
            refine ⟨5455372103398203107366947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7273829471197604143155929 5455372103398203107366947)
            ·
              refine ⟨8183058155097304661050421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5455372103398203107366947 8183058155097304661050421)
              ·
                refine ⟨767161702040372311973477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8183058155097304661050421 767161702040372311973477)
                ·
                  refine ⟨143842819132569808495027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 767161702040372311973477 143842819132569808495027)
                  ·
                    rfl

theorem cell22_1260598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1260598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260598 prefixEnd_1260598 := by exact prefixLift 1260598
  have htrace : WordTrace (prefixWord ++ tailWord_1260598) baseStart_1260598 baseEnd_1260598 := by
    simpa [prefixWord, tailWord_1260598, baseEnd_1260598] using wordTrace_append hprefix tailTrace_1260598
  have hstable : (prefixWord ++ tailWord_1260598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260598).length < 2 ^ (prefixWord ++ tailWord_1260598).sum := by decide
  have hdescent : baseEnd_1260598 < baseStart_1260598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260641 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 3, 3]
def baseStart_1260641 : Nat := 118140960795 + 1260641 * 2 ^ 59
def prefixEnd_1260641 : Nat := 4983230072969 + 3 ^ 40 * 1260641 * 2
def baseEnd_1260641 : Nat := 431543177176471646659949

theorem tailTrace_1260641 : CollatzResearch.WordTrace tailWord_1260641 prefixEnd_1260641 431543177176471646659949 := by
  unfold tailWord_1260641
  simp only [CollatzResearch.WordTrace]
  refine ⟨45979354625920432186973777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30652903083946954791315851 45979354625920432186973777)
  ·
    refine ⟨34484515969440324140230333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45979354625920432186973777 34484515969440324140230333)
    ·
      refine ⟨12931693488540121552586375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34484515969440324140230333 12931693488540121552586375)
      ·
        refine ⟨19397540232810182328879563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12931693488540121552586375 19397540232810182328879563)
        ·
          refine ⟨29096310349215273493319345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19397540232810182328879563 29096310349215273493319345)
          ·
            refine ⟨21822232761911455119989509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29096310349215273493319345 21822232761911455119989509)
            ·
              refine ⟨4091668642858397834998033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21822232761911455119989509 4091668642858397834998033)
              ·
                refine ⟨3068751482143798376248525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4091668642858397834998033 3068751482143798376248525)
                ·
                  refine ⟨1150781805803924391093197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3068751482143798376248525 1150781805803924391093197)
                  ·
                    refine ⟨431543177176471646659949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150781805803924391093197 431543177176471646659949)
                    ·
                      rfl

theorem cell22_1260641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_1260641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260641 prefixEnd_1260641 := by exact prefixLift 1260641
  have htrace : WordTrace (prefixWord ++ tailWord_1260641) baseStart_1260641 baseEnd_1260641 := by
    simpa [prefixWord, tailWord_1260641, baseEnd_1260641] using wordTrace_append hprefix tailTrace_1260641
  have hstable : (prefixWord ++ tailWord_1260641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260641).length < 2 ^ (prefixWord ++ tailWord_1260641).sum := by decide
  have hdescent : baseEnd_1260641 < baseStart_1260641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260675 : List Nat := [1, 1, 1, 3, 3, 2, 5, 2, 1, 3]
def baseStart_1260675 : Nat := 118140960795 + 1260675 * 2 ^ 59
def prefixEnd_1260675 : Nat := 4983230072969 + 3 ^ 40 * 1260675 * 2
def baseEnd_1260675 : Nat := 431554816071306891309845

theorem tailTrace_1260675 : CollatzResearch.WordTrace tailWord_1260675 prefixEnd_1260675 431554816071306891309845 := by
  unfold tailWord_1260675
  simp only [CollatzResearch.WordTrace]
  refine ⟨45980594707797255993711479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30653729805198170662474319 45980594707797255993711479)
  ·
    refine ⟨68970892061695883990567219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45980594707797255993711479 68970892061695883990567219)
    ·
      refine ⟨103456338092543825985850829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68970892061695883990567219 103456338092543825985850829)
      ·
        refine ⟨38796126784703934744694061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103456338092543825985850829 38796126784703934744694061)
        ·
          refine ⟨14548547544263975529260273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38796126784703934744694061 14548547544263975529260273)
          ·
            refine ⟨10911410658197981646945205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14548547544263975529260273 10911410658197981646945205)
            ·
              refine ⟨1022944749206060779401113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10911410658197981646945205 1022944749206060779401113)
              ·
                refine ⟨767208561904545584550835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022944749206060779401113 767208561904545584550835)
                ·
                  refine ⟨1150812842856818376826253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767208561904545584550835 1150812842856818376826253)
                  ·
                    refine ⟨431554816071306891309845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150812842856818376826253 431554816071306891309845)
                    ·
                      rfl

theorem cell22_1260675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 3].length) (baseStart_1260675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260675 prefixEnd_1260675 := by exact prefixLift 1260675
  have htrace : WordTrace (prefixWord ++ tailWord_1260675) baseStart_1260675 baseEnd_1260675 := by
    simpa [prefixWord, tailWord_1260675, baseEnd_1260675] using wordTrace_append hprefix tailTrace_1260675
  have hstable : (prefixWord ++ tailWord_1260675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260675).length < 2 ^ (prefixWord ++ tailWord_1260675).sum := by decide
  have hdescent : baseEnd_1260675 < baseStart_1260675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260701 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1260701 : Nat := 118140960795 + 1260701 * 2 ^ 59
def prefixEnd_1260701 : Nat := 4983230072969 + 3 ^ 40 * 1260701 * 2
def baseEnd_1260701 : Nat := 431563716402651490159765

theorem tailTrace_1260701 : CollatzResearch.WordTrace tailWord_1260701 prefixEnd_1260701 431563716402651490159765 := by
  unfold tailWord_1260701
  simp only [CollatzResearch.WordTrace]
  refine ⟨45981543005703062434157957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30654362003802041622771971 45981543005703062434157957)
  ·
    refine ⟨8621539313569324206404617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45981543005703062434157957 8621539313569324206404617)
    ·
      refine ⟨6466154485176993154803463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8621539313569324206404617 6466154485176993154803463)
      ·
        refine ⟨9699231727765489732205195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466154485176993154803463 9699231727765489732205195)
        ·
          refine ⟨14548847591648234598307793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9699231727765489732205195 14548847591648234598307793)
          ·
            refine ⟨10911635693736175948730845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14548847591648234598307793 10911635693736175948730845)
            ·
              refine ⟨4091863385151065980774067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10911635693736175948730845 4091863385151065980774067)
              ·
                refine ⟨6137795077726598971161101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091863385151065980774067 6137795077726598971161101)
                ·
                  refine ⟨2301673154147474614185413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6137795077726598971161101 2301673154147474614185413)
                  ·
                    refine ⟨431563716402651490159765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2301673154147474614185413 431563716402651490159765)
                    ·
                      rfl

theorem cell22_1260701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1260701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260701 prefixEnd_1260701 := by exact prefixLift 1260701
  have htrace : WordTrace (prefixWord ++ tailWord_1260701) baseStart_1260701 baseEnd_1260701 := by
    simpa [prefixWord, tailWord_1260701, baseEnd_1260701] using wordTrace_append hprefix tailTrace_1260701
  have hstable : (prefixWord ++ tailWord_1260701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260701).length < 2 ^ (prefixWord ++ tailWord_1260701).sum := by decide
  have hdescent : baseEnd_1260701 < baseStart_1260701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260793 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 3, 3]
def baseStart_1260793 : Nat := 118140960795 + 1260793 * 2 ^ 59
def prefixEnd_1260793 : Nat := 4983230072969 + 3 ^ 40 * 1260793 * 2
def baseEnd_1260793 : Nat := 431595209882793916859483

theorem tailTrace_1260793 : CollatzResearch.WordTrace tailWord_1260793 prefixEnd_1260793 431595209882793916859483 := by
  unfold tailWord_1260793
  simp only [CollatzResearch.WordTrace]
  refine ⟨45984898521369762146507033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30656599014246508097671355 45984898521369762146507033)
  ·
    refine ⟨34488673891027321609880275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45984898521369762146507033 34488673891027321609880275)
    ·
      refine ⟨51733010836540982414820413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34488673891027321609880275 51733010836540982414820413)
      ·
        refine ⟨19399879063702868405557655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51733010836540982414820413 19399879063702868405557655)
        ·
          refine ⟨29099818595554302608336483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19399879063702868405557655 29099818595554302608336483)
          ·
            refine ⟨43649727893331453912504725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29099818595554302608336483 43649727893331453912504725)
            ·
              refine ⟨2046080994999911902148659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43649727893331453912504725 2046080994999911902148659)
              ·
                refine ⟨3069121492499867853222989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046080994999911902148659 3069121492499867853222989)
                ·
                  refine ⟨1150920559687450444958621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3069121492499867853222989 1150920559687450444958621)
                  ·
                    refine ⟨431595209882793916859483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150920559687450444958621 431595209882793916859483)
                    ·
                      rfl

theorem cell22_1260793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_1260793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260793 prefixEnd_1260793 := by exact prefixLift 1260793
  have htrace : WordTrace (prefixWord ++ tailWord_1260793) baseStart_1260793 baseEnd_1260793 := by
    simpa [prefixWord, tailWord_1260793, baseEnd_1260793] using wordTrace_append hprefix tailTrace_1260793
  have hstable : (prefixWord ++ tailWord_1260793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260793).length < 2 ^ (prefixWord ++ tailWord_1260793).sum := by decide
  have hdescent : baseEnd_1260793 < baseStart_1260793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260857 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 5]
def baseStart_1260857 : Nat := 118140960795 + 1260857 * 2 ^ 59
def prefixEnd_1260857 : Nat := 4983230072969 + 3 ^ 40 * 1260857 * 2
def baseEnd_1260857 : Nat := 143872372796906361086429

theorem tailTrace_1260857 : CollatzResearch.WordTrace tailWord_1260857 prefixEnd_1260857 143872372796906361086429 := by
  unfold tailWord_1260857
  simp only [CollatzResearch.WordTrace]
  refine ⟨45987232793137901076836825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30658155195425267384557883 45987232793137901076836825)
  ·
    refine ⟨34490424594853425807627619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45987232793137901076836825 34490424594853425807627619)
    ·
      refine ⟨51735636892280138711441429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34490424594853425807627619 51735636892280138711441429)
      ·
        refine ⟨2425107979325631502098817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51735636892280138711441429 2425107979325631502098817)
        ·
          refine ⟨1818830984494223626574113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2425107979325631502098817 1818830984494223626574113)
          ·
            refine ⟨1364123238370667719930585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1818830984494223626574113 1364123238370667719930585)
            ·
              refine ⟨1023092428778000789947939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364123238370667719930585 1023092428778000789947939)
              ·
                refine ⟨1534638643167001184921909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023092428778000789947939 1534638643167001184921909)
                ·
                  refine ⟨143872372796906361086429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1534638643167001184921909 143872372796906361086429)
                  ·
                    rfl

theorem cell22_1260857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_1260857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260857 prefixEnd_1260857 := by exact prefixLift 1260857
  have htrace : WordTrace (prefixWord ++ tailWord_1260857) baseStart_1260857 baseEnd_1260857 := by
    simpa [prefixWord, tailWord_1260857, baseEnd_1260857] using wordTrace_append hprefix tailTrace_1260857
  have hstable : (prefixWord ++ tailWord_1260857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260857).length < 2 ^ (prefixWord ++ tailWord_1260857).sum := by decide
  have hdescent : baseEnd_1260857 < baseStart_1260857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260896 : List Nat := [2, 1, 1, 3, 4, 11]
def baseStart_1260896 : Nat := 118140960795 + 1260896 * 2 ^ 59
def prefixEnd_1260896 : Nat := 4983230072969 + 3 ^ 40 * 1260896 * 2
def baseEnd_1260896 : Nat := 5328771220836246685607

theorem tailTrace_1260896 : CollatzResearch.WordTrace tailWord_1260896 prefixEnd_1260896 5328771220836246685607 := by
  unfold tailWord_1260896
  simp only [CollatzResearch.WordTrace]
  refine ⟨22994327619998305368753271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30659103493331073825004361 22994327619998305368753271)
  ·
    refine ⟨34491491429997458053129907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22994327619998305368753271 34491491429997458053129907)
    ·
      refine ⟨51737237144996187079694861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34491491429997458053129907 51737237144996187079694861)
      ·
        refine ⟨19401463929373570154885573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51737237144996187079694861 19401463929373570154885573)
        ·
          refine ⟨3637774486757544404041045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19401463929373570154885573 3637774486757544404041045)
          ·
            refine ⟨5328771220836246685607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3637774486757544404041045 5328771220836246685607)
            ·
              rfl

theorem cell22_1260896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 11].length) (baseStart_1260896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260896 prefixEnd_1260896 := by exact prefixLift 1260896
  have htrace : WordTrace (prefixWord ++ tailWord_1260896) baseStart_1260896 baseEnd_1260896 := by
    simpa [prefixWord, tailWord_1260896, baseEnd_1260896] using wordTrace_append hprefix tailTrace_1260896
  have hstable : (prefixWord ++ tailWord_1260896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260896).length < 2 ^ (prefixWord ++ tailWord_1260896).sum := by decide
  have hdescent : baseEnd_1260896 < baseStart_1260896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260900 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_1260900 : Nat := 118140960795 + 1260900 * 2 ^ 59
def prefixEnd_1260900 : Nat := 4983230072969 + 3 ^ 40 * 1260900 * 2
def baseEnd_1260900 : Nat := 431631838169481304434155

theorem tailTrace_1260900 : CollatzResearch.WordTrace tailWord_1260900 prefixEnd_1260900 431631838169481304434155 := by
  unfold tailWord_1260900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22994400565991059710326077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30659200754654746280434769 22994400565991059710326077)
  ·
    refine ⟨8622900212246647391372279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22994400565991059710326077 8622900212246647391372279)
    ·
      refine ⟨12934350318369971087058419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8622900212246647391372279 12934350318369971087058419)
      ·
        refine ⟨19401525477554956630587629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12934350318369971087058419 19401525477554956630587629)
        ·
          refine ⟨7275572054083108736470361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19401525477554956630587629 7275572054083108736470361)
          ·
            refine ⟨5456679040562331552352771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7275572054083108736470361 5456679040562331552352771)
            ·
              refine ⟨8185018560843497328529157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5456679040562331552352771 8185018560843497328529157)
              ·
                refine ⟨1534690980158155749099217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8185018560843497328529157 1534690980158155749099217)
                ·
                  refine ⟨1151018235118616811824413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1534690980158155749099217 1151018235118616811824413)
                  ·
                    refine ⟨431631838169481304434155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151018235118616811824413 431631838169481304434155)
                    ·
                      rfl

theorem cell22_1260900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_1260900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260900 prefixEnd_1260900 := by exact prefixLift 1260900
  have htrace : WordTrace (prefixWord ++ tailWord_1260900) baseStart_1260900 baseEnd_1260900 := by
    simpa [prefixWord, tailWord_1260900, baseEnd_1260900] using wordTrace_append hprefix tailTrace_1260900
  have hstable : (prefixWord ++ tailWord_1260900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260900).length < 2 ^ (prefixWord ++ tailWord_1260900).sum := by decide
  have hdescent : baseEnd_1260900 < baseStart_1260900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260962 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1260962 : Nat := 118140960795 + 1260962 * 2 ^ 59
def prefixEnd_1260962 : Nat := 4983230072969 + 3 ^ 40 * 1260962 * 2
def baseEnd_1260962 : Nat := 431653062036533809383965

theorem tailTrace_1260962 : CollatzResearch.WordTrace tailWord_1260962 prefixEnd_1260962 431653062036533809383965 := by
  unfold tailWord_1260962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497765614439376002352285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30660708305171669339606093 11497765614439376002352285)
  ·
    refine ⟨4311662105414766000882107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11497765614439376002352285 4311662105414766000882107)
    ·
      refine ⟨6467493158122149001323161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311662105414766000882107 6467493158122149001323161)
      ·
        refine ⟨4850619868591611750992371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6467493158122149001323161 4850619868591611750992371)
        ·
          refine ⟨7275929802887417626488557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850619868591611750992371 7275929802887417626488557)
          ·
            refine ⟨2728473676082781609933209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7275929802887417626488557 2728473676082781609933209)
            ·
              refine ⟨2046355257062086207449907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728473676082781609933209 2046355257062086207449907)
              ·
                refine ⟨3069532885593129311174861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046355257062086207449907 3069532885593129311174861)
                ·
                  refine ⟨1151074832097423491690573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3069532885593129311174861 1151074832097423491690573)
                  ·
                    refine ⟨431653062036533809383965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151074832097423491690573 431653062036533809383965)
                    ·
                      rfl

theorem cell22_1260962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1260962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260962 prefixEnd_1260962 := by exact prefixLift 1260962
  have htrace : WordTrace (prefixWord ++ tailWord_1260962) baseStart_1260962 baseEnd_1260962 := by
    simpa [prefixWord, tailWord_1260962, baseEnd_1260962] using wordTrace_append hprefix tailTrace_1260962
  have hstable : (prefixWord ++ tailWord_1260962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260962).length < 2 ^ (prefixWord ++ tailWord_1260962).sum := by decide
  have hdescent : baseEnd_1260962 < baseStart_1260962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260996 : List Nat := [2, 3, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1260996 : Nat := 118140960795 + 1260996 * 2 ^ 59
def prefixEnd_1260996 : Nat := 4983230072969 + 3 ^ 40 * 1260996 * 2
def baseEnd_1260996 : Nat := 431664700931369054033861

theorem tailTrace_1260996 : CollatzResearch.WordTrace tailWord_1260996 prefixEnd_1260996 431664700931369054033861 := by
  unfold tailWord_1260996
  simp only [CollatzResearch.WordTrace]
  refine ⟨22996151269817163908073421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30661535026422885210764561 22996151269817163908073421)
  ·
    refine ⟨8623556726181436465527533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22996151269817163908073421 8623556726181436465527533)
    ·
      refine ⟨3233833772318038674572825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8623556726181436465527533 3233833772318038674572825)
      ·
        refine ⟨2425375329238529005929619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3233833772318038674572825 2425375329238529005929619)
        ·
          refine ⟨3638062993857793508894429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425375329238529005929619 3638062993857793508894429)
          ·
            refine ⟨1364273622696672565835411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3638062993857793508894429 1364273622696672565835411)
            ·
              refine ⟨2046410434045008848753117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364273622696672565835411 2046410434045008848753117)
              ·
                refine ⟨767403912766878318282419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2046410434045008848753117 767403912766878318282419)
                ·
                  refine ⟨1151105869150317477423629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767403912766878318282419 1151105869150317477423629)
                  ·
                    refine ⟨431664700931369054033861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151105869150317477423629 431664700931369054033861)
                    ·
                      rfl

theorem cell22_1260996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1260996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260996 prefixEnd_1260996 := by exact prefixLift 1260996
  have htrace : WordTrace (prefixWord ++ tailWord_1260996) baseStart_1260996 baseEnd_1260996 := by
    simpa [prefixWord, tailWord_1260996, baseEnd_1260996] using wordTrace_append hprefix tailTrace_1260996
  have hstable : (prefixWord ++ tailWord_1260996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260996).length < 2 ^ (prefixWord ++ tailWord_1260996).sum := by decide
  have hdescent : baseEnd_1260996 < baseStart_1260996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261048 : List Nat := [2, 1, 2, 1, 1, 5, 2, 8]
def baseStart_1261048 : Nat := 118140960795 + 1261048 * 2 ^ 59
def prefixEnd_1261048 : Nat := 4983230072969 + 3 ^ 40 * 1261048 * 2
def baseEnd_1261048 : Nat := 47964722399339805748189

theorem tailTrace_1261048 : CollatzResearch.WordTrace tailWord_1261048 prefixEnd_1261048 47964722399339805748189 := by
  unfold tailWord_1261048
  simp only [CollatzResearch.WordTrace]
  refine ⟨22997099567722970348519899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30662799423630627131359865 22997099567722970348519899)
  ·
    refine ⟨34495649351584455522779849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22997099567722970348519899 34495649351584455522779849)
    ·
      refine ⟨25871737013688341642084887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34495649351584455522779849 25871737013688341642084887)
      ·
        refine ⟨38807605520532512463127331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25871737013688341642084887 38807605520532512463127331)
        ·
          refine ⟨58211408280798768694690997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38807605520532512463127331 58211408280798768694690997)
          ·
            refine ⟨5457319526324884565127281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58211408280798768694690997 5457319526324884565127281)
            ·
              refine ⟨4092989644743663423845461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457319526324884565127281 4092989644743663423845461)
              ·
                refine ⟨47964722399339805748189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4092989644743663423845461 47964722399339805748189)
                ·
                  rfl

theorem cell22_1261048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_1261048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261048 prefixEnd_1261048 := by exact prefixLift 1261048
  have htrace : WordTrace (prefixWord ++ tailWord_1261048) baseStart_1261048 baseEnd_1261048 := by
    simpa [prefixWord, tailWord_1261048, baseEnd_1261048] using wordTrace_append hprefix tailTrace_1261048
  have hstable : (prefixWord ++ tailWord_1261048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261048).length < 2 ^ (prefixWord ++ tailWord_1261048).sum := by decide
  have hdescent : baseEnd_1261048 < baseStart_1261048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261050 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_1261050 : Nat := 118140960795 + 1261050 * 2 ^ 59
def prefixEnd_1261050 : Nat := 4983230072969 + 3 ^ 40 * 1261050 * 2
def baseEnd_1261050 : Nat := 431683186234930913183695

theorem tailTrace_1261050 : CollatzResearch.WordTrace tailWord_1261050 prefixEnd_1261050 431683186234930913183695 := by
  unfold tailWord_1261050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11498568020359673759653151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30662848054292463359075069 11498568020359673759653151)
  ·
    refine ⟨17247852030539510639479727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11498568020359673759653151 17247852030539510639479727)
    ·
      refine ⟨25871778045809265959219591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17247852030539510639479727 25871778045809265959219591)
      ·
        refine ⟨38807667068713898938829387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25871778045809265959219591 38807667068713898938829387)
        ·
          refine ⟨58211500603070848408244081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38807667068713898938829387 58211500603070848408244081)
          ·
            refine ⟨43658625452303136306183061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58211500603070848408244081 43658625452303136306183061)
            ·
              refine ⟨2046498068076709514352331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43658625452303136306183061 2046498068076709514352331)
              ·
                refine ⟨3069747102115064271528497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046498068076709514352331 3069747102115064271528497)
                ·
                  refine ⟨2302310326586298203646373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3069747102115064271528497 2302310326586298203646373)
                  ·
                    refine ⟨431683186234930913183695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2302310326586298203646373 431683186234930913183695)
                    ·
                      rfl

theorem cell22_1261050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_1261050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261050 prefixEnd_1261050 := by exact prefixLift 1261050
  have htrace : WordTrace (prefixWord ++ tailWord_1261050) baseStart_1261050 baseEnd_1261050 := by
    simpa [prefixWord, tailWord_1261050, baseEnd_1261050] using wordTrace_append hprefix tailTrace_1261050
  have hstable : (prefixWord ++ tailWord_1261050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261050).length < 2 ^ (prefixWord ++ tailWord_1261050).sum := by decide
  have hdescent : baseEnd_1261050 < baseStart_1261050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261093 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 9]
def baseStart_1261093 : Nat := 118140960795 + 1261093 * 2 ^ 59
def prefixEnd_1261093 : Nat := 4983230072969 + 3 ^ 40 * 1261093 * 2
def baseEnd_1261093 : Nat := 143899302004564378119521

theorem tailTrace_1261093 : CollatzResearch.WordTrace tailWord_1261093 prefixEnd_1261093 143899302004564378119521 := by
  unfold tailWord_1261093
  simp only [CollatzResearch.WordTrace]
  refine ⟨45995840420282913382427933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30663893613521942254951955 45995840420282913382427933)
  ·
    refine ⟨17248440157606092518410475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45995840420282913382427933 17248440157606092518410475)
    ·
      refine ⟨25872660236409138777615713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17248440157606092518410475 25872660236409138777615713)
      ·
        refine ⟨19404495177306854083211785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25872660236409138777615713 19404495177306854083211785)
        ·
          refine ⟨14553371382980140562408839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19404495177306854083211785 14553371382980140562408839)
          ·
            refine ⟨21830057074470210843613259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14553371382980140562408839 21830057074470210843613259)
            ·
              refine ⟨32745085611705316265419889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21830057074470210843613259 32745085611705316265419889)
              ·
                refine ⟨24558814208778987199064917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32745085611705316265419889 24558814208778987199064917)
                ·
                  refine ⟨143899302004564378119521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24558814208778987199064917 143899302004564378119521)
                  ·
                    rfl

theorem cell22_1261093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_1261093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261093 prefixEnd_1261093 := by exact prefixLift 1261093
  have htrace : WordTrace (prefixWord ++ tailWord_1261093) baseStart_1261093 baseEnd_1261093 := by
    simpa [prefixWord, tailWord_1261093, baseEnd_1261093] using wordTrace_append hprefix tailTrace_1261093
  have hstable : (prefixWord ++ tailWord_1261093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261093).length < 2 ^ (prefixWord ++ tailWord_1261093).sum := by decide
  have hdescent : baseEnd_1261093 < baseStart_1261093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261114 : List Nat := [3, 1, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_1261114 : Nat := 118140960795 + 1261114 * 2 ^ 59
def prefixEnd_1261114 : Nat := 4983230072969 + 3 ^ 40 * 1261114 * 2
def baseEnd_1261114 : Nat := 431705094742856079583499

theorem tailTrace_1261114 : CollatzResearch.WordTrace tailWord_1261114 prefixEnd_1261114 431705094742856079583499 := by
  unfold tailWord_1261114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11499151588301708492235599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30664404235471222645961597 11499151588301708492235599)
  ·
    refine ⟨17248727382452562738353399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11499151588301708492235599 17248727382452562738353399)
    ·
      refine ⟨25873091073678844107530099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17248727382452562738353399 25873091073678844107530099)
      ·
        refine ⟨38809636610518266161295149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25873091073678844107530099 38809636610518266161295149)
        ·
          refine ⟨14553613728944349810485681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38809636610518266161295149 14553613728944349810485681)
          ·
            refine ⟨10915210296708262357864261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14553613728944349810485681 10915210296708262357864261)
            ·
              refine ⟨2046601930632799192099549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10915210296708262357864261 2046601930632799192099549)
              ·
                refine ⟨767475723987299697037331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2046601930632799192099549 767475723987299697037331)
                ·
                  refine ⟨1151213585980949545555997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767475723987299697037331 1151213585980949545555997)
                  ·
                    refine ⟨431705094742856079583499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151213585980949545555997 431705094742856079583499)
                    ·
                      rfl

theorem cell22_1261114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_1261114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261114 prefixEnd_1261114 := by exact prefixLift 1261114
  have htrace : WordTrace (prefixWord ++ tailWord_1261114) baseStart_1261114 baseEnd_1261114 := by
    simpa [prefixWord, tailWord_1261114, baseEnd_1261114] using wordTrace_append hprefix tailTrace_1261114
  have hstable : (prefixWord ++ tailWord_1261114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261114).length < 2 ^ (prefixWord ++ tailWord_1261114).sum := by decide
  have hdescent : baseEnd_1261114 < baseStart_1261114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261155 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 6]
def baseStart_1261155 : Nat := 118140960795 + 1261155 * 2 ^ 59
def prefixEnd_1261155 : Nat := 4983230072969 + 3 ^ 40 * 1261155 * 2
def baseEnd_1261155 : Nat := 143906376626915213102791

theorem tailTrace_1261155 : CollatzResearch.WordTrace tailWord_1261155 prefixEnd_1261155 143906376626915213102791 := by
  unfold tailWord_1261155
  simp only [CollatzResearch.WordTrace]
  refine ⟨45998101746058297971184919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30665401164038865314123279 45998101746058297971184919)
  ·
    refine ⟨68997152619087446956777379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45998101746058297971184919 68997152619087446956777379)
    ·
      refine ⟨103495728928631170435166069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68997152619087446956777379 103495728928631170435166069)
      ·
        refine ⟨9702724587059172228296819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103495728928631170435166069 9702724587059172228296819)
        ·
          refine ⟨14554086880588758342445229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9702724587059172228296819 14554086880588758342445229)
          ·
            refine ⟨5457782580220784378416961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14554086880588758342445229 5457782580220784378416961)
            ·
              refine ⟨4093336935165588283812721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457782580220784378416961 4093336935165588283812721)
              ·
                refine ⟨3070002701374191212859541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4093336935165588283812721 3070002701374191212859541)
                ·
                  refine ⟨143906376626915213102791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3070002701374191212859541 143906376626915213102791)
                  ·
                    rfl

theorem cell22_1261155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 6].length) (baseStart_1261155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261155 prefixEnd_1261155 := by exact prefixLift 1261155
  have htrace : WordTrace (prefixWord ++ tailWord_1261155) baseStart_1261155 baseEnd_1261155 := by
    simpa [prefixWord, tailWord_1261155, baseEnd_1261155] using wordTrace_append hprefix tailTrace_1261155
  have hstable : (prefixWord ++ tailWord_1261155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261155).length < 2 ^ (prefixWord ++ tailWord_1261155).sum := by decide
  have hdescent : baseEnd_1261155 < baseStart_1261155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261157 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_1261157 : Nat := 118140960795 + 1261157 * 2 ^ 59
def prefixEnd_1261157 : Nat := 4983230072969 + 3 ^ 40 * 1261157 * 2
def baseEnd_1261157 : Nat := 431719814521618300758367

theorem tailTrace_1261157 : CollatzResearch.WordTrace tailWord_1261157 prefixEnd_1261157 431719814521618300758367 := by
  unfold tailWord_1261157
  simp only [CollatzResearch.WordTrace]
  refine ⟨45998174692051052312757725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30665449794700701541838483 45998174692051052312757725)
  ·
    refine ⟨17249315509519144617284147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45998174692051052312757725 17249315509519144617284147)
    ·
      refine ⟨25873973264278716925926221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17249315509519144617284147 25873973264278716925926221)
      ·
        refine ⟨9702739974104518847222333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25873973264278716925926221 9702739974104518847222333)
        ·
          refine ⟨3638527490289194567708375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9702739974104518847222333 3638527490289194567708375)
          ·
            refine ⟨5457791235433791851562563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638527490289194567708375 5457791235433791851562563)
            ·
              refine ⟨8186686853150687777343845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5457791235433791851562563 8186686853150687777343845)
              ·
                refine ⟨1535003784965753958251971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8186686853150687777343845 1535003784965753958251971)
                ·
                  refine ⟨2302505677448630937377957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535003784965753958251971 2302505677448630937377957)
                  ·
                    refine ⟨431719814521618300758367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2302505677448630937377957 431719814521618300758367)
                    ·
                      rfl

theorem cell22_1261157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_1261157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261157 prefixEnd_1261157 := by exact prefixLift 1261157
  have htrace : WordTrace (prefixWord ++ tailWord_1261157) baseStart_1261157 baseEnd_1261157 := by
    simpa [prefixWord, tailWord_1261157, baseEnd_1261157] using wordTrace_append hprefix tailTrace_1261157
  have hstable : (prefixWord ++ tailWord_1261157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261157).length < 2 ^ (prefixWord ++ tailWord_1261157).sum := by decide
  have hdescent : baseEnd_1261157 < baseStart_1261157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261174 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1261174 : Nat := 118140960795 + 1261174 * 2 ^ 59
def prefixEnd_1261174 : Nat := 4983230072969 + 3 ^ 40 * 1261174 * 2
def baseEnd_1261174 : Nat := 431725633969035923083315

theorem tailTrace_1261174 : CollatzResearch.WordTrace tailWord_1261174 prefixEnd_1261174 431725633969035923083315 := by
  unfold tailWord_1261174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874924670811841513507911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30665863155326309477417717 2874924670811841513507911)
  ·
    refine ⟨4312387006217762270261867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874924670811841513507911 4312387006217762270261867)
    ·
      refine ⟨6468580509326643405392801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4312387006217762270261867 6468580509326643405392801)
      ·
        refine ⟨4851435381994982554044601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6468580509326643405392801 4851435381994982554044601)
        ·
          refine ⟨3638576536496236915533451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4851435381994982554044601 3638576536496236915533451)
          ·
            refine ⟨5457864804744355373300177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638576536496236915533451 5457864804744355373300177)
            ·
              refine ⟨4093398603558266529975133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457864804744355373300177 4093398603558266529975133)
              ·
                refine ⟨1535024476334349948740675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4093398603558266529975133 1535024476334349948740675)
                ·
                  refine ⟨2302536714501524923111013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535024476334349948740675 2302536714501524923111013)
                  ·
                    refine ⟨431725633969035923083315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2302536714501524923111013 431725633969035923083315)
                    ·
                      rfl

theorem cell22_1261174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1261174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261174 prefixEnd_1261174 := by exact prefixLift 1261174
  have htrace : WordTrace (prefixWord ++ tailWord_1261174) baseStart_1261174 baseEnd_1261174 := by
    simpa [prefixWord, tailWord_1261174, baseEnd_1261174] using wordTrace_append hprefix tailTrace_1261174
  have hstable : (prefixWord ++ tailWord_1261174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261174).length < 2 ^ (prefixWord ++ tailWord_1261174).sum := by decide
  have hdescent : baseEnd_1261174 < baseStart_1261174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261187 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 2, 3]
def baseStart_1261187 : Nat := 118140960795 + 1261187 * 2 ^ 59
def prefixEnd_1261187 : Nat := 4983230072969 + 3 ^ 40 * 1261187 * 2
def baseEnd_1261187 : Nat := 431730084134708222508275

theorem tailTrace_1261187 : CollatzResearch.WordTrace tailWord_1261187 prefixEnd_1261187 431730084134708222508275 := by
  unfold tailWord_1261187
  simp only [CollatzResearch.WordTrace]
  refine ⟨45999268881942367436349815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30666179254628244957566543 45999268881942367436349815)
  ·
    refine ⟨68998903322913551154524723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45999268881942367436349815 68998903322913551154524723)
    ·
      refine ⟨103498354984370326731787085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68998903322913551154524723 103498354984370326731787085)
      ·
        refine ⟨38811883119138872524420157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103498354984370326731787085 38811883119138872524420157)
        ·
          refine ⟨14554456169677077196657559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38811883119138872524420157 14554456169677077196657559)
          ·
            refine ⟨21831684254515615794986339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14554456169677077196657559 21831684254515615794986339)
            ·
              refine ⟨32747526381773423692479509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21831684254515615794986339 32747526381773423692479509)
              ·
                refine ⟨1535040299145629235584977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32747526381773423692479509 1535040299145629235584977)
                ·
                  refine ⟨1151280224359221926688733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1535040299145629235584977 1151280224359221926688733)
                  ·
                    refine ⟨431730084134708222508275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151280224359221926688733 431730084134708222508275)
                    ·
                      rfl

theorem cell22_1261187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 3].length) (baseStart_1261187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261187 prefixEnd_1261187 := by exact prefixLift 1261187
  have htrace : WordTrace (prefixWord ++ tailWord_1261187) baseStart_1261187 baseEnd_1261187 := by
    simpa [prefixWord, tailWord_1261187, baseEnd_1261187] using wordTrace_append hprefix tailTrace_1261187
  have hstable : (prefixWord ++ tailWord_1261187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261187).length < 2 ^ (prefixWord ++ tailWord_1261187).sum := by decide
  have hdescent : baseEnd_1261187 < baseStart_1261187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261189 : List Nat := [1, 3, 1, 1, 4, 1, 5, 2, 4]
def baseStart_1261189 : Nat := 118140960795 + 1261189 * 2 ^ 59
def prefixEnd_1261189 : Nat := 4983230072969 + 3 ^ 40 * 1261189 * 2
def baseEnd_1261189 : Nat := 143910256258526961319423

theorem tailTrace_1261189 : CollatzResearch.WordTrace tailWord_1261189 prefixEnd_1261189 143910256258526961319423 := by
  unfold tailWord_1261189
  simp only [CollatzResearch.WordTrace]
  refine ⟨45999341827935121777922621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30666227885290081185281747 45999341827935121777922621)
  ·
    refine ⟨17249753185475670666720983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45999341827935121777922621 17249753185475670666720983)
    ·
      refine ⟨25874629778213506000081475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17249753185475670666720983 25874629778213506000081475)
      ·
        refine ⟨38811944667320259000122213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25874629778213506000081475 38811944667320259000122213)
        ·
          refine ⟨7277239625122548562522915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38811944667320259000122213 7277239625122548562522915)
          ·
            refine ⟨10915859437683822843784373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7277239625122548562522915 10915859437683822843784373)
            ·
              refine ⟨1023361822282858391604785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10915859437683822843784373 1023361822282858391604785)
              ·
                refine ⟨767521366712143793703589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023361822282858391604785 767521366712143793703589)
                ·
                  refine ⟨143910256258526961319423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 767521366712143793703589 143910256258526961319423)
                  ·
                    rfl

theorem cell22_1261189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_1261189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261189 prefixEnd_1261189 := by exact prefixLift 1261189
  have htrace : WordTrace (prefixWord ++ tailWord_1261189) baseStart_1261189 baseEnd_1261189 := by
    simpa [prefixWord, tailWord_1261189, baseEnd_1261189] using wordTrace_append hprefix tailTrace_1261189
  have hstable : (prefixWord ++ tailWord_1261189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261189).length < 2 ^ (prefixWord ++ tailWord_1261189).sum := by decide
  have hdescent : baseEnd_1261189 < baseStart_1261189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261238 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1261238 : Nat := 118140960795 + 1261238 * 2 ^ 59
def prefixEnd_1261238 : Nat := 4983230072969 + 3 ^ 40 * 1261238 * 2
def baseEnd_1261238 : Nat := 431747542476961089483119

theorem tailTrace_1261238 : CollatzResearch.WordTrace tailWord_1261238 prefixEnd_1261238 431747542476961089483119 := by
  unfold tailWord_1261238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875070562797350196653523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30667419336505068764304245 2875070562797350196653523)
  ·
    refine ⟨4312605844196025294980285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2875070562797350196653523 4312605844196025294980285)
    ·
      refine ⟨1617227191573509485617607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4312605844196025294980285 1617227191573509485617607)
      ·
        refine ⟨2425840787360264228426411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617227191573509485617607 2425840787360264228426411)
        ·
          refine ⟨3638761181040396342639617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425840787360264228426411 3638761181040396342639617)
          ·
            refine ⟨2729070885780297256979713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3638761181040396342639617 2729070885780297256979713)
            ·
              refine ⟨2046803164335222942734785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729070885780297256979713 2046803164335222942734785)
              ·
                refine ⟨1535102373251417207051089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046803164335222942734785 1535102373251417207051089)
                ·
                  refine ⟨1151326779938562905288317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1535102373251417207051089 1151326779938562905288317)
                  ·
                    refine ⟨431747542476961089483119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151326779938562905288317 431747542476961089483119)
                    ·
                      rfl

theorem cell22_1261238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1261238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261238 prefixEnd_1261238 := by exact prefixLift 1261238
  have htrace : WordTrace (prefixWord ++ tailWord_1261238) baseStart_1261238 baseEnd_1261238 := by
    simpa [prefixWord, tailWord_1261238, baseEnd_1261238] using wordTrace_append hprefix tailTrace_1261238
  have hstable : (prefixWord ++ tailWord_1261238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261238).length < 2 ^ (prefixWord ++ tailWord_1261238).sum := by decide
  have hdescent : baseEnd_1261238 < baseStart_1261238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261262 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1261262 : Nat := 118140960795 + 1261262 * 2 ^ 59
def prefixEnd_1261262 : Nat := 4983230072969 + 3 ^ 40 * 1261262 * 2
def baseEnd_1261262 : Nat := 143918586055811008961015

theorem tailTrace_1261262 : CollatzResearch.WordTrace tailWord_1261262 prefixEnd_1261262 143918586055811008961015 := by
  unfold tailWord_1261262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750250544583831905666255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30668002904447103496886693 5750250544583831905666255)
  ·
    refine ⟨8625375816875747858499383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5750250544583831905666255 8625375816875747858499383)
    ·
      refine ⟨12938063725313621787749075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8625375816875747858499383 12938063725313621787749075)
      ·
        refine ⟨19407095587970432681623613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12938063725313621787749075 19407095587970432681623613)
        ·
          refine ⟨7277660845488912255608855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19407095587970432681623613 7277660845488912255608855)
          ·
            refine ⟨10916491268233368383413283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7277660845488912255608855 10916491268233368383413283)
            ·
              refine ⟨16374736902350052575119925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10916491268233368383413283 16374736902350052575119925)
              ·
                refine ⟨1535131584595317428917493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16374736902350052575119925 1535131584595317428917493)
                ·
                  refine ⟨143918586055811008961015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1535131584595317428917493 143918586055811008961015)
                  ·
                    rfl

theorem cell22_1261262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1261262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261262 prefixEnd_1261262 := by exact prefixLift 1261262
  have htrace : WordTrace (prefixWord ++ tailWord_1261262) baseStart_1261262 baseEnd_1261262 := by
    simpa [prefixWord, tailWord_1261262, baseEnd_1261262] using wordTrace_append hprefix tailTrace_1261262
  have hstable : (prefixWord ++ tailWord_1261262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261262).length < 2 ^ (prefixWord ++ tailWord_1261262).sum := by decide
  have hdescent : baseEnd_1261262 < baseStart_1261262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261270 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1261270 : Nat := 118140960795 + 1261270 * 2 ^ 59
def prefixEnd_1261270 : Nat := 4983230072969 + 3 ^ 40 * 1261270 * 2
def baseEnd_1261270 : Nat := 431758496730923672683021

theorem tailTrace_1261270 : CollatzResearch.WordTrace tailWord_1261270 prefixEnd_1261270 431758496730923672683021 := by
  unfold tailWord_1261270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875143508790104538226329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30668197427094448407747509 2875143508790104538226329)
  ·
    refine ⟨2156357631592578403669747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2875143508790104538226329 2156357631592578403669747)
    ·
      refine ⟨3234536447388867605504621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156357631592578403669747 3234536447388867605504621)
      ·
        refine ⟨1212951167770825352064233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3234536447388867605504621 1212951167770825352064233)
        ·
          refine ⟨909713375828119014048175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1212951167770825352064233 909713375828119014048175)
          ·
            refine ⟨1364570063742178521072263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909713375828119014048175 1364570063742178521072263)
            ·
              refine ⟨2046855095613267781608395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364570063742178521072263 2046855095613267781608395)
              ·
                refine ⟨3070282643419901672412593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046855095613267781608395 3070282643419901672412593)
                ·
                  refine ⟨2302711982564926254309445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070282643419901672412593 2302711982564926254309445)
                  ·
                    refine ⟨431758496730923672683021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2302711982564926254309445 431758496730923672683021)
                    ·
                      rfl

theorem cell22_1261270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1261270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261270 prefixEnd_1261270 := by exact prefixLift 1261270
  have htrace : WordTrace (prefixWord ++ tailWord_1261270) baseStart_1261270 baseEnd_1261270 := by
    simpa [prefixWord, tailWord_1261270, baseEnd_1261270] using wordTrace_append hprefix tailTrace_1261270
  have hstable : (prefixWord ++ tailWord_1261270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261270).length < 2 ^ (prefixWord ++ tailWord_1261270).sum := by decide
  have hdescent : baseEnd_1261270 < baseStart_1261270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261283 : List Nat := [1, 1, 1, 7, 2, 1, 2, 3, 1, 3]
def baseStart_1261283 : Nat := 118140960795 + 1261283 * 2 ^ 59
def prefixEnd_1261283 : Nat := 4983230072969 + 3 ^ 40 * 1261283 * 2
def baseEnd_1261283 : Nat := 431762946896595972107981

theorem tailTrace_1261283 : CollatzResearch.WordTrace tailWord_1261283 prefixEnd_1261283 431762946896595972107981 := by
  unfold tailWord_1261283
  simp only [CollatzResearch.WordTrace]
  refine ⟨46002770289594575831844503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30668513526396383887896335 46002770289594575831844503)
  ·
    refine ⟨69004155434391863747766755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46002770289594575831844503 69004155434391863747766755)
    ·
      refine ⟨103506233151587795621650133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69004155434391863747766755 103506233151587795621650133)
      ·
        refine ⟨2425927339490338959882425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 103506233151587795621650133 2425927339490338959882425)
        ·
          refine ⟨1819445504617754219911819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2425927339490338959882425 1819445504617754219911819)
          ·
            refine ⟨2729168256926631329867729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819445504617754219911819 2729168256926631329867729)
            ·
              refine ⟨2046876192694973497400797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729168256926631329867729 2046876192694973497400797)
              ·
                refine ⟨767578572260615061525299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2046876192694973497400797 767578572260615061525299)
                ·
                  refine ⟨1151367858390922592287949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767578572260615061525299 1151367858390922592287949)
                  ·
                    refine ⟨431762946896595972107981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151367858390922592287949 431762946896595972107981)
                    ·
                      rfl

theorem cell22_1261283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 3].length) (baseStart_1261283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261283 prefixEnd_1261283 := by exact prefixLift 1261283
  have htrace : WordTrace (prefixWord ++ tailWord_1261283) baseStart_1261283 baseEnd_1261283 := by
    simpa [prefixWord, tailWord_1261283, baseEnd_1261283] using wordTrace_append hprefix tailTrace_1261283
  have hstable : (prefixWord ++ tailWord_1261283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261283).length < 2 ^ (prefixWord ++ tailWord_1261283).sum := by decide
  have hdescent : baseEnd_1261283 < baseStart_1261283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261300 : List Nat := [2, 6, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1261300 : Nat := 118140960795 + 1261300 * 2 ^ 59
def prefixEnd_1261300 : Nat := 4983230072969 + 3 ^ 40 * 1261300 * 2
def baseEnd_1261300 : Nat := 431768766344013594432929

theorem tailTrace_1261300 : CollatzResearch.WordTrace tailWord_1261300 prefixEnd_1261300 431768766344013594432929 := by
  unfold tailWord_1261300
  simp only [CollatzResearch.WordTrace]
  refine ⟨23001695165266493867606677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30668926887021991823475569 23001695165266493867606677)
  ·
    refine ⟨1078204460871866900044063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23001695165266493867606677 1078204460871866900044063)
    ·
      refine ⟨1617306691307800350066095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078204460871866900044063 1617306691307800350066095)
      ·
        refine ⟨2425960036961700525099143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617306691307800350066095 2425960036961700525099143)
        ·
          refine ⟨3638940055442550787648715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425960036961700525099143 3638940055442550787648715)
          ·
            refine ⟨5458410083163826181473073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638940055442550787648715 5458410083163826181473073)
            ·
              refine ⟨4093807562372869636104805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458410083163826181473073 4093807562372869636104805)
              ·
                refine ⟨767588917944913056769651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4093807562372869636104805 767588917944913056769651)
                ·
                  refine ⟨1151383376917369585154477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767588917944913056769651 1151383376917369585154477)
                  ·
                    refine ⟨431768766344013594432929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151383376917369585154477 431768766344013594432929)
                    ·
                      rfl

theorem cell22_1261300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1261300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261300 prefixEnd_1261300 := by exact prefixLift 1261300
  have htrace : WordTrace (prefixWord ++ tailWord_1261300) baseStart_1261300 baseEnd_1261300 := by
    simpa [prefixWord, tailWord_1261300, baseEnd_1261300] using wordTrace_append hprefix tailTrace_1261300
  have hstable : (prefixWord ++ tailWord_1261300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261300).length < 2 ^ (prefixWord ++ tailWord_1261300).sum := by decide
  have hdescent : baseEnd_1261300 < baseStart_1261300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261305 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_1261305 : Nat := 118140960795 + 1261305 * 2 ^ 59
def prefixEnd_1261305 : Nat := 4983230072969 + 3 ^ 40 * 1261305 * 2
def baseEnd_1261305 : Nat := 431770477946195248057913

theorem tailTrace_1261305 : CollatzResearch.WordTrace tailWord_1261305 prefixEnd_1261305 431770477946195248057913 := by
  unfold tailWord_1261305
  simp only [CollatzResearch.WordTrace]
  refine ⟨46003572695514873589145369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30669048463676582392763579 46003572695514873589145369)
  ·
    refine ⟨34502679521636155191859027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46003572695514873589145369 34502679521636155191859027)
    ·
      refine ⟨51754019282454232787788541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34502679521636155191859027 51754019282454232787788541)
      ·
        refine ⟨19407757230920337295420703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51754019282454232787788541 19407757230920337295420703)
        ·
          refine ⟨29111635846380505943131055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19407757230920337295420703 29111635846380505943131055)
          ·
            refine ⟨43667453769570758914696583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29111635846380505943131055 43667453769570758914696583)
            ·
              refine ⟨65501180654356138372044875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43667453769570758914696583 65501180654356138372044875)
              ·
                refine ⟨98251770981534207558067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65501180654356138372044875 98251770981534207558067313)
                ·
                  refine ⟨73688828236150655668550485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98251770981534207558067313 73688828236150655668550485)
                  ·
                    refine ⟨431770477946195248057913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73688828236150655668550485 431770477946195248057913)
                    ·
                      rfl

theorem cell22_1261305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_1261305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261305 prefixEnd_1261305 := by exact prefixLift 1261305
  have htrace : WordTrace (prefixWord ++ tailWord_1261305) baseStart_1261305 baseEnd_1261305 := by
    simpa [prefixWord, tailWord_1261305, baseEnd_1261305] using wordTrace_append hprefix tailTrace_1261305
  have hstable : (prefixWord ++ tailWord_1261305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261305).length < 2 ^ (prefixWord ++ tailWord_1261305).sum := by decide
  have hdescent : baseEnd_1261305 < baseStart_1261305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261352 : List Nat := [2, 1, 5, 1, 1, 2, 10]
def baseStart_1261352 : Nat := 118140960795 + 1261352 * 2 ^ 59
def prefixEnd_1261352 : Nat := 4983230072969 + 3 ^ 40 * 1261352 * 2
def baseEnd_1261352 : Nat := 15992095074322325634547

theorem tailTrace_1261352 : CollatzResearch.WordTrace tailWord_1261352 prefixEnd_1261352 15992095074322325634547 := by
  unfold tailWord_1261352
  simp only [CollatzResearch.WordTrace]
  refine ⟨23002643463172300308053155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30670191284229733744070873 23002643463172300308053155)
  ·
    refine ⟨34503965194758450462079733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23002643463172300308053155 34503965194758450462079733)
    ·
      refine ⟨3234746737008604730819975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34503965194758450462079733 3234746737008604730819975)
      ·
        refine ⟨4852120105512907096229963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234746737008604730819975 4852120105512907096229963)
        ·
          refine ⟨7278180158269360644344945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4852120105512907096229963 7278180158269360644344945)
          ·
            refine ⟨5458635118702020483258709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7278180158269360644344945 5458635118702020483258709)
            ·
              refine ⟨15992095074322325634547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5458635118702020483258709 15992095074322325634547)
              ·
                rfl

theorem cell22_1261352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 10].length) (baseStart_1261352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261352 prefixEnd_1261352 := by exact prefixLift 1261352
  have htrace : WordTrace (prefixWord ++ tailWord_1261352) baseStart_1261352 baseEnd_1261352 := by
    simpa [prefixWord, tailWord_1261352, baseEnd_1261352] using wordTrace_append hprefix tailTrace_1261352
  have hstable : (prefixWord ++ tailWord_1261352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261352).length < 2 ^ (prefixWord ++ tailWord_1261352).sum := by decide
  have hdescent : baseEnd_1261352 < baseStart_1261352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261358 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_1261358 : Nat := 118140960795 + 1261358 * 2 ^ 59
def prefixEnd_1261358 : Nat := 4983230072969 + 3 ^ 40 * 1261358 * 2
def baseEnd_1261358 : Nat := 143929540309773592160917

theorem tailTrace_1261358 : CollatzResearch.WordTrace tailWord_1261358 prefixEnd_1261358 143929540309773592160917 := by
  unfold tailWord_1261358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750688220540357955103091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30670337176215242427216485 5750688220540357955103091)
  ·
    refine ⟨8626032330810536932654637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5750688220540357955103091 8626032330810536932654637)
    ·
      refine ⟨3234762124053951349745489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8626032330810536932654637 3234762124053951349745489)
      ·
        refine ⟨2426071593040463512309117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3234762124053951349745489 2426071593040463512309117)
        ·
          refine ⟨909776847390173817115919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2426071593040463512309117 909776847390173817115919)
          ·
            refine ⟨1364665271085260725673879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909776847390173817115919 1364665271085260725673879)
            ·
              refine ⟨2046997906627891088510819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364665271085260725673879 2046997906627891088510819)
              ·
                refine ⟨3070496859941836632766229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046997906627891088510819 3070496859941836632766229)
                ·
                  refine ⟨143929540309773592160917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3070496859941836632766229 143929540309773592160917)
                  ·
                    rfl

theorem cell22_1261358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_1261358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261358 prefixEnd_1261358 := by exact prefixLift 1261358
  have htrace : WordTrace (prefixWord ++ tailWord_1261358) baseStart_1261358 baseEnd_1261358 := by
    simpa [prefixWord, tailWord_1261358, baseEnd_1261358] using wordTrace_append hprefix tailTrace_1261358
  have hstable : (prefixWord ++ tailWord_1261358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261358).length < 2 ^ (prefixWord ++ tailWord_1261358).sum := by decide
  have hdescent : baseEnd_1261358 < baseStart_1261358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261373 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_1261373 : Nat := 118140960795 + 1261373 * 2 ^ 59
def prefixEnd_1261373 : Nat := 4983230072969 + 3 ^ 40 * 1261373 * 2
def baseEnd_1261373 : Nat := 431793755735865737357705

theorem tailTrace_1261373 : CollatzResearch.WordTrace tailWord_1261373 prefixEnd_1261373 431793755735865737357705 := by
  unfold tailWord_1261373
  simp only [CollatzResearch.WordTrace]
  refine ⟨46006052859268521202620773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30670701906179014135080515 46006052859268521202620773)
  ·
    refine ⟨8626134911112847725491395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46006052859268521202620773 8626134911112847725491395)
    ·
      refine ⟨12939202366669271588237093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8626134911112847725491395 12939202366669271588237093)
      ·
        refine ⟨2426100443750488422794455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12939202366669271588237093 2426100443750488422794455)
        ·
          refine ⟨3639150665625732634191683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426100443750488422794455 3639150665625732634191683)
          ·
            refine ⟨5458725998438598951287525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639150665625732634191683 5458725998438598951287525)
            ·
              refine ⟨1023511124707237303366411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5458725998438598951287525 1023511124707237303366411)
              ·
                refine ⟨1535266687060855955049617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023511124707237303366411 1535266687060855955049617)
                ·
                  refine ⟨1151450015295641966287213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1535266687060855955049617 1151450015295641966287213)
                  ·
                    refine ⟨431793755735865737357705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151450015295641966287213 431793755735865737357705)
                    ·
                      rfl

theorem cell22_1261373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_1261373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261373 prefixEnd_1261373 := by exact prefixLift 1261373
  have htrace : WordTrace (prefixWord ++ tailWord_1261373) baseStart_1261373 baseEnd_1261373 := by
    simpa [prefixWord, tailWord_1261373, baseEnd_1261373] using wordTrace_append hprefix tailTrace_1261373
  have hstable : (prefixWord ++ tailWord_1261373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261373).length < 2 ^ (prefixWord ++ tailWord_1261373).sum := by decide
  have hdescent : baseEnd_1261373 < baseStart_1261373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261401 : List Nat := [1, 2, 1, 2, 2, 3, 2, 5, 1, 3]
def baseStart_1261401 : Nat := 118140960795 + 1261401 * 2 ^ 59
def prefixEnd_1261401 : Nat := 4983230072969 + 3 ^ 40 * 1261401 * 2
def baseEnd_1261401 : Nat := 431803340708082997657619

theorem tailTrace_1261401 : CollatzResearch.WordTrace tailWord_1261401 prefixEnd_1261401 431803340708082997657619 := by
  unfold tailWord_1261401
  simp only [CollatzResearch.WordTrace]
  refine ⟨46007074103167081984640057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30671382735444721323093371 46007074103167081984640057)
  ·
    refine ⟨34505305577375311488480043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46007074103167081984640057 34505305577375311488480043)
    ·
      refine ⟨51757958366062967232720065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34505305577375311488480043 51757958366062967232720065)
      ·
        refine ⟨38818468774547225424540049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51757958366062967232720065 38818468774547225424540049)
        ·
          refine ⟨29113851580910419068405037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38818468774547225424540049 29113851580910419068405037)
          ·
            refine ⟨10917694342841407150651889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29113851580910419068405037 10917694342841407150651889)
            ·
              refine ⟨8188270757131055362988917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10917694342841407150651889 8188270757131055362988917)
              ·
                refine ⟨767650383481036440280211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8188270757131055362988917 767650383481036440280211)
                ·
                  refine ⟨1151475575221554660420317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767650383481036440280211 1151475575221554660420317)
                  ·
                    refine ⟨431803340708082997657619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151475575221554660420317 431803340708082997657619)
                    ·
                      rfl

theorem cell22_1261401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 3].length) (baseStart_1261401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261401 prefixEnd_1261401 := by exact prefixLift 1261401
  have htrace : WordTrace (prefixWord ++ tailWord_1261401) baseStart_1261401 baseEnd_1261401 := by
    simpa [prefixWord, tailWord_1261401, baseEnd_1261401] using wordTrace_append hprefix tailTrace_1261401
  have hstable : (prefixWord ++ tailWord_1261401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261401).length < 2 ^ (prefixWord ++ tailWord_1261401).sum := by decide
  have hdescent : baseEnd_1261401 < baseStart_1261401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261429 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1261429 : Nat := 118140960795 + 1261429 * 2 ^ 59
def prefixEnd_1261429 : Nat := 4983230072969 + 3 ^ 40 * 1261429 * 2
def baseEnd_1261429 : Nat := 431812925680300257957533

theorem tailTrace_1261429 : CollatzResearch.WordTrace tailWord_1261429 prefixEnd_1261429 431812925680300257957533 := by
  unfold tailWord_1261429
  simp only [CollatzResearch.WordTrace]
  refine ⟨46008095347065642766659341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30672063564710428511106227 46008095347065642766659341)
  ·
    refine ⟨17253035755149616037497253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46008095347065642766659341 17253035755149616037497253)
    ·
      refine ⟨3234944204090553007030735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17253035755149616037497253 3234944204090553007030735)
      ·
        refine ⟨4852416306135829510546103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234944204090553007030735 4852416306135829510546103)
        ·
          refine ⟨7278624459203744265819155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4852416306135829510546103 7278624459203744265819155)
          ·
            refine ⟨10917936688805616398728733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7278624459203744265819155 10917936688805616398728733)
            ·
              refine ⟨4094226258302106149523275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10917936688805616398728733 4094226258302106149523275)
              ·
                refine ⟨6141339387453159224284913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094226258302106149523275 6141339387453159224284913)
                ·
                  refine ⟨4606004540589869418213685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6141339387453159224284913 4606004540589869418213685)
                  ·
                    refine ⟨431812925680300257957533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4606004540589869418213685 431812925680300257957533)
                    ·
                      rfl

theorem cell22_1261429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1261429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261429 prefixEnd_1261429 := by exact prefixLift 1261429
  have htrace : WordTrace (prefixWord ++ tailWord_1261429) baseStart_1261429 baseEnd_1261429 := by
    simpa [prefixWord, tailWord_1261429, baseEnd_1261429] using wordTrace_append hprefix tailTrace_1261429
  have hstable : (prefixWord ++ tailWord_1261429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261429).length < 2 ^ (prefixWord ++ tailWord_1261429).sum := by decide
  have hdescent : baseEnd_1261429 < baseStart_1261429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261444 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1261444 : Nat := 118140960795 + 1261444 * 2 ^ 59
def prefixEnd_1261444 : Nat := 4983230072969 + 3 ^ 40 * 1261444 * 2
def baseEnd_1261444 : Nat := 431818060486845218832487

theorem tailTrace_1261444 : CollatzResearch.WordTrace tailWord_1261444 prefixEnd_1261444 431818060486845218832487 := by
  unfold tailWord_1261444
  simp only [CollatzResearch.WordTrace]
  refine ⟨23004321221005650164227693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30672428294674200218970257 23004321221005650164227693)
  ·
    refine ⟨8626620457877118811585385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23004321221005650164227693 8626620457877118811585385)
    ·
      refine ⟨6469965343407839108689039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8626620457877118811585385 6469965343407839108689039)
      ·
        refine ⟨9704948015111758663033559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6469965343407839108689039 9704948015111758663033559)
        ·
          refine ⟨14557422022667637994550339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9704948015111758663033559 14557422022667637994550339)
          ·
            refine ⟨21836133034001456991825509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14557422022667637994550339 21836133034001456991825509)
            ·
              refine ⟨4094274943875273185967283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21836133034001456991825509 4094274943875273185967283)
              ·
                refine ⟨6141412415812909778950925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094274943875273185967283 6141412415812909778950925)
                ·
                  refine ⟨2303029655929841167106597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6141412415812909778950925 2303029655929841167106597)
                  ·
                    refine ⟨431818060486845218832487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2303029655929841167106597 431818060486845218832487)
                    ·
                      rfl

theorem cell22_1261444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1261444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261444 prefixEnd_1261444 := by exact prefixLift 1261444
  have htrace : WordTrace (prefixWord ++ tailWord_1261444) baseStart_1261444 baseEnd_1261444 := by
    simpa [prefixWord, tailWord_1261444, baseEnd_1261444] using wordTrace_append hprefix tailTrace_1261444
  have hstable : (prefixWord ++ tailWord_1261444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261444).length < 2 ^ (prefixWord ++ tailWord_1261444).sum := by decide
  have hdescent : baseEnd_1261444 < baseStart_1261444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261476 : List Nat := [2, 3, 1, 2, 1, 3, 2, 4, 4]
def baseStart_1261476 : Nat := 118140960795 + 1261476 * 2 ^ 59
def prefixEnd_1261476 : Nat := 4983230072969 + 3 ^ 40 * 1261476 * 2
def baseEnd_1261476 : Nat := 143943004913602600677463

theorem tailTrace_1261476 : CollatzResearch.WordTrace tailWord_1261476 prefixEnd_1261476 143943004913602600677463 := by
  unfold tailWord_1261476
  simp only [CollatzResearch.WordTrace]
  refine ⟨23004904788947684896810141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30673206385263579862413521 23004904788947684896810141)
  ·
    refine ⟨8626839295855381836303803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23004904788947684896810141 8626839295855381836303803)
    ·
      refine ⟨12940258943783072754455705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8626839295855381836303803 12940258943783072754455705)
      ·
        refine ⟨9705194207837304565841779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12940258943783072754455705 9705194207837304565841779)
        ·
          refine ⟨14557791311755956848762669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9705194207837304565841779 14557791311755956848762669)
          ·
            refine ⟨5459171741908483818286001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14557791311755956848762669 5459171741908483818286001)
            ·
              refine ⟨4094378806431362863714501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5459171741908483818286001 4094378806431362863714501)
              ·
                refine ⟨767696026205880536946469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4094378806431362863714501 767696026205880536946469)
                ·
                  refine ⟨143943004913602600677463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 767696026205880536946469 143943004913602600677463)
                  ·
                    rfl

theorem cell22_1261476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_1261476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261476 prefixEnd_1261476 := by exact prefixLift 1261476
  have htrace : WordTrace (prefixWord ++ tailWord_1261476) baseStart_1261476 baseEnd_1261476 := by
    simpa [prefixWord, tailWord_1261476, baseEnd_1261476] using wordTrace_append hprefix tailTrace_1261476
  have hstable : (prefixWord ++ tailWord_1261476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261476).length < 2 ^ (prefixWord ++ tailWord_1261476).sum := by decide
  have hdescent : baseEnd_1261476 < baseStart_1261476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261487 : List Nat := [1, 1, 2, 1, 2, 2, 4, 9]
def baseStart_1261487 : Nat := 118140960795 + 1261487 * 2 ^ 59
def prefixEnd_1261487 : Nat := 4983230072969 + 3 ^ 40 * 1261487 * 2
def baseEnd_1261487 : Nat := 47981420029511937778595

theorem tailTrace_1261487 : CollatzResearch.WordTrace tailWord_1261487 prefixEnd_1261487 47981420029511937778595 := by
  unfold tailWord_1261487
  simp only [CollatzResearch.WordTrace]
  refine ⟨46010210780855518672270715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30673473853903679114847143 46010210780855518672270715)
  ·
    refine ⟨69015316171283278008406073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46010210780855518672270715 69015316171283278008406073)
    ·
      refine ⟨51761487128462458506304555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69015316171283278008406073 51761487128462458506304555)
      ·
        refine ⟨77642230692693687759456833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51761487128462458506304555 77642230692693687759456833)
        ·
          refine ⟨58231673019520265819592625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77642230692693687759456833 58231673019520265819592625)
          ·
            refine ⟨43673754764640199364694469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58231673019520265819592625 43673754764640199364694469)
            ·
              refine ⟨8188829018370037380880213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43673754764640199364694469 8188829018370037380880213)
              ·
                refine ⟨47981420029511937778595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8188829018370037380880213 47981420029511937778595)
                ·
                  rfl

theorem cell22_1261487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 9].length) (baseStart_1261487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261487 prefixEnd_1261487 := by exact prefixLift 1261487
  have htrace : WordTrace (prefixWord ++ tailWord_1261487) baseStart_1261487 baseEnd_1261487 := by
    simpa [prefixWord, tailWord_1261487, baseEnd_1261487] using wordTrace_append hprefix tailTrace_1261487
  have hstable : (prefixWord ++ tailWord_1261487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261487).length < 2 ^ (prefixWord ++ tailWord_1261487).sum := by decide
  have hdescent : baseEnd_1261487 < baseStart_1261487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261489 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_1261489 : Nat := 118140960795 + 1261489 * 2 ^ 59
def prefixEnd_1261489 : Nat := 4983230072969 + 3 ^ 40 * 1261489 * 2
def baseEnd_1261489 : Nat := 431833464906480101457349

theorem tailTrace_1261489 : CollatzResearch.WordTrace tailWord_1261489 prefixEnd_1261489 431833464906480101457349 := by
  unfold tailWord_1261489
  simp only [CollatzResearch.WordTrace]
  refine ⟨46010283726848273013843521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30673522484565515342562347 46010283726848273013843521)
  ·
    refine ⟨34507712795136204760382641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46010283726848273013843521 34507712795136204760382641)
    ·
      refine ⟨25880784596352153570286981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34507712795136204760382641 25880784596352153570286981)
      ·
        refine ⟨4852647111816028794428809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25880784596352153570286981 4852647111816028794428809)
        ·
          refine ⟨3639485333862021595821607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4852647111816028794428809 3639485333862021595821607)
          ·
            refine ⟨5459228000793032393732411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639485333862021595821607 5459228000793032393732411)
            ·
              refine ⟨8188842001189548590598617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459228000793032393732411 8188842001189548590598617)
              ·
                refine ⟨6141631500892161442948963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8188842001189548590598617 6141631500892161442948963)
                ·
                  refine ⟨9212447251338242164423445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6141631500892161442948963 9212447251338242164423445)
                  ·
                    refine ⟨431833464906480101457349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9212447251338242164423445 431833464906480101457349)
                    ·
                      rfl

theorem cell22_1261489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_1261489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261489 prefixEnd_1261489 := by exact prefixLift 1261489
  have htrace : WordTrace (prefixWord ++ tailWord_1261489) baseStart_1261489 baseEnd_1261489 := by
    simpa [prefixWord, tailWord_1261489, baseEnd_1261489] using wordTrace_append hprefix tailTrace_1261489
  have hstable : (prefixWord ++ tailWord_1261489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261489).length < 2 ^ (prefixWord ++ tailWord_1261489).sum := by decide
  have hdescent : baseEnd_1261489 < baseStart_1261489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261538 : List Nat := [3, 3, 3, 1, 2, 1, 2, 7]
def baseStart_1261538 : Nat := 118140960795 + 1261538 * 2 ^ 59
def prefixEnd_1261538 : Nat := 4983230072969 + 3 ^ 40 * 1261538 * 2
def baseEnd_1261538 : Nat := 47983359845317811886911

theorem tailTrace_1261538 : CollatzResearch.WordTrace tailWord_1261538 prefixEnd_1261538 47983359845317811886911 := by
  unfold tailWord_1261538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11503017725917688595594317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30674713935780502921584845 11503017725917688595594317)
  ·
    refine ⟨4313631647219133223347869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11503017725917688595594317 4313631647219133223347869)
    ·
      refine ⟨1617611867707174958755451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4313631647219133223347869 1617611867707174958755451)
      ·
        refine ⟨2426417801560762438133177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617611867707174958755451 2426417801560762438133177)
        ·
          refine ⟨1819813351170571828599883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426417801560762438133177 1819813351170571828599883)
          ·
            refine ⟨2729720026755857742899825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819813351170571828599883 2729720026755857742899825)
            ·
              refine ⟨2047290020066893307174869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729720026755857742899825 2047290020066893307174869)
              ·
                refine ⟨47983359845317811886911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2047290020066893307174869 47983359845317811886911)
                ·
                  rfl

theorem cell22_1261538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_1261538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261538 prefixEnd_1261538 := by exact prefixLift 1261538
  have htrace : WordTrace (prefixWord ++ tailWord_1261538) baseStart_1261538 baseEnd_1261538 := by
    simpa [prefixWord, tailWord_1261538, baseEnd_1261538] using wordTrace_append hprefix tailTrace_1261538
  have hstable : (prefixWord ++ tailWord_1261538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261538).length < 2 ^ (prefixWord ++ tailWord_1261538).sum := by decide
  have hdescent : baseEnd_1261538 < baseStart_1261538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261596 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1261596 : Nat := 118140960795 + 1261596 * 2 ^ 59
def prefixEnd_1261596 : Nat := 4983230072969 + 3 ^ 40 * 1261596 * 2
def baseEnd_1261596 : Nat := 431870093193167489032021

theorem tailTrace_1261596 : CollatzResearch.WordTrace tailWord_1261596 prefixEnd_1261596 431870093193167489032021 := by
  unfold tailWord_1261596
  simp only [CollatzResearch.WordTrace]
  refine ⟨23007093168730315143994321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30676124224973753525325761 23007093168730315143994321)
  ·
    refine ⟨17255319876547736357995741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23007093168730315143994321 17255319876547736357995741)
    ·
      refine ⟨6470744953705401134248403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17255319876547736357995741 6470744953705401134248403)
      ·
        refine ⟨9706117430558101701372605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6470744953705401134248403 9706117430558101701372605)
        ·
          refine ⟨3639794036459288138014727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9706117430558101701372605 3639794036459288138014727)
          ·
            refine ⟨5459691054688932207022091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639794036459288138014727 5459691054688932207022091)
            ·
              refine ⟨8189536582033398310533137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459691054688932207022091 8189536582033398310533137)
              ·
                refine ⟨6142152436525048732899853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8189536582033398310533137 6142152436525048732899853)
                ·
                  refine ⟨2303307163696893274837445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6142152436525048732899853 2303307163696893274837445)
                  ·
                    refine ⟨431870093193167489032021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2303307163696893274837445 431870093193167489032021)
                    ·
                      rfl

theorem cell22_1261596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1261596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261596 prefixEnd_1261596 := by exact prefixLift 1261596
  have htrace : WordTrace (prefixWord ++ tailWord_1261596) baseStart_1261596 baseEnd_1261596 := by
    simpa [prefixWord, tailWord_1261596, baseEnd_1261596] using wordTrace_append hprefix tailTrace_1261596
  have hstable : (prefixWord ++ tailWord_1261596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261596).length < 2 ^ (prefixWord ++ tailWord_1261596).sum := by decide
  have hdescent : baseEnd_1261596 < baseStart_1261596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261626 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_1261626 : Nat := 118140960795 + 1261626 * 2 ^ 59
def prefixEnd_1261626 : Nat := 4983230072969 + 3 ^ 40 * 1261626 * 2
def baseEnd_1261626 : Nat := 431880362806257410781929

theorem tailTrace_1261626 : CollatzResearch.WordTrace tailWord_1261626 prefixEnd_1261626 431880362806257410781929 := by
  unfold tailWord_1261626
  simp only [CollatzResearch.WordTrace]
  refine ⟨11503820131837986352895183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30676853684901296941053821 11503820131837986352895183)
  ·
    refine ⟨17255730197756979529342775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11503820131837986352895183 17255730197756979529342775)
    ·
      refine ⟨25883595296635469294014163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17255730197756979529342775 25883595296635469294014163)
      ·
        refine ⟨38825392944953203941021245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25883595296635469294014163 38825392944953203941021245)
        ·
          refine ⟨14559522354357451477882967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38825392944953203941021245 14559522354357451477882967)
          ·
            refine ⟨21839283531536177216824451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14559522354357451477882967 21839283531536177216824451)
            ·
              refine ⟨32758925297304265825236677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21839283531536177216824451 32758925297304265825236677)
              ·
                refine ⟨6142298493244549842231877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32758925297304265825236677 6142298493244549842231877)
                ·
                  refine ⟨1151680967483353095418477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6142298493244549842231877 1151680967483353095418477)
                  ·
                    refine ⟨431880362806257410781929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151680967483353095418477 431880362806257410781929)
                    ·
                      rfl

theorem cell22_1261626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_1261626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261626 prefixEnd_1261626 := by exact prefixLift 1261626
  have htrace : WordTrace (prefixWord ++ tailWord_1261626) baseStart_1261626 baseEnd_1261626 := by
    simpa [prefixWord, tailWord_1261626, baseEnd_1261626] using wordTrace_append hprefix tailTrace_1261626
  have hstable : (prefixWord ++ tailWord_1261626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261626).length < 2 ^ (prefixWord ++ tailWord_1261626).sum := by decide
  have hdescent : baseEnd_1261626 < baseStart_1261626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261628 : List Nat := [2, 2, 2, 2, 2, 1, 4, 3, 4]
def baseStart_1261628 : Nat := 118140960795 + 1261628 * 2 ^ 59
def prefixEnd_1261628 : Nat := 4983230072969 + 3 ^ 40 * 1261628 * 2
def baseEnd_1261628 : Nat := 143960349149043357410641

theorem tailTrace_1261628 : CollatzResearch.WordTrace tailWord_1261628 prefixEnd_1261628 143960349149043357410641 := by
  unfold tailWord_1261628
  simp only [CollatzResearch.WordTrace]
  refine ⟨23007676736672349876576769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30676902315563133168769025 23007676736672349876576769)
  ·
    refine ⟨17255757552504262407432577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23007676736672349876576769 17255757552504262407432577)
    ·
      refine ⟨12941818164378196805574433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17255757552504262407432577 12941818164378196805574433)
      ·
        refine ⟨9706363623283647604180825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12941818164378196805574433 9706363623283647604180825)
        ·
          refine ⟨7279772717462735703135619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9706363623283647604180825 7279772717462735703135619)
          ·
            refine ⟨10919659076194103554703429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279772717462735703135619 10919659076194103554703429)
            ·
              refine ⟨2047436076786394416506893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10919659076194103554703429 2047436076786394416506893)
              ·
                refine ⟨767788528794897906190085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2047436076786394416506893 767788528794897906190085)
                ·
                  refine ⟨143960349149043357410641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 767788528794897906190085 143960349149043357410641)
                  ·
                    rfl

theorem cell22_1261628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_1261628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261628 prefixEnd_1261628 := by exact prefixLift 1261628
  have htrace : WordTrace (prefixWord ++ tailWord_1261628) baseStart_1261628 baseEnd_1261628 := by
    simpa [prefixWord, tailWord_1261628, baseEnd_1261628] using wordTrace_append hprefix tailTrace_1261628
  have hstable : (prefixWord ++ tailWord_1261628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261628).length < 2 ^ (prefixWord ++ tailWord_1261628).sum := by decide
  have hdescent : baseEnd_1261628 < baseStart_1261628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261630 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1261630 : Nat := 118140960795 + 1261630 * 2 ^ 59
def prefixEnd_1261630 : Nat := 4983230072969 + 3 ^ 40 * 1261630 * 2
def baseEnd_1261630 : Nat := 431881732088002733681917

theorem tailTrace_1261630 : CollatzResearch.WordTrace tailWord_1261630 prefixEnd_1261630 431881732088002733681917 := by
  unfold tailWord_1261630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5751928302417181761840793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30676950946224969396484229 5751928302417181761840793)
  ·
    refine ⟨4313946226812886321380595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5751928302417181761840793 4313946226812886321380595)
    ·
      refine ⟨6470919340219329482070893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4313946226812886321380595 6470919340219329482070893)
      ·
        refine ⟨2426594752582248555776585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6470919340219329482070893 2426594752582248555776585)
        ·
          refine ⟨1819946064436686416832439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426594752582248555776585 1819946064436686416832439)
          ·
            refine ⟨2729919096655029625248659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819946064436686416832439 2729919096655029625248659)
            ·
              refine ⟨4094878644982544437872989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729919096655029625248659 4094878644982544437872989)
              ·
                refine ⟨1535579491868454164202371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4094878644982544437872989 1535579491868454164202371)
                ·
                  refine ⟨2303369237802681246303557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535579491868454164202371 2303369237802681246303557)
                  ·
                    refine ⟨431881732088002733681917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2303369237802681246303557 431881732088002733681917)
                    ·
                      rfl

theorem cell22_1261630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1261630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261630 prefixEnd_1261630 := by exact prefixLift 1261630
  have htrace : WordTrace (prefixWord ++ tailWord_1261630) baseStart_1261630 baseEnd_1261630 := by
    simpa [prefixWord, tailWord_1261630, baseEnd_1261630] using wordTrace_append hprefix tailTrace_1261630
  have hstable : (prefixWord ++ tailWord_1261630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261630).length < 2 ^ (prefixWord ++ tailWord_1261630).sum := by decide
  have hdescent : baseEnd_1261630 < baseStart_1261630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261639 : List Nat := [1, 1, 4, 1, 3, 1, 11]
def baseStart_1261639 : Nat := 118140960795 + 1261639 * 2 ^ 59
def prefixEnd_1261639 : Nat := 4983230072969 + 3 ^ 40 * 1261639 * 2
def baseEnd_1261639 : Nat := 15995733813775174452107

theorem tailTrace_1261639 : CollatzResearch.WordTrace tailWord_1261639 prefixEnd_1261639 15995733813775174452107 := by
  unfold tailWord_1261639
  simp only [CollatzResearch.WordTrace]
  refine ⟨46015754676304848631803971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30677169784203232421202647 46015754676304848631803971)
  ·
    refine ⟨69023632014457272947705957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46015754676304848631803971 69023632014457272947705957)
    ·
      refine ⟨12941931002710738677694867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69023632014457272947705957 12941931002710738677694867)
      ·
        refine ⟨19412896504066108016542301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12941931002710738677694867 19412896504066108016542301)
        ·
          refine ⟨7279836189024790506203363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19412896504066108016542301 7279836189024790506203363)
          ·
            refine ⟨10919754283537185759305045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279836189024790506203363 10919754283537185759305045)
            ·
              refine ⟨15995733813775174452107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10919754283537185759305045 15995733813775174452107)
              ·
                rfl

theorem cell22_1261639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 11].length) (baseStart_1261639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261639 prefixEnd_1261639 := by exact prefixLift 1261639
  have htrace : WordTrace (prefixWord ++ tailWord_1261639) baseStart_1261639 baseEnd_1261639 := by
    simpa [prefixWord, tailWord_1261639, baseEnd_1261639] using wordTrace_append hprefix tailTrace_1261639
  have hstable : (prefixWord ++ tailWord_1261639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261639).length < 2 ^ (prefixWord ++ tailWord_1261639).sum := by decide
  have hdescent : baseEnd_1261639 < baseStart_1261639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261701 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 7]
def baseStart_1261701 : Nat := 118140960795 + 1261701 * 2 ^ 59
def prefixEnd_1261701 : Nat := 4983230072969 + 3 ^ 40 * 1261701 * 2
def baseEnd_1261701 : Nat := 143968678946327405052233

theorem tailTrace_1261701 : CollatzResearch.WordTrace tailWord_1261701 prefixEnd_1261701 143968678946327405052233 := by
  unfold tailWord_1261701
  simp only [CollatzResearch.WordTrace]
  refine ⟨46018016002080233220560957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30678677334720155480373971 46018016002080233220560957)
  ·
    refine ⟨17256756000780087457710359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46018016002080233220560957 17256756000780087457710359)
    ·
      refine ⟨25885134001170131186565539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17256756000780087457710359 25885134001170131186565539)
      ·
        refine ⟨38827701001755196779848309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25885134001170131186565539 38827701001755196779848309)
        ·
          refine ⟨3640096968914549698110779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38827701001755196779848309 3640096968914549698110779)
          ·
            refine ⟨5460145453371824547166169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640096968914549698110779 5460145453371824547166169)
            ·
              refine ⟨4095109090028868410374627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460145453371824547166169 4095109090028868410374627)
              ·
                refine ⟨6142663635043302615561941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095109090028868410374627 6142663635043302615561941)
                ·
                  refine ⟨143968678946327405052233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6142663635043302615561941 143968678946327405052233)
                  ·
                    rfl

theorem cell22_1261701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_1261701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261701 prefixEnd_1261701 := by exact prefixLift 1261701
  have htrace : WordTrace (prefixWord ++ tailWord_1261701) baseStart_1261701 baseEnd_1261701 := by
    simpa [prefixWord, tailWord_1261701, baseEnd_1261701] using wordTrace_append hprefix tailTrace_1261701
  have hstable : (prefixWord ++ tailWord_1261701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261701).length < 2 ^ (prefixWord ++ tailWord_1261701).sum := by decide
  have hdescent : baseEnd_1261701 < baseStart_1261701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261756 : List Nat := [2, 2, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_1261756 : Nat := 118140960795 + 1261756 * 2 ^ 59
def prefixEnd_1261756 : Nat := 4983230072969 + 3 ^ 40 * 1261756 * 2
def baseEnd_1261756 : Nat := 431924864462980405031531

theorem tailTrace_1261756 : CollatzResearch.WordTrace tailWord_1261756 prefixEnd_1261756 431924864462980405031531 := by
  unfold tailWord_1261756
  simp only [CollatzResearch.WordTrace]
  refine ⟨23010011008440488806906561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30680014677920651742542081 23010011008440488806906561)
  ·
    refine ⟨17257508256330366605179921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23010011008440488806906561 17257508256330366605179921)
    ·
      refine ⟨12943131192247774953884941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17257508256330366605179921 12943131192247774953884941)
      ·
        refine ⟨4853674197092915607706853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12943131192247774953884941 4853674197092915607706853)
        ·
          refine ⟨910063911954921676445035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4853674197092915607706853 910063911954921676445035)
          ·
            refine ⟨1365095867932382514667553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910063911954921676445035 1365095867932382514667553)
            ·
              refine ⟨1023821900949286886000665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365095867932382514667553 1023821900949286886000665)
              ·
                refine ⟨767866425711965164500499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023821900949286886000665 767866425711965164500499)
                ·
                  refine ⟨1151799638567947746750749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767866425711965164500499 1151799638567947746750749)
                  ·
                    refine ⟨431924864462980405031531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151799638567947746750749 431924864462980405031531)
                    ·
                      rfl

theorem cell22_1261756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_1261756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261756 prefixEnd_1261756 := by exact prefixLift 1261756
  have htrace : WordTrace (prefixWord ++ tailWord_1261756) baseStart_1261756 baseEnd_1261756 := by
    simpa [prefixWord, tailWord_1261756, baseEnd_1261756] using wordTrace_append hprefix tailTrace_1261756
  have hstable : (prefixWord ++ tailWord_1261756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261756).length < 2 ^ (prefixWord ++ tailWord_1261756).sum := by decide
  have hdescent : baseEnd_1261756 < baseStart_1261756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
