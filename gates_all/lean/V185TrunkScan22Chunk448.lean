import V185TrunkScan22Chunk447

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3992681 : List Nat := [1, 2, 1, 1, 1, 6, 3, 3, 1, 3]
def baseStart_3992681 : Nat := 118140960795 + 3992681 * 2 ^ 59
def prefixEnd_3992681 : Nat := 4983230072969 + 3 ^ 40 * 3992681 * 2
def baseEnd_3992681 : Nat := 1366776302049465567283667

theorem tailTrace_3992681 : CollatzResearch.WordTrace tailWord_3992681 prefixEnd_3992681 1366776302049465567283667 := by
  unfold tailWord_3992681
  simp only [CollatzResearch.WordTrace]
  refine ⟨145625039648206107471425897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97083359765470738314283931 145625039648206107471425897)
  ·
    refine ⟨109218779736154580603569423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145625039648206107471425897 109218779736154580603569423)
    ·
      refine ⟨163828169604231870905354135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109218779736154580603569423 163828169604231870905354135)
      ·
        refine ⟨245742254406347806358031203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163828169604231870905354135 245742254406347806358031203)
        ·
          refine ⟨368613381609521709537046805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245742254406347806358031203 368613381609521709537046805)
          ·
            refine ⟨17278752262946330134549069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 368613381609521709537046805 17278752262946330134549069)
            ·
              refine ⟨6479532098604873800455901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17278752262946330134549069 6479532098604873800455901)
              ·
                refine ⟨2429824536976827675170963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6479532098604873800455901 2429824536976827675170963)
                ·
                  refine ⟨3644736805465241512756445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429824536976827675170963 3644736805465241512756445)
                  ·
                    refine ⟨1366776302049465567283667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644736805465241512756445 1366776302049465567283667)
                    ·
                      rfl

theorem cell22_3992681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 3].length) (baseStart_3992681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992681 prefixEnd_3992681 := by exact prefixLift 3992681
  have htrace : WordTrace (prefixWord ++ tailWord_3992681) baseStart_3992681 baseEnd_3992681 := by
    simpa [prefixWord, tailWord_3992681, baseEnd_3992681] using wordTrace_append hprefix tailTrace_3992681
  have hstable : (prefixWord ++ tailWord_3992681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992681).length < 2 ^ (prefixWord ++ tailWord_3992681).sum := by decide
  have hdescent : baseEnd_3992681 < baseStart_3992681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992694 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_3992694 : Nat := 118140960795 + 3992694 * 2 ^ 59
def prefixEnd_3992694 : Nat := 4983230072969 + 3 ^ 40 * 3992694 * 2
def baseEnd_3992694 : Nat := 455593584071712622236209

theorem tailTrace_3992694 : CollatzResearch.WordTrace tailWord_3992694 prefixEnd_3992694 455593584071712622236209 := by
  unfold tailWord_3992694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101594612322438168228071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97083675864772673794432757 9101594612322438168228071)
  ·
    refine ⟨13652391918483657252342107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9101594612322438168228071 13652391918483657252342107)
    ·
      refine ⟨20478587877725485878513161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13652391918483657252342107 20478587877725485878513161)
      ·
        refine ⟨15358940908294114408884871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20478587877725485878513161 15358940908294114408884871)
        ·
          refine ⟨23038411362441171613327307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15358940908294114408884871 23038411362441171613327307)
          ·
            refine ⟨34557617043661757419990961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23038411362441171613327307 34557617043661757419990961)
            ·
              refine ⟨25918212782746318064993221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34557617043661757419990961 25918212782746318064993221)
              ·
                refine ⟨4859664896764934637186229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25918212782746318064993221 4859664896764934637186229)
                ·
                  refine ⟨455593584071712622236209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4859664896764934637186229 455593584071712622236209)
                  ·
                    rfl

theorem cell22_3992694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_3992694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992694 prefixEnd_3992694 := by exact prefixLift 3992694
  have htrace : WordTrace (prefixWord ++ tailWord_3992694) baseStart_3992694 baseEnd_3992694 := by
    simpa [prefixWord, tailWord_3992694, baseEnd_3992694] using wordTrace_append hprefix tailTrace_3992694
  have hstable : (prefixWord ++ tailWord_3992694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992694).length < 2 ^ (prefixWord ++ tailWord_3992694).sum := by decide
  have hdescent : baseEnd_3992694 < baseStart_3992694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992707 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 3, 4]
def baseStart_3992707 : Nat := 118140960795 + 3992707 * 2 ^ 59
def prefixEnd_3992707 : Nat := 4983230072969 + 3 ^ 40 * 3992707 * 2
def baseEnd_3992707 : Nat := 1366785202380810166133587

theorem tailTrace_3992707 : CollatzResearch.WordTrace tailWord_3992707 prefixEnd_3992707 1366785202380810166133587 := by
  unfold tailWord_3992707
  simp only [CollatzResearch.WordTrace]
  refine ⟨145625987946111913911872375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97083991964074609274581583 145625987946111913911872375)
  ·
    refine ⟨218438981919167870867808563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145625987946111913911872375 218438981919167870867808563)
    ·
      refine ⟨327658472878751806301712845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218438981919167870867808563 327658472878751806301712845)
      ·
        refine ⟨122871927329531927363142317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327658472878751806301712845 122871927329531927363142317)
        ·
          refine ⟨46076972748574472761178369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122871927329531927363142317 46076972748574472761178369)
          ·
            refine ⟨34557729561430854570883777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46076972748574472761178369 34557729561430854570883777)
            ·
              refine ⟨25918297171073140928162833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34557729561430854570883777 25918297171073140928162833)
              ·
                refine ⟨19438722878304855696122125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25918297171073140928162833 19438722878304855696122125)
                ·
                  refine ⟨7289521079364320886045797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19438722878304855696122125 7289521079364320886045797)
                  ·
                    refine ⟨1366785202380810166133587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7289521079364320886045797 1366785202380810166133587)
                    ·
                      rfl

theorem cell22_3992707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_3992707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992707 prefixEnd_3992707 := by exact prefixLift 3992707
  have htrace : WordTrace (prefixWord ++ tailWord_3992707) baseStart_3992707 baseEnd_3992707 := by
    simpa [prefixWord, tailWord_3992707, baseEnd_3992707] using wordTrace_append hprefix tailTrace_3992707
  have hstable : (prefixWord ++ tailWord_3992707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992707).length < 2 ^ (prefixWord ++ tailWord_3992707).sum := by decide
  have hdescent : baseEnd_3992707 < baseStart_3992707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992741 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_3992741 : Nat := 118140960795 + 3992741 * 2 ^ 59
def prefixEnd_3992741 : Nat := 4983230072969 + 3 ^ 40 * 3992741 * 2
def baseEnd_3992741 : Nat := 1366796841275645410783483

theorem tailTrace_3992741 : CollatzResearch.WordTrace tailWord_3992741 prefixEnd_3992741 1366796841275645410783483 := by
  unfold tailWord_3992741
  simp only [CollatzResearch.WordTrace]
  refine ⟨145627228027988737718610077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97084818685325825145740051 145627228027988737718610077)
  ·
    refine ⟨54610210510495776644478779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145627228027988737718610077 54610210510495776644478779)
    ·
      refine ⟨81915315765743664966718169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54610210510495776644478779 81915315765743664966718169)
      ·
        refine ⟨61436486824307748725038627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81915315765743664966718169 61436486824307748725038627)
        ·
          refine ⟨92154730236461623087557941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61436486824307748725038627 92154730236461623087557941)
          ·
            refine ⟨8639505959668277164458557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92154730236461623087557941 8639505959668277164458557)
            ·
              refine ⟨3239814734875603936671959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8639505959668277164458557 3239814734875603936671959)
              ·
                refine ⟨4859722102313405905007939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239814734875603936671959 4859722102313405905007939)
                ·
                  refine ⟨7289583153470108857511909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859722102313405905007939 7289583153470108857511909)
                  ·
                    refine ⟨1366796841275645410783483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7289583153470108857511909 1366796841275645410783483)
                    ·
                      rfl

theorem cell22_3992741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_3992741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992741 prefixEnd_3992741 := by exact prefixLift 3992741
  have htrace : WordTrace (prefixWord ++ tailWord_3992741) baseStart_3992741 baseEnd_3992741 := by
    simpa [prefixWord, tailWord_3992741, baseEnd_3992741] using wordTrace_append hprefix tailTrace_3992741
  have hstable : (prefixWord ++ tailWord_3992741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992741).length < 2 ^ (prefixWord ++ tailWord_3992741).sum := by decide
  have hdescent : baseEnd_3992741 < baseStart_3992741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992767 : List Nat := [1, 1, 2, 2, 2, 2, 5, 7]
def baseStart_3992767 : Nat := 118140960795 + 3992767 * 2 ^ 59
def prefixEnd_3992767 : Nat := 4983230072969 + 3 ^ 40 * 3992767 * 2
def baseEnd_3992767 : Nat := 151867304622998889959267

theorem tailTrace_3992767 : CollatzResearch.WordTrace tailWord_3992767 prefixEnd_3992767 151867304622998889959267 := by
  unfold tailWord_3992767
  simp only [CollatzResearch.WordTrace]
  refine ⟨145628176325894544159056555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97085450883929696106037703 145628176325894544159056555)
  ·
    refine ⟨218442264488841816238584833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145628176325894544159056555 218442264488841816238584833)
    ·
      refine ⟨163831698366631362178938625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218442264488841816238584833 163831698366631362178938625)
      ·
        refine ⟨122873773774973521634203969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163831698366631362178938625 122873773774973521634203969)
        ·
          refine ⟨92155330331230141225652977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122873773774973521634203969 92155330331230141225652977)
          ·
            refine ⟨69116497748422605919239733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92155330331230141225652977 69116497748422605919239733)
            ·
              refine ⟨6479671663914619304928725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69116497748422605919239733 6479671663914619304928725)
              ·
                refine ⟨151867304622998889959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6479671663914619304928725 151867304622998889959267)
                ·
                  rfl

theorem cell22_3992767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 7].length) (baseStart_3992767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992767 prefixEnd_3992767 := by exact prefixLift 3992767
  have htrace : WordTrace (prefixWord ++ tailWord_3992767) baseStart_3992767 baseEnd_3992767 := by
    simpa [prefixWord, tailWord_3992767, baseEnd_3992767] using wordTrace_append hprefix tailTrace_3992767
  have hstable : (prefixWord ++ tailWord_3992767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992767).length < 2 ^ (prefixWord ++ tailWord_3992767).sum := by decide
  have hdescent : baseEnd_3992767 < baseStart_3992767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992790 : List Nat := [5, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3992790 : Nat := 118140960795 + 3992790 * 2 ^ 59
def prefixEnd_3992790 : Nat := 4983230072969 + 3 ^ 40 * 3992790 * 2
def baseEnd_3992790 : Nat := 455604538325675205436111

theorem tailTrace_3992790 : CollatzResearch.WordTrace tailWord_3992790 prefixEnd_3992790 455604538325675205436111 := by
  unfold tailWord_3992790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101813450300701192946489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97086010136540812724762549 9101813450300701192946489)
  ·
    refine ⟨6826360087725525894709867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9101813450300701192946489 6826360087725525894709867)
    ·
      refine ⟨10239540131588288842064801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826360087725525894709867 10239540131588288842064801)
      ·
        refine ⟨7679655098691216631548601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10239540131588288842064801 7679655098691216631548601)
        ·
          refine ⟨5759741324018412473661451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7679655098691216631548601 5759741324018412473661451)
          ·
            refine ⟨8639611986027618710492177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759741324018412473661451 8639611986027618710492177)
            ·
              refine ⟨6479708989520714032869133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8639611986027618710492177 6479708989520714032869133)
              ·
                refine ⟨2429890871070267762325925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6479708989520714032869133 2429890871070267762325925)
                ·
                  refine ⟨455604538325675205436111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2429890871070267762325925 455604538325675205436111)
                  ·
                    rfl

theorem cell22_3992790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3992790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992790 prefixEnd_3992790 := by exact prefixLift 3992790
  have htrace : WordTrace (prefixWord ++ tailWord_3992790) baseStart_3992790 baseEnd_3992790 := by
    simpa [prefixWord, tailWord_3992790, baseEnd_3992790] using wordTrace_append hprefix tailTrace_3992790
  have hstable : (prefixWord ++ tailWord_3992790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992790).length < 2 ^ (prefixWord ++ tailWord_3992790).sum := by decide
  have hdescent : baseEnd_3992790 < baseStart_3992790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992805 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_3992805 : Nat := 118140960795 + 3992805 * 2 ^ 59
def prefixEnd_3992805 : Nat := 4983230072969 + 3 ^ 40 * 3992805 * 2
def baseEnd_3992805 : Nat := 1366818749783570577183287

theorem tailTrace_3992805 : CollatzResearch.WordTrace tailWord_3992805 prefixEnd_3992805 1366818749783570577183287 := by
  unfold tailWord_3992805
  simp only [CollatzResearch.WordTrace]
  refine ⟨145629562299756876648939869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97086374866504584432626579 145629562299756876648939869)
  ·
    refine ⟨54611085862408828743352451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145629562299756876648939869 54611085862408828743352451)
    ·
      refine ⟨81916628793613243115028677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54611085862408828743352451 81916628793613243115028677)
      ·
        refine ⟨15359367898802483084067877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81916628793613243115028677 15359367898802483084067877)
        ·
          refine ⟨2879881481025465578262727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15359367898802483084067877 2879881481025465578262727)
          ·
            refine ⟨4319822221538198367394091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879881481025465578262727 4319822221538198367394091)
            ·
              refine ⟨6479733332307297551091137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319822221538198367394091 6479733332307297551091137)
              ·
                refine ⟨4859799999230473163318353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6479733332307297551091137 4859799999230473163318353)
                ·
                  refine ⟨3644849999422854872488765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859799999230473163318353 3644849999422854872488765)
                  ·
                    refine ⟨1366818749783570577183287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644849999422854872488765 1366818749783570577183287)
                    ·
                      rfl

theorem cell22_3992805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_3992805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992805 prefixEnd_3992805 := by exact prefixLift 3992805
  have htrace : WordTrace (prefixWord ++ tailWord_3992805) baseStart_3992805 baseEnd_3992805 := by
    simpa [prefixWord, tailWord_3992805, baseEnd_3992805] using wordTrace_append hprefix tailTrace_3992805
  have hstable : (prefixWord ++ tailWord_3992805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992805).length < 2 ^ (prefixWord ++ tailWord_3992805).sum := by decide
  have hdescent : baseEnd_3992805 < baseStart_3992805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992893 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_3992893 : Nat := 118140960795 + 3992893 * 2 ^ 59
def prefixEnd_3992893 : Nat := 4983230072969 + 3 ^ 40 * 3992893 * 2
def baseEnd_3992893 : Nat := 1366848873981967680983017

theorem tailTrace_3992893 : CollatzResearch.WordTrace tailWord_3992893 prefixEnd_3992893 1366848873981967680983017 := by
  unfold tailWord_3992893
  simp only [CollatzResearch.WordTrace]
  refine ⟨145632771923438067678143333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97088514615625378452095555 145632771923438067678143333)
  ·
    refine ⟨27306144735644637689651875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145632771923438067678143333 27306144735644637689651875)
    ·
      refine ⟨40959217103466956534477813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27306144735644637689651875 40959217103466956534477813)
      ·
        refine ⟨3839926603450027175107295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40959217103466956534477813 3839926603450027175107295)
        ·
          refine ⟨5759889905175040762660943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839926603450027175107295 5759889905175040762660943)
          ·
            refine ⟨8639834857762561143991415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759889905175040762660943 8639834857762561143991415)
            ·
              refine ⟨12959752286643841715987123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8639834857762561143991415 12959752286643841715987123)
              ·
                refine ⟨19439628429965762573980685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12959752286643841715987123 19439628429965762573980685)
                ·
                  refine ⟨7289860661237160965242757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19439628429965762573980685 7289860661237160965242757)
                  ·
                    refine ⟨1366848873981967680983017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7289860661237160965242757 1366848873981967680983017)
                    ·
                      rfl

theorem cell22_3992893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_3992893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992893 prefixEnd_3992893 := by exact prefixLift 3992893
  have htrace : WordTrace (prefixWord ++ tailWord_3992893) baseStart_3992893 baseEnd_3992893 := by
    simpa [prefixWord, tailWord_3992893, baseEnd_3992893] using wordTrace_append hprefix tailTrace_3992893
  have hstable : (prefixWord ++ tailWord_3992893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992893).length < 2 ^ (prefixWord ++ tailWord_3992893).sum := by decide
  have hdescent : baseEnd_3992893 < baseStart_3992893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992918 : List Nat := [5, 2, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3992918 : Nat := 118140960795 + 3992918 * 2 ^ 59
def prefixEnd_3992918 : Nat := 4983230072969 + 3 ^ 40 * 3992918 * 2
def baseEnd_3992918 : Nat := 1366857431992875949107941

theorem tailTrace_3992918 : CollatzResearch.WordTrace tailWord_3992918 prefixEnd_3992918 1366857431992875949107941 := by
  unfold tailWord_3992918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9102105234271718559237713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97089122498898331298535605 9102105234271718559237713)
  ·
    refine ⟨6826578925703788919428285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9102105234271718559237713 6826578925703788919428285)
    ·
      refine ⟨2559967097138920844785607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6826578925703788919428285 2559967097138920844785607)
      ·
        refine ⟨3839950645708381267178411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559967097138920844785607 3839950645708381267178411)
        ·
          refine ⟨5759925968562571900767617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839950645708381267178411 5759925968562571900767617)
          ·
            refine ⟨4319944476421928925575713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5759925968562571900767617 4319944476421928925575713)
            ·
              refine ⟨3239958357316446694181785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319944476421928925575713 3239958357316446694181785)
              ·
                refine ⟨2429968767987335020636339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239958357316446694181785 2429968767987335020636339)
                ·
                  refine ⟨3644953151981002530954509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429968767987335020636339 3644953151981002530954509)
                  ·
                    refine ⟨1366857431992875949107941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644953151981002530954509 1366857431992875949107941)
                    ·
                      rfl

theorem cell22_3992918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3992918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992918 prefixEnd_3992918 := by exact prefixLift 3992918
  have htrace : WordTrace (prefixWord ++ tailWord_3992918) baseStart_3992918 baseEnd_3992918 := by
    simpa [prefixWord, tailWord_3992918, baseEnd_3992918] using wordTrace_append hprefix tailTrace_3992918
  have hstable : (prefixWord ++ tailWord_3992918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992918).length < 2 ^ (prefixWord ++ tailWord_3992918).sum := by decide
  have hdescent : baseEnd_3992918 < baseStart_3992918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992951 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 3, 3]
def baseStart_3992951 : Nat := 118140960795 + 3992951 * 2 ^ 59
def prefixEnd_3992951 : Nat := 4983230072969 + 3 ^ 40 * 3992951 * 2
def baseEnd_3992951 : Nat := 1366868728567274863032839

theorem tailTrace_3992951 : CollatzResearch.WordTrace tailWord_3992951 prefixEnd_3992951 1366868728567274863032839 := by
  unfold tailWord_3992951
  simp only [CollatzResearch.WordTrace]
  refine ⟨145634887357227943583754707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97089924904818629055836471 145634887357227943583754707)
  ·
    refine ⟨218452331035841915375632061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145634887357227943583754707 218452331035841915375632061)
    ·
      refine ⟨81919624138440718265862023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218452331035841915375632061 81919624138440718265862023)
      ·
        refine ⟨122879436207661077398793035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81919624138440718265862023 122879436207661077398793035)
        ·
          refine ⟨184319154311491616098189553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122879436207661077398793035 184319154311491616098189553)
          ·
            refine ⟨138239365733618712073642165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184319154311491616098189553 138239365733618712073642165)
            ·
              refine ⟨12959940537526754256903953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138239365733618712073642165 12959940537526754256903953)
              ·
                refine ⟨9719955403145065692677965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12959940537526754256903953 9719955403145065692677965)
                ·
                  refine ⟨3644983276179399634754237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9719955403145065692677965 3644983276179399634754237)
                  ·
                    refine ⟨1366868728567274863032839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644983276179399634754237 1366868728567274863032839)
                    ·
                      rfl

theorem cell22_3992951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_3992951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992951 prefixEnd_3992951 := by exact prefixLift 3992951
  have htrace : WordTrace (prefixWord ++ tailWord_3992951) baseStart_3992951 baseEnd_3992951 := by
    simpa [prefixWord, tailWord_3992951, baseEnd_3992951] using wordTrace_append hprefix tailTrace_3992951
  have hstable : (prefixWord ++ tailWord_3992951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992951).length < 2 ^ (prefixWord ++ tailWord_3992951).sum := by decide
  have hdescent : baseEnd_3992951 < baseStart_3992951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992981 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 5]
def baseStart_3992981 : Nat := 118140960795 + 3992981 * 2 ^ 59
def prefixEnd_3992981 : Nat := 4983230072969 + 3 ^ 40 * 3992981 * 2
def baseEnd_3992981 : Nat := 455626332726788261594249

theorem tailTrace_3992981 : CollatzResearch.WordTrace tailWord_3992981 prefixEnd_3992981 455626332726788261594249 := by
  unfold tailWord_3992981
  simp only [CollatzResearch.WordTrace]
  refine ⟨145635981547119258707346797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97090654364746172471564531 145635981547119258707346797)
  ·
    refine ⟨54613493080169722015255049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145635981547119258707346797 54613493080169722015255049)
    ·
      refine ⟨40960119810127291511441287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54613493080169722015255049 40960119810127291511441287)
      ·
        refine ⟨61440179715190937267161931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40960119810127291511441287 61440179715190937267161931)
        ·
          refine ⟨92160269572786405900742897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61440179715190937267161931 92160269572786405900742897)
          ·
            refine ⟨69120202179589804425557173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92160269572786405900742897 69120202179589804425557173)
            ·
              refine ⟨6480018954336544164895985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69120202179589804425557173 6480018954336544164895985)
              ·
                refine ⟨4860014215752408123671989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480018954336544164895985 4860014215752408123671989)
                ·
                  refine ⟨455626332726788261594249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4860014215752408123671989 455626332726788261594249)
                  ·
                    rfl

theorem cell22_3992981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_3992981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992981 prefixEnd_3992981 := by exact prefixLift 3992981
  have htrace : WordTrace (prefixWord ++ tailWord_3992981) baseStart_3992981 baseEnd_3992981 := by
    simpa [prefixWord, tailWord_3992981, baseEnd_3992981] using wordTrace_append hprefix tailTrace_3992981
  have hstable : (prefixWord ++ tailWord_3992981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992981).length < 2 ^ (prefixWord ++ tailWord_3992981).sum := by decide
  have hdescent : baseEnd_3992981 < baseStart_3992981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993073 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_3993073 : Nat := 118140960795 + 3993073 * 2 ^ 59
def prefixEnd_3993073 : Nat := 4983230072969 + 3 ^ 40 * 3993073 * 2
def baseEnd_3993073 : Nat := 1366910491660507211482465

theorem tailTrace_3993073 : CollatzResearch.WordTrace tailWord_3993073 prefixEnd_3993073 1366910491660507211482465 := by
  unfold tailWord_3993073
  simp only [CollatzResearch.WordTrace]
  refine ⟨145639337062785958419695873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97092891375190638946463915 145639337062785958419695873)
  ·
    refine ⟨109229502797089468814771905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145639337062785958419695873 109229502797089468814771905)
    ·
      refine ⟨81922127097817101611078929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109229502797089468814771905 81922127097817101611078929)
      ·
        refine ⟨61441595323362826208309197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81922127097817101611078929 61441595323362826208309197)
        ·
          refine ⟨23040598246261059828115949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61441595323362826208309197 23040598246261059828115949)
          ·
            refine ⟨8640224342347897435543481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23040598246261059828115949 8640224342347897435543481)
            ·
              refine ⟨6480168256760923076657611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640224342347897435543481 6480168256760923076657611)
              ·
                refine ⟨9720252385141384614986417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480168256760923076657611 9720252385141384614986417)
                ·
                  refine ⟨7290189288856038461239813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9720252385141384614986417 7290189288856038461239813)
                  ·
                    refine ⟨1366910491660507211482465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290189288856038461239813 1366910491660507211482465)
                    ·
                      rfl

theorem cell22_3993073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_3993073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993073 prefixEnd_3993073 := by exact prefixLift 3993073
  have htrace : WordTrace (prefixWord ++ tailWord_3993073) baseStart_3993073 baseEnd_3993073 := by
    simpa [prefixWord, tailWord_3993073, baseEnd_3993073] using wordTrace_append hprefix tailTrace_3993073
  have hstable : (prefixWord ++ tailWord_3993073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993073).length < 2 ^ (prefixWord ++ tailWord_3993073).sum := by decide
  have hdescent : baseEnd_3993073 < baseStart_3993073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993090 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3993090 : Nat := 118140960795 + 3993090 * 2 ^ 59
def prefixEnd_3993090 : Nat := 4983230072969 + 3 ^ 40 * 3993090 * 2
def baseEnd_3993090 : Nat := 1366916311107924833807413

theorem tailTrace_3993090 : CollatzResearch.WordTrace tailWord_3993090 prefixEnd_3993090 1366916311107924833807413 := by
  unfold tailWord_3993090
  simp only [CollatzResearch.WordTrace]
  refine ⟨36409989275931092580766181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97093304735816246882043149 36409989275931092580766181)
  ·
    refine ⟨6826872989237079858893659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36409989275931092580766181 6826872989237079858893659)
    ·
      refine ⟨10240309483855619788340489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826872989237079858893659 10240309483855619788340489)
      ·
        refine ⟨7680232112891714841255367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10240309483855619788340489 7680232112891714841255367)
        ·
          refine ⟨11520348169337572261883051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680232112891714841255367 11520348169337572261883051)
          ·
            refine ⟨17280522254006358392824577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520348169337572261883051 17280522254006358392824577)
            ·
              refine ⟨12960391690504768794618433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17280522254006358392824577 12960391690504768794618433)
              ·
                refine ⟨9720293767878576595963825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12960391690504768794618433 9720293767878576595963825)
                ·
                  refine ⟨7290220325908932446972869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9720293767878576595963825 7290220325908932446972869)
                  ·
                    refine ⟨1366916311107924833807413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290220325908932446972869 1366916311107924833807413)
                    ·
                      rfl

theorem cell22_3993090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3993090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993090 prefixEnd_3993090 := by exact prefixLift 3993090
  have htrace : WordTrace (prefixWord ++ tailWord_3993090) baseStart_3993090 baseEnd_3993090 := by
    simpa [prefixWord, tailWord_3993090, baseEnd_3993090] using wordTrace_append hprefix tailTrace_3993090
  have hstable : (prefixWord ++ tailWord_3993090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993090).length < 2 ^ (prefixWord ++ tailWord_3993090).sum := by decide
  have hdescent : baseEnd_3993090 < baseStart_3993090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993092 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_3993092 : Nat := 118140960795 + 3993092 * 2 ^ 59
def prefixEnd_3993092 : Nat := 4983230072969 + 3 ^ 40 * 3993092 * 2
def baseEnd_3993092 : Nat := 1366916995748797495257407

theorem tailTrace_3993092 : CollatzResearch.WordTrace tailWord_3993092 prefixEnd_3993092 1366916995748797495257407 := by
  unfold tailWord_3993092
  simp only [CollatzResearch.WordTrace]
  refine ⟨72820015024858562332318765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97093353366478083109758353 72820015024858562332318765)
  ·
    refine ⟨27307505634321960874619537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72820015024858562332318765 27307505634321960874619537)
    ·
      refine ⟨20480629225741470655964653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27307505634321960874619537 20480629225741470655964653)
      ·
        refine ⟨7680235959653051495986745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20480629225741470655964653 7680235959653051495986745)
        ·
          refine ⟨5760176969739788621990059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7680235959653051495986745 5760176969739788621990059)
          ·
            refine ⟨8640265454609682932985089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760176969739788621990059 8640265454609682932985089)
            ·
              refine ⟨6480199090957262199738817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640265454609682932985089 6480199090957262199738817)
              ·
                refine ⟨4860149318217946649804113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480199090957262199738817 4860149318217946649804113)
                ·
                  refine ⟨3645111988663459987353085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860149318217946649804113 3645111988663459987353085)
                  ·
                    refine ⟨1366916995748797495257407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645111988663459987353085 1366916995748797495257407)
                    ·
                      rfl

theorem cell22_3993092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_3993092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993092 prefixEnd_3993092 := by exact prefixLift 3993092
  have htrace : WordTrace (prefixWord ++ tailWord_3993092) baseStart_3993092 baseEnd_3993092 := by
    simpa [prefixWord, tailWord_3993092, baseEnd_3993092] using wordTrace_append hprefix tailTrace_3993092
  have hstable : (prefixWord ++ tailWord_3993092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993092).length < 2 ^ (prefixWord ++ tailWord_3993092).sum := by decide
  have hdescent : baseEnd_3993092 < baseStart_3993092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993120 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 3, 3]
def baseStart_3993120 : Nat := 118140960795 + 3993120 * 2 ^ 59
def prefixEnd_3993120 : Nat := 4983230072969 + 3 ^ 40 * 3993120 * 2
def baseEnd_3993120 : Nat := 1366926580721014755557321

theorem tailTrace_3993120 : CollatzResearch.WordTrace tailWord_3993120 prefixEnd_3993120 1366926580721014755557321 := by
  unfold tailWord_3993120
  simp only [CollatzResearch.WordTrace]
  refine ⟨72820525646807842723328407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97094034195743790297771209 72820525646807842723328407)
  ·
    refine ⟨109230788470211764084992611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72820525646807842723328407 109230788470211764084992611)
    ·
      refine ⟨163846182705317646127488917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109230788470211764084992611 163846182705317646127488917)
      ·
        refine ⟨7680289814311764662226043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163846182705317646127488917 7680289814311764662226043)
        ·
          refine ⟨11520434721467646993339065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680289814311764662226043 11520434721467646993339065)
          ·
            refine ⟨8640326041100735245004299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11520434721467646993339065 8640326041100735245004299)
            ·
              refine ⟨12960489061651102867506449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640326041100735245004299 12960489061651102867506449)
              ·
                refine ⟨9720366796238327150629837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12960489061651102867506449 9720366796238327150629837)
                ·
                  refine ⟨3645137548589372681486189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9720366796238327150629837 3645137548589372681486189)
                  ·
                    refine ⟨1366926580721014755557321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645137548589372681486189 1366926580721014755557321)
                    ·
                      rfl

theorem cell22_3993120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_3993120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993120 prefixEnd_3993120 := by exact prefixLift 3993120
  have htrace : WordTrace (prefixWord ++ tailWord_3993120) baseStart_3993120 baseEnd_3993120 := by
    simpa [prefixWord, tailWord_3993120, baseEnd_3993120] using wordTrace_append hprefix tailTrace_3993120
  have hstable : (prefixWord ++ tailWord_3993120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993120).length < 2 ^ (prefixWord ++ tailWord_3993120).sum := by decide
  have hdescent : baseEnd_3993120 < baseStart_3993120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993180 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3993180 : Nat := 118140960795 + 3993180 * 2 ^ 59
def prefixEnd_3993180 : Nat := 4983230072969 + 3 ^ 40 * 3993180 * 2
def baseEnd_3993180 : Nat := 1366947119947194599057137

theorem tailTrace_3993180 : CollatzResearch.WordTrace tailWord_3993180 prefixEnd_3993180 1366947119947194599057137 := by
  unfold tailWord_3993180
  simp only [CollatzResearch.WordTrace]
  refine ⟨72821619836699157846920497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97095493115598877129227329 72821619836699157846920497)
  ·
    refine ⟨54616214877524368385190373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72821619836699157846920497 54616214877524368385190373)
    ·
      refine ⟨10240540289535819072223195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54616214877524368385190373 10240540289535819072223195)
      ·
        refine ⟨15360810434303728608334793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240540289535819072223195 15360810434303728608334793)
        ·
          refine ⟨11520607825727796456251095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15360810434303728608334793 11520607825727796456251095)
          ·
            refine ⟨17280911738591694684376643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520607825727796456251095 17280911738591694684376643)
            ·
              refine ⟨25921367607887542026564965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17280911738591694684376643 25921367607887542026564965)
              ·
                refine ⟨4860256426478914129980931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25921367607887542026564965 4860256426478914129980931)
                ·
                  refine ⟨7290384639718371194971397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860256426478914129980931 7290384639718371194971397)
                  ·
                    refine ⟨1366947119947194599057137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290384639718371194971397 1366947119947194599057137)
                    ·
                      rfl

theorem cell22_3993180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3993180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993180 prefixEnd_3993180 := by exact prefixLift 3993180
  have htrace : WordTrace (prefixWord ++ tailWord_3993180) baseStart_3993180 baseEnd_3993180 := by
    simpa [prefixWord, tailWord_3993180, baseEnd_3993180] using wordTrace_append hprefix tailTrace_3993180
  have hstable : (prefixWord ++ tailWord_3993180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993180).length < 2 ^ (prefixWord ++ tailWord_3993180).sum := by decide
  have hdescent : baseEnd_3993180 < baseStart_3993180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993193 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 4, 3]
def baseStart_3993193 : Nat := 118140960795 + 3993193 * 2 ^ 59
def prefixEnd_3993193 : Nat := 4983230072969 + 3 ^ 40 * 3993193 * 2
def baseEnd_3993193 : Nat := 1366951570112866898482097

theorem tailTrace_3993193 : CollatzResearch.WordTrace tailWord_3993193 prefixEnd_3993193 1366951570112866898482097 := by
  unfold tailWord_3993193
  simp only [CollatzResearch.WordTrace]
  refine ⟨145643713822351218914064233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97095809214900812609376155 145643713822351218914064233)
  ·
    refine ⟨109232785366763414185548175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145643713822351218914064233 109232785366763414185548175)
    ·
      refine ⟨163849178050145121278322263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109232785366763414185548175 163849178050145121278322263)
      ·
        refine ⟨245773767075217681917483395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163849178050145121278322263 245773767075217681917483395)
        ·
          refine ⟨368660650612826522876225093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245773767075217681917483395 368660650612826522876225093)
          ·
            refine ⟨69123871989904973039292205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368660650612826522876225093 69123871989904973039292205)
            ·
              refine ⟨25921451996214364889734577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69123871989904973039292205 25921451996214364889734577)
              ·
                refine ⟨19441088997160773667300933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25921451996214364889734577 19441088997160773667300933)
                ·
                  refine ⟨3645204186967645062618925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19441088997160773667300933 3645204186967645062618925)
                  ·
                    refine ⟨1366951570112866898482097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645204186967645062618925 1366951570112866898482097)
                    ·
                      rfl

theorem cell22_3993193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_3993193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993193 prefixEnd_3993193 := by exact prefixLift 3993193
  have htrace : WordTrace (prefixWord ++ tailWord_3993193) baseStart_3993193 baseEnd_3993193 := by
    simpa [prefixWord, tailWord_3993193, baseEnd_3993193] using wordTrace_append hprefix tailTrace_3993193
  have hstable : (prefixWord ++ tailWord_3993193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993193).length < 2 ^ (prefixWord ++ tailWord_3993193).sum := by decide
  have hdescent : baseEnd_3993193 < baseStart_3993193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993223 : List Nat := [1, 1, 4, 2, 1, 4, 2, 7]
def baseStart_3993223 : Nat := 118140960795 + 3993223 * 2 ^ 59
def prefixEnd_3993223 : Nat := 4983230072969 + 3 ^ 40 * 3993223 * 2
def baseEnd_3993223 : Nat := 151884648858439646692445

theorem tailTrace_3993223 : CollatzResearch.WordTrace tailWord_3993223 prefixEnd_3993223 151884648858439646692445 := by
  unfold tailWord_3993223
  simp only [CollatzResearch.WordTrace]
  refine ⟨145644808012242534037656323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97096538674828356025104215 145644808012242534037656323)
  ·
    refine ⟨218467212018363801056484485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145644808012242534037656323 218467212018363801056484485)
    ·
      refine ⟨40962602253443212698090841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218467212018363801056484485 40962602253443212698090841)
      ·
        refine ⟨30721951690082409523568131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40962602253443212698090841 30721951690082409523568131)
        ·
          refine ⟨46082927535123614285352197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30721951690082409523568131 46082927535123614285352197)
          ·
            refine ⟨8640548912835677678503537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46082927535123614285352197 8640548912835677678503537)
            ·
              refine ⟨6480411684626758258877653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640548912835677678503537 6480411684626758258877653)
              ·
                refine ⟨151884648858439646692445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6480411684626758258877653 151884648858439646692445)
                ·
                  rfl

theorem cell22_3993223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 7].length) (baseStart_3993223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993223 prefixEnd_3993223 := by exact prefixLift 3993223
  have htrace : WordTrace (prefixWord ++ tailWord_3993223) baseStart_3993223 baseEnd_3993223 := by
    simpa [prefixWord, tailWord_3993223, baseEnd_3993223] using wordTrace_append hprefix tailTrace_3993223
  have hstable : (prefixWord ++ tailWord_3993223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993223).length < 2 ^ (prefixWord ++ tailWord_3993223).sum := by decide
  have hdescent : baseEnd_3993223 < baseStart_3993223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993319 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 5]
def baseStart_3993319 : Nat := 118140960795 + 3993319 * 2 ^ 59
def prefixEnd_3993319 : Nat := 4983230072969 + 3 ^ 40 * 3993319 * 2
def baseEnd_3993319 : Nat := 455664900829281523277237

theorem tailTrace_3993319 : CollatzResearch.WordTrace tailWord_3993319 prefixEnd_3993319 455664900829281523277237 := by
  unfold tailWord_3993319
  simp only [CollatzResearch.WordTrace]
  refine ⟨145648309419894742433151011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97098872946596494955434007 145648309419894742433151011)
  ·
    refine ⟨218472464129842113649726517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145648309419894742433151011 218472464129842113649726517)
    ·
      refine ⟨20481793512172698154661861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218472464129842113649726517 20481793512172698154661861)
      ·
        refine ⟨3840336283532380903999099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20481793512172698154661861 3840336283532380903999099)
        ·
          refine ⟨5760504425298571355998649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3840336283532380903999099 5760504425298571355998649)
          ·
            refine ⟨4320378318973928516998987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5760504425298571355998649 4320378318973928516998987)
            ·
              refine ⟨6480567478460892775498481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320378318973928516998987 6480567478460892775498481)
              ·
                refine ⟨4860425608845669581623861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480567478460892775498481 4860425608845669581623861)
                ·
                  refine ⟨455664900829281523277237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4860425608845669581623861 455664900829281523277237)
                  ·
                    rfl

theorem cell22_3993319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 5].length) (baseStart_3993319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993319 prefixEnd_3993319 := by exact prefixLift 3993319
  have htrace : WordTrace (prefixWord ++ tailWord_3993319) baseStart_3993319 baseEnd_3993319 := by
    simpa [prefixWord, tailWord_3993319, baseEnd_3993319] using wordTrace_append hprefix tailTrace_3993319
  have hstable : (prefixWord ++ tailWord_3993319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993319).length < 2 ^ (prefixWord ++ tailWord_3993319).sum := by decide
  have hdescent : baseEnd_3993319 < baseStart_3993319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993330 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_3993330 : Nat := 118140960795 + 3993330 * 2 ^ 59
def prefixEnd_3993330 : Nat := 4983230072969 + 3 ^ 40 * 3993330 * 2
def baseEnd_3993330 : Nat := 455666156004214735935559

theorem tailTrace_3993330 : CollatzResearch.WordTrace tailWord_3993330 prefixEnd_3993330 455666156004214735935559 := by
  unfold tailWord_3993330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36412177655713722827950361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97099140415236594207867629 36412177655713722827950361)
  ·
    refine ⟨27309133241785292120962771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36412177655713722827950361 27309133241785292120962771)
    ·
      refine ⟨40963699862677938181444157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27309133241785292120962771 40963699862677938181444157)
      ·
        refine ⟨15361387448504226818041559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40963699862677938181444157 15361387448504226818041559)
        ·
          refine ⟨23042081172756340227062339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15361387448504226818041559 23042081172756340227062339)
          ·
            refine ⟨34563121759134510340593509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23042081172756340227062339 34563121759134510340593509)
            ·
              refine ⟨6480585329837720688861283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34563121759134510340593509 6480585329837720688861283)
              ·
                refine ⟨9720877994756581033291925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480585329837720688861283 9720877994756581033291925)
                ·
                  refine ⟨455666156004214735935559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9720877994756581033291925 455666156004214735935559)
                  ·
                    rfl

theorem cell22_3993330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_3993330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993330 prefixEnd_3993330 := by exact prefixLift 3993330
  have htrace : WordTrace (prefixWord ++ tailWord_3993330) baseStart_3993330 baseEnd_3993330 := by
    simpa [prefixWord, tailWord_3993330, baseEnd_3993330] using wordTrace_append hprefix tailTrace_3993330
  have hstable : (prefixWord ++ tailWord_3993330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993330).length < 2 ^ (prefixWord ++ tailWord_3993330).sum := by decide
  have hdescent : baseEnd_3993330 < baseStart_3993330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993343 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 1, 6]
def baseStart_3993343 : Nat := 118140960795 + 3993343 * 2 ^ 59
def prefixEnd_3993343 : Nat := 4983230072969 + 3 ^ 40 * 3993343 * 2
def baseEnd_3993343 : Nat := 1367002918178316507231637

theorem tailTrace_3993343 : CollatzResearch.WordTrace tailWord_3993343 prefixEnd_3993343 1367002918178316507231637 := by
  unfold tailWord_3993343
  simp only [CollatzResearch.WordTrace]
  refine ⟨145649184771807794532024683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97099456514538529688016455 145649184771807794532024683)
  ·
    refine ⟨218473777157711691798037025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145649184771807794532024683 218473777157711691798037025)
    ·
      refine ⟨163855332868283768848527769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218473777157711691798037025 163855332868283768848527769)
      ·
        refine ⟨122891499651212826636395827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163855332868283768848527769 122891499651212826636395827)
        ·
          refine ⟨184337249476819239954593741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122891499651212826636395827 184337249476819239954593741)
          ·
            refine ⟨69126468553807214982972653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184337249476819239954593741 69126468553807214982972653)
            ·
              refine ⟨25922425707677705618614745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69126468553807214982972653 25922425707677705618614745)
              ·
                refine ⟨19441819280758279213961059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25922425707677705618614745 19441819280758279213961059)
                ·
                  refine ⟨29162728921137418820941589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19441819280758279213961059 29162728921137418820941589)
                  ·
                    refine ⟨1367002918178316507231637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29162728921137418820941589 1367002918178316507231637)
                    ·
                      rfl

theorem cell22_3993343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_3993343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993343 prefixEnd_3993343 := by exact prefixLift 3993343
  have htrace : WordTrace (prefixWord ++ tailWord_3993343) baseStart_3993343 baseEnd_3993343 := by
    simpa [prefixWord, tailWord_3993343, baseEnd_3993343] using wordTrace_append hprefix tailTrace_3993343
  have hstable : (prefixWord ++ tailWord_3993343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993343).length < 2 ^ (prefixWord ++ tailWord_3993343).sum := by decide
  have hdescent : baseEnd_3993343 < baseStart_3993343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993345 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3993345 : Nat := 118140960795 + 3993345 * 2 ^ 59
def prefixEnd_3993345 : Nat := 4983230072969 + 3 ^ 40 * 3993345 * 2
def baseEnd_3993345 : Nat := 1367003602819189168681631

theorem tailTrace_3993345 : CollatzResearch.WordTrace tailWord_3993345 prefixEnd_3993345 1367003602819189168681631 := by
  unfold tailWord_3993345
  simp only [CollatzResearch.WordTrace]
  refine ⟨145649257717800548873597489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97099505145200365915731659 145649257717800548873597489)
  ·
    refine ⟨109236943288350411655198117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145649257717800548873597489 109236943288350411655198117)
    ·
      refine ⟨20481926866565702185349647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109236943288350411655198117 20481926866565702185349647)
      ·
        refine ⟨30722890299848553278024471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20481926866565702185349647 30722890299848553278024471)
        ·
          refine ⟨46084335449772829917036707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30722890299848553278024471 46084335449772829917036707)
          ·
            refine ⟨69126503174659244875555061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46084335449772829917036707 69126503174659244875555061)
            ·
              refine ⟨6480609672624304207083287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69126503174659244875555061 6480609672624304207083287)
              ·
                refine ⟨9720914508936456310624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480609672624304207083287 9720914508936456310624931)
                ·
                  refine ⟨14581371763404684465937397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9720914508936456310624931 14581371763404684465937397)
                  ·
                    refine ⟨1367003602819189168681631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14581371763404684465937397 1367003602819189168681631)
                    ·
                      rfl

theorem cell22_3993345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3993345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993345 prefixEnd_3993345 := by exact prefixLift 3993345
  have htrace : WordTrace (prefixWord ++ tailWord_3993345) baseStart_3993345 baseEnd_3993345 := by
    simpa [prefixWord, tailWord_3993345, baseEnd_3993345] using wordTrace_append hprefix tailTrace_3993345
  have hstable : (prefixWord ++ tailWord_3993345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993345).length < 2 ^ (prefixWord ++ tailWord_3993345).sum := by decide
  have hdescent : baseEnd_3993345 < baseStart_3993345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993357 : List Nat := [1, 7, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3993357 : Nat := 118140960795 + 3993357 * 2 ^ 59
def prefixEnd_3993357 : Nat := 4983230072969 + 3 ^ 40 * 3993357 * 2
def baseEnd_3993357 : Nat := 1367007710664425137381595

theorem tailTrace_3993357 : CollatzResearch.WordTrace tailWord_3993357 prefixEnd_3993357 1367007710664425137381595 := by
  unfold tailWord_3993357
  simp only [CollatzResearch.WordTrace]
  refine ⟨145649695393757074923034325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97099796929171383282022883 145649695393757074923034325)
  ·
    refine ⟨3413664735791181443508617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 145649695393757074923034325 3413664735791181443508617)
    ·
      refine ⟨2560248551843386082631463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3413664735791181443508617 2560248551843386082631463)
      ·
        refine ⟨3840372827765079123947195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560248551843386082631463 3840372827765079123947195)
        ·
          refine ⟨5760559241647618685920793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3840372827765079123947195 5760559241647618685920793)
          ·
            refine ⟨4320419431235714014440595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5760559241647618685920793 4320419431235714014440595)
            ·
              refine ⟨6480629146853571021660893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320419431235714014440595 6480629146853571021660893)
              ·
                refine ⟨2430235930070089133122835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6480629146853571021660893 2430235930070089133122835)
                ·
                  refine ⟨3645353895105133699684253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430235930070089133122835 3645353895105133699684253)
                  ·
                    refine ⟨1367007710664425137381595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645353895105133699684253 1367007710664425137381595)
                    ·
                      rfl

theorem cell22_3993357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3993357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993357 prefixEnd_3993357 := by exact prefixLift 3993357
  have htrace : WordTrace (prefixWord ++ tailWord_3993357) baseStart_3993357 baseEnd_3993357 := by
    simpa [prefixWord, tailWord_3993357, baseEnd_3993357] using wordTrace_append hprefix tailTrace_3993357
  have hstable : (prefixWord ++ tailWord_3993357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993357).length < 2 ^ (prefixWord ++ tailWord_3993357).sum := by decide
  have hdescent : baseEnd_3993357 < baseStart_3993357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993396 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3993396 : Nat := 118140960795 + 3993396 * 2 ^ 59
def prefixEnd_3993396 : Nat := 4983230072969 + 3 ^ 40 * 3993396 * 2
def baseEnd_3993396 : Nat := 1367021061161442035656475

theorem tailTrace_3993396 : CollatzResearch.WordTrace tailWord_3993396 prefixEnd_3993396 1367021061161442035656475 := by
  unfold tailWord_3993396
  simp only [CollatzResearch.WordTrace]
  refine ⟨72825558920307892291852021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97100745227077189722469361 72825558920307892291852021)
  ·
    refine ⟨6827396148778864902361127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72825558920307892291852021 6827396148778864902361127)
    ·
      refine ⟨10241094223168297353541691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6827396148778864902361127 10241094223168297353541691)
      ·
        refine ⟨15361641334752446030312537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241094223168297353541691 15361641334752446030312537)
        ·
          refine ⟨11521231001064334522734403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15361641334752446030312537 11521231001064334522734403)
          ·
            refine ⟨17281846501596501784101605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11521231001064334522734403 17281846501596501784101605)
            ·
              refine ⟨3240346219049344084519051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17281846501596501784101605 3240346219049344084519051)
              ·
                refine ⟨4860519328574016126778577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240346219049344084519051 4860519328574016126778577)
                ·
                  refine ⟨3645389496430512095083933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860519328574016126778577 3645389496430512095083933)
                  ·
                    refine ⟨1367021061161442035656475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645389496430512095083933 1367021061161442035656475)
                    ·
                      rfl

theorem cell22_3993396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3993396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993396 prefixEnd_3993396 := by exact prefixLift 3993396
  have htrace : WordTrace (prefixWord ++ tailWord_3993396) baseStart_3993396 baseEnd_3993396 := by
    simpa [prefixWord, tailWord_3993396, baseEnd_3993396] using wordTrace_append hprefix tailTrace_3993396
  have hstable : (prefixWord ++ tailWord_3993396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993396).length < 2 ^ (prefixWord ++ tailWord_3993396).sum := by decide
  have hdescent : baseEnd_3993396 < baseStart_3993396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993465 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 6]
def baseStart_3993465 : Nat := 118140960795 + 3993465 * 2 ^ 59
def prefixEnd_3993465 : Nat := 4983230072969 + 3 ^ 40 * 3993465 * 2
def baseEnd_3993465 : Nat := 455681560423849618560421

theorem tailTrace_3993465 : CollatzResearch.WordTrace tailWord_3993465 prefixEnd_3993465 455681560423849618560421 := by
  unfold tailWord_3993465
  simp only [CollatzResearch.WordTrace]
  refine ⟨145653634477365809367965849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97102422984910539578643899 145653634477365809367965849)
  ·
    refine ⟨109240225858024357025974387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145653634477365809367965849 109240225858024357025974387)
    ·
      refine ⟨163860338787036535538961581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109240225858024357025974387 163860338787036535538961581)
      ·
        refine ⟨61447627045138700827110593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163860338787036535538961581 61447627045138700827110593)
        ·
          refine ⟨46085720283854025620332945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61447627045138700827110593 46085720283854025620332945)
          ·
            refine ⟨34564290212890519215249709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46085720283854025620332945 34564290212890519215249709)
            ·
              refine ⟨12961608829833944705718641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34564290212890519215249709 12961608829833944705718641)
              ·
                refine ⟨9721206622375458529288981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12961608829833944705718641 9721206622375458529288981)
                ·
                  refine ⟨455681560423849618560421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9721206622375458529288981 455681560423849618560421)
                  ·
                    rfl

theorem cell22_3993465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_3993465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993465 prefixEnd_3993465 := by exact prefixLift 3993465
  have htrace : WordTrace (prefixWord ++ tailWord_3993465) baseStart_3993465 baseEnd_3993465 := by
    simpa [prefixWord, tailWord_3993465, baseEnd_3993465] using wordTrace_append hprefix tailTrace_3993465
  have hstable : (prefixWord ++ tailWord_3993465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993465).length < 2 ^ (prefixWord ++ tailWord_3993465).sum := by decide
  have hdescent : baseEnd_3993465 < baseStart_3993465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993565 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3993565 : Nat := 118140960795 + 3993565 * 2 ^ 59
def prefixEnd_3993565 : Nat := 4983230072969 + 3 ^ 40 * 3993565 * 2
def baseEnd_3993565 : Nat := 1367078913315181928180957

theorem tailTrace_3993565 : CollatzResearch.WordTrace tailWord_3993565 prefixEnd_3993565 1367078913315181928180957 := by
  unfold tailWord_3993565
  simp only [CollatzResearch.WordTrace]
  refine ⟨145657281777003526446606149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97104854518002350964404099 145657281777003526446606149)
  ·
    refine ⟨27310740333188161208738653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145657281777003526446606149 27310740333188161208738653)
    ·
      refine ⟨10241527624945560453276995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27310740333188161208738653 10241527624945560453276995)
      ·
        refine ⟨15362291437418340679915493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241527624945560453276995 15362291437418340679915493)
        ·
          refine ⟨2880429644515938877484155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15362291437418340679915493 2880429644515938877484155)
          ·
            refine ⟨4320644466773908316226233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880429644515938877484155 4320644466773908316226233)
            ·
              refine ⟨3240483350080431237169675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320644466773908316226233 3240483350080431237169675)
              ·
                refine ⟨4860725025120646855754513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240483350080431237169675 4860725025120646855754513)
                ·
                  refine ⟨3645543768840485141815885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860725025120646855754513 3645543768840485141815885)
                  ·
                    refine ⟨1367078913315181928180957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645543768840485141815885 1367078913315181928180957)
                    ·
                      rfl

theorem cell22_3993565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3993565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993565 prefixEnd_3993565 := by exact prefixLift 3993565
  have htrace : WordTrace (prefixWord ++ tailWord_3993565) baseStart_3993565 baseEnd_3993565 := by
    simpa [prefixWord, tailWord_3993565, baseEnd_3993565] using wordTrace_append hprefix tailTrace_3993565
  have hstable : (prefixWord ++ tailWord_3993565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993565).length < 2 ^ (prefixWord ++ tailWord_3993565).sum := by decide
  have hdescent : baseEnd_3993565 < baseStart_3993565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993572 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 5]
def baseStart_3993572 : Nat := 118140960795 + 3993572 * 2 ^ 59
def prefixEnd_3993572 : Nat := 4983230072969 + 3 ^ 40 * 3993572 * 2
def baseEnd_3993572 : Nat := 455693769852745414418645

theorem tailTrace_3993572 : CollatzResearch.WordTrace tailWord_3993572 prefixEnd_3993572 455693769852745414418645 := by
  unfold tailWord_3993572
  simp only [CollatzResearch.WordTrace]
  refine ⟨72828768543989083321055485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97105024725318777761407313 72828768543989083321055485)
  ·
    refine ⟨27310788203995906245395807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72828768543989083321055485 27310788203995906245395807)
    ·
      refine ⟨40966182305993859368093711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27310788203995906245395807 40966182305993859368093711)
      ·
        refine ⟨61449273458990789052140567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40966182305993859368093711 61449273458990789052140567)
        ·
          refine ⟨92173910188486183578210851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61449273458990789052140567 92173910188486183578210851)
          ·
            refine ⟨138260865282729275367316277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92173910188486183578210851 138260865282729275367316277)
            ·
              refine ⟨12961956120255869565685901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138260865282729275367316277 12961956120255869565685901)
              ·
                refine ⟨4860733545095951087132213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12961956120255869565685901 4860733545095951087132213)
                ·
                  refine ⟨455693769852745414418645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4860733545095951087132213 455693769852745414418645)
                  ·
                    rfl

theorem cell22_3993572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_3993572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993572 prefixEnd_3993572 := by exact prefixLift 3993572
  have htrace : WordTrace (prefixWord ++ tailWord_3993572) baseStart_3993572 baseEnd_3993572 := by
    simpa [prefixWord, tailWord_3993572, baseEnd_3993572] using wordTrace_append hprefix tailTrace_3993572
  have hstable : (prefixWord ++ tailWord_3993572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993572).length < 2 ^ (prefixWord ++ tailWord_3993572).sum := by decide
  have hdescent : baseEnd_3993572 < baseStart_3993572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993600 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 10]
def baseStart_3993600 : Nat := 118140960795 + 3993600 * 2 ^ 59
def prefixEnd_3993600 : Nat := 4983230072969 + 3 ^ 40 * 3993600 * 2
def baseEnd_3993600 : Nat := 455696964843484501185283

theorem tailTrace_3993600 : CollatzResearch.WordTrace tailWord_3993600 prefixEnd_3993600 455696964843484501185283 := by
  unfold tailWord_3993600
  simp only [CollatzResearch.WordTrace]
  refine ⟨72829279165938363712065127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97105705554584484949420169 72829279165938363712065127)
  ·
    refine ⟨109243918748907545568097691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72829279165938363712065127 109243918748907545568097691)
    ·
      refine ⟨163865878123361318352146537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109243918748907545568097691 163865878123361318352146537)
      ·
        refine ⟨122899408592520988764109903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163865878123361318352146537 122899408592520988764109903)
        ·
          refine ⟨184349112888781483146164855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122899408592520988764109903 184349112888781483146164855)
          ·
            refine ⟨276523669333172224719247283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184349112888781483146164855 276523669333172224719247283)
            ·
              refine ⟨414785503999758337078870925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276523669333172224719247283 414785503999758337078870925)
              ·
                refine ⟨155544563999909376404576597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414785503999758337078870925 155544563999909376404576597)
                ·
                  refine ⟨455696964843484501185283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155544563999909376404576597 455696964843484501185283)
                  ·
                    rfl

theorem cell22_3993600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_3993600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993600 prefixEnd_3993600 := by exact prefixLift 3993600
  have htrace : WordTrace (prefixWord ++ tailWord_3993600) baseStart_3993600 baseEnd_3993600 := by
    simpa [prefixWord, tailWord_3993600, baseEnd_3993600] using wordTrace_append hprefix tailTrace_3993600
  have hstable : (prefixWord ++ tailWord_3993600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993600).length < 2 ^ (prefixWord ++ tailWord_3993600).sum := by decide
  have hdescent : baseEnd_3993600 < baseStart_3993600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993610 : List Nat := [3, 1, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_3993610 : Nat := 118140960795 + 3993610 * 2 ^ 59
def prefixEnd_3993610 : Nat := 4983230072969 + 3 ^ 40 * 3993610 * 2
def baseEnd_3993610 : Nat := 1367094317734816810805819

theorem tailTrace_3993610 : CollatzResearch.WordTrace tailWord_3993610 prefixEnd_3993610 1367094317734816810805819 := by
  unfold tailWord_3993610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36414730765460124782998571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97105948707893666087996189 36414730765460124782998571)
  ·
    refine ⟨54622096148190187174497857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36414730765460124782998571 54622096148190187174497857)
    ·
      refine ⟨40966572111142640380873393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54622096148190187174497857 40966572111142640380873393)
      ·
        refine ⟨30724929083356980285655045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40966572111142640380873393 30724929083356980285655045)
        ·
          refine ⟨5760924203129433803560321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30724929083356980285655045 5760924203129433803560321)
          ·
            refine ⟨4320693152347075352670241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5760924203129433803560321 4320693152347075352670241)
            ·
              refine ⟨3240519864260306514502681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320693152347075352670241 3240519864260306514502681)
              ·
                refine ⟨2430389898195229885877011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240519864260306514502681 2430389898195229885877011)
                ·
                  refine ⟨3645584847292844828815517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430389898195229885877011 3645584847292844828815517)
                  ·
                    refine ⟨1367094317734816810805819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645584847292844828815517 1367094317734816810805819)
                    ·
                      rfl

theorem cell22_3993610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_3993610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993610 prefixEnd_3993610 := by exact prefixLift 3993610
  have htrace : WordTrace (prefixWord ++ tailWord_3993610) baseStart_3993610 baseEnd_3993610 := by
    simpa [prefixWord, tailWord_3993610, baseEnd_3993610] using wordTrace_append hprefix tailTrace_3993610
  have hstable : (prefixWord ++ tailWord_3993610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993610).length < 2 ^ (prefixWord ++ tailWord_3993610).sum := by decide
  have hdescent : baseEnd_3993610 < baseStart_3993610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993615 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 11]
def baseStart_3993615 : Nat := 118140960795 + 3993615 * 2 ^ 59
def prefixEnd_3993615 : Nat := 4983230072969 + 3 ^ 40 * 3993615 * 2
def baseEnd_3993615 : Nat := 1367096029336998464430803

theorem tailTrace_3993615 : CollatzResearch.WordTrace tailWord_3993615 prefixEnd_3993615 1367096029336998464430803 := by
  unfold tailWord_3993615
  simp only [CollatzResearch.WordTrace]
  refine ⟨145659105426822384985926299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97106070284548256657284199 145659105426822384985926299)
  ·
    refine ⟨218488658140233577478889449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145659105426822384985926299 218488658140233577478889449)
    ·
      refine ⟨163866493605175183109167087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218488658140233577478889449 163866493605175183109167087)
      ·
        refine ⟨245799740407762774663750631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163866493605175183109167087 245799740407762774663750631)
        ·
          refine ⟨368699610611644161995625947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245799740407762774663750631 368699610611644161995625947)
          ·
            refine ⟨553049415917466242993438921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368699610611644161995625947 553049415917466242993438921)
            ·
              refine ⟨414787061938099682245079191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553049415917466242993438921 414787061938099682245079191)
              ·
                refine ⟨622180592907149523367618787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414787061938099682245079191 622180592907149523367618787)
                ·
                  refine ⟨933270889360724285051428181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 622180592907149523367618787 933270889360724285051428181)
                  ·
                    refine ⟨1367096029336998464430803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 933270889360724285051428181 1367096029336998464430803)
                    ·
                      rfl

theorem cell22_3993615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_3993615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993615 prefixEnd_3993615 := by exact prefixLift 3993615
  have htrace : WordTrace (prefixWord ++ tailWord_3993615) baseStart_3993615 baseEnd_3993615 := by
    simpa [prefixWord, tailWord_3993615, baseEnd_3993615] using wordTrace_append hprefix tailTrace_3993615
  have hstable : (prefixWord ++ tailWord_3993615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993615).length < 2 ^ (prefixWord ++ tailWord_3993615).sum := by decide
  have hdescent : baseEnd_3993615 < baseStart_3993615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993647 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 2, 4]
def baseStart_3993647 : Nat := 118140960795 + 3993647 * 2 ^ 59
def prefixEnd_3993647 : Nat := 4983230072969 + 3 ^ 40 * 3993647 * 2
def baseEnd_3993647 : Nat := 1367106983590961047630705

theorem tailTrace_3993647 : CollatzResearch.WordTrace tailWord_3993647 prefixEnd_3993647 1367106983590961047630705 := by
  unfold tailWord_3993647
  simp only [CollatzResearch.WordTrace]
  refine ⟨145660272562706454451091195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97106848375137636300727463 145660272562706454451091195)
  ·
    refine ⟨218490408844059681676636793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145660272562706454451091195 218490408844059681676636793)
    ·
      refine ⟨163867806633044761257477595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218490408844059681676636793 163867806633044761257477595)
      ·
        refine ⟨245801709949567141886216393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163867806633044761257477595 245801709949567141886216393)
        ·
          refine ⟨184351282462175356414662295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245801709949567141886216393 184351282462175356414662295)
          ·
            refine ⟨276526923693263034621993443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184351282462175356414662295 276526923693263034621993443)
            ·
              refine ⟨414790385539894551932990165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276526923693263034621993443 414790385539894551932990165)
              ·
                refine ⟨9721649661091278560929457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 414790385539894551932990165 9721649661091278560929457)
                ·
                  refine ⟨7291237245818458920697093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721649661091278560929457 7291237245818458920697093)
                  ·
                    refine ⟨1367106983590961047630705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291237245818458920697093 1367106983590961047630705)
                    ·
                      rfl

theorem cell22_3993647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_3993647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993647 prefixEnd_3993647 := by exact prefixLift 3993647
  have htrace : WordTrace (prefixWord ++ tailWord_3993647) baseStart_3993647 baseEnd_3993647 := by
    simpa [prefixWord, tailWord_3993647, baseEnd_3993647] using wordTrace_append hprefix tailTrace_3993647
  have hstable : (prefixWord ++ tailWord_3993647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993647).length < 2 ^ (prefixWord ++ tailWord_3993647).sum := by decide
  have hdescent : baseEnd_3993647 < baseStart_3993647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993816 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_3993816 : Nat := 118140960795 + 3993816 * 2 ^ 59
def prefixEnd_3993816 : Nat := 4983230072969 + 3 ^ 40 * 3993816 * 2
def baseEnd_3993816 : Nat := 1367164835744700940155187

theorem tailTrace_3993816 : CollatzResearch.WordTrace tailWord_3993816 prefixEnd_3993816 1367164835744700940155187 := by
  unfold tailWord_3993816
  simp only [CollatzResearch.WordTrace]
  refine ⟨72833218249547098156996651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97110957666062797542662201 72833218249547098156996651)
  ·
    refine ⟨109249827374320647235494977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72833218249547098156996651 109249827374320647235494977)
    ·
      refine ⟨81937370530740485426621233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109249827374320647235494977 81937370530740485426621233)
      ·
        refine ⟨61453027898055364069965925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81937370530740485426621233 61453027898055364069965925)
        ·
          refine ⟨11522442730885380763118611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61453027898055364069965925 11522442730885380763118611)
          ·
            refine ⟨17283664096328071144677917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11522442730885380763118611 17283664096328071144677917)
            ·
              refine ⟨6481374036123026679254219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17283664096328071144677917 6481374036123026679254219)
              ·
                refine ⟨9722061054184540018881329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481374036123026679254219 9722061054184540018881329)
                ·
                  refine ⟨7291545790638405014160997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722061054184540018881329 7291545790638405014160997)
                  ·
                    refine ⟨1367164835744700940155187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291545790638405014160997 1367164835744700940155187)
                    ·
                      rfl

theorem cell22_3993816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_3993816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993816 prefixEnd_3993816 := by exact prefixLift 3993816
  have htrace : WordTrace (prefixWord ++ tailWord_3993816) baseStart_3993816 baseEnd_3993816 := by
    simpa [prefixWord, tailWord_3993816, baseEnd_3993816] using wordTrace_append hprefix tailTrace_3993816
  have hstable : (prefixWord ++ tailWord_3993816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993816).length < 2 ^ (prefixWord ++ tailWord_3993816).sum := by decide
  have hdescent : baseEnd_3993816 < baseStart_3993816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993904 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 6]
def baseStart_3993904 : Nat := 118140960795 + 3993904 * 2 ^ 59
def prefixEnd_3993904 : Nat := 4983230072969 + 3 ^ 40 * 3993904 * 2
def baseEnd_3993904 : Nat := 455731653314366014651639

theorem tailTrace_3993904 : CollatzResearch.WordTrace tailWord_3993904 prefixEnd_3993904 455731653314366014651639 := by
  unfold tailWord_3993904
  simp only [CollatzResearch.WordTrace]
  refine ⟨72834823061387693671598383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97113097415183591562131177 72834823061387693671598383)
  ·
    refine ⟨109252234592081540507397575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72834823061387693671598383 109252234592081540507397575)
    ·
      refine ⟨163878351888122310761096363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109252234592081540507397575 163878351888122310761096363)
      ·
        refine ⟨245817527832183466141644545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163878351888122310761096363 245817527832183466141644545)
        ·
          refine ⟨184363145874137599606233409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245817527832183466141644545 184363145874137599606233409)
          ·
            refine ⟨138272359405603199704675057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184363145874137599606233409 138272359405603199704675057)
            ·
              refine ⟨103704269554202399778506293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138272359405603199704675057 103704269554202399778506293)
              ·
                refine ⟨9722275270706474979234965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103704269554202399778506293 9722275270706474979234965)
                ·
                  refine ⟨455731653314366014651639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9722275270706474979234965 455731653314366014651639)
                  ·
                    rfl

theorem cell22_3993904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_3993904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993904 prefixEnd_3993904 := by exact prefixLift 3993904
  have htrace : WordTrace (prefixWord ++ tailWord_3993904) baseStart_3993904 baseEnd_3993904 := by
    simpa [prefixWord, tailWord_3993904, baseEnd_3993904] using wordTrace_append hprefix tailTrace_3993904
  have hstable : (prefixWord ++ tailWord_3993904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993904).length < 2 ^ (prefixWord ++ tailWord_3993904).sum := by decide
  have hdescent : baseEnd_3993904 < baseStart_3993904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993936 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_3993936 : Nat := 118140960795 + 3993936 * 2 ^ 59
def prefixEnd_3993936 : Nat := 4983230072969 + 3 ^ 40 * 3993936 * 2
def baseEnd_3993936 : Nat := 1367205914197060627154819

theorem tailTrace_3993936 : CollatzResearch.WordTrace tailWord_3993936 prefixEnd_3993936 1367205914197060627154819 := by
  unfold tailWord_3993936
  simp only [CollatzResearch.WordTrace]
  refine ⟨72835406629329728404180831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97113875505772971205574441 72835406629329728404180831)
  ·
    refine ⟨109253109943994592606271247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72835406629329728404180831 109253109943994592606271247)
    ·
      refine ⟨163879664915991888909406871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109253109943994592606271247 163879664915991888909406871)
      ·
        refine ⟨245819497373987833364110307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163879664915991888909406871 245819497373987833364110307)
        ·
          refine ⟨368729246060981750046165461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245819497373987833364110307 368729246060981750046165461)
          ·
            refine ⟨8642091704554259766707003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 368729246060981750046165461 8642091704554259766707003)
            ·
              refine ⟨12963137556831389650060505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642091704554259766707003 12963137556831389650060505)
              ·
                refine ⟨9722353167623542237545379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12963137556831389650060505 9722353167623542237545379)
                ·
                  refine ⟨14583529751435313356318069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9722353167623542237545379 14583529751435313356318069)
                  ·
                    refine ⟨1367205914197060627154819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14583529751435313356318069 1367205914197060627154819)
                    ·
                      rfl

theorem cell22_3993936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_3993936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993936 prefixEnd_3993936 := by exact prefixLift 3993936
  have htrace : WordTrace (prefixWord ++ tailWord_3993936) baseStart_3993936 baseEnd_3993936 := by
    simpa [prefixWord, tailWord_3993936, baseEnd_3993936] using wordTrace_append hprefix tailTrace_3993936
  have hstable : (prefixWord ++ tailWord_3993936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993936).length < 2 ^ (prefixWord ++ tailWord_3993936).sum := by decide
  have hdescent : baseEnd_3993936 < baseStart_3993936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993940 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_3993940 : Nat := 118140960795 + 3993940 * 2 ^ 59
def prefixEnd_3993940 : Nat := 4983230072969 + 3 ^ 40 * 3993940 * 2
def baseEnd_3993940 : Nat := 1367207283478805950054807

theorem tailTrace_3993940 : CollatzResearch.WordTrace tailWord_3993940 prefixEnd_3993940 1367207283478805950054807 := by
  unfold tailWord_3993940
  simp only [CollatzResearch.WordTrace]
  refine ⟨72835479575322482745753637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97113972767096643661004849 72835479575322482745753637)
  ·
    refine ⟨13656652420372965514828807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72835479575322482745753637 13656652420372965514828807)
    ·
      refine ⟨20484978630559448272243211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13656652420372965514828807 20484978630559448272243211)
      ·
        refine ⟨30727467945839172408364817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20484978630559448272243211 30727467945839172408364817)
        ·
          refine ⟨23045600959379379306273613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30727467945839172408364817 23045600959379379306273613)
          ·
            refine ⟨8642100359767267239852605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23045600959379379306273613 8642100359767267239852605)
            ·
              refine ⟨3240787634912725214944727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8642100359767267239852605 3240787634912725214944727)
              ·
                refine ⟨4861181452369087822417091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240787634912725214944727 4861181452369087822417091)
                ·
                  refine ⟨7291772178553631733625637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861181452369087822417091 7291772178553631733625637)
                  ·
                    refine ⟨1367207283478805950054807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291772178553631733625637 1367207283478805950054807)
                    ·
                      rfl

theorem cell22_3993940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_3993940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993940 prefixEnd_3993940 := by exact prefixLift 3993940
  have htrace : WordTrace (prefixWord ++ tailWord_3993940) baseStart_3993940 baseEnd_3993940 := by
    simpa [prefixWord, tailWord_3993940, baseEnd_3993940] using wordTrace_append hprefix tailTrace_3993940
  have hstable : (prefixWord ++ tailWord_3993940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993940).length < 2 ^ (prefixWord ++ tailWord_3993940).sum := by decide
  have hdescent : baseEnd_3993940 < baseStart_3993940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993951 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 2, 4]
def baseStart_3993951 : Nat := 118140960795 + 3993951 * 2 ^ 59
def prefixEnd_3993951 : Nat := 4983230072969 + 3 ^ 40 * 3993951 * 2
def baseEnd_3993951 : Nat := 1367211049003605588029773

theorem tailTrace_3993951 : CollatzResearch.WordTrace tailWord_3993951 prefixEnd_3993951 1367211049003605588029773 := by
  unfold tailWord_3993951
  simp only [CollatzResearch.WordTrace]
  refine ⟨145671360353605114370157707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97114240235736742913438471 145671360353605114370157707)
  ·
    refine ⟨218507040530407671555236561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145671360353605114370157707 218507040530407671555236561)
    ·
      refine ⟨163880280397805753666427421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218507040530407671555236561 163880280397805753666427421)
      ·
        refine ⟨61455105149177157624910283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163880280397805753666427421 61455105149177157624910283)
        ·
          refine ⟨92182657723765736437365425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61455105149177157624910283 92182657723765736437365425)
          ·
            refine ⟨69136993292824302328024069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92182657723765736437365425 69136993292824302328024069)
            ·
              refine ⟨12963186242404556686504513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69136993292824302328024069 12963186242404556686504513)
              ·
                refine ⟨9722389681803417514878385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12963186242404556686504513 9722389681803417514878385)
                ·
                  refine ⟨7291792261352563136158789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722389681803417514878385 7291792261352563136158789)
                  ·
                    refine ⟨1367211049003605588029773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291792261352563136158789 1367211049003605588029773)
                    ·
                      rfl

theorem cell22_3993951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_3993951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993951 prefixEnd_3993951 := by exact prefixLift 3993951
  have htrace : WordTrace (prefixWord ++ tailWord_3993951) baseStart_3993951 baseEnd_3993951 := by
    simpa [prefixWord, tailWord_3993951, baseEnd_3993951] using wordTrace_append hprefix tailTrace_3993951
  have hstable : (prefixWord ++ tailWord_3993951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993951).length < 2 ^ (prefixWord ++ tailWord_3993951).sum := by decide
  have hdescent : baseEnd_3993951 < baseStart_3993951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993985 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3993985 : Nat := 118140960795 + 3993985 * 2 ^ 59
def prefixEnd_3993985 : Nat := 4983230072969 + 3 ^ 40 * 3993985 * 2
def baseEnd_3993985 : Nat := 1367222687898440832679669

theorem tailTrace_3993985 : CollatzResearch.WordTrace tailWord_3993985 prefixEnd_3993985 1367222687898440832679669 := by
  unfold tailWord_3993985
  simp only [CollatzResearch.WordTrace]
  refine ⟨145672600435481938176895409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97115066956987958784596939 145672600435481938176895409)
  ·
    refine ⟨109254450326611453632671557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145672600435481938176895409 109254450326611453632671557)
    ·
      refine ⟨20485209436239647556125917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109254450326611453632671557 20485209436239647556125917)
      ·
        refine ⟨7681953538589867833547219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20485209436239647556125917 7681953538589867833547219)
        ·
          refine ⟨11522930307884801750320829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7681953538589867833547219 11522930307884801750320829)
          ·
            refine ⟨4321098865456800656370311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11522930307884801750320829 4321098865456800656370311)
            ·
              refine ⟨6481648298185200984555467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321098865456800656370311 6481648298185200984555467)
              ·
                refine ⟨9722472447277801476833201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481648298185200984555467 9722472447277801476833201)
                ·
                  refine ⟨7291854335458351107624901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722472447277801476833201 7291854335458351107624901)
                  ·
                    refine ⟨1367222687898440832679669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291854335458351107624901 1367222687898440832679669)
                    ·
                      rfl

theorem cell22_3993985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3993985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3993985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3993985 prefixEnd_3993985 := by exact prefixLift 3993985
  have htrace : WordTrace (prefixWord ++ tailWord_3993985) baseStart_3993985 baseEnd_3993985 := by
    simpa [prefixWord, tailWord_3993985, baseEnd_3993985] using wordTrace_append hprefix tailTrace_3993985
  have hstable : (prefixWord ++ tailWord_3993985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993985).length < 2 ^ (prefixWord ++ tailWord_3993985).sum := by decide
  have hdescent : baseEnd_3993985 < baseStart_3993985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994004 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3994004 : Nat := 118140960795 + 3994004 * 2 ^ 59
def prefixEnd_3994004 : Nat := 4983230072969 + 3 ^ 40 * 3994004 * 2
def baseEnd_3994004 : Nat := 1367229191986731116454611

theorem tailTrace_3994004 : CollatzResearch.WordTrace tailWord_3994004 prefixEnd_3994004 1367229191986731116454611 := by
  unfold tailWord_3994004
  simp only [CollatzResearch.WordTrace]
  refine ⟨72836646711206552210918533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97115528948275402947891377 72836646711206552210918533)
  ·
    refine ⟨13656871258351228539547225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72836646711206552210918533 13656871258351228539547225)
    ·
      refine ⟨10242653443763421404660419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13656871258351228539547225 10242653443763421404660419)
      ·
        refine ⟨15363980165645132106990629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242653443763421404660419 15363980165645132106990629)
        ·
          refine ⟨2880746281058462270060743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15363980165645132106990629 2880746281058462270060743)
          ·
            refine ⟨4321119421587693405091115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880746281058462270060743 4321119421587693405091115)
            ·
              refine ⟨6481679132381540107636673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321119421587693405091115 6481679132381540107636673)
              ·
                refine ⟨4861259349286155080727505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6481679132381540107636673 4861259349286155080727505)
                ·
                  refine ⟨3645944511964616310545629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4861259349286155080727505 3645944511964616310545629)
                  ·
                    refine ⟨1367229191986731116454611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645944511964616310545629 1367229191986731116454611)
                    ·
                      rfl

theorem cell22_3994004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3994004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994004 prefixEnd_3994004 := by exact prefixLift 3994004
  have htrace : WordTrace (prefixWord ++ tailWord_3994004) baseStart_3994004 baseEnd_3994004 := by
    simpa [prefixWord, tailWord_3994004, baseEnd_3994004] using wordTrace_append hprefix tailTrace_3994004
  have hstable : (prefixWord ++ tailWord_3994004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994004).length < 2 ^ (prefixWord ++ tailWord_3994004).sum := by decide
  have hdescent : baseEnd_3994004 < baseStart_3994004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994015 : List Nat := [1, 1, 2, 5, 1, 1, 1, 6, 1, 3]
def baseStart_3994015 : Nat := 118140960795 + 3994015 * 2 ^ 59
def prefixEnd_3994015 : Nat := 4983230072969 + 3 ^ 40 * 3994015 * 2
def baseEnd_3994015 : Nat := 1367232957511530754429577

theorem tailTrace_3994015 : CollatzResearch.WordTrace tailWord_3994015 prefixEnd_3994015 1367232957511530754429577 := by
  unfold tailWord_3994015
  simp only [CollatzResearch.WordTrace]
  refine ⟨145673694625373253300487499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97115796416915502200324999 145673694625373253300487499)
  ·
    refine ⟨218510541938059879950731249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145673694625373253300487499 218510541938059879950731249)
    ·
      refine ⟨163882906453544909963048437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218510541938059879950731249 163882906453544909963048437)
      ·
        refine ⟨15364022480019835309035791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163882906453544909963048437 15364022480019835309035791)
        ·
          refine ⟨23046033720029752963553687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15364022480019835309035791 23046033720029752963553687)
          ·
            refine ⟨34569050580044629445330531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23046033720029752963553687 34569050580044629445330531)
            ·
              refine ⟨51853575870066944167995797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34569050580044629445330531 51853575870066944167995797)
              ·
                refine ⟨2430636368909388007874803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51853575870066944167995797 2430636368909388007874803)
                ·
                  refine ⟨3645954553364082011812205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430636368909388007874803 3645954553364082011812205)
                  ·
                    refine ⟨1367232957511530754429577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645954553364082011812205 1367232957511530754429577)
                    ·
                      rfl

theorem cell22_3994015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 3].length) (baseStart_3994015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994015 prefixEnd_3994015 := by exact prefixLift 3994015
  have htrace : WordTrace (prefixWord ++ tailWord_3994015) baseStart_3994015 baseEnd_3994015 := by
    simpa [prefixWord, tailWord_3994015, baseEnd_3994015] using wordTrace_append hprefix tailTrace_3994015
  have hstable : (prefixWord ++ tailWord_3994015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994015).length < 2 ^ (prefixWord ++ tailWord_3994015).sum := by decide
  have hdescent : baseEnd_3994015 < baseStart_3994015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994058 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_3994058 : Nat := 118140960795 + 3994058 * 2 ^ 59
def prefixEnd_3994058 : Nat := 4983230072969 + 3 ^ 40 * 3994058 * 2
def baseEnd_3994058 : Nat := 1367247677290292975604445

theorem tailTrace_3994058 : CollatzResearch.WordTrace tailWord_3994058 prefixEnd_3994058 1367247677290292975604445 := by
  unfold tailWord_3994058
  simp only [CollatzResearch.WordTrace]
  refine ⟨36418815741054367911075707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97116841976144981096201885 36418815741054367911075707)
  ·
    refine ⟨54628223611581551866613561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36418815741054367911075707 54628223611581551866613561)
    ·
      refine ⟨40971167708686163899960171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54628223611581551866613561 40971167708686163899960171)
      ·
        refine ⟨61456751563029245849940257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40971167708686163899960171 61456751563029245849940257)
        ·
          refine ⟨46092563672271934387455193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61456751563029245849940257 46092563672271934387455193)
          ·
            refine ⟨34569422754203950790591395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46092563672271934387455193 34569422754203950790591395)
            ·
              refine ⟨51854134131305926185887093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34569422754203950790591395 51854134131305926185887093)
              ·
                refine ⟨4861325074809930579926915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51854134131305926185887093 4861325074809930579926915)
                ·
                  refine ⟨7291987612214895869890373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861325074809930579926915 7291987612214895869890373)
                  ·
                    refine ⟨1367247677290292975604445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291987612214895869890373 1367247677290292975604445)
                    ·
                      rfl

theorem cell22_3994058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_3994058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994058 prefixEnd_3994058 := by exact prefixLift 3994058
  have htrace : WordTrace (prefixWord ++ tailWord_3994058) baseStart_3994058 baseEnd_3994058 := by
    simpa [prefixWord, tailWord_3994058, baseEnd_3994058] using wordTrace_append hprefix tailTrace_3994058
  have hstable : (prefixWord ++ tailWord_3994058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994058).length < 2 ^ (prefixWord ++ tailWord_3994058).sum := by decide
  have hdescent : baseEnd_3994058 < baseStart_3994058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994066 : List Nat := [3, 2, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3994066 : Nat := 118140960795 + 3994066 * 2 ^ 59
def prefixEnd_3994066 : Nat := 4983230072969 + 3 ^ 40 * 3994066 * 2
def baseEnd_3994066 : Nat := 1367250415853783621404421

theorem tailTrace_3994066 : CollatzResearch.WordTrace tailWord_3994066 prefixEnd_3994066 1367250415853783621404421 := by
  unfold tailWord_3994066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36418888687047122252648513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97117036498792326007062701 36418888687047122252648513)
  ·
    refine ⟨27314166515285341689486385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36418888687047122252648513 27314166515285341689486385)
    ·
      refine ⟨20485624886464006267114789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27314166515285341689486385 20485624886464006267114789)
      ·
        refine ⟨3841054666212001175084023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20485624886464006267114789 3841054666212001175084023)
        ·
          refine ⟨5761581999318001762626035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841054666212001175084023 5761581999318001762626035)
          ·
            refine ⟨8642372998977002643939053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761581999318001762626035 8642372998977002643939053)
            ·
              refine ⟨3240889874616375991477145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8642372998977002643939053 3240889874616375991477145)
              ·
                refine ⟨2430667405962281993607859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240889874616375991477145 2430667405962281993607859)
                ·
                  refine ⟨3646001108943422990411789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430667405962281993607859 3646001108943422990411789)
                  ·
                    refine ⟨1367250415853783621404421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3646001108943422990411789 1367250415853783621404421)
                    ·
                      rfl

theorem cell22_3994066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3994066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994066 prefixEnd_3994066 := by exact prefixLift 3994066
  have htrace : WordTrace (prefixWord ++ tailWord_3994066) baseStart_3994066 baseEnd_3994066 := by
    simpa [prefixWord, tailWord_3994066, baseEnd_3994066] using wordTrace_append hprefix tailTrace_3994066
  have hstable : (prefixWord ++ tailWord_3994066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994066).length < 2 ^ (prefixWord ++ tailWord_3994066).sum := by decide
  have hdescent : baseEnd_3994066 < baseStart_3994066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994131 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 8]
def baseStart_3994131 : Nat := 118140960795 + 3994131 * 2 ^ 59
def prefixEnd_3994131 : Nat := 4983230072969 + 3 ^ 40 * 3994131 * 2
def baseEnd_3994131 : Nat := 1367272666682145118529221

theorem tailTrace_3994131 : CollatzResearch.WordTrace tailWord_3994131 prefixEnd_3994131 1367272666682145118529221 := by
  unfold tailWord_3994131
  simp only [CollatzResearch.WordTrace]
  refine ⟨145677925492953005111710247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97118616995302003407806831 145677925492953005111710247)
  ·
    refine ⟨218516888239429507667565371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145677925492953005111710247 218516888239429507667565371)
    ·
      refine ⟨327775332359144261501348057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218516888239429507667565371 327775332359144261501348057)
      ·
        refine ⟨245831499269358196126011043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327775332359144261501348057 245831499269358196126011043)
        ·
          refine ⟨368747248904037294189016565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245831499269358196126011043 368747248904037294189016565)
          ·
            refine ⟨34570054584753496330220303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368747248904037294189016565 34570054584753496330220303)
            ·
              refine ⟨51855081877130244495330455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34570054584753496330220303 51855081877130244495330455)
              ·
                refine ⟨77782622815695366742995683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51855081877130244495330455 77782622815695366742995683)
                ·
                  refine ⟨116673934223543050114493525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77782622815695366742995683 116673934223543050114493525)
                  ·
                    refine ⟨1367272666682145118529221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116673934223543050114493525 1367272666682145118529221)
                    ·
                      rfl

theorem cell22_3994131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_3994131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994131 prefixEnd_3994131 := by exact prefixLift 3994131
  have htrace : WordTrace (prefixWord ++ tailWord_3994131) baseStart_3994131 baseEnd_3994131 := by
    simpa [prefixWord, tailWord_3994131, baseEnd_3994131] using wordTrace_append hprefix tailTrace_3994131
  have hstable : (prefixWord ++ tailWord_3994131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994131).length < 2 ^ (prefixWord ++ tailWord_3994131).sum := by decide
  have hdescent : baseEnd_3994131 < baseStart_3994131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994167 : List Nat := [1, 1, 3, 1, 2, 3, 4, 3, 1, 3]
def baseStart_3994167 : Nat := 118140960795 + 3994167 * 2 ^ 59
def prefixEnd_3994167 : Nat := 4983230072969 + 3 ^ 40 * 3994167 * 2
def baseEnd_3994167 : Nat := 1367284990217853024629111

theorem tailTrace_3994167 : CollatzResearch.WordTrace tailWord_3994167 prefixEnd_3994167 1367284990217853024629111 := by
  unfold tailWord_3994167
  simp only [CollatzResearch.WordTrace]
  refine ⟨145679238520822583260020755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97119492347215055506680503 145679238520822583260020755)
  ·
    refine ⟨218518857781233874890031133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145679238520822583260020755 218518857781233874890031133)
    ·
      refine ⟨81944571667962703083761675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218518857781233874890031133 81944571667962703083761675)
      ·
        refine ⟨122916857501944054625642513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81944571667962703083761675 122916857501944054625642513)
        ·
          refine ⟨92187643126458040969231885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122916857501944054625642513 92187643126458040969231885)
          ·
            refine ⟨34570366172421765363461957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92187643126458040969231885 34570366172421765363461957)
            ·
              refine ⟨6481943657329081005649117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34570366172421765363461957 6481943657329081005649117)
              ·
                refine ⟨2430728871498405377118419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6481943657329081005649117 2430728871498405377118419)
                ·
                  refine ⟨3646093307247608065677629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430728871498405377118419 3646093307247608065677629)
                  ·
                    refine ⟨1367284990217853024629111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3646093307247608065677629 1367284990217853024629111)
                    ·
                      rfl

theorem cell22_3994167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_3994167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994167 prefixEnd_3994167 := by exact prefixLift 3994167
  have htrace : WordTrace (prefixWord ++ tailWord_3994167) baseStart_3994167 baseEnd_3994167 := by
    simpa [prefixWord, tailWord_3994167, baseEnd_3994167] using wordTrace_append hprefix tailTrace_3994167
  have hstable : (prefixWord ++ tailWord_3994167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994167).length < 2 ^ (prefixWord ++ tailWord_3994167).sum := by decide
  have hdescent : baseEnd_3994167 < baseStart_3994167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994208 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 6]
def baseStart_3994208 : Nat := 118140960795 + 3994208 * 2 ^ 59
def prefixEnd_3994208 : Nat := 4983230072969 + 3 ^ 40 * 3994208 * 2
def baseEnd_3994208 : Nat := 455766341785247528117995

theorem tailTrace_3994208 : CollatzResearch.WordTrace tailWord_3994208 prefixEnd_3994208 455766341785247528117995 := by
  unfold tailWord_3994208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72840366956837023631131639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97120489275782698174842185 72840366956837023631131639)
  ·
    refine ⟨109260550435255535446697459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72840366956837023631131639 109260550435255535446697459)
    ·
      refine ⟨163890825652883303170046189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109260550435255535446697459 163890825652883303170046189)
      ·
        refine ⟨61459059619831238688767321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163890825652883303170046189 61459059619831238688767321)
        ·
          refine ⟨46094294714873429016575491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61459059619831238688767321 46094294714873429016575491)
          ·
            refine ⟨69141442072310143524863237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46094294714873429016575491 69141442072310143524863237)
            ·
              refine ⟨12964020388558151910911857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69141442072310143524863237 12964020388558151910911857)
              ·
                refine ⟨9723015291418613933183893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12964020388558151910911857 9723015291418613933183893)
                ·
                  refine ⟨455766341785247528117995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9723015291418613933183893 455766341785247528117995)
                  ·
                    rfl

theorem cell22_3994208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_3994208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994208 prefixEnd_3994208 := by exact prefixLift 3994208
  have htrace : WordTrace (prefixWord ++ tailWord_3994208) baseStart_3994208 baseEnd_3994208 := by
    simpa [prefixWord, tailWord_3994208, baseEnd_3994208] using wordTrace_append hprefix tailTrace_3994208
  have hstable : (prefixWord ++ tailWord_3994208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994208).length < 2 ^ (prefixWord ++ tailWord_3994208).sum := by decide
  have hdescent : baseEnd_3994208 < baseStart_3994208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994223 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 1, 5]
def baseStart_3994223 : Nat := 118140960795 + 3994223 * 2 ^ 59
def prefixEnd_3994223 : Nat := 4983230072969 + 3 ^ 40 * 3994223 * 2
def baseEnd_3994223 : Nat := 1367304160162287545228939

theorem tailTrace_3994223 : CollatzResearch.WordTrace tailWord_3994223 prefixEnd_3994223 1367304160162287545228939 := by
  unfold tailWord_3994223
  simp only [CollatzResearch.WordTrace]
  refine ⟨145681281008619704824059323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97120854005746469882706215 145681281008619704824059323)
  ·
    refine ⟨218521921512929557236088985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145681281008619704824059323 218521921512929557236088985)
    ·
      refine ⟨163891441134697167927066739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218521921512929557236088985 163891441134697167927066739)
      ·
        refine ⟨245837161702045751890600109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163891441134697167927066739 245837161702045751890600109)
        ·
          refine ⟨92188935638267156958975041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245837161702045751890600109 92188935638267156958975041)
          ·
            refine ⟨69141701728700367719231281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92188935638267156958975041 69141701728700367719231281)
            ·
              refine ⟨51856276296525275789423461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69141701728700367719231281 51856276296525275789423461)
              ·
                refine ⟨9723051805598489210516899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51856276296525275789423461 9723051805598489210516899)
                ·
                  refine ⟨14584577708397733815775349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9723051805598489210516899 14584577708397733815775349)
                  ·
                    refine ⟨1367304160162287545228939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14584577708397733815775349 1367304160162287545228939)
                    ·
                      rfl

theorem cell22_3994223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_3994223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994223 prefixEnd_3994223 := by exact prefixLift 3994223
  have htrace : WordTrace (prefixWord ++ tailWord_3994223) baseStart_3994223 baseEnd_3994223 := by
    simpa [prefixWord, tailWord_3994223, baseEnd_3994223] using wordTrace_append hprefix tailTrace_3994223
  have hstable : (prefixWord ++ tailWord_3994223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994223).length < 2 ^ (prefixWord ++ tailWord_3994223).sum := by decide
  have hdescent : baseEnd_3994223 < baseStart_3994223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994240 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 4, 3]
def baseStart_3994240 : Nat := 118140960795 + 3994240 * 2 ^ 59
def prefixEnd_3994240 : Nat := 4983230072969 + 3 ^ 40 * 3994240 * 2
def baseEnd_3994240 : Nat := 1367309979609705167553887

theorem tailTrace_3994240 : CollatzResearch.WordTrace tailWord_3994240 prefixEnd_3994240 1367309979609705167553887 := by
  unfold tailWord_3994240
  simp only [CollatzResearch.WordTrace]
  refine ⟨72840950524779058363714087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97121267366372077818285449 72840950524779058363714087)
  ·
    refine ⟨109261425787168587545571131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72840950524779058363714087 109261425787168587545571131)
    ·
      refine ⟨163892138680752881318356697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109261425787168587545571131 163892138680752881318356697)
      ·
        refine ⟨122919104010564660988767523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163892138680752881318356697 122919104010564660988767523)
        ·
          refine ⟨184378656015846991483151285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122919104010564660988767523 184378656015846991483151285)
          ·
            refine ⟨17285499001485655451545433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184378656015846991483151285 17285499001485655451545433)
            ·
              refine ⟨12964124251114241588659075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17285499001485655451545433 12964124251114241588659075)
              ·
                refine ⟨19446186376671362382988613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12964124251114241588659075 19446186376671362382988613)
                ·
                  refine ⟨3646159945625880446810365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19446186376671362382988613 3646159945625880446810365)
                  ·
                    refine ⟨1367309979609705167553887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3646159945625880446810365 1367309979609705167553887)
                    ·
                      rfl

theorem cell22_3994240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_3994240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994240 prefixEnd_3994240 := by exact prefixLift 3994240
  have htrace : WordTrace (prefixWord ++ tailWord_3994240) baseStart_3994240 baseEnd_3994240 := by
    simpa [prefixWord, tailWord_3994240, baseEnd_3994240] using wordTrace_append hprefix tailTrace_3994240
  have hstable : (prefixWord ++ tailWord_3994240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994240).length < 2 ^ (prefixWord ++ tailWord_3994240).sum := by decide
  have hdescent : baseEnd_3994240 < baseStart_3994240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994270 : List Nat := [4, 3, 1, 1, 1, 1, 1, 10]
def baseStart_3994270 : Nat := 118140960795 + 3994270 * 2 ^ 59
def prefixEnd_3994270 : Nat := 4983230072969 + 3 ^ 40 * 3994270 * 2
def baseEnd_3994270 : Nat := 151924472135866121033755

theorem tailTrace_3994270 : CollatzResearch.WordTrace tailWord_3994270 prefixEnd_3994270 151924472135866121033755 := by
  unfold tailWord_3994270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18210374404931178981377533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97121996826299621234013509 18210374404931178981377533)
  ·
    refine ⟨6828890401849192118016575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18210374404931178981377533 6828890401849192118016575)
    ·
      refine ⟨10243335602773788177024863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6828890401849192118016575 10243335602773788177024863)
      ·
        refine ⟨15365003404160682265537295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243335602773788177024863 15365003404160682265537295)
        ·
          refine ⟨23047505106241023398305943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15365003404160682265537295 23047505106241023398305943)
          ·
            refine ⟨34571257659361535097458915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047505106241023398305943 34571257659361535097458915)
            ·
              refine ⟨51856886489042302646188373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34571257659361535097458915 51856886489042302646188373)
              ·
                refine ⟨151924472135866121033755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51856886489042302646188373 151924472135866121033755)
                ·
                  rfl

theorem cell22_3994270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_3994270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994270 prefixEnd_3994270 := by exact prefixLift 3994270
  have htrace : WordTrace (prefixWord ++ tailWord_3994270) baseStart_3994270 baseEnd_3994270 := by
    simpa [prefixWord, tailWord_3994270, baseEnd_3994270] using wordTrace_append hprefix tailTrace_3994270
  have hstable : (prefixWord ++ tailWord_3994270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994270).length < 2 ^ (prefixWord ++ tailWord_3994270).sum := by decide
  have hdescent : baseEnd_3994270 < baseStart_3994270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994272 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_3994272 : Nat := 118140960795 + 3994272 * 2 ^ 59
def prefixEnd_3994272 : Nat := 4983230072969 + 3 ^ 40 * 3994272 * 2
def baseEnd_3994272 : Nat := 1367320933863667750753789

theorem tailTrace_3994272 : CollatzResearch.WordTrace tailWord_3994272 prefixEnd_3994272 1367320933863667750753789 := by
  unfold tailWord_3994272
  simp only [CollatzResearch.WordTrace]
  refine ⟨72841534092721093096296535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97122045456961457461728713 72841534092721093096296535)
  ·
    refine ⟨109262301139081639644444803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72841534092721093096296535 109262301139081639644444803)
    ·
      refine ⟨163893451708622459466667205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109262301139081639644444803 163893451708622459466667205)
      ·
        refine ⟨30730022195366711150000101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163893451708622459466667205 30730022195366711150000101)
        ·
          refine ⟨5761879161631258340625019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30730022195366711150000101 5761879161631258340625019)
          ·
            refine ⟨8642818742446887510937529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761879161631258340625019 8642818742446887510937529)
            ·
              refine ⟨6482114056835165633203147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8642818742446887510937529 6482114056835165633203147)
              ·
                refine ⟨9723171085252748449804721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482114056835165633203147 9723171085252748449804721)
                ·
                  refine ⟨7292378313939561337353541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9723171085252748449804721 7292378313939561337353541)
                  ·
                    refine ⟨1367320933863667750753789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7292378313939561337353541 1367320933863667750753789)
                    ·
                      rfl

theorem cell22_3994272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_3994272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994272 prefixEnd_3994272 := by exact prefixLift 3994272
  have htrace : WordTrace (prefixWord ++ tailWord_3994272) baseStart_3994272 baseEnd_3994272 := by
    simpa [prefixWord, tailWord_3994272, baseEnd_3994272] using wordTrace_append hprefix tailTrace_3994272
  have hstable : (prefixWord ++ tailWord_3994272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994272).length < 2 ^ (prefixWord ++ tailWord_3994272).sum := by decide
  have hdescent : baseEnd_3994272 < baseStart_3994272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994302 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3994302 : Nat := 118140960795 + 3994302 * 2 ^ 59
def prefixEnd_3994302 : Nat := 4983230072969 + 3 ^ 40 * 3994302 * 2
def baseEnd_3994302 : Nat := 1367331203476757672503697

theorem tailTrace_3994302 : CollatzResearch.WordTrace tailWord_3994302 prefixEnd_3994302 1367331203476757672503697 := by
  unfold tailWord_3994302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18210520296916687664523145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97122774916889000877456773 18210520296916687664523145)
  ·
    refine ⟨13657890222687515748392359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18210520296916687664523145 13657890222687515748392359)
    ·
      refine ⟨20486835334031273622588539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13657890222687515748392359 20486835334031273622588539)
      ·
        refine ⟨30730253001046910433882809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20486835334031273622588539 30730253001046910433882809)
        ·
          refine ⟨23047689750785182825412107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30730253001046910433882809 23047689750785182825412107)
          ·
            refine ⟨34571534626177774238118161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047689750785182825412107 34571534626177774238118161)
            ·
              refine ⟨25928650969633330678588621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34571534626177774238118161 25928650969633330678588621)
              ·
                refine ⟨9723244113612499004470733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25928650969633330678588621 9723244113612499004470733)
                ·
                  refine ⟨3646216542604687126676525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9723244113612499004470733 3646216542604687126676525)
                  ·
                    refine ⟨1367331203476757672503697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3646216542604687126676525 1367331203476757672503697)
                    ·
                      rfl

theorem cell22_3994302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3994302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994302 prefixEnd_3994302 := by exact prefixLift 3994302
  have htrace : WordTrace (prefixWord ++ tailWord_3994302) baseStart_3994302 baseEnd_3994302 := by
    simpa [prefixWord, tailWord_3994302, baseEnd_3994302] using wordTrace_append hprefix tailTrace_3994302
  have hstable : (prefixWord ++ tailWord_3994302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994302).length < 2 ^ (prefixWord ++ tailWord_3994302).sum := by decide
  have hdescent : baseEnd_3994302 < baseStart_3994302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994360 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 6]
def baseStart_3994360 : Nat := 118140960795 + 3994360 * 2 ^ 59
def prefixEnd_3994360 : Nat := 4983230072969 + 3 ^ 40 * 3994360 * 2
def baseEnd_3994360 : Nat := 455783686020688284851173

theorem tailTrace_3994360 : CollatzResearch.WordTrace tailWord_3994360 prefixEnd_3994360 455783686020688284851173 := by
  unfold tailWord_3994360
  simp only [CollatzResearch.WordTrace]
  refine ⟨72843138904561688610898267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97124185206082251481197689 72843138904561688610898267)
  ·
    refine ⟨109264708356842532916347401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72843138904561688610898267 109264708356842532916347401)
    ·
      refine ⟨81948531267631899687260551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109264708356842532916347401 81948531267631899687260551)
      ·
        refine ⟨122922796901447849530890827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81948531267631899687260551 122922796901447849530890827)
        ·
          refine ⟨184384195352171774296336241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122922796901447849530890827 184384195352171774296336241)
          ·
            refine ⟨138288146514128830722252181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184384195352171774296336241 138288146514128830722252181)
            ·
              refine ⟨6482256867849788940105571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138288146514128830722252181 6482256867849788940105571)
              ·
                refine ⟨9723385301774683410158357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482256867849788940105571 9723385301774683410158357)
                ·
                  refine ⟨455783686020688284851173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9723385301774683410158357 455783686020688284851173)
                  ·
                    rfl

theorem cell22_3994360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_3994360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994360 prefixEnd_3994360 := by exact prefixLift 3994360
  have htrace : WordTrace (prefixWord ++ tailWord_3994360) baseStart_3994360 baseEnd_3994360 := by
    simpa [prefixWord, tailWord_3994360, baseEnd_3994360] using wordTrace_append hprefix tailTrace_3994360
  have hstable : (prefixWord ++ tailWord_3994360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994360).length < 2 ^ (prefixWord ++ tailWord_3994360).sum := by decide
  have hdescent : baseEnd_3994360 < baseStart_3994360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994467 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 5]
def baseStart_3994467 : Nat := 118140960795 + 3994467 * 2 ^ 59
def prefixEnd_3994467 : Nat := 4983230072969 + 3 ^ 40 * 3994467 * 2
def baseEnd_3994467 : Nat := 455795895449584080709397

theorem tailTrace_3994467 : CollatzResearch.WordTrace tailWord_3994467 prefixEnd_3994467 455795895449584080709397 := by
  unfold tailWord_3994467
  simp only [CollatzResearch.WordTrace]
  refine ⟨145690180419735734495941655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97126786946490489663961103 145690180419735734495941655)
  ·
    refine ⟨218535270629603601743912483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145690180419735734495941655 218535270629603601743912483)
    ·
      refine ⟨327802905944405402615868725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218535270629603601743912483 327802905944405402615868725)
      ·
        refine ⟨30731522432288006495237693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327802905944405402615868725 30731522432288006495237693)
        ·
          refine ⟨11524320912108002435714135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30731522432288006495237693 11524320912108002435714135)
          ·
            refine ⟨17286481368162003653571203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524320912108002435714135 17286481368162003653571203)
            ·
              refine ⟨25929722052243005480356805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17286481368162003653571203 25929722052243005480356805)
              ·
                refine ⟨4861822884795563527566901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25929722052243005480356805 4861822884795563527566901)
                ·
                  refine ⟨455795895449584080709397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4861822884795563527566901 455795895449584080709397)
                  ·
                    rfl

theorem cell22_3994467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 5].length) (baseStart_3994467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994467 prefixEnd_3994467 := by exact prefixLift 3994467
  have htrace : WordTrace (prefixWord ++ tailWord_3994467) baseStart_3994467 baseEnd_3994467 := by
    simpa [prefixWord, tailWord_3994467, baseEnd_3994467] using wordTrace_append hprefix tailTrace_3994467
  have hstable : (prefixWord ++ tailWord_3994467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994467).length < 2 ^ (prefixWord ++ tailWord_3994467).sum := by decide
  have hdescent : baseEnd_3994467 < baseStart_3994467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994471 : List Nat := [1, 1, 5, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3994471 : Nat := 118140960795 + 3994471 * 2 ^ 59
def prefixEnd_3994471 : Nat := 4983230072969 + 3 ^ 40 * 3994471 * 2
def baseEnd_3994471 : Nat := 1367389055630497565028179

theorem tailTrace_3994471 : CollatzResearch.WordTrace tailWord_3994471 prefixEnd_3994471 1367389055630497565028179 := by
  unfold tailWord_3994471
  simp only [CollatzResearch.WordTrace]
  refine ⟨145690326311721243179087267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97126884207814162119391511 145690326311721243179087267)
  ·
    refine ⟨218535489467581864768630901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145690326311721243179087267 218535489467581864768630901)
    ·
      refine ⟨20487702137585799822059147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218535489467581864768630901 20487702137585799822059147)
      ·
        refine ⟨30731553206378699733088721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20487702137585799822059147 30731553206378699733088721)
        ·
          refine ⟨23048664904784024799816541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30731553206378699733088721 23048664904784024799816541)
          ·
            refine ⟨8643249339294009299931203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23048664904784024799816541 8643249339294009299931203)
            ·
              refine ⟨12964874008941013949896805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8643249339294009299931203 12964874008941013949896805)
              ·
                refine ⟨2430913876676440115605651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12964874008941013949896805 2430913876676440115605651)
                ·
                  refine ⟨3646370815014660173408477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430913876676440115605651 3646370815014660173408477)
                  ·
                    refine ⟨1367389055630497565028179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3646370815014660173408477 1367389055630497565028179)
                    ·
                      rfl

theorem cell22_3994471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3994471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994471 prefixEnd_3994471 := by exact prefixLift 3994471
  have htrace : WordTrace (prefixWord ++ tailWord_3994471) baseStart_3994471 baseEnd_3994471 := by
    simpa [prefixWord, tailWord_3994471, baseEnd_3994471] using wordTrace_append hprefix tailTrace_3994471
  have hstable : (prefixWord ++ tailWord_3994471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994471).length < 2 ^ (prefixWord ++ tailWord_3994471).sum := by decide
  have hdescent : baseEnd_3994471 < baseStart_3994471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994495 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 8]
def baseStart_3994495 : Nat := 118140960795 + 3994495 * 2 ^ 59
def prefixEnd_3994495 : Nat := 4983230072969 + 3 ^ 40 * 3994495 * 2
def baseEnd_3994495 : Nat := 455799090440323167476035

theorem tailTrace_3994495 : CollatzResearch.WordTrace tailWord_3994495 prefixEnd_3994495 455799090440323167476035 := by
  unfold tailWord_3994495
  simp only [CollatzResearch.WordTrace]
  refine ⟨145691201663634295277960939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97127467775756196851973959 145691201663634295277960939)
  ·
    refine ⟨218536802495451442916941409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145691201663634295277960939 218536802495451442916941409)
    ·
      refine ⟨163902601871588582187706057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218536802495451442916941409 163902601871588582187706057)
      ·
        refine ⟨122926951403691436640779543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163902601871588582187706057 122926951403691436640779543)
        ·
          refine ⟨184390427105537154961169315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122926951403691436640779543 184390427105537154961169315)
          ·
            refine ⟨276585640658305732441753973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184390427105537154961169315 276585640658305732441753973)
            ·
              refine ⟨25929903811716162416414435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276585640658305732441753973 25929903811716162416414435)
              ·
                refine ⟨38894855717574243624621653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25929903811716162416414435 38894855717574243624621653)
                ·
                  refine ⟨455799090440323167476035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38894855717574243624621653 455799090440323167476035)
                  ·
                    rfl

theorem cell22_3994495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 8].length) (baseStart_3994495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994495 prefixEnd_3994495 := by exact prefixLift 3994495
  have htrace : WordTrace (prefixWord ++ tailWord_3994495) baseStart_3994495 baseEnd_3994495 := by
    simpa [prefixWord, tailWord_3994495, baseEnd_3994495] using wordTrace_append hprefix tailTrace_3994495
  have hstable : (prefixWord ++ tailWord_3994495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994495).length < 2 ^ (prefixWord ++ tailWord_3994495).sum := by decide
  have hdescent : baseEnd_3994495 < baseStart_3994495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994518 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3994518 : Nat := 118140960795 + 3994518 * 2 ^ 59
def prefixEnd_3994518 : Nat := 4983230072969 + 3 ^ 40 * 3994518 * 2
def baseEnd_3994518 : Nat := 455801714897001703034345

theorem tailTrace_3994518 : CollatzResearch.WordTrace tailWord_3994518 prefixEnd_3994518 455801714897001703034345 := by
  unfold tailWord_3994518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9105752533909435637878013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97128027028367313470698805 9105752533909435637878013)
  ·
    refine ⟨3414657200216038364204255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9105752533909435637878013 3414657200216038364204255)
    ·
      refine ⟨5121985800324057546306383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414657200216038364204255 5121985800324057546306383)
      ·
        refine ⟨7682978700486086319459575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121985800324057546306383 7682978700486086319459575)
        ·
          refine ⟨11524468050729129479189363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682978700486086319459575 11524468050729129479189363)
          ·
            refine ⟨17286702076093694218784045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524468050729129479189363 17286702076093694218784045)
            ·
              refine ⟨6482513278535135332044017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17286702076093694218784045 6482513278535135332044017)
              ·
                refine ⟨4861884958901351499033013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6482513278535135332044017 4861884958901351499033013)
                ·
                  refine ⟨455801714897001703034345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4861884958901351499033013 455801714897001703034345)
                  ·
                    rfl

theorem cell22_3994518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3994518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994518 prefixEnd_3994518 := by exact prefixLift 3994518
  have htrace : WordTrace (prefixWord ++ tailWord_3994518) baseStart_3994518 baseEnd_3994518 := by
    simpa [prefixWord, tailWord_3994518, baseEnd_3994518] using wordTrace_append hprefix tailTrace_3994518
  have hstable : (prefixWord ++ tailWord_3994518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994518).length < 2 ^ (prefixWord ++ tailWord_3994518).sum := by decide
  have hdescent : baseEnd_3994518 < baseStart_3994518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994529 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 6]
def baseStart_3994529 : Nat := 118140960795 + 3994529 * 2 ^ 59
def prefixEnd_3994529 : Nat := 4983230072969 + 3 ^ 40 * 3994529 * 2
def baseEnd_3994529 : Nat := 455802970071934915692667

theorem tailTrace_3994529 : CollatzResearch.WordTrace tailWord_3994529 prefixEnd_3994529 455802970071934915692667 := by
  unfold tailWord_3994529
  simp only [CollatzResearch.WordTrace]
  refine ⟨145692441745511119084698641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97128294497007412723132427 145692441745511119084698641)
  ·
    refine ⟨109269331309133339313523981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145692441745511119084698641 109269331309133339313523981)
    ·
      refine ⟨40975999240925002242571493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109269331309133339313523981 40975999240925002242571493)
      ·
        refine ⟨7682999857673437920482155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40975999240925002242571493 7682999857673437920482155)
        ·
          refine ⟨11524499786510156880723233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682999857673437920482155 11524499786510156880723233)
          ·
            refine ⟨8643374839882617660542425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11524499786510156880723233 8643374839882617660542425)
            ·
              refine ⟨6482531129911963245406819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8643374839882617660542425 6482531129911963245406819)
              ·
                refine ⟨9723796694867944868110229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482531129911963245406819 9723796694867944868110229)
                ·
                  refine ⟨455802970071934915692667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9723796694867944868110229 455802970071934915692667)
                  ·
                    rfl

theorem cell22_3994529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_3994529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994529 prefixEnd_3994529 := by exact prefixLift 3994529
  have htrace : WordTrace (prefixWord ++ tailWord_3994529) baseStart_3994529 baseEnd_3994529 := by
    simpa [prefixWord, tailWord_3994529, baseEnd_3994529] using wordTrace_append hprefix tailTrace_3994529
  have hstable : (prefixWord ++ tailWord_3994529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994529).length < 2 ^ (prefixWord ++ tailWord_3994529).sum := by decide
  have hdescent : baseEnd_3994529 < baseStart_3994529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994548 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3994548 : Nat := 118140960795 + 3994548 * 2 ^ 59
def prefixEnd_3994548 : Nat := 4983230072969 + 3 ^ 40 * 3994548 * 2
def baseEnd_3994548 : Nat := 1367415414304095030852943

theorem tailTrace_3994548 : CollatzResearch.WordTrace tailWord_3994548 prefixEnd_3994548 1367415414304095030852943 := by
  unfold tailWord_3994548
  simp only [CollatzResearch.WordTrace]
  refine ⟨72846567366221142664820149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97128756488294856886426865 72846567366221142664820149)
  ·
    refine ⟨6829365690583232124826889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72846567366221142664820149 6829365690583232124826889)
    ·
      refine ⟨5122024267937424093620167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6829365690583232124826889 5122024267937424093620167)
      ·
        refine ⟨7683036401906136140430251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122024267937424093620167 7683036401906136140430251)
        ·
          refine ⟨11524554602859204210645377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7683036401906136140430251 11524554602859204210645377)
          ·
            refine ⟨8643415952144403157984033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11524554602859204210645377 8643415952144403157984033)
            ·
              refine ⟨6482561964108302368488025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8643415952144403157984033 6482561964108302368488025)
              ·
                refine ⟨4861921473081226776366019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6482561964108302368488025 4861921473081226776366019)
                ·
                  refine ⟨7292882209621840164549029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861921473081226776366019 7292882209621840164549029)
                  ·
                    refine ⟨1367415414304095030852943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7292882209621840164549029 1367415414304095030852943)
                    ·
                      rfl

theorem cell22_3994548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3994548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994548 prefixEnd_3994548 := by exact prefixLift 3994548
  have htrace : WordTrace (prefixWord ++ tailWord_3994548) baseStart_3994548 baseEnd_3994548 := by
    simpa [prefixWord, tailWord_3994548, baseEnd_3994548] using wordTrace_append hprefix tailTrace_3994548
  have hstable : (prefixWord ++ tailWord_3994548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994548).length < 2 ^ (prefixWord ++ tailWord_3994548).sum := by decide
  have hdescent : baseEnd_3994548 < baseStart_3994548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994679 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 4, 3]
def baseStart_3994679 : Nat := 118140960795 + 3994679 * 2 ^ 59
def prefixEnd_3994679 : Nat := 4983230072969 + 3 ^ 40 * 3994679 * 2
def baseEnd_3994679 : Nat := 1367460258281254355827541

theorem tailTrace_3994679 : CollatzResearch.WordTrace tailWord_3994679 prefixEnd_3994679 1367460258281254355827541 := by
  unfold tailWord_3994679
  simp only [CollatzResearch.WordTrace]
  refine ⟨145697912694967694702659091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97131941796645129801772727 145697912694967694702659091)
  ·
    refine ⟨218546869042451542053988637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145697912694967694702659091 218546869042451542053988637)
    ·
      refine ⟨81955075890919328270245739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218546869042451542053988637 81955075890919328270245739)
      ·
        refine ⟨122932613836378992405368609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81955075890919328270245739 122932613836378992405368609)
        ·
          refine ⟨92199460377284244304026457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122932613836378992405368609 92199460377284244304026457)
          ·
            refine ⟨69149595282963183228019843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92199460377284244304026457 69149595282963183228019843)
            ·
              refine ⟨103724392924444774842029765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69149595282963183228019843 103724392924444774842029765)
              ·
                refine ⟨19448323673333395282880581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103724392924444774842029765 19448323673333395282880581)
                ·
                  refine ⟨3646560688750011615540109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19448323673333395282880581 3646560688750011615540109)
                  ·
                    refine ⟨1367460258281254355827541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3646560688750011615540109 1367460258281254355827541)
                    ·
                      rfl

theorem cell22_3994679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_3994679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994679 prefixEnd_3994679 := by exact prefixLift 3994679
  have htrace : WordTrace (prefixWord ++ tailWord_3994679) baseStart_3994679 baseEnd_3994679 := by
    simpa [prefixWord, tailWord_3994679, baseEnd_3994679] using wordTrace_append hprefix tailTrace_3994679
  have hstable : (prefixWord ++ tailWord_3994679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994679).length < 2 ^ (prefixWord ++ tailWord_3994679).sum := by decide
  have hdescent : baseEnd_3994679 < baseStart_3994679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994681 : List Nat := [1, 2, 1, 5, 2, 1, 1, 5, 4]
def baseStart_3994681 : Nat := 118140960795 + 3994681 * 2 ^ 59
def prefixEnd_3994681 : Nat := 4983230072969 + 3 ^ 40 * 3994681 * 2
def baseEnd_3994681 : Nat := 455820314307375672425845

theorem tailTrace_3994681 : CollatzResearch.WordTrace tailWord_3994681 prefixEnd_3994681 455820314307375672425845 := by
  unfold tailWord_3994681
  simp only [CollatzResearch.WordTrace]
  refine ⟨145697985640960449044231897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97131990427306966029487931 145697985640960449044231897)
  ·
    refine ⟨109273489230720336783173923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145697985640960449044231897 109273489230720336783173923)
    ·
      refine ⟨163910233846080505174760885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109273489230720336783173923 163910233846080505174760885)
      ·
        refine ⟨15366584423070047360133833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163910233846080505174760885 15366584423070047360133833)
        ·
          refine ⟨11524938317302535520100375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15366584423070047360133833 11524938317302535520100375)
          ·
            refine ⟨17287407475953803280150563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524938317302535520100375 17287407475953803280150563)
            ·
              refine ⟨25931111213930704920225845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17287407475953803280150563 25931111213930704920225845)
              ·
                refine ⟨2431041676306003586271173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25931111213930704920225845 2431041676306003586271173)
                ·
                  refine ⟨455820314307375672425845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431041676306003586271173 455820314307375672425845)
                  ·
                    rfl

theorem cell22_3994681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_3994681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994681 prefixEnd_3994681 := by exact prefixLift 3994681
  have htrace : WordTrace (prefixWord ++ tailWord_3994681) baseStart_3994681 baseEnd_3994681 := by
    simpa [prefixWord, tailWord_3994681, baseEnd_3994681] using wordTrace_append hprefix tailTrace_3994681
  have hstable : (prefixWord ++ tailWord_3994681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994681).length < 2 ^ (prefixWord ++ tailWord_3994681).sum := by decide
  have hdescent : baseEnd_3994681 < baseStart_3994681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994707 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 2, 7]
def baseStart_3994707 : Nat := 118140960795 + 3994707 * 2 ^ 59
def prefixEnd_3994707 : Nat := 4983230072969 + 3 ^ 40 * 3994707 * 2
def baseEnd_3994707 : Nat := 1367469843253471616127455

theorem tailTrace_3994707 : CollatzResearch.WordTrace tailWord_3994707 prefixEnd_3994707 1367469843253471616127455 := by
  unfold tailWord_3994707
  simp only [CollatzResearch.WordTrace]
  refine ⟨145698933938866255484678375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97132622625910836989785583 145698933938866255484678375)
  ·
    refine ⟨218548400908299383227017563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145698933938866255484678375 218548400908299383227017563)
    ·
      refine ⟨327822601362449074840526345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218548400908299383227017563 327822601362449074840526345)
      ·
        refine ⟨245866951021836806130394759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327822601362449074840526345 245866951021836806130394759)
        ·
          refine ⟨368800426532755209195592139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245866951021836806130394759 368800426532755209195592139)
          ·
            refine ⟨553200639799132813793388209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368800426532755209195592139 553200639799132813793388209)
            ·
              refine ⟨414900479849349610345041157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553200639799132813793388209 414900479849349610345041157)
              ·
                refine ⟨77793839971753051939695217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414900479849349610345041157 77793839971753051939695217)
                ·
                  refine ⟨58345379978814788954771413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77793839971753051939695217 58345379978814788954771413)
                  ·
                    refine ⟨1367469843253471616127455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58345379978814788954771413 1367469843253471616127455)
                    ·
                      rfl

theorem cell22_3994707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_3994707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994707 prefixEnd_3994707 := by exact prefixLift 3994707
  have htrace : WordTrace (prefixWord ++ tailWord_3994707) baseStart_3994707 baseEnd_3994707 := by
    simpa [prefixWord, tailWord_3994707, baseEnd_3994707] using wordTrace_append hprefix tailTrace_3994707
  have hstable : (prefixWord ++ tailWord_3994707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994707).length < 2 ^ (prefixWord ++ tailWord_3994707).sum := by decide
  have hdescent : baseEnd_3994707 < baseStart_3994707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994771 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 5]
def baseStart_3994771 : Nat := 118140960795 + 3994771 * 2 ^ 59
def prefixEnd_3994771 : Nat := 4983230072969 + 3 ^ 40 * 3994771 * 2
def baseEnd_3994771 : Nat := 455830583920465594175753

theorem tailTrace_3994771 : CollatzResearch.WordTrace tailWord_3994771 prefixEnd_3994771 455830583920465594175753 := by
  unfold tailWord_3994771
  simp only [CollatzResearch.WordTrace]
  refine ⟨145701268210634394415008167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97134178807089596276672111 145701268210634394415008167)
  ·
    refine ⟨218551902315951591622512251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145701268210634394415008167 218551902315951591622512251)
    ·
      refine ⟨327827853473927387433768377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218551902315951591622512251 327827853473927387433768377)
      ·
        refine ⟨245870890105445540575326283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327827853473927387433768377 245870890105445540575326283)
        ·
          refine ⟨368806335158168310862989425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245870890105445540575326283 368806335158168310862989425)
          ·
            refine ⟨276604751368626233147242069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368806335158168310862989425 276604751368626233147242069)
            ·
              refine ⟨3241461930101088669694243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 276604751368626233147242069 3241461930101088669694243)
              ·
                refine ⟨4862192895151633004541365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241461930101088669694243 4862192895151633004541365)
                ·
                  refine ⟨455830583920465594175753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4862192895151633004541365 455830583920465594175753)
                  ·
                    rfl

theorem cell22_3994771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 5].length) (baseStart_3994771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994771 prefixEnd_3994771 := by exact prefixLift 3994771
  have htrace : WordTrace (prefixWord ++ tailWord_3994771) baseStart_3994771 baseEnd_3994771 := by
    simpa [prefixWord, tailWord_3994771, baseEnd_3994771] using wordTrace_append hprefix tailTrace_3994771
  have hstable : (prefixWord ++ tailWord_3994771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994771).length < 2 ^ (prefixWord ++ tailWord_3994771).sum := by decide
  have hdescent : baseEnd_3994771 < baseStart_3994771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994861 : List Nat := [1, 5, 1, 2, 2, 2, 9]
def baseStart_3994861 : Nat := 118140960795 + 3994861 * 2 ^ 59
def prefixEnd_3994861 : Nat := 4983230072969 + 3 ^ 40 * 3994861 * 2
def baseEnd_3994861 : Nat := 50648983725950612880629

theorem tailTrace_3994861 : CollatzResearch.WordTrace tailWord_3994861 prefixEnd_3994861 50648983725950612880629 := by
  unfold tailWord_3994861
  simp only [CollatzResearch.WordTrace]
  refine ⟨145704550780308339785784437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97136367186872226523856291 145704550780308339785784437)
  ·
    refine ⟨13659801635653906854917291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145704550780308339785784437 13659801635653906854917291)
    ·
      refine ⟨20489702453480860282375937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13659801635653906854917291 20489702453480860282375937)
      ·
        refine ⟨15367276840110645211781953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20489702453480860282375937 15367276840110645211781953)
        ·
          refine ⟨11525457630082983908836465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15367276840110645211781953 11525457630082983908836465)
          ·
            refine ⟨8644093222562237931627349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11525457630082983908836465 8644093222562237931627349)
            ·
              refine ⟨50648983725950612880629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8644093222562237931627349 50648983725950612880629)
              ·
                rfl

theorem cell22_3994861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 9].length) (baseStart_3994861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994861 prefixEnd_3994861 := by exact prefixLift 3994861
  have htrace : WordTrace (prefixWord ++ tailWord_3994861) baseStart_3994861 baseEnd_3994861 := by
    simpa [prefixWord, tailWord_3994861, baseEnd_3994861] using wordTrace_append hprefix tailTrace_3994861
  have hstable : (prefixWord ++ tailWord_3994861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994861).length < 2 ^ (prefixWord ++ tailWord_3994861).sum := by decide
  have hdescent : baseEnd_3994861 < baseStart_3994861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994882 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3994882 : Nat := 118140960795 + 3994882 * 2 ^ 59
def prefixEnd_3994882 : Nat := 4983230072969 + 3 ^ 40 * 3994882 * 2
def baseEnd_3994882 : Nat := 1367529749329829493001919

theorem tailTrace_3994882 : CollatzResearch.WordTrace tailWord_3994882 prefixEnd_3994882 1367529749329829493001919 := by
  unfold tailWord_3994882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36426329178308065093074725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97136877808821506914865933 36426329178308065093074725)
  ·
    refine ⟨6829936720932762204951511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36426329178308065093074725 6829936720932762204951511)
    ·
      refine ⟨10244905081399143307427267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829936720932762204951511 10244905081399143307427267)
      ·
        refine ⟨15367357622098714961140901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10244905081399143307427267 15367357622098714961140901)
        ·
          refine ⟨2881379554143509055213919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15367357622098714961140901 2881379554143509055213919)
          ·
            refine ⟨4322069331215263582820879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881379554143509055213919 4322069331215263582820879)
            ·
              refine ⟨6483103996822895374231319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322069331215263582820879 6483103996822895374231319)
              ·
                refine ⟨9724655995234343061346979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483103996822895374231319 9724655995234343061346979)
                ·
                  refine ⟨14586983992851514592020469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724655995234343061346979 14586983992851514592020469)
                  ·
                    refine ⟨1367529749329829493001919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14586983992851514592020469 1367529749329829493001919)
                    ·
                      rfl

theorem cell22_3994882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3994882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994882 prefixEnd_3994882 := by exact prefixLift 3994882
  have htrace : WordTrace (prefixWord ++ tailWord_3994882) baseStart_3994882 baseEnd_3994882 := by
    simpa [prefixWord, tailWord_3994882, baseEnd_3994882] using wordTrace_append hprefix tailTrace_3994882
  have hstable : (prefixWord ++ tailWord_3994882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994882).length < 2 ^ (prefixWord ++ tailWord_3994882).sum := by decide
  have hdescent : baseEnd_3994882 < baseStart_3994882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994906 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_3994906 : Nat := 118140960795 + 3994906 * 2 ^ 59
def prefixEnd_3994906 : Nat := 4983230072969 + 3 ^ 40 * 3994906 * 2
def baseEnd_3994906 : Nat := 455845988340100476800615

theorem tailTrace_3994906 : CollatzResearch.WordTrace tailWord_3994906 prefixEnd_3994906 455845988340100476800615 := by
  unfold tailWord_3994906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36426548016286328117793143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97137461376763541647448381 36426548016286328117793143)
  ·
    refine ⟨54639822024429492176689715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36426548016286328117793143 54639822024429492176689715)
    ·
      refine ⟨81959733036644238265034573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54639822024429492176689715 81959733036644238265034573)
      ·
        refine ⟨30734899888741589349387965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81959733036644238265034573 30734899888741589349387965)
        ·
          refine ⟨11525587458278096006020487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30734899888741589349387965 11525587458278096006020487)
          ·
            refine ⟨17288381187417144009030731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525587458278096006020487 17288381187417144009030731)
            ·
              refine ⟨25932571781125716013546097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17288381187417144009030731 25932571781125716013546097)
              ·
                refine ⟨19449428835844287010159573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25932571781125716013546097 19449428835844287010159573)
                ·
                  refine ⟨455845988340100476800615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19449428835844287010159573 455845988340100476800615)
                  ·
                    rfl

theorem cell22_3994906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_3994906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994906 prefixEnd_3994906 := by exact prefixLift 3994906
  have htrace : WordTrace (prefixWord ++ tailWord_3994906) baseStart_3994906 baseEnd_3994906 := by
    simpa [prefixWord, tailWord_3994906, baseEnd_3994906] using wordTrace_append hprefix tailTrace_3994906
  have hstable : (prefixWord ++ tailWord_3994906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994906).length < 2 ^ (prefixWord ++ tailWord_3994906).sum := by decide
  have hdescent : baseEnd_3994906 < baseStart_3994906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994936 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_3994936 : Nat := 118140960795 + 3994936 * 2 ^ 59
def prefixEnd_3994936 : Nat := 4983230072969 + 3 ^ 40 * 3994936 * 2
def baseEnd_3994936 : Nat := 1367548234633391352151753

theorem tailTrace_3994936 : CollatzResearch.WordTrace tailWord_3994936 prefixEnd_3994936 1367548234633391352151753 := by
  unfold tailWord_3994936
  simp only [CollatzResearch.WordTrace]
  refine ⟨72853643127518313797382331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97138190836691085063176441 72853643127518313797382331)
  ·
    refine ⟨109280464691277470696073497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72853643127518313797382331 109280464691277470696073497)
    ·
      refine ⟨81960348518458103022055123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109280464691277470696073497 81960348518458103022055123)
      ·
        refine ⟨122940522777687154533082685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81960348518458103022055123 122940522777687154533082685)
        ·
          refine ⟨46102696041632682949906007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122940522777687154533082685 46102696041632682949906007)
          ·
            refine ⟨69154044062449024424859011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46102696041632682949906007 69154044062449024424859011)
            ·
              refine ⟨103731066093673536637288517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69154044062449024424859011 103731066093673536637288517)
              ·
                refine ⟨19449574892563788119491597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103731066093673536637288517 19449574892563788119491597)
                ·
                  refine ⟨7293590584711420544809349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19449574892563788119491597 7293590584711420544809349)
                  ·
                    refine ⟨1367548234633391352151753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7293590584711420544809349 1367548234633391352151753)
                    ·
                      rfl

theorem cell22_3994936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_3994936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994936 prefixEnd_3994936 := by exact prefixLift 3994936
  have htrace : WordTrace (prefixWord ++ tailWord_3994936) baseStart_3994936 baseEnd_3994936 := by
    simpa [prefixWord, tailWord_3994936, baseEnd_3994936] using wordTrace_append hprefix tailTrace_3994936
  have hstable : (prefixWord ++ tailWord_3994936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994936).length < 2 ^ (prefixWord ++ tailWord_3994936).sum := by decide
  have hdescent : baseEnd_3994936 < baseStart_3994936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994940 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 5]
def baseStart_3994940 : Nat := 118140960795 + 3994940 * 2 ^ 59
def prefixEnd_3994940 : Nat := 4983230072969 + 3 ^ 40 * 3994940 * 2
def baseEnd_3994940 : Nat := 455849867971712225017247

theorem tailTrace_3994940 : CollatzResearch.WordTrace tailWord_3994940 prefixEnd_3994940 455849867971712225017247 := by
  unfold tailWord_3994940
  simp only [CollatzResearch.WordTrace]
  refine ⟨72853716073511068138955137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97138288098014757518606849 72853716073511068138955137)
  ·
    refine ⟨54640287055133301104216353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72853716073511068138955137 54640287055133301104216353)
    ·
      refine ⟨40980215291349975828162265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54640287055133301104216353 40980215291349975828162265)
      ·
        refine ⟨30735161468512481871121699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40980215291349975828162265 30735161468512481871121699)
        ·
          refine ⟨46102742202768722806682549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30735161468512481871121699 46102742202768722806682549)
          ·
            refine ⟨4322132081509567763126489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46102742202768722806682549 4322132081509567763126489)
            ·
              refine ⟨3241599061132175822344867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322132081509567763126489 3241599061132175822344867)
              ·
                refine ⟨4862398591698263733517301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241599061132175822344867 4862398591698263733517301)
                ·
                  refine ⟨455849867971712225017247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4862398591698263733517301 455849867971712225017247)
                  ·
                    rfl

theorem cell22_3994940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_3994940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994940 prefixEnd_3994940 := by exact prefixLift 3994940
  have htrace : WordTrace (prefixWord ++ tailWord_3994940) baseStart_3994940 baseEnd_3994940 := by
    simpa [prefixWord, tailWord_3994940, baseEnd_3994940] using wordTrace_append hprefix tailTrace_3994940
  have hstable : (prefixWord ++ tailWord_3994940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994940).length < 2 ^ (prefixWord ++ tailWord_3994940).sum := by decide
  have hdescent : baseEnd_3994940 < baseStart_3994940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994953 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_3994953 : Nat := 118140960795 + 3994953 * 2 ^ 59
def prefixEnd_3994953 : Nat := 4983230072969 + 3 ^ 40 * 3994953 * 2
def baseEnd_3994953 : Nat := 1367554054080808974476701

theorem tailTrace_3994953 : CollatzResearch.WordTrace tailWord_3994953 prefixEnd_3994953 1367554054080808974476701 := by
  unfold tailWord_3994953
  simp only [CollatzResearch.WordTrace]
  refine ⟨145707906295975039498133513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97138604197316692998755675 145707906295975039498133513)
  ·
    refine ⟨109280929721981279623600135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145707906295975039498133513 109280929721981279623600135)
    ·
      refine ⟨163921394582971919435400203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109280929721981279623600135 163921394582971919435400203)
      ·
        refine ⟨245882091874457879153100305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163921394582971919435400203 245882091874457879153100305)
        ·
          refine ⟨184411568905843409364825229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245882091874457879153100305 184411568905843409364825229)
          ·
            refine ⟨69154338339691278511809461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184411568905843409364825229 69154338339691278511809461)
            ·
              refine ⟨6483219219346057360482137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69154338339691278511809461 6483219219346057360482137)
              ·
                refine ⟨4862414414509543020361603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483219219346057360482137 4862414414509543020361603)
                ·
                  refine ⟨7293621621764314530542405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862414414509543020361603 7293621621764314530542405)
                  ·
                    refine ⟨1367554054080808974476701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7293621621764314530542405 1367554054080808974476701)
                    ·
                      rfl

theorem cell22_3994953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_3994953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994953 prefixEnd_3994953 := by exact prefixLift 3994953
  have htrace : WordTrace (prefixWord ++ tailWord_3994953) baseStart_3994953 baseEnd_3994953 := by
    simpa [prefixWord, tailWord_3994953, baseEnd_3994953] using wordTrace_append hprefix tailTrace_3994953
  have hstable : (prefixWord ++ tailWord_3994953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994953).length < 2 ^ (prefixWord ++ tailWord_3994953).sum := by decide
  have hdescent : baseEnd_3994953 < baseStart_3994953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994968 : List Nat := [2, 1, 2, 2, 1, 1, 4, 5, 4]
def baseStart_3994968 : Nat := 118140960795 + 3994968 * 2 ^ 59
def prefixEnd_3994968 : Nat := 4983230072969 + 3 ^ 40 * 3994968 * 2
def baseEnd_3994968 : Nat := 455853062962451311783885

theorem tailTrace_3994968 : CollatzResearch.WordTrace tailWord_3994968 prefixEnd_3994968 455853062962451311783885 := by
  unfold tailWord_3994968
  simp only [CollatzResearch.WordTrace]
  refine ⟨72854226695460348529964779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97138968927280464706619705 72854226695460348529964779)
  ·
    refine ⟨109281340043190522794947169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72854226695460348529964779 109281340043190522794947169)
    ·
      refine ⟨81961005032392892096210377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109281340043190522794947169 81961005032392892096210377)
      ·
        refine ⟨61470753774294669072157783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81961005032392892096210377 61470753774294669072157783)
        ·
          refine ⟨92206130661442003608236675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61470753774294669072157783 92206130661442003608236675)
          ·
            refine ⟨138309195992163005412355013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92206130661442003608236675 138309195992163005412355013)
            ·
              refine ⟨25932974248530563514816565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138309195992163005412355013 25932974248530563514816565)
              ·
                refine ⟨2431216335799740329514053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25932974248530563514816565 2431216335799740329514053)
                ·
                  refine ⟨455853062962451311783885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431216335799740329514053 455853062962451311783885)
                  ·
                    rfl

theorem cell22_3994968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_3994968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3994968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3994968 prefixEnd_3994968 := by exact prefixLift 3994968
  have htrace : WordTrace (prefixWord ++ tailWord_3994968) baseStart_3994968 baseEnd_3994968 := by
    simpa [prefixWord, tailWord_3994968, baseEnd_3994968] using wordTrace_append hprefix tailTrace_3994968
  have hstable : (prefixWord ++ tailWord_3994968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994968).length < 2 ^ (prefixWord ++ tailWord_3994968).sum := by decide
  have hdescent : baseEnd_3994968 < baseStart_3994968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995015 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 2, 4]
def baseStart_3995015 : Nat := 118140960795 + 3995015 * 2 ^ 59
def prefixEnd_3995015 : Nat := 4983230072969 + 3 ^ 40 * 3995015 * 2
def baseEnd_3995015 : Nat := 1367575277947861479426511

theorem tailTrace_3995015 : CollatzResearch.WordTrace tailWord_3995015 prefixEnd_3995015 1367575277947861479426511 := by
  unfold tailWord_3995015
  simp only [CollatzResearch.WordTrace]
  refine ⟨145710167621750424086890499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97140111747833616057926999 145710167621750424086890499)
  ·
    refine ⟨218565251432625636130335749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145710167621750424086890499 218565251432625636130335749)
    ·
      refine ⟨40980984643617306774437953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218565251432625636130335749 40980984643617306774437953)
      ·
        refine ⟨30735738482712980080828465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40980984643617306774437953 30735738482712980080828465)
        ·
          refine ⟨23051803862034735060621349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30735738482712980080828465 23051803862034735060621349)
          ·
            refine ⟨4322213224131512823866503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23051803862034735060621349 4322213224131512823866503)
            ·
              refine ⟨6483319836197269235799755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322213224131512823866503 6483319836197269235799755)
              ·
                refine ⟨9724979754295903853699633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483319836197269235799755 9724979754295903853699633)
                ·
                  refine ⟨7293734815721927890274725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9724979754295903853699633 7293734815721927890274725)
                  ·
                    refine ⟨1367575277947861479426511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7293734815721927890274725 1367575277947861479426511)
                    ·
                      rfl

theorem cell22_3995015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_3995015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995015 prefixEnd_3995015 := by exact prefixLift 3995015
  have htrace : WordTrace (prefixWord ++ tailWord_3995015) baseStart_3995015 baseEnd_3995015 := by
    simpa [prefixWord, tailWord_3995015, baseEnd_3995015] using wordTrace_append hprefix tailTrace_3995015
  have hstable : (prefixWord ++ tailWord_3995015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995015).length < 2 ^ (prefixWord ++ tailWord_3995015).sum := by decide
  have hdescent : baseEnd_3995015 < baseStart_3995015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995056 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_3995056 : Nat := 118140960795 + 3995056 * 2 ^ 59
def prefixEnd_3995056 : Nat := 4983230072969 + 3 ^ 40 * 3995056 * 2
def baseEnd_3995056 : Nat := 1367589313085751039151385

theorem tailTrace_3995056 : CollatzResearch.WordTrace tailWord_3995056 prefixEnd_3995056 1367589313085751039151385 := by
  unfold tailWord_3995056
  simp only [CollatzResearch.WordTrace]
  refine ⟨72855831507300944044566511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97141108676401258726088681 72855831507300944044566511)
  ·
    refine ⟨109283747260951416066849767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72855831507300944044566511 109283747260951416066849767)
    ·
      refine ⟨163925620891427124100274651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109283747260951416066849767 163925620891427124100274651)
      ·
        refine ⟨245888431337140686150411977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163925620891427124100274651 245888431337140686150411977)
        ·
          refine ⟨184416323502855514612808983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245888431337140686150411977 184416323502855514612808983)
          ·
            refine ⟨276624485254283271919213475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184416323502855514612808983 276624485254283271919213475)
            ·
              refine ⟨414936727881424907878820213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276624485254283271919213475 414936727881424907878820213)
              ·
                refine ⟨38900318238883585113639395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 414936727881424907878820213 38900318238883585113639395)
                ·
                  refine ⟨58350477358325377670459093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38900318238883585113639395 58350477358325377670459093)
                  ·
                    refine ⟨1367589313085751039151385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58350477358325377670459093 1367589313085751039151385)
                    ·
                      rfl

theorem cell22_3995056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_3995056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995056 prefixEnd_3995056 := by exact prefixLift 3995056
  have htrace : WordTrace (prefixWord ++ tailWord_3995056) baseStart_3995056 baseEnd_3995056 := by
    simpa [prefixWord, tailWord_3995056, baseEnd_3995056] using wordTrace_append hprefix tailTrace_3995056
  have hstable : (prefixWord ++ tailWord_3995056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995056).length < 2 ^ (prefixWord ++ tailWord_3995056).sum := by decide
  have hdescent : baseEnd_3995056 < baseStart_3995056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995071 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 8]
def baseStart_3995071 : Nat := 118140960795 + 3995071 * 2 ^ 59
def prefixEnd_3995071 : Nat := 4983230072969 + 3 ^ 40 * 3995071 * 2
def baseEnd_3995071 : Nat := 1367594447892296000026339

theorem tailTrace_3995071 : CollatzResearch.WordTrace tailWord_3995071 prefixEnd_3995071 1367594447892296000026339 := by
  unfold tailWord_3995071
  simp only [CollatzResearch.WordTrace]
  refine ⟨145712210109547545650929067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97141473406365030433952711 145712210109547545650929067)
  ·
    refine ⟨218568315164321318476393601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145712210109547545650929067 218568315164321318476393601)
    ·
      refine ⟨163926236373240988857295201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218568315164321318476393601 163926236373240988857295201)
      ·
        refine ⟨122944677279930741642971401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163926236373240988857295201 122944677279930741642971401)
        ·
          refine ⟨92208507959948056232228551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122944677279930741642971401 92208507959948056232228551)
          ·
            refine ⟨138312761939922084348342827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92208507959948056232228551 138312761939922084348342827)
            ·
              refine ⟨207469142909883126522514241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138312761939922084348342827 207469142909883126522514241)
              ·
                refine ⟨155601857182412344891885681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207469142909883126522514241 155601857182412344891885681)
                ·
                  refine ⟨116701392886809258668914261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155601857182412344891885681 116701392886809258668914261)
                  ·
                    refine ⟨1367594447892296000026339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116701392886809258668914261 1367594447892296000026339)
                    ·
                      rfl

theorem cell22_3995071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_3995071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995071 prefixEnd_3995071 := by exact prefixLift 3995071
  have htrace : WordTrace (prefixWord ++ tailWord_3995071) baseStart_3995071 baseEnd_3995071 := by
    simpa [prefixWord, tailWord_3995071, baseEnd_3995071] using wordTrace_append hprefix tailTrace_3995071
  have hstable : (prefixWord ++ tailWord_3995071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995071).length < 2 ^ (prefixWord ++ tailWord_3995071).sum := by decide
  have hdescent : baseEnd_3995071 < baseStart_3995071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995122 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_3995122 : Nat := 118140960795 + 3995122 * 2 ^ 59
def prefixEnd_3995122 : Nat := 4983230072969 + 3 ^ 40 * 3995122 * 2
def baseEnd_3995122 : Nat := 1367611906234548867001183

theorem tailTrace_3995122 : CollatzResearch.WordTrace tailWord_3995122 prefixEnd_3995122 1367611906234548867001183 := by
  unfold tailWord_3995122
  simp only [CollatzResearch.WordTrace]
  refine ⟨36428517558090695340258905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97142713488241854240690413 36428517558090695340258905)
  ·
    refine ⟨27321388168568021505194179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36428517558090695340258905 27321388168568021505194179)
    ·
      refine ⟨40982082252852032257791269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27321388168568021505194179 40982082252852032257791269)
      ·
        refine ⟨7684140422409756048335863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40982082252852032257791269 7684140422409756048335863)
        ·
          refine ⟨11526210633614634072503795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684140422409756048335863 11526210633614634072503795)
          ·
            refine ⟨17289315950421951108755693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11526210633614634072503795 17289315950421951108755693)
            ·
              refine ⟨6483493481408231665783385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17289315950421951108755693 6483493481408231665783385)
              ·
                refine ⟨4862620111056173749337539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483493481408231665783385 4862620111056173749337539)
                ·
                  refine ⟨7293930166584260624006309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862620111056173749337539 7293930166584260624006309)
                  ·
                    refine ⟨1367611906234548867001183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7293930166584260624006309 1367611906234548867001183)
                    ·
                      rfl

theorem cell22_3995122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_3995122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995122 prefixEnd_3995122 := by exact prefixLift 3995122
  have htrace : WordTrace (prefixWord ++ tailWord_3995122) baseStart_3995122 baseEnd_3995122 := by
    simpa [prefixWord, tailWord_3995122, baseEnd_3995122] using wordTrace_append hprefix tailTrace_3995122
  have hstable : (prefixWord ++ tailWord_3995122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995122).length < 2 ^ (prefixWord ++ tailWord_3995122).sum := by decide
  have hdescent : baseEnd_3995122 < baseStart_3995122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995148 : List Nat := [2, 2, 1, 2, 5, 10]
def baseStart_3995148 : Nat := 118140960795 + 3995148 * 2 ^ 59
def prefixEnd_3995148 : Nat := 4983230072969 + 3 ^ 40 * 3995148 * 2
def baseEnd_3995148 : Nat := 16884207488467820566063

theorem tailTrace_3995148 : CollatzResearch.WordTrace tailWord_3995148 prefixEnd_3995148 16884207488467820566063 := by
  unfold tailWord_3995148
  simp only [CollatzResearch.WordTrace]
  refine ⟨72857509265134293900741049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97143345686845725200988065 72857509265134293900741049)
  ·
    refine ⟨54643131948850720425555787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72857509265134293900741049 54643131948850720425555787)
    ·
      refine ⟨81964697923276080638333681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54643131948850720425555787 81964697923276080638333681)
      ·
        refine ⟨61473523442457060478750261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81964697923276080638333681 61473523442457060478750261)
        ·
          refine ⟨5763142822730349419882837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61473523442457060478750261 5763142822730349419882837)
          ·
            refine ⟨16884207488467820566063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5763142822730349419882837 16884207488467820566063)
            ·
              rfl

theorem cell22_3995148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 10].length) (baseStart_3995148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995148 prefixEnd_3995148 := by exact prefixLift 3995148
  have htrace : WordTrace (prefixWord ++ tailWord_3995148) baseStart_3995148 baseEnd_3995148 := by
    simpa [prefixWord, tailWord_3995148, baseEnd_3995148] using wordTrace_append hprefix tailTrace_3995148
  have hstable : (prefixWord ++ tailWord_3995148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995148).length < 2 ^ (prefixWord ++ tailWord_3995148).sum := by decide
  have hdescent : baseEnd_3995148 < baseStart_3995148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995182 : List Nat := [4, 1, 3, 1, 2, 2, 3, 6]
def baseStart_3995182 : Nat := 118140960795 + 3995182 * 2 ^ 59
def prefixEnd_3995182 : Nat := 4983230072969 + 3 ^ 40 * 3995182 * 2
def baseEnd_3995182 : Nat := 151959160606747634500111

theorem tailTrace_3995182 : CollatzResearch.WordTrace tailWord_3995182 prefixEnd_3995182 151959160606747634500111 := by
  unfold tailWord_3995182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18214532326518176451027475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97144172408096941072146533 18214532326518176451027475)
  ·
    refine ⟨27321798489777264676541213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18214532326518176451027475 27321798489777264676541213)
    ·
      refine ⟨10245674433666474253702955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27321798489777264676541213 10245674433666474253702955)
      ·
        refine ⟨15368511650499711380554433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245674433666474253702955 15368511650499711380554433)
        ·
          refine ⟨11526383737874783535415825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15368511650499711380554433 11526383737874783535415825)
          ·
            refine ⟨8644787803406087651561869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11526383737874783535415825 8644787803406087651561869)
            ·
              refine ⟨3241795426277282869335701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8644787803406087651561869 3241795426277282869335701)
              ·
                refine ⟨151959160606747634500111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3241795426277282869335701 151959160606747634500111)
                ·
                  rfl

theorem cell22_3995182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_3995182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995182 prefixEnd_3995182 := by exact prefixLift 3995182
  have htrace : WordTrace (prefixWord ++ tailWord_3995182) baseStart_3995182 baseEnd_3995182 := by
    simpa [prefixWord, tailWord_3995182, baseEnd_3995182] using wordTrace_append hprefix tailTrace_3995182
  have hstable : (prefixWord ++ tailWord_3995182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995182).length < 2 ^ (prefixWord ++ tailWord_3995182).sum := by decide
  have hdescent : baseEnd_3995182 < baseStart_3995182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995300 : List Nat := [2, 3, 1, 2, 2, 2, 2, 8]
def baseStart_3995300 : Nat := 118140960795 + 3995300 * 2 ^ 59
def prefixEnd_3995300 : Nat := 4983230072969 + 3 ^ 40 * 3995300 * 2
def baseEnd_3995300 : Nat := 151963648808023970672293

theorem tailTrace_3995300 : CollatzResearch.WordTrace tailWord_3995300 prefixEnd_3995300 151963648808023970672293 := by
  unfold tailWord_3995300
  simp only [CollatzResearch.WordTrace]
  refine ⟨72860281212858958880507677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97147041617145278507343569 72860281212858958880507677)
  ·
    refine ⟨27322605454822109580190379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72860281212858958880507677 27322605454822109580190379)
    ·
      refine ⟨40983908182233164370285569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27322605454822109580190379 40983908182233164370285569)
      ·
        refine ⟨30737931136674873277714177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40983908182233164370285569 30737931136674873277714177)
        ·
          refine ⟨23053448352506154958285633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30737931136674873277714177 23053448352506154958285633)
          ·
            refine ⟨17290086264379616218714225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23053448352506154958285633 17290086264379616218714225)
            ·
              refine ⟨12967564698284712164035669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17290086264379616218714225 12967564698284712164035669)
              ·
                refine ⟨151963648808023970672293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12967564698284712164035669 151963648808023970672293)
                ·
                  rfl

theorem cell22_3995300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 8].length) (baseStart_3995300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995300 prefixEnd_3995300 := by exact prefixLift 3995300
  have htrace : WordTrace (prefixWord ++ tailWord_3995300) baseStart_3995300 baseEnd_3995300 := by
    simpa [prefixWord, tailWord_3995300, baseEnd_3995300] using wordTrace_append hprefix tailTrace_3995300
  have hstable : (prefixWord ++ tailWord_3995300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995300).length < 2 ^ (prefixWord ++ tailWord_3995300).sum := by decide
  have hdescent : baseEnd_3995300 < baseStart_3995300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995317 : List Nat := [1, 3, 3, 3, 3, 9]
def baseStart_3995317 : Nat := 118140960795 + 3995317 * 2 ^ 59
def prefixEnd_3995317 : Nat := 4983230072969 + 3 ^ 40 * 3995317 * 2
def baseEnd_3995317 : Nat := 16884921712588066152785

theorem tailTrace_3995317 : CollatzResearch.WordTrace tailWord_3995317 prefixEnd_3995317 16884921712588066152785 := by
  unfold tailWord_3995317
  simp only [CollatzResearch.WordTrace]
  refine ⟨145721182466656329664384205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97147454977770886442922803 145721182466656329664384205)
  ·
    refine ⟨54645443424996123624144077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145721182466656329664384205 54645443424996123624144077)
    ·
      refine ⟨20492041284373546359054029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54645443424996123624144077 20492041284373546359054029)
      ·
        refine ⟨7684515481640079884645261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20492041284373546359054029 7684515481640079884645261)
        ·
          refine ⟨2881693305615029956741973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7684515481640079884645261 2881693305615029956741973)
          ·
            refine ⟨16884921712588066152785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2881693305615029956741973 16884921712588066152785)
            ·
              rfl

theorem cell22_3995317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 9].length) (baseStart_3995317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995317 prefixEnd_3995317 := by exact prefixLift 3995317
  have htrace : WordTrace (prefixWord ++ tailWord_3995317) baseStart_3995317 baseEnd_3995317 := by
    simpa [prefixWord, tailWord_3995317, baseEnd_3995317] using wordTrace_append hprefix tailTrace_3995317
  have hstable : (prefixWord ++ tailWord_3995317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995317).length < 2 ^ (prefixWord ++ tailWord_3995317).sum := by decide
  have hdescent : baseEnd_3995317 < baseStart_3995317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995441 : List Nat := [1, 2, 2, 3, 2, 3, 3, 2, 4]
def baseStart_3995441 : Nat := 118140960795 + 3995441 * 2 ^ 59
def prefixEnd_3995441 : Nat := 4983230072969 + 3 ^ 40 * 3995441 * 2
def baseEnd_3995441 : Nat := 455907035484579456091735

theorem tailTrace_3995441 : CollatzResearch.WordTrace tailWord_3995441 prefixEnd_3995441 455907035484579456091735 := by
  unfold tailWord_3995441
  simp only [CollatzResearch.WordTrace]
  refine ⟨145725705118207098841898177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97150470078804732561265451 145725705118207098841898177)
  ·
    refine ⟨109294278838655324131423633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145725705118207098841898177 109294278838655324131423633)
    ·
      refine ⟨81970709128991493098567725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109294278838655324131423633 81970709128991493098567725)
      ·
        refine ⟨30739015923371809911962897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81970709128991493098567725 30739015923371809911962897)
        ·
          refine ⟨23054261942528857433972173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30739015923371809911962897 23054261942528857433972173)
          ·
            refine ⟨8645348228448321537739565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23054261942528857433972173 8645348228448321537739565)
            ·
              refine ⟨3242005585668120576652337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8645348228448321537739565 3242005585668120576652337)
              ·
                refine ⟨2431504189251090432489253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242005585668120576652337 2431504189251090432489253)
                ·
                  refine ⟨455907035484579456091735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431504189251090432489253 455907035484579456091735)
                  ·
                    rfl

theorem cell22_3995441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_3995441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995441 prefixEnd_3995441 := by exact prefixLift 3995441
  have htrace : WordTrace (prefixWord ++ tailWord_3995441) baseStart_3995441 baseEnd_3995441 := by
    simpa [prefixWord, tailWord_3995441, baseEnd_3995441] using wordTrace_append hprefix tailTrace_3995441
  have hstable : (prefixWord ++ tailWord_3995441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995441).length < 2 ^ (prefixWord ++ tailWord_3995441).sum := by decide
  have hdescent : baseEnd_3995441 < baseStart_3995441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995469 : List Nat := [1, 6, 1, 2, 1, 1, 2, 8]
def baseStart_3995469 : Nat := 118140960795 + 3995469 * 2 ^ 59
def prefixEnd_3995469 : Nat := 4983230072969 + 3 ^ 40 * 3995469 * 2
def baseEnd_3995469 : Nat := 151970076825106180952791

theorem tailTrace_3995469 : CollatzResearch.WordTrace tailWord_3995469 prefixEnd_3995469 151970076825106180952791 := by
  unfold tailWord_3995469
  simp only [CollatzResearch.WordTrace]
  refine ⟨145726726362105659623917461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97151150908070439749278307 145726726362105659623917461)
  ·
    refine ⟨6830940298223702794871131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145726726362105659623917461 6830940298223702794871131)
    ·
      refine ⟨10246410447335554192306697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830940298223702794871131 10246410447335554192306697)
      ·
        refine ⟨7684807835501665644230023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10246410447335554192306697 7684807835501665644230023)
        ·
          refine ⟨11527211753252498466345035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684807835501665644230023 11527211753252498466345035)
          ·
            refine ⟨17290817629878747699517553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527211753252498466345035 17290817629878747699517553)
            ·
              refine ⟨12968113222409060774638165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17290817629878747699517553 12968113222409060774638165)
              ·
                refine ⟨151970076825106180952791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12968113222409060774638165 151970076825106180952791)
                ·
                  rfl

theorem cell22_3995469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 8].length) (baseStart_3995469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995469 prefixEnd_3995469 := by exact prefixLift 3995469
  have htrace : WordTrace (prefixWord ++ tailWord_3995469) baseStart_3995469 baseEnd_3995469 := by
    simpa [prefixWord, tailWord_3995469, baseEnd_3995469] using wordTrace_append hprefix tailTrace_3995469
  have hstable : (prefixWord ++ tailWord_3995469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995469).length < 2 ^ (prefixWord ++ tailWord_3995469).sum := by decide
  have hdescent : baseEnd_3995469 < baseStart_3995469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995518 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3995518 : Nat := 118140960795 + 3995518 * 2 ^ 59
def prefixEnd_3995518 : Nat := 4983230072969 + 3 ^ 40 * 3995518 * 2
def baseEnd_3995518 : Nat := 1367747465127335834099969

theorem tailTrace_3995518 : CollatzResearch.WordTrace tailWord_3995518 prefixEnd_3995518 1367747465127335834099969 := by
  unfold tailWord_3995518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216064192366017624056401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97152342359285427328300805 18216064192366017624056401)
  ·
    refine ⟨13662048144274513218042301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18216064192366017624056401 13662048144274513218042301)
    ·
      refine ⟨5123268054102942456765863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13662048144274513218042301 5123268054102942456765863)
      ·
        refine ⟨7684902081154413685148795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123268054102942456765863 7684902081154413685148795)
        ·
          refine ⟨11527353121731620527723193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684902081154413685148795 11527353121731620527723193)
          ·
            refine ⟨8645514841298715395792395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11527353121731620527723193 8645514841298715395792395)
            ·
              refine ⟨12968272261948073093688593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645514841298715395792395 12968272261948073093688593)
              ·
                refine ⟨9726204196461054820266445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12968272261948073093688593 9726204196461054820266445)
                ·
                  refine ⟨3647326573672895557599917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9726204196461054820266445 3647326573672895557599917)
                  ·
                    refine ⟨1367747465127335834099969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3647326573672895557599917 1367747465127335834099969)
                    ·
                      rfl

theorem cell22_3995518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3995518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995518 prefixEnd_3995518 := by exact prefixLift 3995518
  have htrace : WordTrace (prefixWord ++ tailWord_3995518) baseStart_3995518 baseEnd_3995518 := by
    simpa [prefixWord, tailWord_3995518, baseEnd_3995518] using wordTrace_append hprefix tailTrace_3995518
  have hstable : (prefixWord ++ tailWord_3995518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995518).length < 2 ^ (prefixWord ++ tailWord_3995518).sum := by decide
  have hdescent : baseEnd_3995518 < baseStart_3995518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995557 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3995557 : Nat := 118140960795 + 3995557 * 2 ^ 59
def prefixEnd_3995557 : Nat := 4983230072969 + 3 ^ 40 * 3995557 * 2
def baseEnd_3995557 : Nat := 1367760815624352732374849

theorem tailTrace_3995557 : CollatzResearch.WordTrace tailWord_3995557 prefixEnd_3995557 1367760815624352732374849 := by
  unfold tailWord_3995557
  simp only [CollatzResearch.WordTrace]
  refine ⟨145729935985786850653120925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97153290657191233768747283 145729935985786850653120925)
  ·
    refine ⟨54648725994670068994920347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145729935985786850653120925 54648725994670068994920347)
    ·
      refine ⟨81973088992005103492380521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54648725994670068994920347 81973088992005103492380521)
      ·
        refine ⟨61479816744003827619285391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81973088992005103492380521 61479816744003827619285391)
        ·
          refine ⟨92219725116005741428928087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61479816744003827619285391 92219725116005741428928087)
          ·
            refine ⟨138329587674008612143392131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92219725116005741428928087 138329587674008612143392131)
            ·
              refine ⟨207494381511012918215088197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138329587674008612143392131 207494381511012918215088197)
              ·
                refine ⟨38905196533314922165329037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207494381511012918215088197 38905196533314922165329037)
                ·
                  refine ⟨14589448699993095811998389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38905196533314922165329037 14589448699993095811998389)
                  ·
                    refine ⟨1367760815624352732374849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14589448699993095811998389 1367760815624352732374849)
                    ·
                      rfl

theorem cell22_3995557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3995557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995557 prefixEnd_3995557 := by exact prefixLift 3995557
  have htrace : WordTrace (prefixWord ++ tailWord_3995557) baseStart_3995557 baseEnd_3995557 := by
    simpa [prefixWord, tailWord_3995557, baseEnd_3995557] using wordTrace_append hprefix tailTrace_3995557
  have hstable : (prefixWord ++ tailWord_3995557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995557).length < 2 ^ (prefixWord ++ tailWord_3995557).sum := by decide
  have hdescent : baseEnd_3995557 < baseStart_3995557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995559 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 6]
def baseStart_3995559 : Nat := 118140960795 + 3995559 * 2 ^ 59
def prefixEnd_3995559 : Nat := 4983230072969 + 3 ^ 40 * 3995559 * 2
def baseEnd_3995559 : Nat := 455920500088408464608281

theorem tailTrace_3995559 : CollatzResearch.WordTrace tailWord_3995559 prefixEnd_3995559 455920500088408464608281 := by
  unfold tailWord_3995559
  simp only [CollatzResearch.WordTrace]
  refine ⟨145730008931779604994693731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97153339287853069996462487 145730008931779604994693731)
  ·
    refine ⟨218595013397669407492040597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145730008931779604994693731 218595013397669407492040597)
    ·
      refine ⟨10246641253015753476189403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218595013397669407492040597 10246641253015753476189403)
      ·
        refine ⟨15369961879523630214284105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10246641253015753476189403 15369961879523630214284105)
        ·
          refine ⟨11527471409642722660713079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15369961879523630214284105 11527471409642722660713079)
          ·
            refine ⟨17291207114464083991069619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527471409642722660713079 17291207114464083991069619)
            ·
              refine ⟨25936810671696125986604429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17291207114464083991069619 25936810671696125986604429)
              ·
                refine ⟨9726304001886047244976661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25936810671696125986604429 9726304001886047244976661)
                ·
                  refine ⟨455920500088408464608281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9726304001886047244976661 455920500088408464608281)
                  ·
                    rfl

theorem cell22_3995559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 6].length) (baseStart_3995559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995559 prefixEnd_3995559 := by exact prefixLift 3995559
  have htrace : WordTrace (prefixWord ++ tailWord_3995559) baseStart_3995559 baseEnd_3995559 := by
    simpa [prefixWord, tailWord_3995559, baseEnd_3995559] using wordTrace_append hprefix tailTrace_3995559
  have hstable : (prefixWord ++ tailWord_3995559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995559).length < 2 ^ (prefixWord ++ tailWord_3995559).sum := by decide
  have hdescent : baseEnd_3995559 < baseStart_3995559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995661 : List Nat := [1, 7, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3995661 : Nat := 118140960795 + 3995661 * 2 ^ 59
def prefixEnd_3995661 : Nat := 4983230072969 + 3 ^ 40 * 3995661 * 2
def baseEnd_3995661 : Nat := 455932138983243709258177

theorem tailTrace_3995661 : CollatzResearch.WordTrace tailWord_3995661 prefixEnd_3995661 455932138983243709258177 := by
  unfold tailWord_3995661
  simp only [CollatzResearch.WordTrace]
  refine ⟨145733729177410076414906837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97155819451606717609937891 145733729177410076414906837)
  ·
    refine ⟨3415634277595548665974379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 145733729177410076414906837 3415634277595548665974379)
    ·
      refine ⟨5123451416393322998961569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415634277595548665974379 5123451416393322998961569)
      ·
        refine ⟨3842588562294992249221177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5123451416393322998961569 3842588562294992249221177)
        ·
          refine ⟨2881941421721244186915883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3842588562294992249221177 2881941421721244186915883)
          ·
            refine ⟨4322912132581866280373825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881941421721244186915883 4322912132581866280373825)
            ·
              refine ⟨3242184099436399710280369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322912132581866280373825 3242184099436399710280369)
              ·
                refine ⟨2431638074577299782710277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242184099436399710280369 2431638074577299782710277)
                ·
                  refine ⟨455932138983243709258177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431638074577299782710277 455932138983243709258177)
                  ·
                    rfl

theorem cell22_3995661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3995661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995661 prefixEnd_3995661 := by exact prefixLift 3995661
  have htrace : WordTrace (prefixWord ++ tailWord_3995661) baseStart_3995661 baseEnd_3995661 := by
    simpa [prefixWord, tailWord_3995661, baseEnd_3995661] using wordTrace_append hprefix tailTrace_3995661
  have hstable : (prefixWord ++ tailWord_3995661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995661).length < 2 ^ (prefixWord ++ tailWord_3995661).sum := by decide
  have hdescent : baseEnd_3995661 < baseStart_3995661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995679 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 5, 4]
def baseStart_3995679 : Nat := 118140960795 + 3995679 * 2 ^ 59
def prefixEnd_3995679 : Nat := 4983230072969 + 3 ^ 40 * 3995679 * 2
def baseEnd_3995679 : Nat := 1367802578717585080824475

theorem tailTrace_3995679 : CollatzResearch.WordTrace tailWord_3995679 prefixEnd_3995679 1367802578717585080824475 := by
  unfold tailWord_3995679
  simp only [CollatzResearch.WordTrace]
  refine ⟨145734385691344865489062091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97156257127563243659374727 145734385691344865489062091)
  ·
    refine ⟨218601578537017298233593137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145734385691344865489062091 218601578537017298233593137)
    ·
      refine ⟨163951183902762973675194853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218601578537017298233593137 163951183902762973675194853)
      ·
        refine ⟨30740846981768057564099035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163951183902762973675194853 30740846981768057564099035)
        ·
          refine ⟨46111270472652086346148553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30740846981768057564099035 46111270472652086346148553)
          ·
            refine ⟨34583452854489064759611415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46111270472652086346148553 34583452854489064759611415)
            ·
              refine ⟨51875179281733597139417123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34583452854489064759611415 51875179281733597139417123)
              ·
                refine ⟨77812768922600395709125685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51875179281733597139417123 77812768922600395709125685)
                ·
                  refine ⟨7294947086493787097730533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77812768922600395709125685 7294947086493787097730533)
                  ·
                    refine ⟨1367802578717585080824475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7294947086493787097730533 1367802578717585080824475)
                    ·
                      rfl

theorem cell22_3995679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_3995679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995679 prefixEnd_3995679 := by exact prefixLift 3995679
  have htrace : WordTrace (prefixWord ++ tailWord_3995679) baseStart_3995679 baseEnd_3995679 := by
    simpa [prefixWord, tailWord_3995679, baseEnd_3995679] using wordTrace_append hprefix tailTrace_3995679
  have hstable : (prefixWord ++ tailWord_3995679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995679).length < 2 ^ (prefixWord ++ tailWord_3995679).sum := by decide
  have hdescent : baseEnd_3995679 < baseStart_3995679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995681 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_3995681 : Nat := 118140960795 + 3995681 * 2 ^ 59
def prefixEnd_3995681 : Nat := 4983230072969 + 3 ^ 40 * 3995681 * 2
def baseEnd_3995681 : Nat := 1367803263358457742274469

theorem tailTrace_3995681 : CollatzResearch.WordTrace tailWord_3995681 prefixEnd_3995681 1367803263358457742274469 := by
  unfold tailWord_3995681
  simp only [CollatzResearch.WordTrace]
  refine ⟨145734458637337619830634897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97156305758225079887089931 145734458637337619830634897)
  ·
    refine ⟨109300843978003214872976173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145734458637337619830634897 109300843978003214872976173)
    ·
      refine ⟨40987816491751205577366065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109300843978003214872976173 40987816491751205577366065)
      ·
        refine ⟨30740862368813404183024549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40987816491751205577366065 30740862368813404183024549)
        ·
          refine ⟨5763911694152513284317103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30740862368813404183024549 5763911694152513284317103)
          ·
            refine ⟨8645867541228769926475655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5763911694152513284317103 8645867541228769926475655)
            ·
              refine ⟨12968801311843154889713483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645867541228769926475655 12968801311843154889713483)
              ·
                refine ⟨19453201967764732334570225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12968801311843154889713483 19453201967764732334570225)
                ·
                  refine ⟨14589901475823549250927669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19453201967764732334570225 14589901475823549250927669)
                  ·
                    refine ⟨1367803263358457742274469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14589901475823549250927669 1367803263358457742274469)
                    ·
                      rfl

theorem cell22_3995681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_3995681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995681 prefixEnd_3995681 := by exact prefixLift 3995681
  have htrace : WordTrace (prefixWord ++ tailWord_3995681) baseStart_3995681 baseEnd_3995681 := by
    simpa [prefixWord, tailWord_3995681, baseEnd_3995681] using wordTrace_append hprefix tailTrace_3995681
  have hstable : (prefixWord ++ tailWord_3995681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995681).length < 2 ^ (prefixWord ++ tailWord_3995681).sum := by decide
  have hdescent : baseEnd_3995681 < baseStart_3995681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995711 : List Nat := [1, 1, 2, 2, 3, 1, 3, 5, 4]
def baseStart_3995711 : Nat := 118140960795 + 3995711 * 2 ^ 59
def prefixEnd_3995711 : Nat := 4983230072969 + 3 ^ 40 * 3995711 * 2
def baseEnd_3995711 : Nat := 455937844323849221341459

theorem tailTrace_3995711 : CollatzResearch.WordTrace tailWord_3995711 prefixEnd_3995711 455937844323849221341459 := by
  unfold tailWord_3995711
  simp only [CollatzResearch.WordTrace]
  refine ⟨145735552827228934954226987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97157035218152623302817991 145735552827228934954226987)
  ·
    refine ⟨218603329240843402431340481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145735552827228934954226987 218603329240843402431340481)
    ·
      refine ⟨163952496930632551823505361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218603329240843402431340481 163952496930632551823505361)
      ·
        refine ⟨122964372697974413867629021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163952496930632551823505361 122964372697974413867629021)
        ·
          refine ⟨46111639761740405200360883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122964372697974413867629021 46111639761740405200360883)
          ·
            refine ⟨69167459642610607800541325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46111639761740405200360883 69167459642610607800541325)
            ·
              refine ⟨25937797365978977925202997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69167459642610607800541325 25937797365978977925202997)
              ·
                refine ⟨2431668503060529180487781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25937797365978977925202997 2431668503060529180487781)
                ·
                  refine ⟨455937844323849221341459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431668503060529180487781 455937844323849221341459)
                  ·
                    rfl

theorem cell22_3995711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 4].length) (baseStart_3995711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995711 prefixEnd_3995711 := by exact prefixLift 3995711
  have htrace : WordTrace (prefixWord ++ tailWord_3995711) baseStart_3995711 baseEnd_3995711 := by
    simpa [prefixWord, tailWord_3995711, baseEnd_3995711] using wordTrace_append hprefix tailTrace_3995711
  have hstable : (prefixWord ++ tailWord_3995711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995711).length < 2 ^ (prefixWord ++ tailWord_3995711).sum := by decide
  have hdescent : baseEnd_3995711 < baseStart_3995711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995713 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3995713 : Nat := 118140960795 + 3995713 * 2 ^ 59
def prefixEnd_3995713 : Nat := 4983230072969 + 3 ^ 40 * 3995713 * 2
def baseEnd_3995713 : Nat := 1367814217612420325474371

theorem tailTrace_3995713 : CollatzResearch.WordTrace tailWord_3995713 prefixEnd_3995713 1367814217612420325474371 := by
  unfold tailWord_3995713
  simp only [CollatzResearch.WordTrace]
  refine ⟨145735625773221689295799793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97157083848814459530533195 145735625773221689295799793)
  ·
    refine ⟨109301719329916266971849845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145735625773221689295799793 109301719329916266971849845)
    ·
      refine ⟨10247036187179650028610923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109301719329916266971849845 10247036187179650028610923)
      ·
        refine ⟨15370554280769475042916385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247036187179650028610923 15370554280769475042916385)
        ·
          refine ⟨11527915710577106282187289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15370554280769475042916385 11527915710577106282187289)
          ·
            refine ⟨8645936782932829711640467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11527915710577106282187289 8645936782932829711640467)
            ·
              refine ⟨12968905174399244567460701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645936782932829711640467 12968905174399244567460701)
              ·
                refine ⟨4863339440399716712797763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12968905174399244567460701 4863339440399716712797763)
                ·
                  refine ⟨7295009160599575069196645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863339440399716712797763 7295009160599575069196645)
                  ·
                    refine ⟨1367814217612420325474371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295009160599575069196645 1367814217612420325474371)
                    ·
                      rfl

theorem cell22_3995713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3995713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995713 prefixEnd_3995713 := by exact prefixLift 3995713
  have htrace : WordTrace (prefixWord ++ tailWord_3995713) baseStart_3995713 baseEnd_3995713 := by
    simpa [prefixWord, tailWord_3995713, baseEnd_3995713] using wordTrace_append hprefix tailTrace_3995713
  have hstable : (prefixWord ++ tailWord_3995713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995713).length < 2 ^ (prefixWord ++ tailWord_3995713).sum := by decide
  have hdescent : baseEnd_3995713 < baseStart_3995713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995756 : List Nat := [2, 2, 1, 1, 3, 3, 4, 6]
def baseStart_3995756 : Nat := 118140960795 + 3995756 * 2 ^ 59
def prefixEnd_3995756 : Nat := 4983230072969 + 3 ^ 40 * 3995756 * 2
def baseEnd_3995756 : Nat := 151980993043464727405471

theorem tailTrace_3995756 : CollatzResearch.WordTrace tailWord_3995756 prefixEnd_3995756 151980993043464727405471 := by
  unfold tailWord_3995756
  simp only [CollatzResearch.WordTrace]
  refine ⟨72868597056032953819807561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97158129408043938426410081 72868597056032953819807561)
  ·
    refine ⟨54651447792024715364855671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72868597056032953819807561 54651447792024715364855671)
    ·
      refine ⟨81977171688037073047283507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54651447792024715364855671 81977171688037073047283507)
      ·
        refine ⟨122965757532055609570925261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81977171688037073047283507 122965757532055609570925261)
        ·
          refine ⟨46112159074520853589096973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122965757532055609570925261 46112159074520853589096973)
          ·
            refine ⟨17292059652945320095911365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46112159074520853589096973 17292059652945320095911365)
            ·
              refine ⟨3242261184927247517983381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17292059652945320095911365 3242261184927247517983381)
              ·
                refine ⟨151980993043464727405471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3242261184927247517983381 151980993043464727405471)
                ·
                  rfl

theorem cell22_3995756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 6].length) (baseStart_3995756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995756 prefixEnd_3995756 := by exact prefixLift 3995756
  have htrace : WordTrace (prefixWord ++ tailWord_3995756) baseStart_3995756 baseEnd_3995756 := by
    simpa [prefixWord, tailWord_3995756, baseEnd_3995756] using wordTrace_append hprefix tailTrace_3995756
  have hstable : (prefixWord ++ tailWord_3995756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995756).length < 2 ^ (prefixWord ++ tailWord_3995756).sum := by decide
  have hdescent : baseEnd_3995756 < baseStart_3995756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995798 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3995798 : Nat := 118140960795 + 3995798 * 2 ^ 59
def prefixEnd_3995798 : Nat := 4983230072969 + 3 ^ 40 * 3995798 * 2
def baseEnd_3995798 : Nat := 1367843314849508437099111

theorem tailTrace_3995798 : CollatzResearch.WordTrace tailWord_3995798 prefixEnd_3995798 1367843314849508437099111 := by
  unfold tailWord_3995798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108670373619609300790253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97159150651942499208429365 9108670373619609300790253)
  ·
    refine ⟨3415751390107353487796345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9108670373619609300790253 3415751390107353487796345)
    ·
      refine ⟨2561813542580515115847259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3415751390107353487796345 2561813542580515115847259)
      ·
        refine ⟨3842720313870772673770889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561813542580515115847259 3842720313870772673770889)
        ·
          refine ⟨2882040235403079505328167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3842720313870772673770889 2882040235403079505328167)
          ·
            refine ⟨4323060353104619257992251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882040235403079505328167 4323060353104619257992251)
            ·
              refine ⟨6484590529656928886988377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323060353104619257992251 6484590529656928886988377)
              ·
                refine ⟨4863442897242696665241283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6484590529656928886988377 4863442897242696665241283)
                ·
                  refine ⟨7295164345864044997861925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863442897242696665241283 7295164345864044997861925)
                  ·
                    refine ⟨1367843314849508437099111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295164345864044997861925 1367843314849508437099111)
                    ·
                      rfl

theorem cell22_3995798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3995798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995798 prefixEnd_3995798 := by exact prefixLift 3995798
  have htrace : WordTrace (prefixWord ++ tailWord_3995798) baseStart_3995798 baseEnd_3995798 := by
    simpa [prefixWord, tailWord_3995798, baseEnd_3995798] using wordTrace_append hprefix tailTrace_3995798
  have hstable : (prefixWord ++ tailWord_3995798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995798).length < 2 ^ (prefixWord ++ tailWord_3995798).sum := by decide
  have hdescent : baseEnd_3995798 < baseStart_3995798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995880 : List Nat := [2, 1, 4, 1, 2, 3, 2, 3, 4]
def baseStart_3995880 : Nat := 118140960795 + 3995880 * 2 ^ 59
def prefixEnd_3995880 : Nat := 4983230072969 + 3 ^ 40 * 3995880 * 2
def baseEnd_3995880 : Nat := 455957128375095852182953

theorem tailTrace_3995880 : CollatzResearch.WordTrace tailWord_3995880 prefixEnd_3995880 455957128375095852182953 := by
  unfold tailWord_3995880
  simp only [CollatzResearch.WordTrace]
  refine ⟨72870858381808338408564547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97161144509077784544752729 72870858381808338408564547)
  ·
    refine ⟨109306287572712507612846821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72870858381808338408564547 109306287572712507612846821)
    ·
      refine ⟨20494928919883595177408779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109306287572712507612846821 20494928919883595177408779)
      ·
        refine ⟨30742393379825392766113169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20494928919883595177408779 30742393379825392766113169)
        ·
          refine ⟨23056795034869044574584877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30742393379825392766113169 23056795034869044574584877)
          ·
            refine ⟨8646298138075891715469329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23056795034869044574584877 8646298138075891715469329)
            ·
              refine ⟨6484723603556918786601997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8646298138075891715469329 6484723603556918786601997)
              ·
                refine ⟨2431771351333844544975749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6484723603556918786601997 2431771351333844544975749)
                ·
                  refine ⟨455957128375095852182953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431771351333844544975749 455957128375095852182953)
                  ·
                    rfl

theorem cell22_3995880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_3995880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995880 prefixEnd_3995880 := by exact prefixLift 3995880
  have htrace : WordTrace (prefixWord ++ tailWord_3995880) baseStart_3995880 baseEnd_3995880 := by
    simpa [prefixWord, tailWord_3995880, baseEnd_3995880] using wordTrace_append hprefix tailTrace_3995880
  have hstable : (prefixWord ++ tailWord_3995880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995880).length < 2 ^ (prefixWord ++ tailWord_3995880).sum := by decide
  have hdescent : baseEnd_3995880 < baseStart_3995880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995912 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 2, 3]
def baseStart_3995912 : Nat := 118140960795 + 3995912 * 2 ^ 59
def prefixEnd_3995912 : Nat := 4983230072969 + 3 ^ 40 * 3995912 * 2
def baseEnd_3995912 : Nat := 1367882339379250139748761

theorem tailTrace_3995912 : CollatzResearch.WordTrace tailWord_3995912 prefixEnd_3995912 1367882339379250139748761 := by
  unfold tailWord_3995912
  simp only [CollatzResearch.WordTrace]
  refine ⟨72871441949750373141146995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97161922599667164188195993 72871441949750373141146995)
  ·
    refine ⟨109307162924625559711720493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72871441949750373141146995 109307162924625559711720493)
    ·
      refine ⟨40990186096734584891895185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109307162924625559711720493 40990186096734584891895185)
      ·
        refine ⟨30742639572550938668921389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40990186096734584891895185 30742639572550938668921389)
        ·
          refine ⟨11528489839706602000845521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30742639572550938668921389 11528489839706602000845521)
          ·
            refine ⟨8646367379779951500634141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11528489839706602000845521 8646367379779951500634141)
            ·
              refine ⟨3242387767417481812737803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8646367379779951500634141 3242387767417481812737803)
              ·
                refine ⟨4863581651126222719106705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242387767417481812737803 4863581651126222719106705)
                ·
                  refine ⟨3647686238344667039330029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4863581651126222719106705 3647686238344667039330029)
                  ·
                    refine ⟨1367882339379250139748761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3647686238344667039330029 1367882339379250139748761)
                    ·
                      rfl

theorem cell22_3995912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_3995912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995912 prefixEnd_3995912 := by exact prefixLift 3995912
  have htrace : WordTrace (prefixWord ++ tailWord_3995912) baseStart_3995912 baseEnd_3995912 := by
    simpa [prefixWord, tailWord_3995912, baseEnd_3995912] using wordTrace_append hprefix tailTrace_3995912
  have hstable : (prefixWord ++ tailWord_3995912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995912).length < 2 ^ (prefixWord ++ tailWord_3995912).sum := by decide
  have hdescent : baseEnd_3995912 < baseStart_3995912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995951 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 4, 5]
def baseStart_3995951 : Nat := 118140960795 + 3995951 * 2 ^ 59
def prefixEnd_3995951 : Nat := 4983230072969 + 3 ^ 40 * 3995951 * 2
def baseEnd_3995951 : Nat := 1367895689876267038023641

theorem tailTrace_3995951 : CollatzResearch.WordTrace tailWord_3995951 prefixEnd_3995951 1367895689876267038023641 := by
  unfold tailWord_3995951
  simp only [CollatzResearch.WordTrace]
  refine ⟨145744306346359455942963707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97162870897572970628642471 145744306346359455942963707)
  ·
    refine ⟨218616459519539183914445561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145744306346359455942963707 218616459519539183914445561)
    ·
      refine ⟨163962344639654387935834171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218616459519539183914445561 163962344639654387935834171)
      ·
        refine ⟨245943516959481581903751257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163962344639654387935834171 245943516959481581903751257)
        ·
          refine ⟨184457637719611186427813443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245943516959481581903751257 184457637719611186427813443)
          ·
            refine ⟨276686456579416779641720165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184457637719611186427813443 276686456579416779641720165)
            ·
              refine ⟨51878710608640646182822531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276686456579416779641720165 51878710608640646182822531)
              ·
                refine ⟨77818065912960969274233797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51878710608640646182822531 77818065912960969274233797)
                ·
                  refine ⟨14590887358680181738918837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77818065912960969274233797 14590887358680181738918837)
                  ·
                    refine ⟨1367895689876267038023641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14590887358680181738918837 1367895689876267038023641)
                    ·
                      rfl

theorem cell22_3995951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_3995951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995951 prefixEnd_3995951 := by exact prefixLift 3995951
  have htrace : WordTrace (prefixWord ++ tailWord_3995951) baseStart_3995951 baseEnd_3995951 := by
    simpa [prefixWord, tailWord_3995951, baseEnd_3995951] using wordTrace_append hprefix tailTrace_3995951
  have hstable : (prefixWord ++ tailWord_3995951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995951).length < 2 ^ (prefixWord ++ tailWord_3995951).sum := by decide
  have hdescent : baseEnd_3995951 < baseStart_3995951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995983 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 1, 4]
def baseStart_3995983 : Nat := 118140960795 + 3995983 * 2 ^ 59
def prefixEnd_3995983 : Nat := 4983230072969 + 3 ^ 40 * 3995983 * 2
def baseEnd_3995983 : Nat := 1367906644130229621223543

theorem tailTrace_3995983 : CollatzResearch.WordTrace tailWord_3995983 prefixEnd_3995983 1367906644130229621223543 := by
  unfold tailWord_3995983
  simp only [CollatzResearch.WordTrace]
  refine ⟨145745473482243525408128603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97163648988162350272085735 145745473482243525408128603)
  ·
    refine ⟨218618210223365288112192905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145745473482243525408128603 218618210223365288112192905)
    ·
      refine ⟨163963657667523966084144679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218618210223365288112192905 163963657667523966084144679)
      ·
        refine ⟨245945486501285949126217019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163963657667523966084144679 245945486501285949126217019)
        ·
          refine ⟨368918229751928923689325529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245945486501285949126217019 368918229751928923689325529)
          ·
            refine ⟨276688672313946692766994147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368918229751928923689325529 276688672313946692766994147)
            ·
              refine ⟨415033008470920039150491221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276688672313946692766994147 415033008470920039150491221)
              ·
                refine ⟨4863668068018594208794819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 415033008470920039150491221 4863668068018594208794819)
                ·
                  refine ⟨7295502102027891313192229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863668068018594208794819 7295502102027891313192229)
                  ·
                    refine ⟨1367906644130229621223543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295502102027891313192229 1367906644130229621223543)
                    ·
                      rfl

theorem cell22_3995983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_3995983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3995983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3995983 prefixEnd_3995983 := by exact prefixLift 3995983
  have htrace : WordTrace (prefixWord ++ tailWord_3995983) baseStart_3995983 baseEnd_3995983 := by
    simpa [prefixWord, tailWord_3995983, baseEnd_3995983] using wordTrace_append hprefix tailTrace_3995983
  have hstable : (prefixWord ++ tailWord_3995983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995983).length < 2 ^ (prefixWord ++ tailWord_3995983).sum := by decide
  have hdescent : baseEnd_3995983 < baseStart_3995983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996013 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3996013 : Nat := 118140960795 + 3996013 * 2 ^ 59
def prefixEnd_3996013 : Nat := 4983230072969 + 3 ^ 40 * 3996013 * 2
def baseEnd_3996013 : Nat := 1367916913743319542973451

theorem tailTrace_3996013 : CollatzResearch.WordTrace tailWord_3996013 prefixEnd_3996013 1367916913743319542973451 := by
  unfold tailWord_3996013
  simp only [CollatzResearch.WordTrace]
  refine ⟨145746567672134840531720693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97164378448089893687813795 145746567672134840531720693)
  ·
    refine ⟨13663740719262641299848815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145746567672134840531720693 13663740719262641299848815)
    ·
      refine ⟨20495611078893961949773223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13663740719262641299848815 20495611078893961949773223)
      ·
        refine ⟨30743416618340942924659835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20495611078893961949773223 30743416618340942924659835)
        ·
          refine ⟨46115124927511414386989753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30743416618340942924659835 46115124927511414386989753)
          ·
            refine ⟨34586343695633560790242315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46115124927511414386989753 34586343695633560790242315)
            ·
              refine ⟨51879515543450341185363473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34586343695633560790242315 51879515543450341185363473)
              ·
                refine ⟨38909636657587755889022605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51879515543450341185363473 38909636657587755889022605)
                ·
                  refine ⟨14591113746595408458383477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38909636657587755889022605 14591113746595408458383477)
                  ·
                    refine ⟨1367916913743319542973451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14591113746595408458383477 1367916913743319542973451)
                    ·
                      rfl

theorem cell22_3996013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3996013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996013 prefixEnd_3996013 := by exact prefixLift 3996013
  have htrace : WordTrace (prefixWord ++ tailWord_3996013) baseStart_3996013 baseEnd_3996013 := by
    simpa [prefixWord, tailWord_3996013, baseEnd_3996013] using wordTrace_append hprefix tailTrace_3996013
  have hstable : (prefixWord ++ tailWord_3996013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996013).length < 2 ^ (prefixWord ++ tailWord_3996013).sum := by decide
  have hdescent : baseEnd_3996013 < baseStart_3996013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996092 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_3996092 : Nat := 118140960795 + 3996092 * 2 ^ 59
def prefixEnd_3996092 : Nat := 4983230072969 + 3 ^ 40 * 3996092 * 2
def baseEnd_3996092 : Nat := 1367943957057789670248209

theorem tailTrace_3996092 : CollatzResearch.WordTrace tailWord_3996092 prefixEnd_3996092 1367943957057789670248209 := by
  unfold tailWord_3996092
  simp only [CollatzResearch.WordTrace]
  refine ⟨72874724519424318511923265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97166299359232424682564353 72874724519424318511923265)
  ·
    refine ⟨54656043389568238883942449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72874724519424318511923265 54656043389568238883942449)
    ·
      refine ⟨40992032542176179162956837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54656043389568238883942449 40992032542176179162956837)
      ·
        refine ⟨7686006101658033593054407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40992032542176179162956837 7686006101658033593054407)
        ·
          refine ⟨11529009152487050389581611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7686006101658033593054407 11529009152487050389581611)
          ·
            refine ⟨17293513728730575584372417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529009152487050389581611 17293513728730575584372417)
            ·
              refine ⟨12970135296547931688279313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17293513728730575584372417 12970135296547931688279313)
              ·
                refine ⟨9727601472410948766209485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12970135296547931688279313 9727601472410948766209485)
                ·
                  refine ⟨3647850552154105787328557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9727601472410948766209485 3647850552154105787328557)
                  ·
                    refine ⟨1367943957057789670248209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3647850552154105787328557 1367943957057789670248209)
                    ·
                      rfl

theorem cell22_3996092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_3996092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996092 prefixEnd_3996092 := by exact prefixLift 3996092
  have htrace : WordTrace (prefixWord ++ tailWord_3996092) baseStart_3996092 baseEnd_3996092 := by
    simpa [prefixWord, tailWord_3996092, baseEnd_3996092] using wordTrace_append hprefix tailTrace_3996092
  have hstable : (prefixWord ++ tailWord_3996092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996092).length < 2 ^ (prefixWord ++ tailWord_3996092).sum := by decide
  have hdescent : baseEnd_3996092 < baseStart_3996092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996135 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3996135 : Nat := 118140960795 + 3996135 * 2 ^ 59
def prefixEnd_3996135 : Nat := 4983230072969 + 3 ^ 40 * 3996135 * 2
def baseEnd_3996135 : Nat := 1367958676836551891423077

theorem tailTrace_3996135 : CollatzResearch.WordTrace tailWord_3996135 prefixEnd_3996135 1367958676836551891423077 := by
  unfold tailWord_3996135
  simp only [CollatzResearch.WordTrace]
  refine ⟨145751017377692855367661859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97167344918461903578441239 145751017377692855367661859)
  ·
    refine ⟨218626526066539283051492789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145751017377692855367661859 218626526066539283051492789)
    ·
      refine ⟨20496236818738057786077449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218626526066539283051492789 20496236818738057786077449)
      ·
        refine ⟨15372177614053543339558087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20496236818738057786077449 15372177614053543339558087)
        ·
          refine ⟨23058266421080315009337131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15372177614053543339558087 23058266421080315009337131)
          ·
            refine ⟨34587399631620472514005697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23058266421080315009337131 34587399631620472514005697)
            ·
              refine ⟨25940549723715354385504273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34587399631620472514005697 25940549723715354385504273)
              ·
                refine ⟨19455412292786515789128205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25940549723715354385504273 19455412292786515789128205)
                ·
                  refine ⟨7295779609794943420923077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19455412292786515789128205 7295779609794943420923077)
                  ·
                    refine ⟨1367958676836551891423077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295779609794943420923077 1367958676836551891423077)
                    ·
                      rfl

theorem cell22_3996135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3996135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996135 prefixEnd_3996135 := by exact prefixLift 3996135
  have htrace : WordTrace (prefixWord ++ tailWord_3996135) baseStart_3996135 baseEnd_3996135 := by
    simpa [prefixWord, tailWord_3996135, baseEnd_3996135] using wordTrace_append hprefix tailTrace_3996135
  have hstable : (prefixWord ++ tailWord_3996135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996135).length < 2 ^ (prefixWord ++ tailWord_3996135).sum := by decide
  have hdescent : baseEnd_3996135 < baseStart_3996135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996150 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3996150 : Nat := 118140960795 + 3996150 * 2 ^ 59
def prefixEnd_3996150 : Nat := 4983230072969 + 3 ^ 40 * 3996150 * 2
def baseEnd_3996150 : Nat := 455987937214365617432677

theorem tailTrace_3996150 : CollatzResearch.WordTrace tailWord_3996150 prefixEnd_3996150 455987937214365617432677 := by
  unfold tailWord_3996150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9109472779539907058091119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97167709648425675286305269 9109472779539907058091119)
  ·
    refine ⟨13664209169309860587136679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9109472779539907058091119 13664209169309860587136679)
    ·
      refine ⟨20496313753964790880705019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13664209169309860587136679 20496313753964790880705019)
      ·
        refine ⟨30744470630947186321057529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20496313753964790880705019 30744470630947186321057529)
        ·
          refine ⟨23058352973210389740793147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30744470630947186321057529 23058352973210389740793147)
          ·
            refine ⟨34587529459815584611189721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23058352973210389740793147 34587529459815584611189721)
            ·
              refine ⟨25940647094861688458392291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34587529459815584611189721 25940647094861688458392291)
              ·
                refine ⟨38910970642292532687588437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25940647094861688458392291 38910970642292532687588437)
                ·
                  refine ⟨455987937214365617432677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38910970642292532687588437 455987937214365617432677)
                  ·
                    rfl

theorem cell22_3996150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3996150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996150 prefixEnd_3996150 := by exact prefixLift 3996150
  have htrace : WordTrace (prefixWord ++ tailWord_3996150) baseStart_3996150 baseEnd_3996150 := by
    simpa [prefixWord, tailWord_3996150, baseEnd_3996150] using wordTrace_append hprefix tailTrace_3996150
  have hstable : (prefixWord ++ tailWord_3996150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996150).length < 2 ^ (prefixWord ++ tailWord_3996150).sum := by decide
  have hdescent : baseEnd_3996150 < baseStart_3996150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996165 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_3996165 : Nat := 118140960795 + 3996165 * 2 ^ 59
def prefixEnd_3996165 : Nat := 4983230072969 + 3 ^ 40 * 3996165 * 2
def baseEnd_3996165 : Nat := 1367968946449641813172985

theorem tailTrace_3996165 : CollatzResearch.WordTrace tailWord_3996165 prefixEnd_3996165 1367968946449641813172985 := by
  unfold tailWord_3996165
  simp only [CollatzResearch.WordTrace]
  refine ⟨145752111567584170491253949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97168074378389446994169299 145752111567584170491253949)
  ·
    refine ⟨54657041837844063934220231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145752111567584170491253949 54657041837844063934220231)
    ·
      refine ⟨81985562756766095901330347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54657041837844063934220231 81985562756766095901330347)
      ·
        refine ⟨122978344135149143851995521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81985562756766095901330347 122978344135149143851995521)
        ·
          refine ⟨92233758101361857888996641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122978344135149143851995521 92233758101361857888996641)
          ·
            refine ⟨69175318576021393416747481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92233758101361857888996641 69175318576021393416747481)
            ·
              refine ⟨51881488932016045062560611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69175318576021393416747481 51881488932016045062560611)
              ·
                refine ⟨77822233398024067593840917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51881488932016045062560611 77822233398024067593840917)
                ·
                  refine ⟨3647917190532378168461293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77822233398024067593840917 3647917190532378168461293)
                  ·
                    refine ⟨1367968946449641813172985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3647917190532378168461293 1367968946449641813172985)
                    ·
                      rfl

theorem cell22_3996165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_3996165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996165 prefixEnd_3996165 := by exact prefixLift 3996165
  have htrace : WordTrace (prefixWord ++ tailWord_3996165) baseStart_3996165 baseEnd_3996165 := by
    simpa [prefixWord, tailWord_3996165, baseEnd_3996165] using wordTrace_append hprefix tailTrace_3996165
  have hstable : (prefixWord ++ tailWord_3996165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996165).length < 2 ^ (prefixWord ++ tailWord_3996165).sum := by decide
  have hdescent : baseEnd_3996165 < baseStart_3996165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996178 : List Nat := [3, 2, 17]
def baseStart_3996178 : Nat := 118140960795 + 3996178 * 2 ^ 59
def prefixEnd_3996178 : Nat := 4983230072969 + 3 ^ 40 * 3996178 * 2
def baseEnd_3996178 : Nat := 625502238964478332235

theorem tailTrace_3996178 : CollatzResearch.WordTrace tailWord_3996178 prefixEnd_3996178 625502238964478332235 := by
  unfold tailWord_3996178
  simp only [CollatzResearch.WordTrace]
  refine ⟨36438146429134268427869297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97168390477691382474318125 36438146429134268427869297)
  ·
    refine ⟨27328609821850701320901973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36438146429134268427869297 27328609821850701320901973)
    ·
      refine ⟨625502238964478332235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 27328609821850701320901973 625502238964478332235)
      ·
        rfl

theorem cell22_3996178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 17].length) (baseStart_3996178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996178 prefixEnd_3996178 := by exact prefixLift 3996178
  have htrace : WordTrace (prefixWord ++ tailWord_3996178) baseStart_3996178 baseEnd_3996178 := by
    simpa [prefixWord, tailWord_3996178, baseEnd_3996178] using wordTrace_append hprefix tailTrace_3996178
  have hstable : (prefixWord ++ tailWord_3996178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996178).length < 2 ^ (prefixWord ++ tailWord_3996178).sum := by decide
  have hdescent : baseEnd_3996178 < baseStart_3996178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996184 : List Nat := [2, 1, 2, 3, 3, 1, 4, 2, 4]
def baseStart_3996184 : Nat := 118140960795 + 3996184 * 2 ^ 59
def prefixEnd_3996184 : Nat := 4983230072969 + 3 ^ 40 * 3996184 * 2
def baseEnd_3996184 : Nat := 455991816845977365649309

theorem tailTrace_3996184 : CollatzResearch.WordTrace tailWord_3996184 prefixEnd_3996184 455991816845977365649309 := by
  unfold tailWord_3996184
  simp only [CollatzResearch.WordTrace]
  refine ⟨72876402277257668368097803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97168536369676891157463737 72876402277257668368097803)
  ·
    refine ⟨109314603415886502552146705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72876402277257668368097803 109314603415886502552146705)
    ·
      refine ⟨81985952561914876914110029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109314603415886502552146705 81985952561914876914110029)
      ·
        refine ⟨30744732210718078842791261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81985952561914876914110029 30744732210718078842791261)
        ·
          refine ⟨11529274579019279566046723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30744732210718078842791261 11529274579019279566046723)
          ·
            refine ⟨17293911868528919349070085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529274579019279566046723 17293911868528919349070085)
            ·
              refine ⟨3242608475349172377950641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17293911868528919349070085 3242608475349172377950641)
              ·
                refine ⟨2431956356511879283462981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242608475349172377950641 2431956356511879283462981)
                ·
                  refine ⟨455991816845977365649309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431956356511879283462981 455991816845977365649309)
                  ·
                    rfl

theorem cell22_3996184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_3996184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996184 prefixEnd_3996184 := by exact prefixLift 3996184
  have htrace : WordTrace (prefixWord ++ tailWord_3996184) baseStart_3996184 baseEnd_3996184 := by
    simpa [prefixWord, tailWord_3996184, baseEnd_3996184] using wordTrace_append hprefix tailTrace_3996184
  have hstable : (prefixWord ++ tailWord_3996184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996184).length < 2 ^ (prefixWord ++ tailWord_3996184).sum := by decide
  have hdescent : baseEnd_3996184 < baseStart_3996184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996195 : List Nat := [1, 1, 1, 4, 4, 1, 3, 7]
def baseStart_3996195 : Nat := 118140960795 + 3996195 * 2 ^ 59
def prefixEnd_3996195 : Nat := 4983230072969 + 3 ^ 40 * 3996195 * 2
def baseEnd_3996195 : Nat := 151997690673636859435877

theorem tailTrace_3996195 : CollatzResearch.WordTrace tailWord_3996195 prefixEnd_3996195 151997690673636859435877 := by
  unfold tailWord_3996195
  simp only [CollatzResearch.WordTrace]
  refine ⟨145753205757475485614846039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97168803838316990409897359 145753205757475485614846039)
  ·
    refine ⟨218629808636213228422269059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145753205757475485614846039 218629808636213228422269059)
    ·
      refine ⟨327944712954319842633403589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218629808636213228422269059 327944712954319842633403589)
      ·
        refine ⟨61489633678934970493763173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327944712954319842633403589 61489633678934970493763173)
        ·
          refine ⟨11529306314800306967580595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61489633678934970493763173 11529306314800306967580595)
          ·
            refine ⟨17293959472200460451370893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529306314800306967580595 17293959472200460451370893)
            ·
              refine ⟨6485234802075172669264085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17293959472200460451370893 6485234802075172669264085)
              ·
                refine ⟨151997690673636859435877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6485234802075172669264085 151997690673636859435877)
                ·
                  rfl

theorem cell22_3996195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 7].length) (baseStart_3996195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996195 prefixEnd_3996195 := by exact prefixLift 3996195
  have htrace : WordTrace (prefixWord ++ tailWord_3996195) baseStart_3996195 baseEnd_3996195 := by
    simpa [prefixWord, tailWord_3996195, baseEnd_3996195] using wordTrace_append hprefix tailTrace_3996195
  have hstable : (prefixWord ++ tailWord_3996195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996195).length < 2 ^ (prefixWord ++ tailWord_3996195).sum := by decide
  have hdescent : baseEnd_3996195 < baseStart_3996195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996214 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3996214 : Nat := 118140960795 + 3996214 * 2 ^ 59
def prefixEnd_3996214 : Nat := 4983230072969 + 3 ^ 40 * 3996214 * 2
def baseEnd_3996214 : Nat := 1367985720151022018697835

theorem tailTrace_3996214 : CollatzResearch.WordTrace tailWord_3996214 prefixEnd_3996214 1367985720151022018697835 := by
  unfold tailWord_3996214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9109618671525415741236731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97169265829604434573191797 9109618671525415741236731)
  ·
    refine ⟨13664428007288123611855097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9109618671525415741236731 13664428007288123611855097)
    ·
      refine ⟨10248321005466092708891323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13664428007288123611855097 10248321005466092708891323)
      ·
        refine ⟨15372481508199139063336985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10248321005466092708891323 15372481508199139063336985)
        ·
          refine ⟨11529361131149354297502739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15372481508199139063336985 11529361131149354297502739)
          ·
            refine ⟨17294041696724031446254109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529361131149354297502739 17294041696724031446254109)
            ·
              refine ⟨6485265636271511792345291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17294041696724031446254109 6485265636271511792345291)
              ·
                refine ⟨9727898454407267688517937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485265636271511792345291 9727898454407267688517937)
                ·
                  refine ⟨7295923840805450766388453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9727898454407267688517937 7295923840805450766388453)
                  ·
                    refine ⟨1367985720151022018697835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295923840805450766388453 1367985720151022018697835)
                    ·
                      rfl

theorem cell22_3996214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3996214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996214 prefixEnd_3996214 := by exact prefixLift 3996214
  have htrace : WordTrace (prefixWord ++ tailWord_3996214) baseStart_3996214 baseEnd_3996214 := by
    simpa [prefixWord, tailWord_3996214, baseEnd_3996214] using wordTrace_append hprefix tailTrace_3996214
  have hstable : (prefixWord ++ tailWord_3996214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996214).length < 2 ^ (prefixWord ++ tailWord_3996214).sum := by decide
  have hdescent : baseEnd_3996214 < baseStart_3996214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996240 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 5]
def baseStart_3996240 : Nat := 118140960795 + 3996240 * 2 ^ 59
def prefixEnd_3996240 : Nat := 4983230072969 + 3 ^ 40 * 3996240 * 2
def baseEnd_3996240 : Nat := 455998206827455539182585

theorem tailTrace_3996240 : CollatzResearch.WordTrace tailWord_3996240 prefixEnd_3996240 455998206827455539182585 := by
  unfold tailWord_3996240
  simp only [CollatzResearch.WordTrace]
  refine ⟨72877423521156229150117087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97169898028208305533489449 72877423521156229150117087)
  ·
    refine ⟨109316135281734343725175631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72877423521156229150117087 109316135281734343725175631)
    ·
      refine ⟨163974202922601515587763447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109316135281734343725175631 163974202922601515587763447)
      ·
        refine ⟨245961304383902273381645171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163974202922601515587763447 245961304383902273381645171)
        ·
          refine ⟨368941956575853410072467757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245961304383902273381645171 368941956575853410072467757)
          ·
            refine ⟨138353233715945028777175409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368941956575853410072467757 138353233715945028777175409)
            ·
              refine ⟨103764925286958771582881557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138353233715945028777175409 103764925286958771582881557)
              ·
                refine ⟨4863980872826192417947573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103764925286958771582881557 4863980872826192417947573)
                ·
                  refine ⟨455998206827455539182585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4863980872826192417947573 455998206827455539182585)
                  ·
                    rfl

theorem cell22_3996240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_3996240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996240 prefixEnd_3996240 := by exact prefixLift 3996240
  have htrace : WordTrace (prefixWord ++ tailWord_3996240) baseStart_3996240 baseEnd_3996240 := by
    simpa [prefixWord, tailWord_3996240, baseEnd_3996240] using wordTrace_append hprefix tailTrace_3996240
  have hstable : (prefixWord ++ tailWord_3996240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996240).length < 2 ^ (prefixWord ++ tailWord_3996240).sum := by decide
  have hdescent : baseEnd_3996240 < baseStart_3996240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996244 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_3996244 : Nat := 118140960795 + 3996244 * 2 ^ 59
def prefixEnd_3996244 : Nat := 4983230072969 + 3 ^ 40 * 3996244 * 2
def baseEnd_3996244 : Nat := 1367995989764111940447743

theorem tailTrace_3996244 : CollatzResearch.WordTrace tailWord_3996244 prefixEnd_3996244 1367995989764111940447743 := by
  unfold tailWord_3996244
  simp only [CollatzResearch.WordTrace]
  refine ⟨72877496467148983491689893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97169995289531977988919857 72877496467148983491689893)
  ·
    refine ⟨13664530587590434404691855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72877496467148983491689893 13664530587590434404691855)
    ·
      refine ⟨20496795881385651607037783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13664530587590434404691855 20496795881385651607037783)
      ·
        refine ⟨30745193822078477410556675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20496795881385651607037783 30745193822078477410556675)
        ·
          refine ⟨46117790733117716115835013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30745193822078477410556675 46117790733117716115835013)
          ·
            refine ⟨8647085762459571771719065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46117790733117716115835013 8647085762459571771719065)
            ·
              refine ⟨6485314321844678828789299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8647085762459571771719065 6485314321844678828789299)
              ·
                refine ⟨9727971482767018243183949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485314321844678828789299 9727971482767018243183949)
                ·
                  refine ⟨3647989306037631841193981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9727971482767018243183949 3647989306037631841193981)
                  ·
                    refine ⟨1367995989764111940447743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3647989306037631841193981 1367995989764111940447743)
                    ·
                      rfl

theorem cell22_3996244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_3996244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996244 prefixEnd_3996244 := by exact prefixLift 3996244
  have htrace : WordTrace (prefixWord ++ tailWord_3996244) baseStart_3996244 baseEnd_3996244 := by
    simpa [prefixWord, tailWord_3996244, baseEnd_3996244] using wordTrace_append hprefix tailTrace_3996244
  have hstable : (prefixWord ++ tailWord_3996244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996244).length < 2 ^ (prefixWord ++ tailWord_3996244).sum := by decide
  have hdescent : baseEnd_3996244 < baseStart_3996244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996300 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_3996300 : Nat := 118140960795 + 3996300 * 2 ^ 59
def prefixEnd_3996300 : Nat := 4983230072969 + 3 ^ 40 * 3996300 * 2
def baseEnd_3996300 : Nat := 1368015159708546461047571

theorem tailTrace_3996300 : CollatzResearch.WordTrace tailWord_3996300 prefixEnd_3996300 1368015159708546461047571 := by
  unfold tailWord_3996300
  simp only [CollatzResearch.WordTrace]
  refine ⟨72878517711047544273709177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97171356948063392364945569 72878517711047544273709177)
  ·
    refine ⟨54658888283285658205281883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72878517711047544273709177 54658888283285658205281883)
    ·
      refine ⟨81988332424928487307922825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54658888283285658205281883 81988332424928487307922825)
      ·
        refine ⟨61491249318696365480942119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81988332424928487307922825 61491249318696365480942119)
        ·
          refine ⟨92236873978044548221413179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61491249318696365480942119 92236873978044548221413179)
          ·
            refine ⟨138355310967066822332119769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92236873978044548221413179 138355310967066822332119769)
            ·
              refine ⟨103766483225300116749089827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138355310967066822332119769 103766483225300116749089827)
              ·
                refine ⟨155649724837950175123634741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103766483225300116749089827 155649724837950175123634741)
                ·
                  refine ⟨14592161703557828917840757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155649724837950175123634741 14592161703557828917840757)
                  ·
                    refine ⟨1368015159708546461047571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14592161703557828917840757 1368015159708546461047571)
                    ·
                      rfl

theorem cell22_3996300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_3996300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996300 prefixEnd_3996300 := by exact prefixLift 3996300
  have htrace : WordTrace (prefixWord ++ tailWord_3996300) baseStart_3996300 baseEnd_3996300 := by
    simpa [prefixWord, tailWord_3996300, baseEnd_3996300] using wordTrace_append hprefix tailTrace_3996300
  have hstable : (prefixWord ++ tailWord_3996300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996300).length < 2 ^ (prefixWord ++ tailWord_3996300).sum := by decide
  have hdescent : baseEnd_3996300 < baseStart_3996300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996321 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3996321 : Nat := 118140960795 + 3996321 * 2 ^ 59
def prefixEnd_3996321 : Nat := 4983230072969 + 3 ^ 40 * 3996321 * 2
def baseEnd_3996321 : Nat := 1368022348437709406272507

theorem tailTrace_3996321 : CollatzResearch.WordTrace tailWord_3996321 prefixEnd_3996321 1368022348437709406272507 := by
  unfold tailWord_3996321
  simp only [CollatzResearch.WordTrace]
  refine ⟨145757801355019009133932817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97171867570012672755955211 145757801355019009133932817)
  ·
    refine ⟨109318351016264256850449613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145757801355019009133932817 109318351016264256850449613)
    ·
      refine ⟨40994381631099096318918605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109318351016264256850449613 40994381631099096318918605)
      ·
        refine ⟨15372893111662161119594477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40994381631099096318918605 15372893111662161119594477)
        ·
          refine ⟨5764834916873310419847929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15372893111662161119594477 5764834916873310419847929)
          ·
            refine ⟨4323626187654982814885947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5764834916873310419847929 4323626187654982814885947)
            ·
              refine ⟨6485439281482474222328921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323626187654982814885947 6485439281482474222328921)
              ·
                refine ⟨4864079461111855666746691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485439281482474222328921 4864079461111855666746691)
                ·
                  refine ⟨7296119191667783500120037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864079461111855666746691 7296119191667783500120037)
                  ·
                    refine ⟨1368022348437709406272507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296119191667783500120037 1368022348437709406272507)
                    ·
                      rfl

theorem cell22_3996321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3996321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996321 prefixEnd_3996321 := by exact prefixLift 3996321
  have htrace : WordTrace (prefixWord ++ tailWord_3996321) baseStart_3996321 baseEnd_3996321 := by
    simpa [prefixWord, tailWord_3996321, baseEnd_3996321] using wordTrace_append hprefix tailTrace_3996321
  have hstable : (prefixWord ++ tailWord_3996321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996321).length < 2 ^ (prefixWord ++ tailWord_3996321).sum := by decide
  have hdescent : baseEnd_3996321 < baseStart_3996321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996334 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3996334 : Nat := 118140960795 + 3996334 * 2 ^ 59
def prefixEnd_3996334 : Nat := 4983230072969 + 3 ^ 40 * 3996334 * 2
def baseEnd_3996334 : Nat := 1368026798603381705697467

theorem tailTrace_3996334 : CollatzResearch.WordTrace tailWord_3996334 prefixEnd_3996334 1368026798603381705697467 := by
  unfold tailWord_3996334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18219784437996489044269507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97172183669314608236104037 18219784437996489044269507)
  ·
    refine ⟨27329676656994733566404261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18219784437996489044269507 27329676656994733566404261)
    ·
      refine ⟨5124314373186512543700799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27329676656994733566404261 5124314373186512543700799)
      ·
        refine ⟨7686471559779768815551199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124314373186512543700799 7686471559779768815551199)
        ·
          refine ⟨11529707339669653223326799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7686471559779768815551199 11529707339669653223326799)
          ·
            refine ⟨17294561009504479834990199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529707339669653223326799 17294561009504479834990199)
            ·
              refine ⟨25941841514256719752485299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17294561009504479834990199 25941841514256719752485299)
              ·
                refine ⟨38912762271385079628727949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25941841514256719752485299 38912762271385079628727949)
                ·
                  refine ⟨14592285851769404860772981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38912762271385079628727949 14592285851769404860772981)
                  ·
                    refine ⟨1368026798603381705697467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14592285851769404860772981 1368026798603381705697467)
                    ·
                      rfl

theorem cell22_3996334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3996334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996334 prefixEnd_3996334 := by exact prefixLift 3996334
  have htrace : WordTrace (prefixWord ++ tailWord_3996334) baseStart_3996334 baseEnd_3996334 := by
    simpa [prefixWord, tailWord_3996334, baseEnd_3996334] using wordTrace_append hprefix tailTrace_3996334
  have hstable : (prefixWord ++ tailWord_3996334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996334).length < 2 ^ (prefixWord ++ tailWord_3996334).sum := by decide
  have hdescent : baseEnd_3996334 < baseStart_3996334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996353 : List Nat := [1, 2, 6, 2, 1, 1, 1, 4, 4]
def baseStart_3996353 : Nat := 118140960795 + 3996353 * 2 ^ 59
def prefixEnd_3996353 : Nat := 4983230072969 + 3 ^ 40 * 3996353 * 2
def baseEnd_3996353 : Nat := 456011100897223996490803

theorem tailTrace_3996353 : CollatzResearch.WordTrace tailWord_3996353 prefixEnd_3996353 456011100897223996490803 := by
  unfold tailWord_3996353
  simp only [CollatzResearch.WordTrace]
  refine ⟨145758968490903078599097713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97172645660602052399398475 145758968490903078599097713)
  ·
    refine ⟨109319226368177308949323285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145758968490903078599097713 109319226368177308949323285)
    ·
      refine ⟨5124338736008311356999529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109319226368177308949323285 5124338736008311356999529)
      ·
        refine ⟨3843254052006233517749647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5124338736008311356999529 3843254052006233517749647)
        ·
          refine ⟨5764881078009350276624471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843254052006233517749647 5764881078009350276624471)
          ·
            refine ⟨8647321617014025414936707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764881078009350276624471 8647321617014025414936707)
            ·
              refine ⟨12970982425521038122405061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8647321617014025414936707 12970982425521038122405061)
              ·
                refine ⟨2432059204785194647950949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12970982425521038122405061 2432059204785194647950949)
                ·
                  refine ⟨456011100897223996490803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432059204785194647950949 456011100897223996490803)
                  ·
                    rfl

theorem cell22_3996353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_3996353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996353 prefixEnd_3996353 := by exact prefixLift 3996353
  have htrace : WordTrace (prefixWord ++ tailWord_3996353) baseStart_3996353 baseEnd_3996353 := by
    simpa [prefixWord, tailWord_3996353, baseEnd_3996353] using wordTrace_append hprefix tailTrace_3996353
  have hstable : (prefixWord ++ tailWord_3996353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996353).length < 2 ^ (prefixWord ++ tailWord_3996353).sum := by decide
  have hdescent : baseEnd_3996353 < baseStart_3996353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996364 : List Nat := [2, 2, 1, 5, 1, 3, 1, 7]
def baseStart_3996364 : Nat := 118140960795 + 3996364 * 2 ^ 59
def prefixEnd_3996364 : Nat := 4983230072969 + 3 ^ 40 * 3996364 * 2
def baseEnd_3996364 : Nat := 152004118690719069716375

theorem tailTrace_3996364 : CollatzResearch.WordTrace tailWord_3996364 prefixEnd_3996364 152004118690719069716375 := by
  unfold tailWord_3996364
  simp only [CollatzResearch.WordTrace]
  refine ⟨72879684846931613738874073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97172913129242151651832097 72879684846931613738874073)
  ·
    refine ⟨54659763635198710304155555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72879684846931613738874073 54659763635198710304155555)
    ·
      refine ⟨81989645452798065456233333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54659763635198710304155555 81989645452798065456233333)
      ·
        refine ⟨7686529261199818636521875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81989645452798065456233333 7686529261199818636521875)
        ·
          refine ⟨11529793891799727954782813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7686529261199818636521875 11529793891799727954782813)
          ·
            refine ⟨4323672709424897983043555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11529793891799727954782813 4323672709424897983043555)
            ·
              refine ⟨6485509064137346974565333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323672709424897983043555 6485509064137346974565333)
              ·
                refine ⟨152004118690719069716375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6485509064137346974565333 152004118690719069716375)
                ·
                  rfl

theorem cell22_3996364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 7].length) (baseStart_3996364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996364 prefixEnd_3996364 := by exact prefixLift 3996364
  have htrace : WordTrace (prefixWord ++ tailWord_3996364) baseStart_3996364 baseEnd_3996364 := by
    simpa [prefixWord, tailWord_3996364, baseEnd_3996364] using wordTrace_append hprefix tailTrace_3996364
  have hstable : (prefixWord ++ tailWord_3996364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996364).length < 2 ^ (prefixWord ++ tailWord_3996364).sum := by decide
  have hdescent : baseEnd_3996364 < baseStart_3996364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996437 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 6]
def baseStart_3996437 : Nat := 118140960795 + 3996437 * 2 ^ 59
def prefixEnd_3996437 : Nat := 4983230072969 + 3 ^ 40 * 3996437 * 2
def baseEnd_3996437 : Nat := 456020685869441256790717

theorem tailTrace_3996437 : CollatzResearch.WordTrace tailWord_3996437 prefixEnd_3996437 456020685869441256790717 := by
  unfold tailWord_3996437
  simp only [CollatzResearch.WordTrace]
  refine ⟨145762032222598760945155565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97174688148399173963437043 145762032222598760945155565)
  ·
    refine ⟨54660762083474535354433337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145762032222598760945155565 54660762083474535354433337)
    ·
      refine ⟨40995571562605901515825003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54660762083474535354433337 40995571562605901515825003)
      ·
        refine ⟨61493357343908852273737505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40995571562605901515825003 61493357343908852273737505)
        ·
          refine ⟨46120018007931639205303129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61493357343908852273737505 46120018007931639205303129)
          ·
            refine ⟨34590013505948729403977347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46120018007931639205303129 34590013505948729403977347)
            ·
              refine ⟨51885020258923094105966021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34590013505948729403977347 51885020258923094105966021)
              ·
                refine ⟨9728441298548080144868629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51885020258923094105966021 9728441298548080144868629)
                ·
                  refine ⟨456020685869441256790717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9728441298548080144868629 456020685869441256790717)
                  ·
                    rfl

theorem cell22_3996437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_3996437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996437 prefixEnd_3996437 := by exact prefixLift 3996437
  have htrace : WordTrace (prefixWord ++ tailWord_3996437) baseStart_3996437 baseEnd_3996437 := by
    simpa [prefixWord, tailWord_3996437, baseEnd_3996437] using wordTrace_append hprefix tailTrace_3996437
  have hstable : (prefixWord ++ tailWord_3996437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996437).length < 2 ^ (prefixWord ++ tailWord_3996437).sum := by decide
  have hdescent : baseEnd_3996437 < baseStart_3996437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996471 : List Nat := [1, 1, 3, 1, 2, 1, 7, 2, 4]
def baseStart_3996471 : Nat := 118140960795 + 3996471 * 2 ^ 59
def prefixEnd_3996471 : Nat := 4983230072969 + 3 ^ 40 * 3996471 * 2
def baseEnd_3996471 : Nat := 456024565501053005007349

theorem tailTrace_3996471 : CollatzResearch.WordTrace tailWord_3996471 prefixEnd_3996471 456024565501053005007349 := by
  unfold tailWord_3996471
  simp only [CollatzResearch.WordTrace]
  refine ⟨145763272304475584751893267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97175514869650389834595511 145763272304475584751893267)
  ·
    refine ⟨218644908456713377127839901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145763272304475584751893267 218644908456713377127839901)
    ·
      refine ⟨81991840671267516422939963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218644908456713377127839901 81991840671267516422939963)
      ·
        refine ⟨122987761006901274634409945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81991840671267516422939963 122987761006901274634409945)
        ·
          refine ⟨92240820755175955975807459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122987761006901274634409945 92240820755175955975807459)
          ·
            refine ⟨138361231132763933963711189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92240820755175955975807459 138361231132763933963711189)
            ·
              refine ⟨3242841354674154702274481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138361231132763933963711189 3242841354674154702274481)
              ·
                refine ⟨2432131016005616026705861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242841354674154702274481 2432131016005616026705861)
                ·
                  refine ⟨456024565501053005007349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432131016005616026705861 456024565501053005007349)
                  ·
                    rfl

theorem cell22_3996471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 4].length) (baseStart_3996471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996471 prefixEnd_3996471 := by exact prefixLift 3996471
  have htrace : WordTrace (prefixWord ++ tailWord_3996471) baseStart_3996471 baseEnd_3996471 := by
    simpa [prefixWord, tailWord_3996471, baseEnd_3996471] using wordTrace_append hprefix tailTrace_3996471
  have hstable : (prefixWord ++ tailWord_3996471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996471).length < 2 ^ (prefixWord ++ tailWord_3996471).sum := by decide
  have hdescent : baseEnd_3996471 < baseStart_3996471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996527 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 7]
def baseStart_3996527 : Nat := 118140960795 + 3996527 * 2 ^ 59
def prefixEnd_3996527 : Nat := 4983230072969 + 3 ^ 40 * 3996527 * 2
def baseEnd_3996527 : Nat := 456030955482531178540625

theorem tailTrace_3996527 : CollatzResearch.WordTrace tailWord_3996527 prefixEnd_3996527 456030955482531178540625 := by
  unfold tailWord_3996527
  simp only [CollatzResearch.WordTrace]
  refine ⟨145765314792272706315931835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97176876528181804210621223 145765314792272706315931835)
  ·
    refine ⟨218647972188409059473897753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145765314792272706315931835 218647972188409059473897753)
    ·
      refine ⟨163985979141306794605423315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218647972188409059473897753 163985979141306794605423315)
      ·
        refine ⟨245978968711960191908134973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163985979141306794605423315 245978968711960191908134973)
        ·
          refine ⟨92242113266985071965550615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245978968711960191908134973 92242113266985071965550615)
          ·
            refine ⟨138363169900477607948325923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92242113266985071965550615 138363169900477607948325923)
            ·
              refine ⟨207544754850716411922488885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138363169900477607948325923 207544754850716411922488885)
              ·
                refine ⟨19457320767254663617733333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207544754850716411922488885 19457320767254663617733333)
                ·
                  refine ⟨456030955482531178540625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19457320767254663617733333 456030955482531178540625)
                  ·
                    rfl

theorem cell22_3996527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 7].length) (baseStart_3996527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996527 prefixEnd_3996527 := by exact prefixLift 3996527
  have htrace : WordTrace (prefixWord ++ tailWord_3996527) baseStart_3996527 baseEnd_3996527 := by
    simpa [prefixWord, tailWord_3996527, baseEnd_3996527] using wordTrace_append hprefix tailTrace_3996527
  have hstable : (prefixWord ++ tailWord_3996527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996527).length < 2 ^ (prefixWord ++ tailWord_3996527).sum := by decide
  have hdescent : baseEnd_3996527 < baseStart_3996527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996578 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_3996578 : Nat := 118140960795 + 3996578 * 2 ^ 59
def prefixEnd_3996578 : Nat := 4983230072969 + 3 ^ 40 * 3996578 * 2
def baseEnd_3996578 : Nat := 456036774929948800865573

theorem tailTrace_3996578 : CollatzResearch.WordTrace tailWord_3996578 prefixEnd_3996578 456036774929948800865573 := by
  unfold tailWord_3996578
  simp only [CollatzResearch.WordTrace]
  refine ⟨36441793728771985506509597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97178116610058628017358925 36441793728771985506509597)
  ·
    refine ⟨13665672648289494564941099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36441793728771985506509597 13665672648289494564941099)
    ·
      refine ⟨20498508972434241847411649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13665672648289494564941099 20498508972434241847411649)
      ·
        refine ⟨15373881729325681385558737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20498508972434241847411649 15373881729325681385558737)
        ·
          refine ⟨11530411296994261039169053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15373881729325681385558737 11530411296994261039169053)
          ·
            refine ⟨4323904236372847889688395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11530411296994261039169053 4323904236372847889688395)
            ·
              refine ⟨6485856354559271834532593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323904236372847889688395 6485856354559271834532593)
              ·
                refine ⟨4864392265919453875899445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485856354559271834532593 4864392265919453875899445)
                ·
                  refine ⟨456036774929948800865573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4864392265919453875899445 456036774929948800865573)
                  ·
                    rfl

theorem cell22_3996578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_3996578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996578 prefixEnd_3996578 := by exact prefixLift 3996578
  have htrace : WordTrace (prefixWord ++ tailWord_3996578) baseStart_3996578 baseEnd_3996578 := by
    simpa [prefixWord, tailWord_3996578, baseEnd_3996578] using wordTrace_append hprefix tailTrace_3996578
  have hstable : (prefixWord ++ tailWord_3996578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996578).length < 2 ^ (prefixWord ++ tailWord_3996578).sum := by decide
  have hdescent : baseEnd_3996578 < baseStart_3996578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996619 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 1, 6]
def baseStart_3996619 : Nat := 118140960795 + 3996619 * 2 ^ 59
def prefixEnd_3996619 : Nat := 4983230072969 + 3 ^ 40 * 3996619 * 2
def baseEnd_3996619 : Nat := 1368124359927735962321593

theorem tailTrace_3996619 : CollatzResearch.WordTrace tailWord_3996619 prefixEnd_3996619 1368124359927735962321593 := by
  unfold tailWord_3996619
  simp only [CollatzResearch.WordTrace]
  refine ⟨145768670307939406028280911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97179113538626270685520607 145768670307939406028280911)
  ·
    refine ⟨218653005461909109042421367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145768670307939406028280911 218653005461909109042421367)
    ·
      refine ⟨327979508192863663563632051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218653005461909109042421367 327979508192863663563632051)
      ·
        refine ⟨491969262289295495345448077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327979508192863663563632051 491969262289295495345448077)
        ·
          refine ⟨184488473358485810754543029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491969262289295495345448077 184488473358485810754543029)
          ·
            refine ⟨17295794377358044758238409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184488473358485810754543029 17295794377358044758238409)
            ·
              refine ⟨12971845783018533568678807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17295794377358044758238409 12971845783018533568678807)
              ·
                refine ⟨19457768674527800353018211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12971845783018533568678807 19457768674527800353018211)
                ·
                  refine ⟨29186653011791700529527317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19457768674527800353018211 29186653011791700529527317)
                  ·
                    refine ⟨1368124359927735962321593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29186653011791700529527317 1368124359927735962321593)
                    ·
                      rfl

theorem cell22_3996619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_3996619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996619 prefixEnd_3996619 := by exact prefixLift 3996619
  have htrace : WordTrace (prefixWord ++ tailWord_3996619) baseStart_3996619 baseEnd_3996619 := by
    simpa [prefixWord, tailWord_3996619, baseEnd_3996619] using wordTrace_append hprefix tailTrace_3996619
  have hstable : (prefixWord ++ tailWord_3996619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996619).length < 2 ^ (prefixWord ++ tailWord_3996619).sum := by decide
  have hdescent : baseEnd_3996619 < baseStart_3996619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996623 : List Nat := [1, 1, 2, 1, 1, 8, 1, 3, 4]
def baseStart_3996623 : Nat := 118140960795 + 3996623 * 2 ^ 59
def prefixEnd_3996623 : Nat := 4983230072969 + 3 ^ 40 * 3996623 * 2
def baseEnd_3996623 : Nat := 456041909736493761740527

theorem tailTrace_3996623 : CollatzResearch.WordTrace tailWord_3996623 prefixEnd_3996623 456041909736493761740527 := by
  unfold tailWord_3996623
  simp only [CollatzResearch.WordTrace]
  refine ⟨145768816199924914711426523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97179210799949943140951015 145768816199924914711426523)
  ·
    refine ⟨218653224299887372067139785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145768816199924914711426523 218653224299887372067139785)
    ·
      refine ⟨163989918224915529050354839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218653224299887372067139785 163989918224915529050354839)
      ·
        refine ⟨245984877337373293575532259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163989918224915529050354839 245984877337373293575532259)
        ·
          refine ⟨368977316006059940363298389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245984877337373293575532259 368977316006059940363298389)
          ·
            refine ⟨4323952921946014926132403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 368977316006059940363298389 4323952921946014926132403)
            ·
              refine ⟨6485929382919022389198605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323952921946014926132403 6485929382919022389198605)
              ·
                refine ⟨2432223518594633395949477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6485929382919022389198605 2432223518594633395949477)
                ·
                  refine ⟨456041909736493761740527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432223518594633395949477 456041909736493761740527)
                  ·
                    rfl

theorem cell22_3996623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 4].length) (baseStart_3996623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996623 prefixEnd_3996623 := by exact prefixLift 3996623
  have htrace : WordTrace (prefixWord ++ tailWord_3996623) baseStart_3996623 baseEnd_3996623 := by
    simpa [prefixWord, tailWord_3996623, baseEnd_3996623] using wordTrace_append hprefix tailTrace_3996623
  have hstable : (prefixWord ++ tailWord_3996623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996623).length < 2 ^ (prefixWord ++ tailWord_3996623).sum := by decide
  have hdescent : baseEnd_3996623 < baseStart_3996623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996634 : List Nat := [3, 1, 1, 2, 4, 1, 10]
def baseStart_3996634 : Nat := 118140960795 + 3996634 * 2 ^ 59
def prefixEnd_3996634 : Nat := 4983230072969 + 3 ^ 40 * 3996634 * 2
def baseEnd_3996634 : Nat := 50671462767936330488761

theorem tailTrace_3996634 : CollatzResearch.WordTrace tailWord_3996634 prefixEnd_3996634 50671462767936330488761 := by
  unfold tailWord_3996634
  simp only [CollatzResearch.WordTrace]
  refine ⟨36442304350721265897519239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97179478268590042393384637 36442304350721265897519239)
  ·
    refine ⟨54663456526081898846278859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36442304350721265897519239 54663456526081898846278859)
    ·
      refine ⟨81995184789122848269418289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54663456526081898846278859 81995184789122848269418289)
      ·
        refine ⟨61496388591842136202063717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81995184789122848269418289 61496388591842136202063717)
        ·
          refine ⟨11530572860970400537886947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61496388591842136202063717 11530572860970400537886947)
          ·
            refine ⟨17295859291455600806830421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11530572860970400537886947 17295859291455600806830421)
            ·
              refine ⟨50671462767936330488761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17295859291455600806830421 50671462767936330488761)
              ·
                rfl

theorem cell22_3996634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 10].length) (baseStart_3996634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996634 prefixEnd_3996634 := by exact prefixLift 3996634
  have htrace : WordTrace (prefixWord ++ tailWord_3996634) baseStart_3996634 baseEnd_3996634 := by
    simpa [prefixWord, tailWord_3996634, baseEnd_3996634] using wordTrace_append hprefix tailTrace_3996634
  have hstable : (prefixWord ++ tailWord_3996634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996634).length < 2 ^ (prefixWord ++ tailWord_3996634).sum := by decide
  have hdescent : baseEnd_3996634 < baseStart_3996634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996655 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 2, 3]
def baseStart_3996655 : Nat := 118140960795 + 3996655 * 2 ^ 59
def prefixEnd_3996655 : Nat := 4983230072969 + 3 ^ 40 * 3996655 * 2
def baseEnd_3996655 : Nat := 1368136683463443868421483

theorem tailTrace_3996655 : CollatzResearch.WordTrace tailWord_3996655 prefixEnd_3996655 1368136683463443868421483 := by
  unfold tailWord_3996655
  simp only [CollatzResearch.WordTrace]
  refine ⟨145769983335808984176591419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97179988890539322784394279 145769983335808984176591419)
  ·
    refine ⟨218654975003713476264887129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145769983335808984176591419 218654975003713476264887129)
    ·
      refine ⟨163991231252785107198665347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218654975003713476264887129 163991231252785107198665347)
      ·
        refine ⟨245986846879177660797998021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163991231252785107198665347 245986846879177660797998021)
        ·
          refine ⟨46122533789845811399624629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245986846879177660797998021 46122533789845811399624629)
          ·
            refine ⟨4323987542798044818714809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46122533789845811399624629 4323987542798044818714809)
            ·
              refine ⟨3242990657098533614036107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4323987542798044818714809 3242990657098533614036107)
              ·
                refine ⟨4864485985647800421054161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242990657098533614036107 4864485985647800421054161)
                ·
                  refine ⟨3648364489235850315790621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864485985647800421054161 3648364489235850315790621)
                  ·
                    refine ⟨1368136683463443868421483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3648364489235850315790621 1368136683463443868421483)
                    ·
                      rfl

theorem cell22_3996655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_3996655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996655 prefixEnd_3996655 := by exact prefixLift 3996655
  have htrace : WordTrace (prefixWord ++ tailWord_3996655) baseStart_3996655 baseEnd_3996655 := by
    simpa [prefixWord, tailWord_3996655, baseEnd_3996655] using wordTrace_append hprefix tailTrace_3996655
  have hstable : (prefixWord ++ tailWord_3996655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996655).length < 2 ^ (prefixWord ++ tailWord_3996655).sum := by decide
  have hdescent : baseEnd_3996655 < baseStart_3996655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996666 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_3996666 : Nat := 118140960795 + 3996666 * 2 ^ 59
def prefixEnd_3996666 : Nat := 4983230072969 + 3 ^ 40 * 3996666 * 2
def baseEnd_3996666 : Nat := 1368140448988243506396449

theorem tailTrace_3996666 : CollatzResearch.WordTrace tailWord_3996666 prefixEnd_3996666 1368140448988243506396449 := by
  unfold tailWord_3996666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36442596134692283263810463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97180256359179422036827901 36442596134692283263810463)
  ·
    refine ⟨54663894202038424895715695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36442596134692283263810463 54663894202038424895715695)
    ·
      refine ⟨81995841303057637343573543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54663894202038424895715695 81995841303057637343573543)
      ·
        refine ⟨122993761954586456015360315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81995841303057637343573543 122993761954586456015360315)
        ·
          refine ⟨184490642931879684023040473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122993761954586456015360315 184490642931879684023040473)
          ·
            refine ⟨138367982198909763017280355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184490642931879684023040473 138367982198909763017280355)
            ·
              refine ⟨207551973298364644525920533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138367982198909763017280355 207551973298364644525920533)
              ·
                refine ⟨9728998748360842712152525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207551973298364644525920533 9728998748360842712152525)
                ·
                  refine ⟨3648374530635316017057197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9728998748360842712152525 3648374530635316017057197)
                  ·
                    refine ⟨1368140448988243506396449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3648374530635316017057197 1368140448988243506396449)
                    ·
                      rfl

theorem cell22_3996666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_3996666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996666 prefixEnd_3996666 := by exact prefixLift 3996666
  have htrace : WordTrace (prefixWord ++ tailWord_3996666) baseStart_3996666 baseEnd_3996666 := by
    simpa [prefixWord, tailWord_3996666, baseEnd_3996666] using wordTrace_append hprefix tailTrace_3996666
  have hstable : (prefixWord ++ tailWord_3996666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996666).length < 2 ^ (prefixWord ++ tailWord_3996666).sum := by decide
  have hdescent : baseEnd_3996666 < baseStart_3996666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996670 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3996670 : Nat := 118140960795 + 3996670 * 2 ^ 59
def prefixEnd_3996670 : Nat := 4983230072969 + 3 ^ 40 * 3996670 * 2
def baseEnd_3996670 : Nat := 1368141818269988829296437

theorem tailTrace_3996670 : CollatzResearch.WordTrace tailWord_3996670 prefixEnd_3996670 1368141818269988829296437 := by
  unfold tailWord_3996670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18221316303844330217298433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97180353620503094492258309 18221316303844330217298433)
  ·
    refine ⟨13665987227883247662973825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18221316303844330217298433 13665987227883247662973825)
    ·
      refine ⟨10249490420912435747230369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13665987227883247662973825 10249490420912435747230369)
      ·
        refine ⟨7687117815684326810422777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10249490420912435747230369 7687117815684326810422777)
        ·
          refine ⟨5765338361763245107817083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7687117815684326810422777 5765338361763245107817083)
          ·
            refine ⟨8648007542644867661725625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765338361763245107817083 8648007542644867661725625)
            ·
              refine ⟨6486005656983650746294219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8648007542644867661725625 6486005656983650746294219)
              ·
                refine ⟨9729008485475476119441329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486005656983650746294219 9729008485475476119441329)
                ·
                  refine ⟨7296756364106607089580997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729008485475476119441329 7296756364106607089580997)
                  ·
                    refine ⟨1368141818269988829296437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296756364106607089580997 1368141818269988829296437)
                    ·
                      rfl

theorem cell22_3996670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3996670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996670 prefixEnd_3996670 := by exact prefixLift 3996670
  have htrace : WordTrace (prefixWord ++ tailWord_3996670) baseStart_3996670 baseEnd_3996670 := by
    simpa [prefixWord, tailWord_3996670, baseEnd_3996670] using wordTrace_append hprefix tailTrace_3996670
  have hstable : (prefixWord ++ tailWord_3996670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996670).length < 2 ^ (prefixWord ++ tailWord_3996670).sum := by decide
  have hdescent : baseEnd_3996670 < baseStart_3996670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996696 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 5]
def baseStart_3996696 : Nat := 118140960795 + 3996696 * 2 ^ 59
def prefixEnd_3996696 : Nat := 4983230072969 + 3 ^ 40 * 3996696 * 2
def baseEnd_3996696 : Nat := 456050239533777809382119

theorem tailTrace_3996696 : CollatzResearch.WordTrace tailWord_3996696 prefixEnd_3996696 456050239533777809382119 := by
  unfold tailWord_3996696
  simp only [CollatzResearch.WordTrace]
  refine ⟨72885739364330224089416971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97180985819106965452555961 72885739364330224089416971)
  ·
    refine ⟨109328609046495336134125457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72885739364330224089416971 109328609046495336134125457)
    ·
      refine ⟨81996456784871502100594093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109328609046495336134125457 81996456784871502100594093)
      ·
        refine ⟨30748671294326813287722785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81996456784871502100594093 30748671294326813287722785)
        ·
          refine ⟨23061503470745109965792089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30748671294326813287722785 23061503470745109965792089)
          ·
            refine ⟨17296127603058832474344067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23061503470745109965792089 17296127603058832474344067)
            ·
              refine ⟨25944191404588248711516101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17296127603058832474344067 25944191404588248711516101)
              ·
                refine ⟨4864535888360296633409269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25944191404588248711516101 4864535888360296633409269)
                ·
                  refine ⟨456050239533777809382119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4864535888360296633409269 456050239533777809382119)
                  ·
                    rfl

theorem cell22_3996696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_3996696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996696 prefixEnd_3996696 := by exact prefixLift 3996696
  have htrace : WordTrace (prefixWord ++ tailWord_3996696) baseStart_3996696 baseEnd_3996696 := by
    simpa [prefixWord, tailWord_3996696, baseEnd_3996696] using wordTrace_append hprefix tailTrace_3996696
  have hstable : (prefixWord ++ tailWord_3996696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996696).length < 2 ^ (prefixWord ++ tailWord_3996696).sum := by decide
  have hdescent : baseEnd_3996696 < baseStart_3996696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996743 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 1, 4]
def baseStart_3996743 : Nat := 118140960795 + 3996743 * 2 ^ 59
def prefixEnd_3996743 : Nat := 4983230072969 + 3 ^ 40 * 3996743 * 2
def baseEnd_3996743 : Nat := 1368166807661840972221213

theorem tailTrace_3996743 : CollatzResearch.WordTrace tailWord_3996743 prefixEnd_3996743 1368166807661840972221213 := by
  unfold tailWord_3996743
  simp only [CollatzResearch.WordTrace]
  refine ⟨145773192959490175205794883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97182128639660116803863255 145773192959490175205794883)
  ·
    refine ⟨218659789439235262808692325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145773192959490175205794883 218659789439235262808692325)
    ·
      refine ⟨40998710519856611776629811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218659789439235262808692325 40998710519856611776629811)
      ·
        refine ⟨61498065779784917664944717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40998710519856611776629811 61498065779784917664944717)
        ·
          refine ⟨23061774667419344124354269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61498065779784917664944717 23061774667419344124354269)
          ·
            refine ⟨8648165500282254046632851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23061774667419344124354269 8648165500282254046632851)
            ·
              refine ⟨12972248250423381069949277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648165500282254046632851 12972248250423381069949277)
              ·
                refine ⟨4864593093908767901230979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12972248250423381069949277 4864593093908767901230979)
                ·
                  refine ⟨7296889640863151851846469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864593093908767901230979 7296889640863151851846469)
                  ·
                    refine ⟨1368166807661840972221213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296889640863151851846469 1368166807661840972221213)
                    ·
                      rfl

theorem cell22_3996743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_3996743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996743 prefixEnd_3996743 := by exact prefixLift 3996743
  have htrace : WordTrace (prefixWord ++ tailWord_3996743) baseStart_3996743 baseEnd_3996743 := by
    simpa [prefixWord, tailWord_3996743, baseEnd_3996743] using wordTrace_append hprefix tailTrace_3996743
  have hstable : (prefixWord ++ tailWord_3996743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996743).length < 2 ^ (prefixWord ++ tailWord_3996743).sum := by decide
  have hdescent : baseEnd_3996743 < baseStart_3996743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996756 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3996756 : Nat := 118140960795 + 3996756 * 2 ^ 59
def prefixEnd_3996756 : Nat := 4983230072969 + 3 ^ 40 * 3996756 * 2
def baseEnd_3996756 : Nat := 1368171257827513271646173

theorem tailTrace_3996756 : CollatzResearch.WordTrace tailWord_3996756 prefixEnd_3996756 1368171257827513271646173 := by
  unfold tailWord_3996756
  simp only [CollatzResearch.WordTrace]
  refine ⟨72886833554221539213009061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97182444738962052284012081 72886833554221539213009061)
  ·
    refine ⟨13666281291416538602439199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72886833554221539213009061 13666281291416538602439199)
    ·
      refine ⟨20499421937124807903658799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13666281291416538602439199 20499421937124807903658799)
      ·
        refine ⟨30749132905687211855488199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20499421937124807903658799 30749132905687211855488199)
        ·
          refine ⟨46123699358530817783232299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30749132905687211855488199 46123699358530817783232299)
          ·
            refine ⟨69185549037796226674848449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46123699358530817783232299 69185549037796226674848449)
            ·
              refine ⟨51889161778347170006136337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69185549037796226674848449 51889161778347170006136337)
              ·
                refine ⟨38916871333760377504602253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51889161778347170006136337 38916871333760377504602253)
                ·
                  refine ⟨14593826750160141564225845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38916871333760377504602253 14593826750160141564225845)
                  ·
                    refine ⟨1368171257827513271646173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14593826750160141564225845 1368171257827513271646173)
                    ·
                      rfl

theorem cell22_3996756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3996756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996756 prefixEnd_3996756 := by exact prefixLift 3996756
  have htrace : WordTrace (prefixWord ++ tailWord_3996756) baseStart_3996756 baseEnd_3996756 := by
    simpa [prefixWord, tailWord_3996756, baseEnd_3996756] using wordTrace_append hprefix tailTrace_3996756
  have hstable : (prefixWord ++ tailWord_3996756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996756).length < 2 ^ (prefixWord ++ tailWord_3996756).sum := by decide
  have hdescent : baseEnd_3996756 < baseStart_3996756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996786 : List Nat := [3, 2, 1, 2, 2, 1, 3, 8]
def baseStart_3996786 : Nat := 118140960795 + 3996786 * 2 ^ 59
def prefixEnd_3996786 : Nat := 4983230072969 + 3 ^ 40 * 3996786 * 2
def baseEnd_3996786 : Nat := 152020169715622577044009

theorem tailTrace_3996786 : CollatzResearch.WordTrace tailWord_3996786 prefixEnd_3996786 152020169715622577044009 := by
  unfold tailWord_3996786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36443690324583598387402553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97183174198889595699740141 36443690324583598387402553)
  ·
    refine ⟨27332767743437698790551915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36443690324583598387402553 27332767743437698790551915)
    ·
      refine ⟨40999151615156548185827873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27332767743437698790551915 40999151615156548185827873)
      ·
        refine ⟨30749363711367411139370905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40999151615156548185827873 30749363711367411139370905)
        ·
          refine ⟨23062022783525558354528179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30749363711367411139370905 23062022783525558354528179)
          ·
            refine ⟨34593034175288337531792269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23062022783525558354528179 34593034175288337531792269)
            ·
              refine ⟨12972387815733126574422101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34593034175288337531792269 12972387815733126574422101)
              ·
                refine ⟨152020169715622577044009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12972387815733126574422101 152020169715622577044009)
                ·
                  rfl

theorem cell22_3996786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_3996786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996786 prefixEnd_3996786 := by exact prefixLift 3996786
  have htrace : WordTrace (prefixWord ++ tailWord_3996786) baseStart_3996786 baseEnd_3996786 := by
    simpa [prefixWord, tailWord_3996786, baseEnd_3996786] using wordTrace_append hprefix tailTrace_3996786
  have hstable : (prefixWord ++ tailWord_3996786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996786).length < 2 ^ (prefixWord ++ tailWord_3996786).sum := by decide
  have hdescent : baseEnd_3996786 < baseStart_3996786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996865 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 5]
def baseStart_3996865 : Nat := 118140960795 + 3996865 * 2 ^ 59
def prefixEnd_3996865 : Nat := 4983230072969 + 3 ^ 40 * 3996865 * 2
def baseEnd_3996865 : Nat := 456069523585024440223613

theorem tailTrace_3996865 : CollatzResearch.WordTrace tailWord_3996865 prefixEnd_3996865 456069523585024440223613 := by
  unfold tailWord_3996865
  simp only [CollatzResearch.WordTrace]
  refine ⟨145777642665048190041736049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97185095110032126694490699 145777642665048190041736049)
  ·
    refine ⟨109333231998786142531302037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145777642665048190041736049 109333231998786142531302037)
    ·
      refine ⟨5124995249943100431154783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109333231998786142531302037 5124995249943100431154783)
      ·
        refine ⟨7687492874914650646732175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124995249943100431154783 7687492874914650646732175)
        ·
          refine ⟨11531239312371975970098263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7687492874914650646732175 11531239312371975970098263)
          ·
            refine ⟨17296858968557963955147395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11531239312371975970098263 17296858968557963955147395)
            ·
              refine ⟨25945288452836945932721093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17296858968557963955147395 25945288452836945932721093)
              ·
                refine ⟨4864741584906927362385205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25945288452836945932721093 4864741584906927362385205)
                ·
                  refine ⟨456069523585024440223613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4864741584906927362385205 456069523585024440223613)
                  ·
                    rfl

theorem cell22_3996865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_3996865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996865 prefixEnd_3996865 := by exact prefixLift 3996865
  have htrace : WordTrace (prefixWord ++ tailWord_3996865) baseStart_3996865 baseEnd_3996865 := by
    simpa [prefixWord, tailWord_3996865, baseEnd_3996865] using wordTrace_append hprefix tailTrace_3996865
  have hstable : (prefixWord ++ tailWord_3996865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996865).length < 2 ^ (prefixWord ++ tailWord_3996865).sum := by decide
  have hdescent : baseEnd_3996865 < baseStart_3996865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996908 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_3996908 : Nat := 118140960795 + 3996908 * 2 ^ 59
def prefixEnd_3996908 : Nat := 4983230072969 + 3 ^ 40 * 3996908 * 2
def baseEnd_3996908 : Nat := 1368223290533835541845707

theorem tailTrace_3996908 : CollatzResearch.WordTrace tailWord_3996908 prefixEnd_3996908 1368223290533835541845707 := by
  unfold tailWord_3996908
  simp only [CollatzResearch.WordTrace]
  refine ⟨72889605501946204192775689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97186140669261605590367585 72889605501946204192775689)
  ·
    refine ⟨54667204126459653144581767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72889605501946204192775689 54667204126459653144581767)
    ·
      refine ⟨82000806189689479716872651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54667204126459653144581767 82000806189689479716872651)
      ·
        refine ⟨123001209284534219575308977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82000806189689479716872651 123001209284534219575308977)
        ·
          refine ⟨92250906963400664681481733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123001209284534219575308977 92250906963400664681481733)
          ·
            refine ⟨17297045055637624627777825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92250906963400664681481733 17297045055637624627777825)
            ·
              refine ⟨12972783791728218470833369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17297045055637624627777825 12972783791728218470833369)
              ·
                refine ⟨9729587843796163853125027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12972783791728218470833369 9729587843796163853125027)
                ·
                  refine ⟨14594381765694245779687541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9729587843796163853125027 14594381765694245779687541)
                  ·
                    refine ⟨1368223290533835541845707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14594381765694245779687541 1368223290533835541845707)
                    ·
                      rfl

theorem cell22_3996908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_3996908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996908 prefixEnd_3996908 := by exact prefixLift 3996908
  have htrace : WordTrace (prefixWord ++ tailWord_3996908) baseStart_3996908 baseEnd_3996908 := by
    simpa [prefixWord, tailWord_3996908, baseEnd_3996908] using wordTrace_append hprefix tailTrace_3996908
  have hstable : (prefixWord ++ tailWord_3996908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996908).length < 2 ^ (prefixWord ++ tailWord_3996908).sum := by decide
  have hdescent : baseEnd_3996908 < baseStart_3996908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996910 : List Nat := [4, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3996910 : Nat := 118140960795 + 3996910 * 2 ^ 59
def prefixEnd_3996910 : Nat := 4983230072969 + 3 ^ 40 * 3996910 * 2
def baseEnd_3996910 : Nat := 456074658391569401098567

theorem tailTrace_3996910 : CollatzResearch.WordTrace tailWord_3996910 prefixEnd_3996910 456074658391569401098567 := by
  unfold tailWord_3996910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18222410493735645340890523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97186189299923441818082789 18222410493735645340890523)
  ·
    refine ⟨27333615740603468011335785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18222410493735645340890523 27333615740603468011335785)
    ·
      refine ⟨20500211805452601008501839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27333615740603468011335785 20500211805452601008501839)
      ·
        refine ⟨30750317708178901512752759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20500211805452601008501839 30750317708178901512752759)
        ·
          refine ⟨46125476562268352269129139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30750317708178901512752759 46125476562268352269129139)
          ·
            refine ⟨69188214843402528403693709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46125476562268352269129139 69188214843402528403693709)
            ·
              refine ⟨25945580566275948151385141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69188214843402528403693709 25945580566275948151385141)
              ·
                refine ⟨2432398178088370139192357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25945580566275948151385141 2432398178088370139192357)
                ·
                  refine ⟨456074658391569401098567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432398178088370139192357 456074658391569401098567)
                  ·
                    rfl

theorem cell22_3996910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3996910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996910 prefixEnd_3996910 := by exact prefixLift 3996910
  have htrace : WordTrace (prefixWord ++ tailWord_3996910) baseStart_3996910 baseEnd_3996910 := by
    simpa [prefixWord, tailWord_3996910, baseEnd_3996910] using wordTrace_append hprefix tailTrace_3996910
  have hstable : (prefixWord ++ tailWord_3996910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996910).length < 2 ^ (prefixWord ++ tailWord_3996910).sum := by decide
  have hdescent : baseEnd_3996910 < baseStart_3996910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996916 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3996916 : Nat := 118140960795 + 3996916 * 2 ^ 59
def prefixEnd_3996916 : Nat := 4983230072969 + 3 ^ 40 * 3996916 * 2
def baseEnd_3996916 : Nat := 456075343032442062548561

theorem tailTrace_3996916 : CollatzResearch.WordTrace tailWord_3996916 prefixEnd_3996916 456075343032442062548561 := by
  unfold tailWord_3996916
  simp only [CollatzResearch.WordTrace]
  refine ⟨72889751393931712875921301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97186335191908950501228401 72889751393931712875921301)
  ·
    refine ⟨3416707096590549041058811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72889751393931712875921301 3416707096590549041058811)
    ·
      refine ⟨5125060644885823561588217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3416707096590549041058811 5125060644885823561588217)
      ·
        refine ⟨3843795483664367671191163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5125060644885823561588217 3843795483664367671191163)
        ·
          refine ⟨5765693225496551506786745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843795483664367671191163 5765693225496551506786745)
          ·
            refine ⟨4324269919122413630090059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5765693225496551506786745 4324269919122413630090059)
            ·
              refine ⟨6486404878683620445135089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324269919122413630090059 6486404878683620445135089)
              ·
                refine ⟨4864803659012715333851317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6486404878683620445135089 4864803659012715333851317)
                ·
                  refine ⟨456075343032442062548561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4864803659012715333851317 456075343032442062548561)
                  ·
                    rfl

theorem cell22_3996916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3996916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996916 prefixEnd_3996916 := by exact prefixLift 3996916
  have htrace : WordTrace (prefixWord ++ tailWord_3996916) baseStart_3996916 baseEnd_3996916 := by
    simpa [prefixWord, tailWord_3996916, baseEnd_3996916] using wordTrace_append hprefix tailTrace_3996916
  have hstable : (prefixWord ++ tailWord_3996916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996916).length < 2 ^ (prefixWord ++ tailWord_3996916).sum := by decide
  have hdescent : baseEnd_3996916 < baseStart_3996916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996921 : List Nat := [1, 2, 1, 3, 1, 1, 13]
def baseStart_3996921 : Nat := 118140960795 + 3996921 * 2 ^ 59
def prefixEnd_3996921 : Nat := 4983230072969 + 3 ^ 40 * 3996921 * 2
def baseEnd_3996921 : Nat := 50675101507389179306321

theorem tailTrace_3996921 : CollatzResearch.WordTrace tailWord_3996921 prefixEnd_3996921 50675101507389179306321 := by
  unfold tailWord_3996921
  simp only [CollatzResearch.WordTrace]
  refine ⟨145779685152845311605774617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97186456768563541070516411 145779685152845311605774617)
  ·
    refine ⟨109334763864633983704330963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145779685152845311605774617 109334763864633983704330963)
    ·
      refine ⟨164002145796950975556496445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109334763864633983704330963 164002145796950975556496445)
      ·
        refine ⟨61500804673856615833686167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164002145796950975556496445 61500804673856615833686167)
        ·
          refine ⟨92251207010784923750529251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61500804673856615833686167 92251207010784923750529251)
          ·
            refine ⟨138376810516177385625793877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92251207010784923750529251 138376810516177385625793877)
            ·
              refine ⟨50675101507389179306321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 138376810516177385625793877 50675101507389179306321)
              ·
                rfl

theorem cell22_3996921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 13].length) (baseStart_3996921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3996921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3996921 prefixEnd_3996921 := by exact prefixLift 3996921
  have htrace : WordTrace (prefixWord ++ tailWord_3996921) baseStart_3996921 baseEnd_3996921 := by
    simpa [prefixWord, tailWord_3996921, baseEnd_3996921] using wordTrace_append hprefix tailTrace_3996921
  have hstable : (prefixWord ++ tailWord_3996921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996921).length < 2 ^ (prefixWord ++ tailWord_3996921).sum := by decide
  have hdescent : baseEnd_3996921 < baseStart_3996921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997060 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3997060 : Nat := 118140960795 + 3997060 * 2 ^ 59
def prefixEnd_3997060 : Nat := 4983230072969 + 3 ^ 40 * 3997060 * 2
def baseEnd_3997060 : Nat := 1368275323240157812045241

theorem tailTrace_3997060 : CollatzResearch.WordTrace tailWord_3997060 prefixEnd_3997060 1368275323240157812045241 := by
  unfold tailWord_3997060
  simp only [CollatzResearch.WordTrace]
  refine ⟨72892377449670869172542317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97189836599561158896723089 72892377449670869172542317)
  ·
    refine ⟨27334641543626575939703369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72892377449670869172542317 27334641543626575939703369)
    ·
      refine ⟨20500981157719931954777527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27334641543626575939703369 20500981157719931954777527)
      ·
        refine ⟨30751471736579897932166291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20500981157719931954777527 30751471736579897932166291)
        ·
          refine ⟨46127207604869846898249437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30751471736579897932166291 46127207604869846898249437)
          ·
            refine ⟨17297702851826192586843539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46127207604869846898249437 17297702851826192586843539)
            ·
              refine ⟨25946554277739288880265309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17297702851826192586843539 25946554277739288880265309)
              ·
                refine ⟨9729957854152233330099491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25946554277739288880265309 9729957854152233330099491)
                ·
                  refine ⟨14594936781228349995149237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9729957854152233330099491 14594936781228349995149237)
                  ·
                    refine ⟨1368275323240157812045241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14594936781228349995149237 1368275323240157812045241)
                    ·
                      rfl

theorem cell22_3997060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3997060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997060 prefixEnd_3997060 := by exact prefixLift 3997060
  have htrace : WordTrace (prefixWord ++ tailWord_3997060) baseStart_3997060 baseEnd_3997060 := by
    simpa [prefixWord, tailWord_3997060, baseEnd_3997060] using wordTrace_append hprefix tailTrace_3997060
  have hstable : (prefixWord ++ tailWord_3997060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997060).length < 2 ^ (prefixWord ++ tailWord_3997060).sum := by decide
  have hdescent : baseEnd_3997060 < baseStart_3997060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997090 : List Nat := [3, 3, 1, 2, 1, 3, 9]
def baseStart_3997090 : Nat := 118140960795 + 3997090 * 2 ^ 59
def prefixEnd_3997090 : Nat := 4983230072969 + 3 ^ 40 * 3997090 * 2
def baseEnd_3997090 : Nat := 50677244179749916066487

theorem tailTrace_3997090 : CollatzResearch.WordTrace tailWord_3997090 prefixEnd_3997090 50677244179749916066487 := by
  unfold tailWord_3997090
  simp only [CollatzResearch.WordTrace]
  refine ⟨36446462272308263367169181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97190566059488702312451149 36446462272308263367169181)
  ·
    refine ⟨13667423352115598762688443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36446462272308263367169181 13667423352115598762688443)
    ·
      refine ⟨20501135028173398144032665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13667423352115598762688443 20501135028173398144032665)
      ·
        refine ⟨15375851271130048608024499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20501135028173398144032665 15375851271130048608024499)
        ·
          refine ⟨23063776906695072912036749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15375851271130048608024499 23063776906695072912036749)
          ·
            refine ⟨8648916340010652342013781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23063776906695072912036749 8648916340010652342013781)
            ·
              refine ⟨50677244179749916066487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8648916340010652342013781 50677244179749916066487)
              ·
                rfl

theorem cell22_3997090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 9].length) (baseStart_3997090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997090 prefixEnd_3997090 := by exact prefixLift 3997090
  have htrace : WordTrace (prefixWord ++ tailWord_3997090) baseStart_3997090 baseEnd_3997090 := by
    simpa [prefixWord, tailWord_3997090, baseEnd_3997090] using wordTrace_append hprefix tailTrace_3997090
  have hstable : (prefixWord ++ tailWord_3997090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997090).length < 2 ^ (prefixWord ++ tailWord_3997090).sum := by decide
  have hdescent : baseEnd_3997090 < baseStart_3997090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997103 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 8]
def baseStart_3997103 : Nat := 118140960795 + 3997103 * 2 ^ 59
def prefixEnd_3997103 : Nat := 4983230072969 + 3 ^ 40 * 3997103 * 2
def baseEnd_3997103 : Nat := 1368290043018920033220109

theorem tailTrace_3997103 : CollatzResearch.WordTrace tailWord_3997103 prefixEnd_3997103 1368290043018920033220109 := by
  unfold tailWord_3997103
  simp only [CollatzResearch.WordTrace]
  refine ⟨145786323238185956688899963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97190882158790637792599975 145786323238185956688899963)
  ·
    refine ⟨218679484857278935033349945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145786323238185956688899963 218679484857278935033349945)
    ·
      refine ⟨164009613642959201275012459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218679484857278935033349945 164009613642959201275012459)
      ·
        refine ⟨246014420464438801912518689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164009613642959201275012459 246014420464438801912518689)
        ·
          refine ⟨184510815348329101434389017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246014420464438801912518689 184510815348329101434389017)
          ·
            refine ⟨138383111511246826075791763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184510815348329101434389017 138383111511246826075791763)
            ·
              refine ⟨207574667266870239113687645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138383111511246826075791763 207574667266870239113687645)
              ·
                refine ⟨77840500225076339667632867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207574667266870239113687645 77840500225076339667632867)
                ·
                  refine ⟨116760750337614509501449301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77840500225076339667632867 116760750337614509501449301)
                  ·
                    refine ⟨1368290043018920033220109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116760750337614509501449301 1368290043018920033220109)
                    ·
                      rfl

theorem cell22_3997103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_3997103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997103 prefixEnd_3997103 := by exact prefixLift 3997103
  have htrace : WordTrace (prefixWord ++ tailWord_3997103) baseStart_3997103 baseEnd_3997103 := by
    simpa [prefixWord, tailWord_3997103, baseEnd_3997103] using wordTrace_append hprefix tailTrace_3997103
  have hstable : (prefixWord ++ tailWord_3997103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997103).length < 2 ^ (prefixWord ++ tailWord_3997103).sum := by decide
  have hdescent : baseEnd_3997103 < baseStart_3997103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997124 : List Nat := [2, 3, 3, 2, 1, 3, 2, 6]
def baseStart_3997124 : Nat := 118140960795 + 3997124 * 2 ^ 59
def prefixEnd_3997124 : Nat := 4983230072969 + 3 ^ 40 * 3997124 * 2
def baseEnd_3997124 : Nat := 152033025749786997605005

theorem tailTrace_3997124 : CollatzResearch.WordTrace tailWord_3997124 prefixEnd_3997124 152033025749786997605005 := by
  unfold tailWord_3997124
  simp only [CollatzResearch.WordTrace]
  refine ⟨72893544585554938637707213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97191392780739918183609617 72893544585554938637707213)
  ·
    refine ⟨27335079219583101989140205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72893544585554938637707213 27335079219583101989140205)
    ·
      refine ⟨10250654707343663245927577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27335079219583101989140205 10250654707343663245927577)
      ·
        refine ⟨7687991030507747434445683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10250654707343663245927577 7687991030507747434445683)
        ·
          refine ⟨11531986545761621151668525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7687991030507747434445683 11531986545761621151668525)
          ·
            refine ⟨4324494954660607931875697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11531986545761621151668525 4324494954660607931875697)
            ·
              refine ⟨3243371215995455948906773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4324494954660607931875697 3243371215995455948906773)
              ·
                refine ⟨152033025749786997605005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3243371215995455948906773 152033025749786997605005)
                ·
                  rfl

theorem cell22_3997124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 6].length) (baseStart_3997124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997124 prefixEnd_3997124 := by exact prefixLift 3997124
  have htrace : WordTrace (prefixWord ++ tailWord_3997124) baseStart_3997124 baseEnd_3997124 := by
    simpa [prefixWord, tailWord_3997124, baseEnd_3997124] using wordTrace_append hprefix tailTrace_3997124
  have hstable : (prefixWord ++ tailWord_3997124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997124).length < 2 ^ (prefixWord ++ tailWord_3997124).sum := by decide
  have hdescent : baseEnd_3997124 < baseStart_3997124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997169 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 5]
def baseStart_3997169 : Nat := 118140960795 + 3997169 * 2 ^ 59
def prefixEnd_3997169 : Nat := 4983230072969 + 3 ^ 40 * 3997169 * 2
def baseEnd_3997169 : Nat := 456104212055905953689969

theorem tailTrace_3997169 : CollatzResearch.WordTrace tailWord_3997169 prefixEnd_3997169 456104212055905953689969 := by
  unfold tailWord_3997169
  simp only [CollatzResearch.WordTrace]
  refine ⟨145788730455946849960802561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97192486970631233307201707 145788730455946849960802561)
  ·
    refine ⟨109341547841960137470601921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145788730455946849960802561 109341547841960137470601921)
    ·
      refine ⟨82006160881470103102951441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109341547841960137470601921 82006160881470103102951441)
      ·
        refine ⟨61504620661102577327213581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82006160881470103102951441 61504620661102577327213581)
        ·
          refine ⟨23064232747913466497705093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61504620661102577327213581 23064232747913466497705093)
          ·
            refine ⟨4324543640233774968319705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23064232747913466497705093 4324543640233774968319705)
            ·
              refine ⟨3243407730175331226239779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4324543640233774968319705 3243407730175331226239779)
              ·
                refine ⟨4865111595262996839359669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243407730175331226239779 4865111595262996839359669)
                ·
                  refine ⟨456104212055905953689969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4865111595262996839359669 456104212055905953689969)
                  ·
                    rfl

theorem cell22_3997169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_3997169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997169 prefixEnd_3997169 := by exact prefixLift 3997169
  have htrace : WordTrace (prefixWord ++ tailWord_3997169) baseStart_3997169 baseEnd_3997169 := by
    simpa [prefixWord, tailWord_3997169, baseEnd_3997169] using wordTrace_append hprefix tailTrace_3997169
  have hstable : (prefixWord ++ tailWord_3997169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997169).length < 2 ^ (prefixWord ++ tailWord_3997169).sum := by decide
  have hdescent : baseEnd_3997169 < baseStart_3997169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997180 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 6]
def baseStart_3997180 : Nat := 118140960795 + 3997180 * 2 ^ 59
def prefixEnd_3997180 : Nat := 4983230072969 + 3 ^ 40 * 3997180 * 2
def baseEnd_3997180 : Nat := 456105467230839166348291

theorem tailTrace_3997180 : CollatzResearch.WordTrace tailWord_3997180 prefixEnd_3997180 456105467230839166348291 := by
  unfold tailWord_3997180
  simp only [CollatzResearch.WordTrace]
  refine ⟨72894565829453499419726497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97192754439271332559635329 72894565829453499419726497)
  ·
    refine ⟨54670924372090124564794873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72894565829453499419726497 54670924372090124564794873)
    ·
      refine ⟨41003193279067593423596155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54670924372090124564794873 41003193279067593423596155)
      ·
        refine ⟨61504789918601390135394233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41003193279067593423596155 61504789918601390135394233)
        ·
          refine ⟨46128592438951042601545675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61504789918601390135394233 46128592438951042601545675)
          ·
            refine ⟨69192888658426563902318513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46128592438951042601545675 69192888658426563902318513)
            ·
              refine ⟨51894666493819922926738885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69192888658426563902318513 51894666493819922926738885)
              ·
                refine ⟨9730249967591235548763541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51894666493819922926738885 9730249967591235548763541)
                ·
                  refine ⟨456105467230839166348291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9730249967591235548763541 456105467230839166348291)
                  ·
                    rfl

theorem cell22_3997180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_3997180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997180 prefixEnd_3997180 := by exact prefixLift 3997180
  have htrace : WordTrace (prefixWord ++ tailWord_3997180) baseStart_3997180 baseEnd_3997180 := by
    simpa [prefixWord, tailWord_3997180, baseEnd_3997180] using wordTrace_append hprefix tailTrace_3997180
  have hstable : (prefixWord ++ tailWord_3997180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997180).length < 2 ^ (prefixWord ++ tailWord_3997180).sum := by decide
  have hdescent : baseEnd_3997180 < baseStart_3997180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997210 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_3997210 : Nat := 118140960795 + 3997210 * 2 ^ 59
def prefixEnd_3997210 : Nat := 4983230072969 + 3 ^ 40 * 3997210 * 2
def baseEnd_3997210 : Nat := 1368326671305607420794781

theorem tailTrace_3997210 : CollatzResearch.WordTrace tailWord_3997210 prefixEnd_3997210 1368326671305607420794781 := by
  unfold tailWord_3997210
  simp only [CollatzResearch.WordTrace]
  refine ⟨36447556462199578490761271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97193483899198875975363389 36447556462199578490761271)
  ·
    refine ⟨54671334693299367736141907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36447556462199578490761271 54671334693299367736141907)
    ·
      refine ⟨82007002039949051604212861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54671334693299367736141907 82007002039949051604212861)
      ·
        refine ⟨30752625764980894351579823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82007002039949051604212861 30752625764980894351579823)
        ·
          refine ⟨46128938647471341527369735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30752625764980894351579823 46128938647471341527369735)
          ·
            refine ⟨69193407971207012291054603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46128938647471341527369735 69193407971207012291054603)
            ·
              refine ⟨103790111956810518436581905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69193407971207012291054603 103790111956810518436581905)
              ·
                refine ⟨77842583967607888827436429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103790111956810518436581905 77842583967607888827436429)
                ·
                  refine ⟨29190968987852958310288661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77842583967607888827436429 29190968987852958310288661)
                  ·
                    refine ⟨1368326671305607420794781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29190968987852958310288661 1368326671305607420794781)
                    ·
                      rfl

theorem cell22_3997210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_3997210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997210 prefixEnd_3997210 := by exact prefixLift 3997210
  have htrace : WordTrace (prefixWord ++ tailWord_3997210) baseStart_3997210 baseEnd_3997210 := by
    simpa [prefixWord, tailWord_3997210, baseEnd_3997210] using wordTrace_append hprefix tailTrace_3997210
  have hstable : (prefixWord ++ tailWord_3997210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997210).length < 2 ^ (prefixWord ++ tailWord_3997210).sum := by decide
  have hdescent : baseEnd_3997210 < baseStart_3997210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997242 : List Nat := [3, 1, 1, 1, 3, 2, 5, 6]
def baseStart_3997242 : Nat := 118140960795 + 3997242 * 2 ^ 59
def prefixEnd_3997242 : Nat := 4983230072969 + 3 ^ 40 * 3997242 * 2
def baseEnd_3997242 : Nat := 152037513951063333777187

theorem tailTrace_3997242 : CollatzResearch.WordTrace tailWord_3997242 prefixEnd_3997242 152037513951063333777187 := by
  unfold tailWord_3997242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36447848246170595857052495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97194261989788255618806653 36447848246170595857052495)
  ·
    refine ⟨54671772369255893785578743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36447848246170595857052495 54671772369255893785578743)
    ·
      refine ⟨82007658553883840678368115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54671772369255893785578743 82007658553883840678368115)
      ·
        refine ⟨123011487830825761017552173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82007658553883840678368115 123011487830825761017552173)
        ·
          refine ⟨46129307936559660381582065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123011487830825761017552173 46129307936559660381582065)
          ·
            refine ⟨34596980952419745286186549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46129307936559660381582065 34596980952419745286186549)
            ·
              refine ⟨3243466964289351120579989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34596980952419745286186549 3243466964289351120579989)
              ·
                refine ⟨152037513951063333777187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3243466964289351120579989 152037513951063333777187)
                ·
                  rfl

theorem cell22_3997242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_3997242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997242 prefixEnd_3997242 := by exact prefixLift 3997242
  have htrace : WordTrace (prefixWord ++ tailWord_3997242) baseStart_3997242 baseEnd_3997242 := by
    simpa [prefixWord, tailWord_3997242, baseEnd_3997242] using wordTrace_append hprefix tailTrace_3997242
  have hstable : (prefixWord ++ tailWord_3997242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997242).length < 2 ^ (prefixWord ++ tailWord_3997242).sum := by decide
  have hdescent : baseEnd_3997242 < baseStart_3997242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997287 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 5]
def baseStart_3997287 : Nat := 118140960795 + 3997287 * 2 ^ 59
def prefixEnd_3997287 : Nat := 4983230072969 + 3 ^ 40 * 3997287 * 2
def baseEnd_3997287 : Nat := 456117676659734962206515

theorem tailTrace_3997287 : CollatzResearch.WordTrace tailWord_3997287 prefixEnd_3997287 456117676659734962206515 := by
  unfold tailWord_3997287
  simp only [CollatzResearch.WordTrace]
  refine ⟨145793034269519356113598115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97195356179679570742398743 145793034269519356113598115)
  ·
    refine ⟨218689551404279034170397173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145793034269519356113598115 218689551404279034170397173)
    ·
      refine ⟨20502145444151159453474735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218689551404279034170397173 20502145444151159453474735)
      ·
        refine ⟨30753218166226739180212103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20502145444151159453474735 30753218166226739180212103)
        ·
          refine ⟨46129827249340108770318155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30753218166226739180212103 46129827249340108770318155)
          ·
            refine ⟨69194740874010163155477233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46129827249340108770318155 69194740874010163155477233)
            ·
              refine ⟨51896055655507622366607925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69194740874010163155477233 51896055655507622366607925)
              ·
                refine ⟨4865255217703839596869493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51896055655507622366607925 4865255217703839596869493)
                ·
                  refine ⟨456117676659734962206515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4865255217703839596869493 456117676659734962206515)
                  ·
                    rfl

theorem cell22_3997287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 5].length) (baseStart_3997287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997287 prefixEnd_3997287 := by exact prefixLift 3997287
  have htrace : WordTrace (prefixWord ++ tailWord_3997287) baseStart_3997287 baseEnd_3997287 := by
    simpa [prefixWord, tailWord_3997287, baseEnd_3997287] using wordTrace_append hprefix tailTrace_3997287
  have hstable : (prefixWord ++ tailWord_3997287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997287).length < 2 ^ (prefixWord ++ tailWord_3997287).sum := by decide
  have hdescent : baseEnd_3997287 < baseStart_3997287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997347 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 1, 5]
def baseStart_3997347 : Nat := 118140960795 + 3997347 * 2 ^ 59
def prefixEnd_3997347 : Nat := 4983230072969 + 3 ^ 40 * 3997347 * 2
def baseEnd_3997347 : Nat := 1368373569205384730119361

theorem tailTrace_3997347 : CollatzResearch.WordTrace tailWord_3997347 prefixEnd_3997347 1368373569205384730119361 := by
  unfold tailWord_3997347
  simp only [CollatzResearch.WordTrace]
  refine ⟨145795222649301986360782295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97196815099534657573854863 145795222649301986360782295)
  ·
    refine ⟨218692833973952979541173443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145795222649301986360782295 218692833973952979541173443)
    ·
      refine ⟨328039250960929469311760165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218692833973952979541173443 328039250960929469311760165)
      ·
        refine ⟨61507359555174275495955031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328039250960929469311760165 61507359555174275495955031)
        ·
          refine ⟨92261039332761413243932547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61507359555174275495955031 92261039332761413243932547)
          ·
            refine ⟨138391558999142119865898821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92261039332761413243932547 138391558999142119865898821)
            ·
              refine ⟨25948417312339147474856029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138391558999142119865898821 25948417312339147474856029)
              ·
                refine ⟨9730656492127180303071011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25948417312339147474856029 9730656492127180303071011)
                ·
                  refine ⟨14595984738190770454606517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9730656492127180303071011 14595984738190770454606517)
                  ·
                    refine ⟨1368373569205384730119361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14595984738190770454606517 1368373569205384730119361)
                    ·
                      rfl

theorem cell22_3997347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_3997347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997347 prefixEnd_3997347 := by exact prefixLift 3997347
  have htrace : WordTrace (prefixWord ++ tailWord_3997347) baseStart_3997347 baseEnd_3997347 := by
    simpa [prefixWord, tailWord_3997347, baseEnd_3997347] using wordTrace_append hprefix tailTrace_3997347
  have hstable : (prefixWord ++ tailWord_3997347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997347).length < 2 ^ (prefixWord ++ tailWord_3997347).sum := by decide
  have hdescent : baseEnd_3997347 < baseStart_3997347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997362 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3997362 : Nat := 118140960795 + 3997362 * 2 ^ 59
def prefixEnd_3997362 : Nat := 4983230072969 + 3 ^ 40 * 3997362 * 2
def baseEnd_3997362 : Nat := 1368378704011929690994315

theorem tailTrace_3997362 : CollatzResearch.WordTrace tailWord_3997362 prefixEnd_3997362 1368378704011929690994315 := by
  unfold tailWord_3997362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36448942436061910980644585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97197179829498429281718893 36448942436061910980644585)
  ·
    refine ⟨27336706827046433235483439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36448942436061910980644585 27336706827046433235483439)
    ·
      refine ⟨41005060240569649853225159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27336706827046433235483439 41005060240569649853225159)
      ·
        refine ⟨61507590360854474779837739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41005060240569649853225159 61507590360854474779837739)
        ·
          refine ⟨92261385541281712169756609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61507590360854474779837739 92261385541281712169756609)
          ·
            refine ⟨69196039155961284127317457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92261385541281712169756609 69196039155961284127317457)
            ·
              refine ⟨51897029366970963095488093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69196039155961284127317457 51897029366970963095488093)
              ·
                refine ⟨19461386012614111160808035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51897029366970963095488093 19461386012614111160808035)
                ·
                  refine ⟨29192079018921166741212053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19461386012614111160808035 29192079018921166741212053)
                  ·
                    refine ⟨1368378704011929690994315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29192079018921166741212053 1368378704011929690994315)
                    ·
                      rfl

theorem cell22_3997362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3997362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997362 prefixEnd_3997362 := by exact prefixLift 3997362
  have htrace : WordTrace (prefixWord ++ tailWord_3997362) baseStart_3997362 baseEnd_3997362 := by
    simpa [prefixWord, tailWord_3997362, baseEnd_3997362] using wordTrace_append hprefix tailTrace_3997362
  have hstable : (prefixWord ++ tailWord_3997362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997362).length < 2 ^ (prefixWord ++ tailWord_3997362).sum := by decide
  have hdescent : baseEnd_3997362 < baseStart_3997362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997377 : List Nat := [1, 2, 6, 13]
def baseStart_3997377 : Nat := 118140960795 + 3997377 * 2 ^ 59
def prefixEnd_3997377 : Nat := 4983230072969 + 3 ^ 40 * 3997377 * 2
def baseEnd_3997377 : Nat := 1877069737748250551261

theorem tailTrace_3997377 : CollatzResearch.WordTrace tailWord_3997377 prefixEnd_3997377 1877069737748250551261 := by
  unfold tailWord_3997377
  simp only [CollatzResearch.WordTrace]
  refine ⟨145796316839193301484374385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97197544559462200989582923 145796316839193301484374385)
  ·
    refine ⟨109347237629394976113280789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145796316839193301484374385 109347237629394976113280789)
    ·
      refine ⟨5125651763877889505310037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109347237629394976113280789 5125651763877889505310037)
      ·
        refine ⟨1877069737748250551261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 5125651763877889505310037 1877069737748250551261)
        ·
          rfl

theorem cell22_3997377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 13].length) (baseStart_3997377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997377 prefixEnd_3997377 := by exact prefixLift 3997377
  have htrace : WordTrace (prefixWord ++ tailWord_3997377) baseStart_3997377 baseEnd_3997377 := by
    simpa [prefixWord, tailWord_3997377, baseEnd_3997377] using wordTrace_append hprefix tailTrace_3997377
  have hstable : (prefixWord ++ tailWord_3997377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997377).length < 2 ^ (prefixWord ++ tailWord_3997377).sum := by decide
  have hdescent : baseEnd_3997377 < baseStart_3997377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997394 : List Nat := [3, 2, 2, 2, 2, 1, 3, 7]
def baseStart_3997394 : Nat := 118140960795 + 3997394 * 2 ^ 59
def prefixEnd_3997394 : Nat := 4983230072969 + 3 ^ 40 * 3997394 * 2
def baseEnd_3997394 : Nat := 152043295362876919354913

theorem tailTrace_3997394 : CollatzResearch.WordTrace tailWord_3997394 prefixEnd_3997394 152043295362876919354913 := by
  unfold tailWord_3997394
  simp only [CollatzResearch.WordTrace]
  refine ⟨36449234220032928346935809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97197957920087808925162157 36449234220032928346935809)
  ·
    refine ⟨27336925665024696260201857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36449234220032928346935809 27336925665024696260201857)
    ·
      refine ⟨20502694248768522195151393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27336925665024696260201857 20502694248768522195151393)
      ·
        refine ⟨15377020686576391646363545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20502694248768522195151393 15377020686576391646363545)
        ·
          refine ⟨11532765514932293734772659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15377020686576391646363545 11532765514932293734772659)
          ·
            refine ⟨17299148272398440602158989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11532765514932293734772659 17299148272398440602158989)
            ·
              refine ⟨6487180602149415225809621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17299148272398440602158989 6487180602149415225809621)
              ·
                refine ⟨152043295362876919354913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6487180602149415225809621 152043295362876919354913)
                ·
                  rfl

theorem cell22_3997394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_3997394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997394 prefixEnd_3997394 := by exact prefixLift 3997394
  have htrace : WordTrace (prefixWord ++ tailWord_3997394) baseStart_3997394 baseEnd_3997394 := by
    simpa [prefixWord, tailWord_3997394, baseEnd_3997394] using wordTrace_append hprefix tailTrace_3997394
  have hstable : (prefixWord ++ tailWord_3997394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997394).length < 2 ^ (prefixWord ++ tailWord_3997394).sum := by decide
  have hdescent : baseEnd_3997394 < baseStart_3997394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997407 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 2, 6]
def baseStart_3997407 : Nat := 118140960795 + 3997407 * 2 ^ 59
def prefixEnd_3997407 : Nat := 4983230072969 + 3 ^ 40 * 3997407 * 2
def baseEnd_3997407 : Nat := 1368394108431564573619177

theorem tailTrace_3997407 : CollatzResearch.WordTrace tailWord_3997407 prefixEnd_3997407 1368394108431564573619177 := by
  unfold tailWord_3997407
  simp only [CollatzResearch.WordTrace]
  refine ⟨145797411029084616607966475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97198274019389744405310983 145797411029084616607966475)
  ·
    refine ⟨218696116543626924911949713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145797411029084616607966475 218696116543626924911949713)
    ·
      refine ⟨164022087407720193683962285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218696116543626924911949713 164022087407720193683962285)
      ·
        refine ⟨61508282777895072631485857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164022087407720193683962285 61508282777895072631485857)
        ·
          refine ⟨46131212083421304473614393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61508282777895072631485857 46131212083421304473614393)
          ·
            refine ⟨34598409062565978355210795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46131212083421304473614393 34598409062565978355210795)
            ·
              refine ⟨51897613593848967532816193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34598409062565978355210795 51897613593848967532816193)
              ·
                refine ⟨38923210195386725649612145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51897613593848967532816193 38923210195386725649612145)
                ·
                  refine ⟨29192407646540044237209109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38923210195386725649612145 29192407646540044237209109)
                  ·
                    refine ⟨1368394108431564573619177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29192407646540044237209109 1368394108431564573619177)
                    ·
                      rfl

theorem cell22_3997407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_3997407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997407 prefixEnd_3997407 := by exact prefixLift 3997407
  have htrace : WordTrace (prefixWord ++ tailWord_3997407) baseStart_3997407 baseEnd_3997407 := by
    simpa [prefixWord, tailWord_3997407, baseEnd_3997407] using wordTrace_append hprefix tailTrace_3997407
  have hstable : (prefixWord ++ tailWord_3997407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997407).length < 2 ^ (prefixWord ++ tailWord_3997407).sum := by decide
  have hdescent : baseEnd_3997407 < baseStart_3997407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997411 : List Nat := [1, 1, 1, 7, 2, 1, 3, 6]
def baseStart_3997411 : Nat := 118140960795 + 3997411 * 2 ^ 59
def prefixEnd_3997411 : Nat := 4983230072969 + 3 ^ 40 * 3997411 * 2
def baseEnd_3997411 : Nat := 152043941968145544057685

theorem tailTrace_3997411 : CollatzResearch.WordTrace tailWord_3997411 prefixEnd_3997411 152043941968145544057685 := by
  unfold tailWord_3997411
  simp only [CollatzResearch.WordTrace]
  refine ⟨145797556921070125291112087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97198371280713416860741391 145797556921070125291112087)
  ·
    refine ⟨218696335381605187936668131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145797556921070125291112087 218696335381605187936668131)
    ·
      refine ⟨328044503072407781905002197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218696335381605187936668131 328044503072407781905002197)
      ·
        refine ⟨7688543040759557388398489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 328044503072407781905002197 7688543040759557388398489)
        ·
          refine ⟨5766407280569668041298867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7688543040759557388398489 5766407280569668041298867)
          ·
            refine ⟨8649610920854502061948301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766407280569668041298867 8649610920854502061948301)
            ·
              refine ⟨3243604095320438273230613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8649610920854502061948301 3243604095320438273230613)
              ·
                refine ⟨152043941968145544057685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3243604095320438273230613 152043941968145544057685)
                ·
                  rfl

theorem cell22_3997411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 6].length) (baseStart_3997411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997411 prefixEnd_3997411 := by exact prefixLift 3997411
  have htrace : WordTrace (prefixWord ++ tailWord_3997411) baseStart_3997411 baseEnd_3997411 := by
    simpa [prefixWord, tailWord_3997411, baseEnd_3997411] using wordTrace_append hprefix tailTrace_3997411
  have hstable : (prefixWord ++ tailWord_3997411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997411).length < 2 ^ (prefixWord ++ tailWord_3997411).sum := by decide
  have hdescent : baseEnd_3997411 < baseStart_3997411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997439 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 5]
def baseStart_3997439 : Nat := 118140960795 + 3997439 * 2 ^ 59
def prefixEnd_3997439 : Nat := 4983230072969 + 3 ^ 40 * 3997439 * 2
def baseEnd_3997439 : Nat := 456135020895175718939693

theorem tailTrace_3997439 : CollatzResearch.WordTrace tailWord_3997439 prefixEnd_3997439 456135020895175718939693 := by
  unfold tailWord_3997439
  simp only [CollatzResearch.WordTrace]
  refine ⟨145798578164968686073131371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97199052109979124048754247 145798578164968686073131371)
  ·
    refine ⟨218697867247453029109697057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145798578164968686073131371 218697867247453029109697057)
    ·
      refine ⟨164023400435589771832272793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218697867247453029109697057 164023400435589771832272793)
      ·
        refine ⟨123017550326692328874204595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164023400435589771832272793 123017550326692328874204595)
        ·
          refine ⟨184526325490038493311306893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123017550326692328874204595 184526325490038493311306893)
          ·
            refine ⟨69197372058764434991740085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184526325490038493311306893 69197372058764434991740085)
            ·
              refine ⟨6487253630509165780475633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69197372058764434991740085 6487253630509165780475633)
              ·
                refine ⟨4865440222881874335356725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6487253630509165780475633 4865440222881874335356725)
                ·
                  refine ⟨456135020895175718939693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4865440222881874335356725 456135020895175718939693)
                  ·
                    rfl

theorem cell22_3997439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 5].length) (baseStart_3997439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997439 prefixEnd_3997439 := by exact prefixLift 3997439
  have htrace : WordTrace (prefixWord ++ tailWord_3997439) baseStart_3997439 baseEnd_3997439 := by
    simpa [prefixWord, tailWord_3997439, baseEnd_3997439] using wordTrace_append hprefix tailTrace_3997439
  have hstable : (prefixWord ++ tailWord_3997439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997439).length < 2 ^ (prefixWord ++ tailWord_3997439).sum := by decide
  have hdescent : baseEnd_3997439 < baseStart_3997439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997454 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_3997454 : Nat := 118140960795 + 3997454 * 2 ^ 59
def prefixEnd_3997454 : Nat := 4983230072969 + 3 ^ 40 * 3997454 * 2
def baseEnd_3997454 : Nat := 1368410197492072117694033

theorem tailTrace_3997454 : CollatzResearch.WordTrace tailWord_3997454 prefixEnd_3997454 1368410197492072117694033 := by
  unfold tailWord_3997454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18224890657489292954365927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97199416839942895756618277 18224890657489292954365927)
  ·
    refine ⟨27337335986233939431548891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18224890657489292954365927 27337335986233939431548891)
    ·
      refine ⟨41006003979350909147323337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27337335986233939431548891 41006003979350909147323337)
      ·
        refine ⟨30754502984513181860492503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41006003979350909147323337 30754502984513181860492503)
        ·
          refine ⟨46131754476769772790738755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30754502984513181860492503 46131754476769772790738755)
          ·
            refine ⟨69197631715154659186108133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46131754476769772790738755 69197631715154659186108133)
            ·
              refine ⟨12974555946591498597395275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69197631715154659186108133 12974555946591498597395275)
              ·
                refine ⟨19461833919887247896092913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12974555946591498597395275 19461833919887247896092913)
                ·
                  refine ⟨14596375439915435922069685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19461833919887247896092913 14596375439915435922069685)
                  ·
                    refine ⟨1368410197492072117694033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14596375439915435922069685 1368410197492072117694033)
                    ·
                      rfl

theorem cell22_3997454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_3997454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997454 prefixEnd_3997454 := by exact prefixLift 3997454
  have htrace : WordTrace (prefixWord ++ tailWord_3997454) baseStart_3997454 baseEnd_3997454 := by
    simpa [prefixWord, tailWord_3997454, baseEnd_3997454] using wordTrace_append hprefix tailTrace_3997454
  have hstable : (prefixWord ++ tailWord_3997454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997454).length < 2 ^ (prefixWord ++ tailWord_3997454).sum := by decide
  have hdescent : baseEnd_3997454 < baseStart_3997454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997501 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 6]
def baseStart_3997501 : Nat := 118140960795 + 3997501 * 2 ^ 59
def prefixEnd_3997501 : Nat := 4983230072969 + 3 ^ 40 * 3997501 * 2
def baseEnd_3997501 : Nat := 456142095517526553922963

theorem tailTrace_3997501 : CollatzResearch.WordTrace tailWord_3997501 prefixEnd_3997501 456142095517526553922963 := by
  unfold tailWord_3997501
  simp only [CollatzResearch.WordTrace]
  refine ⟨145800839490744070661888357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97200559660496047107925571 145800839490744070661888357)
  ·
    refine ⟨27337657404514513249104067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145800839490744070661888357 27337657404514513249104067)
    ·
      refine ⟨41006486106771769873656101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27337657404514513249104067 41006486106771769873656101)
      ·
        refine ⟨7688716145019706851310519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41006486106771769873656101 7688716145019706851310519)
        ·
          refine ⟨11533074217529560276965779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688716145019706851310519 11533074217529560276965779)
          ·
            refine ⟨17299611326294340415448669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11533074217529560276965779 17299611326294340415448669)
            ·
              refine ⟨6487354247360377655793251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17299611326294340415448669 6487354247360377655793251)
              ·
                refine ⟨9731031371040566483689877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487354247360377655793251 9731031371040566483689877)
                ·
                  refine ⟨456142095517526553922963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9731031371040566483689877 456142095517526553922963)
                  ·
                    rfl

theorem cell22_3997501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_3997501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997501 prefixEnd_3997501 := by exact prefixLift 3997501
  have htrace : WordTrace (prefixWord ++ tailWord_3997501) baseStart_3997501 baseEnd_3997501 := by
    simpa [prefixWord, tailWord_3997501, baseEnd_3997501] using wordTrace_append hprefix tailTrace_3997501
  have hstable : (prefixWord ++ tailWord_3997501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997501).length < 2 ^ (prefixWord ++ tailWord_3997501).sum := by decide
  have hdescent : baseEnd_3997501 < baseStart_3997501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997514 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_3997514 : Nat := 118140960795 + 3997514 * 2 ^ 59
def prefixEnd_3997514 : Nat := 4983230072969 + 3 ^ 40 * 3997514 * 2
def baseEnd_3997514 : Nat := 1368430736718251961193849

theorem tailTrace_3997514 : CollatzResearch.WordTrace tailWord_3997514 prefixEnd_3997514 1368430736718251961193849 := by
  unfold tailWord_3997514
  simp only [CollatzResearch.WordTrace]
  refine ⟨36450328409924243470527899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97200875759797982588074397 36450328409924243470527899)
  ·
    refine ⟨54675492614886365205791849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36450328409924243470527899 54675492614886365205791849)
    ·
      refine ⟨41006619461164773904343887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54675492614886365205791849 41006619461164773904343887)
      ·
        refine ⟨61509929191747160856515831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41006619461164773904343887 61509929191747160856515831)
        ·
          refine ⟨92264893787620741284773747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61509929191747160856515831 92264893787620741284773747)
          ·
            refine ⟨138397340681431111927160621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92264893787620741284773747 138397340681431111927160621)
            ·
              refine ⟨51899002755536666972685233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138397340681431111927160621 51899002755536666972685233)
              ·
                refine ⟨38924252066652500229513925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51899002755536666972685233 38924252066652500229513925)
                ·
                  refine ⟨7298297262497343793033861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38924252066652500229513925 7298297262497343793033861)
                  ·
                    refine ⟨1368430736718251961193849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7298297262497343793033861 1368430736718251961193849)
                    ·
                      rfl

theorem cell22_3997514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_3997514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997514 prefixEnd_3997514 := by exact prefixLift 3997514
  have htrace : WordTrace (prefixWord ++ tailWord_3997514) baseStart_3997514 baseEnd_3997514 := by
    simpa [prefixWord, tailWord_3997514, baseEnd_3997514] using wordTrace_append hprefix tailTrace_3997514
  have hstable : (prefixWord ++ tailWord_3997514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997514).length < 2 ^ (prefixWord ++ tailWord_3997514).sum := by decide
  have hdescent : baseEnd_3997514 < baseStart_3997514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997546 : List Nat := [3, 1, 3, 4, 1, 10]
def baseStart_3997546 : Nat := 118140960795 + 3997546 * 2 ^ 59
def prefixEnd_3997546 : Nat := 4983230072969 + 3 ^ 40 * 3997546 * 2
def baseEnd_3997546 : Nat := 16894341863854500548071

theorem tailTrace_3997546 : CollatzResearch.WordTrace tailWord_3997546 prefixEnd_3997546 16894341863854500548071 := by
  unfold tailWord_3997546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36450620193895260836819123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97201653850387362231517661 36450620193895260836819123)
  ·
    refine ⟨54675930290842891255228685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36450620193895260836819123 54675930290842891255228685)
    ·
      refine ⟨20503473859066084220710757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54675930290842891255228685 20503473859066084220710757)
      ·
        refine ⟨3844401348574890791383267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20503473859066084220710757 3844401348574890791383267)
        ·
          refine ⟨5766602022862336187074901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844401348574890791383267 5766602022862336187074901)
          ·
            refine ⟨16894341863854500548071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5766602022862336187074901 16894341863854500548071)
            ·
              rfl

theorem cell22_3997546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 10].length) (baseStart_3997546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997546 prefixEnd_3997546 := by exact prefixLift 3997546
  have htrace : WordTrace (prefixWord ++ tailWord_3997546) baseStart_3997546 baseEnd_3997546 := by
    simpa [prefixWord, tailWord_3997546, baseEnd_3997546] using wordTrace_append hprefix tailTrace_3997546
  have hstable : (prefixWord ++ tailWord_3997546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997546).length < 2 ^ (prefixWord ++ tailWord_3997546).sum := by decide
  have hdescent : baseEnd_3997546 < baseStart_3997546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997550 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_3997550 : Nat := 118140960795 + 3997550 * 2 ^ 59
def prefixEnd_3997550 : Nat := 4983230072969 + 3 ^ 40 * 3997550 * 2
def baseEnd_3997550 : Nat := 1368443060253959867293739

theorem tailTrace_3997550 : CollatzResearch.WordTrace tailWord_3997550 prefixEnd_3997550 1368443060253959867293739 := by
  unfold tailWord_3997550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18225328333445819003802763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97201751111711034686948069 18225328333445819003802763)
  ·
    refine ⟨27337992500168728505704145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18225328333445819003802763 27337992500168728505704145)
    ·
      refine ⟨20503494375126546379278109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27337992500168728505704145 20503494375126546379278109)
      ·
        refine ⟨7688810390672454892229291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20503494375126546379278109 7688810390672454892229291)
        ·
          refine ⟨11533215586008682338343937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688810390672454892229291 11533215586008682338343937)
          ·
            refine ⟨8649911689506511753757953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11533215586008682338343937 8649911689506511753757953)
            ·
              refine ⟨6487433767129883815318465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8649911689506511753757953 6487433767129883815318465)
              ·
                refine ⟨4865575325347412861488849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6487433767129883815318465 4865575325347412861488849)
                ·
                  refine ⟨3649181494010559646116637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4865575325347412861488849 3649181494010559646116637)
                  ·
                    refine ⟨1368443060253959867293739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649181494010559646116637 1368443060253959867293739)
                    ·
                      rfl

theorem cell22_3997550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_3997550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997550 prefixEnd_3997550 := by exact prefixLift 3997550
  have htrace : WordTrace (prefixWord ++ tailWord_3997550) baseStart_3997550 baseEnd_3997550 := by
    simpa [prefixWord, tailWord_3997550, baseEnd_3997550] using wordTrace_append hprefix tailTrace_3997550
  have hstable : (prefixWord ++ tailWord_3997550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997550).length < 2 ^ (prefixWord ++ tailWord_3997550).sum := by decide
  have hdescent : baseEnd_3997550 < baseStart_3997550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997561 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 3, 3]
def baseStart_3997561 : Nat := 118140960795 + 3997561 * 2 ^ 59
def prefixEnd_3997561 : Nat := 4983230072969 + 3 ^ 40 * 3997561 * 2
def baseEnd_3997561 : Nat := 1368446825778759505268705

theorem tailTrace_3997561 : CollatzResearch.WordTrace tailWord_3997561 prefixEnd_3997561 1368446825778759505268705 := by
  unfold tailWord_3997561
  simp only [CollatzResearch.WordTrace]
  refine ⟨145803027870526700909072537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97202018580351133939381691 145803027870526700909072537)
  ·
    refine ⟨109352270902895025681804403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145803027870526700909072537 109352270902895025681804403)
    ·
      refine ⟨164028406354342538522706605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109352270902895025681804403 164028406354342538522706605)
      ·
        refine ⟨61510652382878451946014977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164028406354342538522706605 61510652382878451946014977)
        ·
          refine ⟨46132989287158838959511233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61510652382878451946014977 46132989287158838959511233)
          ·
            refine ⟨34599741965369129219633425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46132989287158838959511233 34599741965369129219633425)
            ·
              refine ⟨25949806474026846914725069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34599741965369129219633425 25949806474026846914725069)
              ·
                refine ⟨9731177427760067593021901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25949806474026846914725069 9731177427760067593021901)
                ·
                  refine ⟨3649191535410025347383213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9731177427760067593021901 3649191535410025347383213)
                  ·
                    refine ⟨1368446825778759505268705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649191535410025347383213 1368446825778759505268705)
                    ·
                      rfl

theorem cell22_3997561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_3997561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997561 prefixEnd_3997561 := by exact prefixLift 3997561
  have htrace : WordTrace (prefixWord ++ tailWord_3997561) baseStart_3997561 baseEnd_3997561 := by
    simpa [prefixWord, tailWord_3997561, baseEnd_3997561] using wordTrace_append hprefix tailTrace_3997561
  have hstable : (prefixWord ++ tailWord_3997561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997561).length < 2 ^ (prefixWord ++ tailWord_3997561).sum := by decide
  have hdescent : baseEnd_3997561 < baseStart_3997561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997582 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_3997582 : Nat := 118140960795 + 3997582 * 2 ^ 59
def prefixEnd_3997582 : Nat := 4983230072969 + 3 ^ 40 * 3997582 * 2
def baseEnd_3997582 : Nat := 1368454014507922450493641

theorem tailTrace_3997582 : CollatzResearch.WordTrace tailWord_3997582 prefixEnd_3997582 1368454014507922450493641 := by
  unfold tailWord_3997582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18225474225431327686948375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97202529202300414330391333 18225474225431327686948375)
  ·
    refine ⟨27338211338146991530422563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18225474225431327686948375 27338211338146991530422563)
    ·
      refine ⟨41007317007220487295633845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27338211338146991530422563 41007317007220487295633845)
      ·
        refine ⟨3844435969426920683965673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41007317007220487295633845 3844435969426920683965673)
        ·
          refine ⟨2883326977070190512974255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3844435969426920683965673 2883326977070190512974255)
          ·
            refine ⟨4324990465605285769461383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883326977070190512974255 4324990465605285769461383)
            ·
              refine ⟨6487485698407928654192075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324990465605285769461383 6487485698407928654192075)
              ·
                refine ⟨9731228547611892981288113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487485698407928654192075 9731228547611892981288113)
                ·
                  refine ⟨7298421410708919735966085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9731228547611892981288113 7298421410708919735966085)
                  ·
                    refine ⟨1368454014507922450493641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7298421410708919735966085 1368454014507922450493641)
                    ·
                      rfl

theorem cell22_3997582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_3997582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997582 prefixEnd_3997582 := by exact prefixLift 3997582
  have htrace : WordTrace (prefixWord ++ tailWord_3997582) baseStart_3997582 baseEnd_3997582 := by
    simpa [prefixWord, tailWord_3997582, baseEnd_3997582] using wordTrace_append hprefix tailTrace_3997582
  have hstable : (prefixWord ++ tailWord_3997582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997582).length < 2 ^ (prefixWord ++ tailWord_3997582).sum := by decide
  have hdescent : baseEnd_3997582 < baseStart_3997582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997589 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3997589 : Nat := 118140960795 + 3997589 * 2 ^ 59
def prefixEnd_3997589 : Nat := 4983230072969 + 3 ^ 40 * 3997589 * 2
def baseEnd_3997589 : Nat := 1368456410750976765568619

theorem tailTrace_3997589 : CollatzResearch.WordTrace tailWord_3997589 prefixEnd_3997589 1368456410750976765568619 := by
  unfold tailWord_3997589
  simp only [CollatzResearch.WordTrace]
  refine ⟨145804049114425261691091821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97202699409616841127394547 145804049114425261691091821)
  ·
    refine ⟨54676518417909473134159433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145804049114425261691091821 54676518417909473134159433)
    ·
      refine ⟨41007388813432104850619575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54676518417909473134159433 41007388813432104850619575)
      ·
        refine ⟨61511083220148157275929363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41007388813432104850619575 61511083220148157275929363)
        ·
          refine ⟨92266624830222235913894045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61511083220148157275929363 92266624830222235913894045)
          ·
            refine ⟨34599984311333338467710267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92266624830222235913894045 34599984311333338467710267)
            ·
              refine ⟨51899976467000007701565401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34599984311333338467710267 51899976467000007701565401)
              ·
                refine ⟨38924982350250005776174051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51899976467000007701565401 38924982350250005776174051)
                ·
                  refine ⟨58387473525375008664261077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38924982350250005776174051 58387473525375008664261077)
                  ·
                    refine ⟨1368456410750976765568619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58387473525375008664261077 1368456410750976765568619)
                    ·
                      rfl

theorem cell22_3997589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3997589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997589 prefixEnd_3997589 := by exact prefixLift 3997589
  have htrace : WordTrace (prefixWord ++ tailWord_3997589) baseStart_3997589 baseEnd_3997589 := by
    simpa [prefixWord, tailWord_3997589, baseEnd_3997589] using wordTrace_append hprefix tailTrace_3997589
  have hstable : (prefixWord ++ tailWord_3997589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997589).length < 2 ^ (prefixWord ++ tailWord_3997589).sum := by decide
  have hdescent : baseEnd_3997589 < baseStart_3997589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997668 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_3997668 : Nat := 118140960795 + 3997668 * 2 ^ 59
def prefixEnd_3997668 : Nat := 4983230072969 + 3 ^ 40 * 3997668 * 2
def baseEnd_3997668 : Nat := 1368483454065446892843377

theorem tailTrace_3997668 : CollatzResearch.WordTrace tailWord_3997668 prefixEnd_3997668 1368483454065446892843377 := by
  unfold tailWord_3997668
  simp only [CollatzResearch.WordTrace]
  refine ⟨72903465240569529091608829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97204620320759372122145105 72903465240569529091608829)
  ·
    refine ⟨27338799465213573409353311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72903465240569529091608829 27338799465213573409353311)
    ·
      refine ⟨41008199197820360114029967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27338799465213573409353311 41008199197820360114029967)
      ·
        refine ⟨61512298796730540171044951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41008199197820360114029967 61512298796730540171044951)
        ·
          refine ⟨92268448195095810256567427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61512298796730540171044951 92268448195095810256567427)
          ·
            refine ⟨138402672292643715384851141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92268448195095810256567427 138402672292643715384851141)
            ·
              refine ⟨25950501054870696634659589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138402672292643715384851141 25950501054870696634659589)
              ·
                refine ⟨4865718947788255618998673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25950501054870696634659589 4865718947788255618998673)
                ·
                  refine ⟨3649289210841191714249005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4865718947788255618998673 3649289210841191714249005)
                  ·
                    refine ⟨1368483454065446892843377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649289210841191714249005 1368483454065446892843377)
                    ·
                      rfl

theorem cell22_3997668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_3997668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997668 prefixEnd_3997668 := by exact prefixLift 3997668
  have htrace : WordTrace (prefixWord ++ tailWord_3997668) baseStart_3997668 baseEnd_3997668 := by
    simpa [prefixWord, tailWord_3997668, baseEnd_3997668] using wordTrace_append hprefix tailTrace_3997668
  have hstable : (prefixWord ++ tailWord_3997668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997668).length < 2 ^ (prefixWord ++ tailWord_3997668).sum := by decide
  have hdescent : baseEnd_3997668 < baseStart_3997668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997788 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 6]
def baseStart_3997788 : Nat := 118140960795 + 3997788 * 2 ^ 59
def prefixEnd_3997788 : Nat := 4983230072969 + 3 ^ 40 * 3997788 * 2
def baseEnd_3997788 : Nat := 456174844172602193281003

theorem tailTrace_3997788 : CollatzResearch.WordTrace tailWord_3997788 prefixEnd_3997788 456174844172602193281003 := by
  unfold tailWord_3997788
  simp only [CollatzResearch.WordTrace]
  refine ⟨72905653620352159338793009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97207538160469545785057345 72905653620352159338793009)
  ·
    refine ⟨54679240215264119504094757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72905653620352159338793009 54679240215264119504094757)
    ·
      refine ⟨10252357540362022407017767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54679240215264119504094757 10252357540362022407017767)
      ·
        refine ⟨15378536310543033610526651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10252357540362022407017767 15378536310543033610526651)
        ·
          refine ⟨23067804465814550415789977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15378536310543033610526651 23067804465814550415789977)
          ·
            refine ⟨17300853349360912811842483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23067804465814550415789977 17300853349360912811842483)
            ·
              refine ⟨25951280024041369217763725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17300853349360912811842483 25951280024041369217763725)
              ·
                refine ⟨9731730009015513456661397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25951280024041369217763725 9731730009015513456661397)
                ·
                  refine ⟨456174844172602193281003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9731730009015513456661397 456174844172602193281003)
                  ·
                    rfl

theorem cell22_3997788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_3997788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997788 prefixEnd_3997788 := by exact prefixLift 3997788
  have htrace : WordTrace (prefixWord ++ tailWord_3997788) baseStart_3997788 baseEnd_3997788 := by
    simpa [prefixWord, tailWord_3997788, baseEnd_3997788] using wordTrace_append hprefix tailTrace_3997788
  have hstable : (prefixWord ++ tailWord_3997788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997788).length < 2 ^ (prefixWord ++ tailWord_3997788).sum := by decide
  have hdescent : baseEnd_3997788 < baseStart_3997788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997801 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_3997801 : Nat := 118140960795 + 3997801 * 2 ^ 59
def prefixEnd_3997801 : Nat := 4983230072969 + 3 ^ 40 * 3997801 * 2
def baseEnd_3997801 : Nat := 1368528982683478879267969

theorem tailTrace_3997801 : CollatzResearch.WordTrace tailWord_3997801 prefixEnd_3997801 1368528982683478879267969 := by
  unfold tailWord_3997801
  simp only [CollatzResearch.WordTrace]
  refine ⟨145811781389657221897809257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97207854259771481265206171 145811781389657221897809257)
  ·
    refine ⟨109358836042242916423356943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145811781389657221897809257 109358836042242916423356943)
    ·
      refine ⟨164038254063364374635035415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109358836042242916423356943 164038254063364374635035415)
      ·
        refine ⟨246057381095046561952553123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164038254063364374635035415 246057381095046561952553123)
        ·
          refine ⟨369086071642569842928829685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246057381095046561952553123 369086071642569842928829685)
          ·
            refine ⟨34601819216490922774577783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369086071642569842928829685 34601819216490922774577783)
            ·
              refine ⟨51902728824736384161866675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34601819216490922774577783 51902728824736384161866675)
              ·
                refine ⟨77854093237104576242800013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51902728824736384161866675 77854093237104576242800013)
                ·
                  refine ⟨29195284963914216091050005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77854093237104576242800013 29195284963914216091050005)
                  ·
                    refine ⟨1368528982683478879267969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29195284963914216091050005 1368528982683478879267969)
                    ·
                      rfl

theorem cell22_3997801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_3997801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997801 prefixEnd_3997801 := by exact prefixLift 3997801
  have htrace : WordTrace (prefixWord ++ tailWord_3997801) baseStart_3997801 baseEnd_3997801 := by
    simpa [prefixWord, tailWord_3997801, baseEnd_3997801] using wordTrace_append hprefix tailTrace_3997801
  have hstable : (prefixWord ++ tailWord_3997801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997801).length < 2 ^ (prefixWord ++ tailWord_3997801).sum := by decide
  have hdescent : baseEnd_3997801 < baseStart_3997801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997850 : List Nat := [3, 1, 1, 5, 2, 1, 2, 7]
def baseStart_3997850 : Nat := 118140960795 + 3997850 * 2 ^ 59
def prefixEnd_3997850 : Nat := 4983230072969 + 3 ^ 40 * 3997850 * 2
def baseEnd_3997850 : Nat := 152060639598317676088091

theorem tailTrace_3997850 : CollatzResearch.WordTrace tailWord_3997850 prefixEnd_3997850 152060639598317676088091 := by
  unfold tailWord_3997850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36453392141619925816585751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97209045710986468844228669 36453392141619925816585751)
  ·
    refine ⟨54680088212429888724878627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36453392141619925816585751 54680088212429888724878627)
    ·
      refine ⟨82020132318644833087317941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54680088212429888724878627 82020132318644833087317941)
      ·
        refine ⟨7689387404872953101936057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82020132318644833087317941 7689387404872953101936057)
        ·
          refine ⟨5767040553654714826452043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7689387404872953101936057 5767040553654714826452043)
          ·
            refine ⟨8650560830482072239678065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767040553654714826452043 8650560830482072239678065)
            ·
              refine ⟨6487920622861554179758549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8650560830482072239678065 6487920622861554179758549)
              ·
                refine ⟨152060639598317676088091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6487920622861554179758549 152060639598317676088091)
                ·
                  rfl

theorem cell22_3997850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_3997850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997850 prefixEnd_3997850 := by exact prefixLift 3997850
  have htrace : WordTrace (prefixWord ++ tailWord_3997850) baseStart_3997850 baseEnd_3997850 := by
    simpa [prefixWord, tailWord_3997850, baseEnd_3997850] using wordTrace_append hprefix tailTrace_3997850
  have hstable : (prefixWord ++ tailWord_3997850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997850).length < 2 ^ (prefixWord ++ tailWord_3997850).sum := by decide
  have hdescent : baseEnd_3997850 < baseStart_3997850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997854 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3997854 : Nat := 118140960795 + 3997854 * 2 ^ 59
def prefixEnd_3997854 : Nat := 4983230072969 + 3 ^ 40 * 3997854 * 2
def baseEnd_3997854 : Nat := 1368547125666604407692807

theorem tailTrace_3997854 : CollatzResearch.WordTrace tailWord_3997854 prefixEnd_3997854 1368547125666604407692807 := by
  unfold tailWord_3997854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18226714307308151493686077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97209142972310141299659077 18226714307308151493686077)
  ·
    refine ⟨6835017865240556810132279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18226714307308151493686077 6835017865240556810132279)
    ·
      refine ⟨10252526797860835215198419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6835017865240556810132279 10252526797860835215198419)
      ·
        refine ⟨15378790196791252822797629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10252526797860835215198419 15378790196791252822797629)
        ·
          refine ⟨5767046323796719808549111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15378790196791252822797629 5767046323796719808549111)
          ·
            refine ⟨8650569485695079712823667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767046323796719808549111 8650569485695079712823667)
            ·
              refine ⟨12975854228542619569235501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650569485695079712823667 12975854228542619569235501)
              ·
                refine ⟨4865945335703482338463313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12975854228542619569235501 4865945335703482338463313)
                ·
                  refine ⟨3649459001777611753847485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4865945335703482338463313 3649459001777611753847485)
                  ·
                    refine ⟨1368547125666604407692807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649459001777611753847485 1368547125666604407692807)
                    ·
                      rfl

theorem cell22_3997854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3997854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997854 prefixEnd_3997854 := by exact prefixLift 3997854
  have htrace : WordTrace (prefixWord ++ tailWord_3997854) baseStart_3997854 baseEnd_3997854 := by
    simpa [prefixWord, tailWord_3997854, baseEnd_3997854] using wordTrace_append hprefix tailTrace_3997854
  have hstable : (prefixWord ++ tailWord_3997854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997854).length < 2 ^ (prefixWord ++ tailWord_3997854).sum := by decide
  have hdescent : baseEnd_3997854 < baseStart_3997854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997925 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_3997925 : Nat := 118140960795 + 3997925 * 2 ^ 59
def prefixEnd_3997925 : Nat := 4983230072969 + 3 ^ 40 * 3997925 * 2
def baseEnd_3997925 : Nat := 1368571430417583889167589

theorem tailTrace_3997925 : CollatzResearch.WordTrace tailWord_3997925 prefixEnd_3997925 1368571430417583889167589 := by
  unfold tailWord_3997925
  simp only [CollatzResearch.WordTrace]
  refine ⟨145816304041207991075323229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97210869360805327383548819 145816304041207991075323229)
  ·
    refine ⟨54681114015452996653246211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145816304041207991075323229 54681114015452996653246211)
    ·
      refine ⟨82021671023179494979869317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54681114015452996653246211 82021671023179494979869317)
      ·
        refine ⟨15379063316846155308725497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82021671023179494979869317 15379063316846155308725497)
        ·
          refine ⟨11534297487634616481544123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15379063316846155308725497 11534297487634616481544123)
          ·
            refine ⟨17301446231451924722316185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534297487634616481544123 17301446231451924722316185)
            ·
              refine ⟨12976084673588943541737139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17301446231451924722316185 12976084673588943541737139)
              ·
                refine ⟨19464127010383415312605709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12976084673588943541737139 19464127010383415312605709)
                ·
                  refine ⟨7299047628893780742227141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19464127010383415312605709 7299047628893780742227141)
                  ·
                    refine ⟨1368571430417583889167589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7299047628893780742227141 1368571430417583889167589)
                    ·
                      rfl

theorem cell22_3997925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_3997925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997925 prefixEnd_3997925 := by exact prefixLift 3997925
  have htrace : WordTrace (prefixWord ++ tailWord_3997925) baseStart_3997925 baseEnd_3997925 := by
    simpa [prefixWord, tailWord_3997925, baseEnd_3997925] using wordTrace_append hprefix tailTrace_3997925
  have hstable : (prefixWord ++ tailWord_3997925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997925).length < 2 ^ (prefixWord ++ tailWord_3997925).sum := by decide
  have hdescent : baseEnd_3997925 < baseStart_3997925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997955 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 4, 3]
def baseStart_3997955 : Nat := 118140960795 + 3997955 * 2 ^ 59
def prefixEnd_3997955 : Nat := 4983230072969 + 3 ^ 40 * 3997955 * 2
def baseEnd_3997955 : Nat := 1368581700030673810917497

theorem tailTrace_3997955 : CollatzResearch.WordTrace tailWord_3997955 prefixEnd_3997955 1368581700030673810917497 := by
  unfold tailWord_3997955
  simp only [CollatzResearch.WordTrace]
  refine ⟨145817398231099306198915319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97211598820732870799276879 145817398231099306198915319)
  ·
    refine ⟨218726097346648959298372979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145817398231099306198915319 218726097346648959298372979)
    ·
      refine ⟨328089146019973438947559469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218726097346648959298372979 328089146019973438947559469)
      ·
        refine ⟨123033429757490039605334801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328089146019973438947559469 123033429757490039605334801)
        ·
          refine ⟨92275072318117529704001101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123033429757490039605334801 92275072318117529704001101)
          ·
            refine ⟨34603152119294073639000413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92275072318117529704001101 34603152119294073639000413)
            ·
              refine ⟨12976182044735277614625155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34603152119294073639000413 12976182044735277614625155)
              ·
                refine ⟨19464273067102916421937733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12976182044735277614625155 19464273067102916421937733)
                ·
                  refine ⟨3649551200081796829113325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19464273067102916421937733 3649551200081796829113325)
                  ·
                    refine ⟨1368581700030673810917497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649551200081796829113325 1368581700030673810917497)
                    ·
                      rfl

theorem cell22_3997955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 3].length) (baseStart_3997955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997955 prefixEnd_3997955 := by exact prefixLift 3997955
  have htrace : WordTrace (prefixWord ++ tailWord_3997955) baseStart_3997955 baseEnd_3997955 := by
    simpa [prefixWord, tailWord_3997955, baseEnd_3997955] using wordTrace_append hprefix tailTrace_3997955
  have hstable : (prefixWord ++ tailWord_3997955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997955).length < 2 ^ (prefixWord ++ tailWord_3997955).sum := by decide
  have hdescent : baseEnd_3997955 < baseStart_3997955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997985 : List Nat := [1, 2, 3, 2, 1, 1, 6, 6]
def baseStart_3997985 : Nat := 118140960795 + 3997985 * 2 ^ 59
def prefixEnd_3997985 : Nat := 4983230072969 + 3 ^ 40 * 3997985 * 2
def baseEnd_3997985 : Nat := 152065774404862636963045

theorem tailTrace_3997985 : CollatzResearch.WordTrace tailWord_3997985 prefixEnd_3997985 152065774404862636963045 := by
  unfold tailWord_3997985
  simp only [CollatzResearch.WordTrace]
  refine ⟨145818492420990621322507409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97212328280660414215004939 145818492420990621322507409)
  ·
    refine ⟨109363869315742965991880557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145818492420990621322507409 109363869315742965991880557)
    ·
      refine ⟨41011450993403612246955209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109363869315742965991880557 41011450993403612246955209)
      ·
        refine ⟨30758588245052709185216407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41011450993403612246955209 30758588245052709185216407)
        ·
          refine ⟨46137882367579063777824611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30758588245052709185216407 46137882367579063777824611)
          ·
            refine ⟨69206823551368595666736917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46137882367579063777824611 69206823551368595666736917)
            ·
              refine ⟨3244069853970402921878293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69206823551368595666736917 3244069853970402921878293)
              ·
                refine ⟨152065774404862636963045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3244069853970402921878293 152065774404862636963045)
                ·
                  rfl

theorem cell22_3997985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 6].length) (baseStart_3997985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3997985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3997985 prefixEnd_3997985 := by exact prefixLift 3997985
  have htrace : WordTrace (prefixWord ++ tailWord_3997985) baseStart_3997985 baseEnd_3997985 := by
    simpa [prefixWord, tailWord_3997985, baseEnd_3997985] using wordTrace_append hprefix tailTrace_3997985
  have hstable : (prefixWord ++ tailWord_3997985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997985).length < 2 ^ (prefixWord ++ tailWord_3997985).sum := by decide
  have hdescent : baseEnd_3997985 < baseStart_3997985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998002 : List Nat := [3, 2, 1, 1, 6, 1, 8]
def baseStart_3998002 : Nat := 118140960795 + 3998002 * 2 ^ 59
def prefixEnd_3998002 : Nat := 4983230072969 + 3 ^ 40 * 3998002 * 2
def baseEnd_3998002 : Nat := 50688807003377087221939

theorem tailTrace_3998002 : CollatzResearch.WordTrace tailWord_3998002 prefixEnd_3998002 50688807003377087221939 := by
  unfold tailWord_3998002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36454778115482258306469065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97212741641286022150584173 36454778115482258306469065)
  ·
    refine ⟨27341083586611693729851799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36454778115482258306469065 27341083586611693729851799)
    ·
      refine ⟨41011625379917540594777699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27341083586611693729851799 41011625379917540594777699)
      ·
        refine ⟨61517438069876310892166549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41011625379917540594777699 61517438069876310892166549)
        ·
          refine ⟨2883629909525452073070307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61517438069876310892166549 2883629909525452073070307)
          ·
            refine ⟨4325444864288178109605461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883629909525452073070307 4325444864288178109605461)
            ·
              refine ⟨50688807003377087221939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4325444864288178109605461 50688807003377087221939)
              ·
                rfl

theorem cell22_3998002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 8].length) (baseStart_3998002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998002 prefixEnd_3998002 := by exact prefixLift 3998002
  have htrace : WordTrace (prefixWord ++ tailWord_3998002) baseStart_3998002 baseEnd_3998002 := by
    simpa [prefixWord, tailWord_3998002, baseEnd_3998002] using wordTrace_append hprefix tailTrace_3998002
  have hstable : (prefixWord ++ tailWord_3998002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998002).length < 2 ^ (prefixWord ++ tailWord_3998002).sum := by decide
  have hdescent : baseEnd_3998002 < baseStart_3998002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998102 : List Nat := [5, 3, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3998102 : Nat := 118140960795 + 3998102 * 2 ^ 59
def prefixEnd_3998102 : Nat := 4983230072969 + 3 ^ 40 * 3998102 * 2
def baseEnd_3998102 : Nat := 1368632021134814427492047

theorem tailTrace_3998102 : CollatzResearch.WordTrace tailWord_3998102 prefixEnd_3998102 1368632021134814427492047 := by
  unfold tailWord_3998102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113922485097921894032285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97215173174377833536344373 9113922485097921894032285)
  ·
    refine ⟨3417720931911720710262107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9113922485097921894032285 3417720931911720710262107)
    ·
      refine ⟨5126581397867581065393161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3417720931911720710262107 5126581397867581065393161)
      ·
        refine ⟨3844936048400685799044871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5126581397867581065393161 3844936048400685799044871)
        ·
          refine ⟨5767404072601028698567307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844936048400685799044871 5767404072601028698567307)
          ·
            refine ⟨8651106108901543047850961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767404072601028698567307 8651106108901543047850961)
            ·
              refine ⟨6488329581676157285888221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651106108901543047850961 6488329581676157285888221)
              ·
                refine ⟨2433123593128558982208083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6488329581676157285888221 2433123593128558982208083)
                ·
                  refine ⟨3649685389692838473312125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433123593128558982208083 3649685389692838473312125)
                  ·
                    refine ⟨1368632021134814427492047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649685389692838473312125 1368632021134814427492047)
                    ·
                      rfl

theorem cell22_3998102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3998102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998102 prefixEnd_3998102 := by exact prefixLift 3998102
  have htrace : WordTrace (prefixWord ++ tailWord_3998102) baseStart_3998102 baseEnd_3998102 := by
    simpa [prefixWord, tailWord_3998102, baseEnd_3998102] using wordTrace_append hprefix tailTrace_3998102
  have hstable : (prefixWord ++ tailWord_3998102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998102).length < 2 ^ (prefixWord ++ tailWord_3998102).sum := by decide
  have hdescent : baseEnd_3998102 < baseStart_3998102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998105 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_3998105 : Nat := 118140960795 + 3998105 * 2 ^ 59
def prefixEnd_3998105 : Nat := 4983230072969 + 3 ^ 40 * 3998105 * 2
def baseEnd_3998105 : Nat := 1368633048096123419667037

theorem tailTrace_3998105 : CollatzResearch.WordTrace tailWord_3998105 prefixEnd_3998105 1368633048096123419667037 := by
  unfold tailWord_3998105
  simp only [CollatzResearch.WordTrace]
  refine ⟨145822869180555881816875769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97215246120370587877917179 145822869180555881816875769)
  ·
    refine ⟨109367151885416911362656827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145822869180555881816875769 109367151885416911362656827)
    ·
      refine ⟨164050727828125367043985241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109367151885416911362656827 164050727828125367043985241)
      ·
        refine ⟨123038045871094025282988931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164050727828125367043985241 123038045871094025282988931)
        ·
          refine ⟨184557068806641037924483397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123038045871094025282988931 184557068806641037924483397)
          ·
            refine ⟨34604450401245194610840637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184557068806641037924483397 34604450401245194610840637)
            ·
              refine ⟨12976668900466947979065239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34604450401245194610840637 12976668900466947979065239)
              ·
                refine ⟨19465003350700421968597859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12976668900466947979065239 19465003350700421968597859)
                ·
                  refine ⟨29197505026050632952896789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19465003350700421968597859 29197505026050632952896789)
                  ·
                    refine ⟨1368633048096123419667037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29197505026050632952896789 1368633048096123419667037)
                    ·
                      rfl

theorem cell22_3998105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_3998105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998105 prefixEnd_3998105 := by exact prefixLift 3998105
  have htrace : WordTrace (prefixWord ++ tailWord_3998105) baseStart_3998105 baseEnd_3998105 := by
    simpa [prefixWord, tailWord_3998105, baseEnd_3998105] using wordTrace_append hprefix tailTrace_3998105
  have hstable : (prefixWord ++ tailWord_3998105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998105).length < 2 ^ (prefixWord ++ tailWord_3998105).sum := by decide
  have hdescent : baseEnd_3998105 < baseStart_3998105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998141 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_3998141 : Nat := 118140960795 + 3998141 * 2 ^ 59
def prefixEnd_3998141 : Nat := 4983230072969 + 3 ^ 40 * 3998141 * 2
def baseEnd_3998141 : Nat := 1368645371631831325766927

theorem tailTrace_3998141 : CollatzResearch.WordTrace tailWord_3998141 prefixEnd_3998141 1368645371631831325766927 := by
  unfold tailWord_3998141
  simp only [CollatzResearch.WordTrace]
  refine ⟨145824182208425459965186277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97216121472283639976790851 145824182208425459965186277)
  ·
    refine ⟨27342034164079773743472427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145824182208425459965186277 27342034164079773743472427)
    ·
      refine ⟨41013051246119660615208641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27342034164079773743472427 41013051246119660615208641)
      ·
        refine ⟨30759788434589745461406481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41013051246119660615208641 30759788434589745461406481)
        ·
          refine ⟨23069841325942309096054861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30759788434589745461406481 23069841325942309096054861)
          ·
            refine ⟨8651190497228365911020573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23069841325942309096054861 8651190497228365911020573)
            ·
              refine ⟨3244196436460637216632715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8651190497228365911020573 3244196436460637216632715)
              ·
                refine ⟨4866294654690955824949073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244196436460637216632715 4866294654690955824949073)
                ·
                  refine ⟨3649720991018216868711805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4866294654690955824949073 3649720991018216868711805)
                  ·
                    refine ⟨1368645371631831325766927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649720991018216868711805 1368645371631831325766927)
                    ·
                      rfl

theorem cell22_3998141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_3998141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998141 prefixEnd_3998141 := by exact prefixLift 3998141
  have htrace : WordTrace (prefixWord ++ tailWord_3998141) baseStart_3998141 baseEnd_3998141 := by
    simpa [prefixWord, tailWord_3998141, baseEnd_3998141] using wordTrace_append hprefix tailTrace_3998141
  have hstable : (prefixWord ++ tailWord_3998141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998141).length < 2 ^ (prefixWord ++ tailWord_3998141).sum := by decide
  have hdescent : baseEnd_3998141 < baseStart_3998141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998186 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_3998186 : Nat := 118140960795 + 3998186 * 2 ^ 59
def prefixEnd_3998186 : Nat := 4983230072969 + 3 ^ 40 * 3998186 * 2
def baseEnd_3998186 : Nat := 1368660776051466208391789

theorem tailTrace_3998186 : CollatzResearch.WordTrace tailWord_3998186 prefixEnd_3998186 1368660776051466208391789 := by
  unfold tailWord_3998186
  simp only [CollatzResearch.WordTrace]
  refine ⟨36456455873315608162643603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97217215662174955100382941 36456455873315608162643603)
  ·
    refine ⟨54684683809973412243965405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36456455873315608162643603 54684683809973412243965405)
    ·
      refine ⟨20506756428740029591487027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54684683809973412243965405 20506756428740029591487027)
      ·
        refine ⟨30760134643110044387230541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506756428740029591487027 30760134643110044387230541)
        ·
          refine ⟨11535050491166266645211453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30760134643110044387230541 11535050491166266645211453)
          ·
            refine ⟨4325643934187349991954295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11535050491166266645211453 4325643934187349991954295)
            ·
              refine ⟨6488465901281024987931443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4325643934187349991954295 6488465901281024987931443)
              ·
                refine ⟨9732698851921537481897165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488465901281024987931443 9732698851921537481897165)
                ·
                  refine ⟨3649762069470576555711437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9732698851921537481897165 3649762069470576555711437)
                  ·
                    refine ⟨1368660776051466208391789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649762069470576555711437 1368660776051466208391789)
                    ·
                      rfl

theorem cell22_3998186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_3998186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998186 prefixEnd_3998186 := by exact prefixLift 3998186
  have htrace : WordTrace (prefixWord ++ tailWord_3998186) baseStart_3998186 baseEnd_3998186 := by
    simpa [prefixWord, tailWord_3998186, baseEnd_3998186] using wordTrace_append hprefix tailTrace_3998186
  have hstable : (prefixWord ++ tailWord_3998186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998186).length < 2 ^ (prefixWord ++ tailWord_3998186).sum := by decide
  have hdescent : baseEnd_3998186 < baseStart_3998186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998242 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3998242 : Nat := 118140960795 + 3998242 * 2 ^ 59
def prefixEnd_3998242 : Nat := 4983230072969 + 3 ^ 40 * 3998242 * 2
def baseEnd_3998242 : Nat := 1368679945995900728991617

theorem tailTrace_3998242 : CollatzResearch.WordTrace tailWord_3998242 prefixEnd_3998242 1368679945995900728991617 := by
  unfold tailWord_3998242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36456966495264888553653245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97218577320706369476408653 36456966495264888553653245)
  ·
    refine ⟨13671362435724333207619967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36456966495264888553653245 13671362435724333207619967)
    ·
      refine ⟨20507043653586499811429951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13671362435724333207619967 20507043653586499811429951)
      ·
        refine ⟨30760565480379749717144927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20507043653586499811429951 30760565480379749717144927)
        ·
          refine ⟨46140848220569624575717391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30760565480379749717144927 46140848220569624575717391)
          ·
            refine ⟨69211272330854436863576087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46140848220569624575717391 69211272330854436863576087)
            ·
              refine ⟨103816908496281655295364131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69211272330854436863576087 103816908496281655295364131)
              ·
                refine ⟨155725362744422482943046197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103816908496281655295364131 155725362744422482943046197)
                ·
                  refine ⟨14599252757289607775910581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155725362744422482943046197 14599252757289607775910581)
                  ·
                    refine ⟨1368679945995900728991617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14599252757289607775910581 1368679945995900728991617)
                    ·
                      rfl

theorem cell22_3998242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3998242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998242 prefixEnd_3998242 := by exact prefixLift 3998242
  have htrace : WordTrace (prefixWord ++ tailWord_3998242) baseStart_3998242 baseEnd_3998242 := by
    simpa [prefixWord, tailWord_3998242, baseEnd_3998242] using wordTrace_append hprefix tailTrace_3998242
  have hstable : (prefixWord ++ tailWord_3998242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998242).length < 2 ^ (prefixWord ++ tailWord_3998242).sum := by decide
  have hdescent : baseEnd_3998242 < baseStart_3998242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998257 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_3998257 : Nat := 118140960795 + 3998257 * 2 ^ 59
def prefixEnd_3998257 : Nat := 4983230072969 + 3 ^ 40 * 3998257 * 2
def baseEnd_3998257 : Nat := 1368685080802445689866571

theorem tailTrace_3998257 : CollatzResearch.WordTrace tailWord_3998257 prefixEnd_3998257 1368685080802445689866571 := by
  unfold tailWord_3998257
  simp only [CollatzResearch.WordTrace]
  refine ⟨145828413076005211776409025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97218942050670141184272683 145828413076005211776409025)
  ·
    refine ⟨109371309807003908832306769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145828413076005211776409025 109371309807003908832306769)
    ·
      refine ⟨82028482355252931624230077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109371309807003908832306769 82028482355252931624230077)
      ·
        refine ⟨30760680883219849359086279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82028482355252931624230077 30760680883219849359086279)
        ·
          refine ⟨46141021324829774038629419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30760680883219849359086279 46141021324829774038629419)
          ·
            refine ⟨69211531987244661057944129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46141021324829774038629419 69211531987244661057944129)
            ·
              refine ⟨51908648990433495793458097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69211531987244661057944129 51908648990433495793458097)
              ·
                refine ⟨38931486742825121845093573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51908648990433495793458097 38931486742825121845093573)
                ·
                  refine ⟨7299653764279710345955045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38931486742825121845093573 7299653764279710345955045)
                  ·
                    refine ⟨1368685080802445689866571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7299653764279710345955045 1368685080802445689866571)
                    ·
                      rfl

theorem cell22_3998257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_3998257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998257 prefixEnd_3998257 := by exact prefixLift 3998257
  have htrace : WordTrace (prefixWord ++ tailWord_3998257) baseStart_3998257 baseEnd_3998257 := by
    simpa [prefixWord, tailWord_3998257, baseEnd_3998257] using wordTrace_append hprefix tailTrace_3998257
  have hstable : (prefixWord ++ tailWord_3998257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998257).length < 2 ^ (prefixWord ++ tailWord_3998257).sum := by decide
  have hdescent : baseEnd_3998257 < baseStart_3998257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998259 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 2, 3]
def baseStart_3998259 : Nat := 118140960795 + 3998259 * 2 ^ 59
def prefixEnd_3998259 : Nat := 4983230072969 + 3 ^ 40 * 3998259 * 2
def baseEnd_3998259 : Nat := 1368685765443318351316565

theorem tailTrace_3998259 : CollatzResearch.WordTrace tailWord_3998259 prefixEnd_3998259 1368685765443318351316565 := by
  unfold tailWord_3998259
  simp only [CollatzResearch.WordTrace]
  refine ⟨145828486021997966117981831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97218990681331977411987887 145828486021997966117981831)
  ·
    refine ⟨218742729032996949176972747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145828486021997966117981831 218742729032996949176972747)
    ·
      refine ⟨328114093549495423765459121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218742729032996949176972747 328114093549495423765459121)
      ·
        refine ⟨246085570162121567824094341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328114093549495423765459121 246085570162121567824094341)
        ·
          refine ⟨46141044405397793967017689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246085570162121567824094341 46141044405397793967017689)
          ·
            refine ⟨34605783304048345475263267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46141044405397793967017689 34605783304048345475263267)
            ·
              refine ⟨51908674956072518212894901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34605783304048345475263267 51908674956072518212894901)
              ·
                refine ⟨4866438277131798582458897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51908674956072518212894901 4866438277131798582458897)
                ·
                  refine ⟨3649828707848848936844173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4866438277131798582458897 3649828707848848936844173)
                  ·
                    refine ⟨1368685765443318351316565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649828707848848936844173 1368685765443318351316565)
                    ·
                      rfl

theorem cell22_3998259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 3].length) (baseStart_3998259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998259 prefixEnd_3998259 := by exact prefixLift 3998259
  have htrace : WordTrace (prefixWord ++ tailWord_3998259) baseStart_3998259 baseEnd_3998259 := by
    simpa [prefixWord, tailWord_3998259, baseEnd_3998259] using wordTrace_append hprefix tailTrace_3998259
  have hstable : (prefixWord ++ tailWord_3998259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998259).length < 2 ^ (prefixWord ++ tailWord_3998259).sum := by decide
  have hdescent : baseEnd_3998259 < baseStart_3998259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998278 : List Nat := [6, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3998278 : Nat := 118140960795 + 3998278 * 2 ^ 59
def prefixEnd_3998278 : Nat := 4983230072969 + 3 ^ 40 * 3998278 * 2
def baseEnd_3998278 : Nat := 456230756510536211697169

theorem tailTrace_3998278 : CollatzResearch.WordTrace tailWord_3998278 prefixEnd_3998278 456230756510536211697169 := by
  unfold tailWord_3998278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557161844029035386341359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97219452672619421575282325 4557161844029035386341359)
  ·
    refine ⟨6835742766043553079512039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4557161844029035386341359 6835742766043553079512039)
    ·
      refine ⟨10253614149065329619268059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6835742766043553079512039 10253614149065329619268059)
      ·
        refine ⟨15380421223597994428902089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253614149065329619268059 15380421223597994428902089)
        ·
          refine ⟨11535315917698495821676567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15380421223597994428902089 11535315917698495821676567)
          ·
            refine ⟨17302973876547743732514851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11535315917698495821676567 17302973876547743732514851)
            ·
              refine ⟨25954460814821615598772277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17302973876547743732514851 25954460814821615598772277)
              ·
                refine ⟨2433230701389526462384901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25954460814821615598772277 2433230701389526462384901)
                ·
                  refine ⟨456230756510536211697169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433230701389526462384901 456230756510536211697169)
                  ·
                    rfl

theorem cell22_3998278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3998278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998278 prefixEnd_3998278 := by exact prefixLift 3998278
  have htrace : WordTrace (prefixWord ++ tailWord_3998278) baseStart_3998278 baseEnd_3998278 := by
    simpa [prefixWord, tailWord_3998278, baseEnd_3998278] using wordTrace_append hprefix tailTrace_3998278
  have hstable : (prefixWord ++ tailWord_3998278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998278).length < 2 ^ (prefixWord ++ tailWord_3998278).sum := by decide
  have hdescent : baseEnd_3998278 < baseStart_3998278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998304 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 3, 3]
def baseStart_3998304 : Nat := 118140960795 + 3998304 * 2 ^ 59
def prefixEnd_3998304 : Nat := 4983230072969 + 3 ^ 40 * 3998304 * 2
def baseEnd_3998304 : Nat := 1368701169862953233941427

theorem tailTrace_3998304 : CollatzResearch.WordTrace tailWord_3998304 prefixEnd_3998304 1368701169862953233941427 := by
  unfold tailWord_3998304
  simp only [CollatzResearch.WordTrace]
  refine ⟨72915063653417469401684983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97220084871223292535579977 72915063653417469401684983)
  ·
    refine ⟨109372595480126204102527475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72915063653417469401684983 109372595480126204102527475)
    ·
      refine ⟨164058893220189306153791213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109372595480126204102527475 164058893220189306153791213)
      ·
        refine ⟨61522084957570989807671705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164058893220189306153791213 61522084957570989807671705)
        ·
          refine ⟨46141563718178242355753779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61522084957570989807671705 46141563718178242355753779)
          ·
            refine ⟨69212345577267363533630669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46141563718178242355753779 69212345577267363533630669)
            ·
              refine ⟨25954629591475261325111501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69212345577267363533630669 25954629591475261325111501)
              ·
                refine ⟨9732986096803222996916813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25954629591475261325111501 9732986096803222996916813)
                ·
                  refine ⟨3649869786301208623843805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9732986096803222996916813 3649869786301208623843805)
                  ·
                    refine ⟨1368701169862953233941427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649869786301208623843805 1368701169862953233941427)
                    ·
                      rfl

theorem cell22_3998304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_3998304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998304 prefixEnd_3998304 := by exact prefixLift 3998304
  have htrace : WordTrace (prefixWord ++ tailWord_3998304) baseStart_3998304 baseEnd_3998304 := by
    simpa [prefixWord, tailWord_3998304, baseEnd_3998304] using wordTrace_append hprefix tailTrace_3998304
  have hstable : (prefixWord ++ tailWord_3998304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998304).length < 2 ^ (prefixWord ++ tailWord_3998304).sum := by decide
  have hdescent : baseEnd_3998304 < baseStart_3998304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998332 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3998332 : Nat := 118140960795 + 3998332 * 2 ^ 59
def prefixEnd_3998332 : Nat := 4983230072969 + 3 ^ 40 * 3998332 * 2
def baseEnd_3998332 : Nat := 1368710754835170494241341

theorem tailTrace_3998332 : CollatzResearch.WordTrace tailWord_3998332 prefixEnd_3998332 1368710754835170494241341 := by
  unfold tailWord_3998332
  simp only [CollatzResearch.WordTrace]
  refine ⟨72915574275366749792694625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97220765700488999723592833 72915574275366749792694625)
  ·
    refine ⟨54686680706525062344520969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72915574275366749792694625 54686680706525062344520969)
    ·
      refine ⟨41015010529893796758390727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54686680706525062344520969 41015010529893796758390727)
      ·
        refine ⟨61522515794840695137586091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41015010529893796758390727 61522515794840695137586091)
        ·
          refine ⟨92283773692261042706379137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61522515794840695137586091 92283773692261042706379137)
          ·
            refine ⟨69212830269195782029784353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92283773692261042706379137 69212830269195782029784353)
            ·
              refine ⟨51909622701896836522338265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69212830269195782029784353 51909622701896836522338265)
              ·
                refine ⟨38932217026422627391753699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51909622701896836522338265 38932217026422627391753699)
                ·
                  refine ⟨58398325539633941087630549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38932217026422627391753699 58398325539633941087630549)
                  ·
                    refine ⟨1368710754835170494241341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58398325539633941087630549 1368710754835170494241341)
                    ·
                      rfl

theorem cell22_3998332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3998332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998332 prefixEnd_3998332 := by exact prefixLift 3998332
  have htrace : WordTrace (prefixWord ++ tailWord_3998332) baseStart_3998332 baseEnd_3998332 := by
    simpa [prefixWord, tailWord_3998332, baseEnd_3998332] using wordTrace_append hprefix tailTrace_3998332
  have hstable : (prefixWord ++ tailWord_3998332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998332).length < 2 ^ (prefixWord ++ tailWord_3998332).sum := by decide
  have hdescent : baseEnd_3998332 < baseStart_3998332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998368 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 5]
def baseStart_3998368 : Nat := 118140960795 + 3998368 * 2 ^ 59
def prefixEnd_3998368 : Nat := 4983230072969 + 3 ^ 40 * 3998368 * 2
def baseEnd_3998368 : Nat := 456241026123626133447077

theorem tailTrace_3998368 : CollatzResearch.WordTrace tailWord_3998368 prefixEnd_3998368 456241026123626133447077 := by
  unfold tailWord_3998368
  simp only [CollatzResearch.WordTrace]
  refine ⟨72916230789301538866849879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97221641052402051822466505 72916230789301538866849879)
  ·
    refine ⟨109374346183952308300274819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72916230789301538866849879 109374346183952308300274819)
    ·
      refine ⟨164061519275928462450412229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109374346183952308300274819 164061519275928462450412229)
      ·
        refine ⟨30761534864236586709452293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164061519275928462450412229 30761534864236586709452293)
        ·
          refine ⟨5767787787044360008022305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30761534864236586709452293 5767787787044360008022305)
          ·
            refine ⟨4325840840283270006016729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5767787787044360008022305 4325840840283270006016729)
            ·
              refine ⟨3244380630212452504512547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325840840283270006016729 3244380630212452504512547)
              ·
                refine ⟨4866570945318678756768821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244380630212452504512547 4866570945318678756768821)
                ·
                  refine ⟨456241026123626133447077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4866570945318678756768821 456241026123626133447077)
                  ·
                    rfl

theorem cell22_3998368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_3998368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998368 prefixEnd_3998368 := by exact prefixLift 3998368
  have htrace : WordTrace (prefixWord ++ tailWord_3998368) baseStart_3998368 baseEnd_3998368 := by
    simpa [prefixWord, tailWord_3998368, baseEnd_3998368] using wordTrace_append hprefix tailTrace_3998368
  have hstable : (prefixWord ++ tailWord_3998368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998368).length < 2 ^ (prefixWord ++ tailWord_3998368).sum := by decide
  have hdescent : baseEnd_3998368 < baseStart_3998368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998381 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3998381 : Nat := 118140960795 + 3998381 * 2 ^ 59
def prefixEnd_3998381 : Nat := 4983230072969 + 3 ^ 40 * 3998381 * 2
def baseEnd_3998381 : Nat := 1368727528536550699766191

theorem tailTrace_3998381 : CollatzResearch.WordTrace tailWord_3998381 prefixEnd_3998381 1368727528536550699766191 := by
  unfold tailWord_3998381
  simp only [CollatzResearch.WordTrace]
  refine ⟨145832935727555980953922997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97221957151703987302615331 145832935727555980953922997)
  ·
    refine ⟨13671837724458373214430281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145832935727555980953922997 13671837724458373214430281)
    ·
      refine ⟨10253878293343779910822711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13671837724458373214430281 10253878293343779910822711)
      ·
        refine ⟨15380817440015669866234067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253878293343779910822711 15380817440015669866234067)
        ·
          refine ⟨23071226160023504799351101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15380817440015669866234067 23071226160023504799351101)
          ·
            refine ⟨8651709810008814299756663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23071226160023504799351101 8651709810008814299756663)
            ·
              refine ⟨12977564715013221449634995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8651709810008814299756663 12977564715013221449634995)
              ·
                refine ⟨19466347072519832174452493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12977564715013221449634995 19466347072519832174452493)
                ·
                  refine ⟨7299880152194937065419685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19466347072519832174452493 7299880152194937065419685)
                  ·
                    refine ⟨1368727528536550699766191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7299880152194937065419685 1368727528536550699766191)
                    ·
                      rfl

theorem cell22_3998381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3998381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998381 prefixEnd_3998381 := by exact prefixLift 3998381
  have htrace : WordTrace (prefixWord ++ tailWord_3998381) baseStart_3998381 baseEnd_3998381 := by
    simpa [prefixWord, tailWord_3998381, baseEnd_3998381] using wordTrace_append hprefix tailTrace_3998381
  have hstable : (prefixWord ++ tailWord_3998381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998381).length < 2 ^ (prefixWord ++ tailWord_3998381).sum := by decide
  have hdescent : baseEnd_3998381 < baseStart_3998381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998394 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_3998394 : Nat := 118140960795 + 3998394 * 2 ^ 59
def prefixEnd_3998394 : Nat := 4983230072969 + 3 ^ 40 * 3998394 * 2
def baseEnd_3998394 : Nat := 1368731978702222999191151

theorem tailTrace_3998394 : CollatzResearch.WordTrace tailWord_3998394 prefixEnd_3998394 1368731978702222999191151 := by
  unfold tailWord_3998394
  simp only [CollatzResearch.WordTrace]
  refine ⟨36458352469127221043536559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97222273251005922782764157 36458352469127221043536559)
  ·
    refine ⟨54687528703690831565304839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36458352469127221043536559 54687528703690831565304839)
    ·
      refine ⟨82031293055536247347957259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54687528703690831565304839 82031293055536247347957259)
      ·
        refine ⟨123046939583304371021935889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82031293055536247347957259 123046939583304371021935889)
        ·
          refine ⟨92285204687478278266451917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123046939583304371021935889 92285204687478278266451917)
          ·
            refine ⟨34606951757804354349919469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92285204687478278266451917 34606951757804354349919469)
            ·
              refine ⟨12977606909176632881219801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34606951757804354349919469 12977606909176632881219801)
              ·
                refine ⟨9733205181882474660914851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12977606909176632881219801 9733205181882474660914851)
                ·
                  refine ⟨14599807772823711991372277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9733205181882474660914851 14599807772823711991372277)
                  ·
                    refine ⟨1368731978702222999191151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14599807772823711991372277 1368731978702222999191151)
                    ·
                      rfl

theorem cell22_3998394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_3998394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998394 prefixEnd_3998394 := by exact prefixLift 3998394
  have htrace : WordTrace (prefixWord ++ tailWord_3998394) baseStart_3998394 baseEnd_3998394 := by
    simpa [prefixWord, tailWord_3998394, baseEnd_3998394] using wordTrace_append hprefix tailTrace_3998394
  have hstable : (prefixWord ++ tailWord_3998394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998394).length < 2 ^ (prefixWord ++ tailWord_3998394).sum := by decide
  have hdescent : baseEnd_3998394 < baseStart_3998394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998396 : List Nat := [2, 2, 2, 3, 1, 1, 2, 5, 4]
def baseStart_3998396 : Nat := 118140960795 + 3998396 * 2 ^ 59
def prefixEnd_3998396 : Nat := 4983230072969 + 3 ^ 40 * 3998396 * 2
def baseEnd_3998396 : Nat := 456244221114365220213715

theorem tailTrace_3998396 : CollatzResearch.WordTrace tailWord_3998396 prefixEnd_3998396 456244221114365220213715 := by
  unfold tailWord_3998396
  simp only [CollatzResearch.WordTrace]
  refine ⟨72916741411250819257859521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97222321881667759010479361 72916741411250819257859521)
  ·
    refine ⟨54687556058438114443394641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72916741411250819257859521 54687556058438114443394641)
    ·
      refine ⟨41015667043828585832545981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54687556058438114443394641 41015667043828585832545981)
      ·
        refine ⟨15380875141435719687204743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41015667043828585832545981 15380875141435719687204743)
        ·
          refine ⟨23071312712153579530807115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15380875141435719687204743 23071312712153579530807115)
          ·
            refine ⟨34606969068230369296210673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23071312712153579530807115 34606969068230369296210673)
            ·
              refine ⟨25955226801172776972158005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34606969068230369296210673 25955226801172776972158005)
              ·
                refine ⟨2433302512609947841139813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25955226801172776972158005 2433302512609947841139813)
                ·
                  refine ⟨456244221114365220213715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433302512609947841139813 456244221114365220213715)
                  ·
                    rfl

theorem cell22_3998396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_3998396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998396 prefixEnd_3998396 := by exact prefixLift 3998396
  have htrace : WordTrace (prefixWord ++ tailWord_3998396) baseStart_3998396 baseEnd_3998396 := by
    simpa [prefixWord, tailWord_3998396, baseEnd_3998396] using wordTrace_append hprefix tailTrace_3998396
  have hstable : (prefixWord ++ tailWord_3998396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998396).length < 2 ^ (prefixWord ++ tailWord_3998396).sum := by decide
  have hdescent : baseEnd_3998396 < baseStart_3998396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998398 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3998398 : Nat := 118140960795 + 3998398 * 2 ^ 59
def prefixEnd_3998398 : Nat := 4983230072969 + 3 ^ 40 * 3998398 * 2
def baseEnd_3998398 : Nat := 1368733347983968322091139

theorem tailTrace_3998398 : CollatzResearch.WordTrace tailWord_3998398 prefixEnd_3998398 1368733347983968322091139 := by
  unfold tailWord_3998398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18229194471061799107161481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97222370512329595238194565 18229194471061799107161481)
  ·
    refine ⟨13671895853296349330371111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18229194471061799107161481 13671895853296349330371111)
    ·
      refine ⟨20507843779944523995556667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13671895853296349330371111 20507843779944523995556667)
      ·
        refine ⟨30761765669916785993335001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20507843779944523995556667 30761765669916785993335001)
        ·
          refine ⟨23071324252437589495001251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30761765669916785993335001 23071324252437589495001251)
          ·
            refine ⟨34606986378656384242501877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23071324252437589495001251 34606986378656384242501877)
            ·
              refine ⟨3244404972999036022734551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34606986378656384242501877 3244404972999036022734551)
              ·
                refine ⟨4866607459498554034101827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244404972999036022734551 4866607459498554034101827)
                ·
                  refine ⟨7299911189247831051152741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4866607459498554034101827 7299911189247831051152741)
                  ·
                    refine ⟨1368733347983968322091139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7299911189247831051152741 1368733347983968322091139)
                    ·
                      rfl

theorem cell22_3998398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3998398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998398 prefixEnd_3998398 := by exact prefixLift 3998398
  have htrace : WordTrace (prefixWord ++ tailWord_3998398) baseStart_3998398 baseEnd_3998398 := by
    simpa [prefixWord, tailWord_3998398, baseEnd_3998398] using wordTrace_append hprefix tailTrace_3998398
  have hstable : (prefixWord ++ tailWord_3998398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998398).length < 2 ^ (prefixWord ++ tailWord_3998398).sum := by decide
  have hdescent : baseEnd_3998398 < baseStart_3998398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998406 : List Nat := [6, 1, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3998406 : Nat := 118140960795 + 3998406 * 2 ^ 59
def prefixEnd_3998406 : Nat := 4983230072969 + 3 ^ 40 * 3998406 * 2
def baseEnd_3998406 : Nat := 1368736086547458967891115

theorem tailTrace_3998406 : CollatzResearch.WordTrace tailWord_3998406 prefixEnd_3998406 1368736086547458967891115 := by
  unfold tailWord_3998406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557307736014544069486971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97222565034976940149055381 4557307736014544069486971)
  ·
    refine ⟨6835961604021816104230457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4557307736014544069486971 6835961604021816104230457)
    ·
      refine ⟨5126971203016362078172843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6835961604021816104230457 5126971203016362078172843)
      ·
        refine ⟨7690456804524543117259265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126971203016362078172843 7690456804524543117259265)
        ·
          refine ⟨5767842603393407337944449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7690456804524543117259265 5767842603393407337944449)
          ·
            refine ⟨4325881952545055503458337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5767842603393407337944449 4325881952545055503458337)
            ·
              refine ⟨3244411464408791627593753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325881952545055503458337 3244411464408791627593753)
              ·
                refine ⟨2433308598306593720695315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244411464408791627593753 2433308598306593720695315)
                ·
                  refine ⟨3649962897459890581042973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433308598306593720695315 3649962897459890581042973)
                  ·
                    refine ⟨1368736086547458967891115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3649962897459890581042973 1368736086547458967891115)
                    ·
                      rfl

theorem cell22_3998406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3998406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998406 prefixEnd_3998406 := by exact prefixLift 3998406
  have htrace : WordTrace (prefixWord ++ tailWord_3998406) baseStart_3998406 baseEnd_3998406 := by
    simpa [prefixWord, tailWord_3998406, baseEnd_3998406] using wordTrace_append hprefix tailTrace_3998406
  have hstable : (prefixWord ++ tailWord_3998406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998406).length < 2 ^ (prefixWord ++ tailWord_3998406).sum := by decide
  have hdescent : baseEnd_3998406 < baseStart_3998406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998424 : List Nat := [2, 1, 2, 2, 3, 2, 3, 7]
def baseStart_3998424 : Nat := 118140960795 + 3998424 * 2 ^ 59
def prefixEnd_3998424 : Nat := 4983230072969 + 3 ^ 40 * 3998424 * 2
def baseEnd_3998424 : Nat := 152082472035034768993451

theorem tailTrace_3998424 : CollatzResearch.WordTrace tailWord_3998424 prefixEnd_3998424 152082472035034768993451 := by
  unfold tailWord_3998424
  simp only [CollatzResearch.WordTrace]
  refine ⟨72917252033200099648869163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97223002710933466198492217 72917252033200099648869163)
  ·
    refine ⟨109375878049800149473303745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72917252033200099648869163 109375878049800149473303745)
    ·
      refine ⟨82031908537350112104977809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109375878049800149473303745 82031908537350112104977809)
      ·
        refine ⟨61523931403012584078733357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82031908537350112104977809 61523931403012584078733357)
        ·
          refine ⟨23071474276129719029525009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61523931403012584078733357 23071474276129719029525009)
          ·
            refine ⟨17303605707097289272143757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23071474276129719029525009 17303605707097289272143757)
            ·
              refine ⟨6488852140161483477053909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17303605707097289272143757 6488852140161483477053909)
              ·
                refine ⟨152082472035034768993451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6488852140161483477053909 152082472035034768993451)
                ·
                  rfl

theorem cell22_3998424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_3998424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998424 prefixEnd_3998424 := by exact prefixLift 3998424
  have htrace : WordTrace (prefixWord ++ tailWord_3998424) baseStart_3998424 baseEnd_3998424 := by
    simpa [prefixWord, tailWord_3998424, baseEnd_3998424] using wordTrace_append hprefix tailTrace_3998424
  have hstable : (prefixWord ++ tailWord_3998424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998424).length < 2 ^ (prefixWord ++ tailWord_3998424).sum := by decide
  have hdescent : baseEnd_3998424 < baseStart_3998424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998428 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3998428 : Nat := 118140960795 + 3998428 * 2 ^ 59
def prefixEnd_3998428 : Nat := 4983230072969 + 3 ^ 40 * 3998428 * 2
def baseEnd_3998428 : Nat := 1368743617597058243841047

theorem tailTrace_3998428 : CollatzResearch.WordTrace tailWord_3998428 prefixEnd_3998428 1368743617597058243841047 := by
  unfold tailWord_3998428
  simp only [CollatzResearch.WordTrace]
  refine ⟨72917324979192853990441969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97223099972257138653922625 72917324979192853990441969)
  ·
    refine ⟨54687993734394640492831477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72917324979192853990441969 54687993734394640492831477)
    ·
      refine ⟨5126999412599497546202951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54687993734394640492831477 5126999412599497546202951)
      ·
        refine ⟨7690499118899246319304427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126999412599497546202951 7690499118899246319304427)
        ·
          refine ⟨11535748678348869478956641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690499118899246319304427 11535748678348869478956641)
          ·
            refine ⟨8651811508761652109217481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11535748678348869478956641 8651811508761652109217481)
            ·
              refine ⟨6488858631571239081913111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651811508761652109217481 6488858631571239081913111)
              ·
                refine ⟨9733287947356858622869667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488858631571239081913111 9733287947356858622869667)
                ·
                  refine ⟨14599931921035287934304501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9733287947356858622869667 14599931921035287934304501)
                  ·
                    refine ⟨1368743617597058243841047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14599931921035287934304501 1368743617597058243841047)
                    ·
                      rfl

theorem cell22_3998428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3998428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998428 prefixEnd_3998428 := by exact prefixLift 3998428
  have htrace : WordTrace (prefixWord ++ tailWord_3998428) baseStart_3998428 baseEnd_3998428 := by
    simpa [prefixWord, tailWord_3998428, baseEnd_3998428] using wordTrace_append hprefix tailTrace_3998428
  have hstable : (prefixWord ++ tailWord_3998428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998428).length < 2 ^ (prefixWord ++ tailWord_3998428).sum := by decide
  have hdescent : baseEnd_3998428 < baseStart_3998428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998473 : List Nat := [1, 2, 1, 1, 3, 2, 4, 4, 1, 3]
def baseStart_3998473 : Nat := 118140960795 + 3998473 * 2 ^ 59
def prefixEnd_3998473 : Nat := 4983230072969 + 3 ^ 40 * 3998473 * 2
def baseEnd_3998473 : Nat := 1368759022016693126465909

theorem tailTrace_3998473 : CollatzResearch.WordTrace tailWord_3998473 prefixEnd_3998473 1368759022016693126465909 := by
  unfold tailWord_3998473
  simp only [CollatzResearch.WordTrace]
  refine ⟨145836291243222680666272073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97224194162148453777514715 145836291243222680666272073)
  ·
    refine ⟨109377218432417010499704055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145836291243222680666272073 109377218432417010499704055)
    ·
      refine ⟨164065827648625515749556083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109377218432417010499704055 164065827648625515749556083)
      ·
        refine ⟨246098741472938273624334125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164065827648625515749556083 246098741472938273624334125)
        ·
          refine ⟨92287028052351852609125297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246098741472938273624334125 92287028052351852609125297)
          ·
            refine ⟨69215271039263889456843973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92287028052351852609125297 69215271039263889456843973)
            ·
              refine ⟨12977863319861979273158245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69215271039263889456843973 12977863319861979273158245)
              ·
                refine ⟨2433349372474121113717171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12977863319861979273158245 2433349372474121113717171)
                ·
                  refine ⟨3650024058711181670575757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433349372474121113717171 3650024058711181670575757)
                  ·
                    refine ⟨1368759022016693126465909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650024058711181670575757 1368759022016693126465909)
                    ·
                      rfl

theorem cell22_3998473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 3].length) (baseStart_3998473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998473 prefixEnd_3998473 := by exact prefixLift 3998473
  have htrace : WordTrace (prefixWord ++ tailWord_3998473) baseStart_3998473 baseEnd_3998473 := by
    simpa [prefixWord, tailWord_3998473, baseEnd_3998473] using wordTrace_append hprefix tailTrace_3998473
  have hstable : (prefixWord ++ tailWord_3998473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998473).length < 2 ^ (prefixWord ++ tailWord_3998473).sum := by decide
  have hdescent : baseEnd_3998473 < baseStart_3998473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998544 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_3998544 : Nat := 118140960795 + 3998544 * 2 ^ 59
def prefixEnd_3998544 : Nat := 4983230072969 + 3 ^ 40 * 3998544 * 2
def baseEnd_3998544 : Nat := 1368783326767672607940691

theorem tailTrace_3998544 : CollatzResearch.WordTrace tailWord_3998544 prefixEnd_3998544 1368783326767672607940691 := by
  unfold tailWord_3998544
  simp only [CollatzResearch.WordTrace]
  refine ⟨72919440412982729896053343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97225920550643639861404457 72919440412982729896053343)
  ·
    refine ⟨109379160619474094844080015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72919440412982729896053343 109379160619474094844080015)
    ·
      refine ⟨164068740929211142266120023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109379160619474094844080015 164068740929211142266120023)
      ·
        refine ⟨246103111393816713399180035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164068740929211142266120023 246103111393816713399180035)
        ·
          refine ⟨369154667090725070098770053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246103111393816713399180035 369154667090725070098770053)
          ·
            refine ⟨69216500079510950643519385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369154667090725070098770053 69216500079510950643519385)
            ·
              refine ⟨51912375059633212982639539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69216500079510950643519385 51912375059633212982639539)
              ·
                refine ⟨77868562589449819473959309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51912375059633212982639539 77868562589449819473959309)
                ·
                  refine ⟨29200710971043682302734741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77868562589449819473959309 29200710971043682302734741)
                  ·
                    refine ⟨1368783326767672607940691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29200710971043682302734741 1368783326767672607940691)
                    ·
                      rfl

theorem cell22_3998544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_3998544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998544 prefixEnd_3998544 := by exact prefixLift 3998544
  have htrace : WordTrace (prefixWord ++ tailWord_3998544) baseStart_3998544 baseEnd_3998544 := by
    simpa [prefixWord, tailWord_3998544, baseEnd_3998544] using wordTrace_append hprefix tailTrace_3998544
  have hstable : (prefixWord ++ tailWord_3998544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998544).length < 2 ^ (prefixWord ++ tailWord_3998544).sum := by decide
  have hdescent : baseEnd_3998544 < baseStart_3998544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998546 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3998546 : Nat := 118140960795 + 3998546 * 2 ^ 59
def prefixEnd_3998546 : Nat := 4983230072969 + 3 ^ 40 * 3998546 * 2
def baseEnd_3998546 : Nat := 1368784011408545269390685

theorem tailTrace_3998546 : CollatzResearch.WordTrace tailWord_3998546 prefixEnd_3998546 1368784011408545269390685 := by
  unfold tailWord_3998546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36459738442989553533419873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97225969181305476089119661 36459738442989553533419873)
  ·
    refine ⟨27344803832242165150064905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36459738442989553533419873 27344803832242165150064905)
    ·
      refine ⟨20508602874181623862548679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27344803832242165150064905 20508602874181623862548679)
      ·
        refine ⟨30762904311272435793823019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20508602874181623862548679 30762904311272435793823019)
        ·
          refine ⟨46144356466908653690734529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30762904311272435793823019 46144356466908653690734529)
          ·
            refine ⟨34608267350181490268050897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46144356466908653690734529 34608267350181490268050897)
            ·
              refine ⟨25956200512636117701038173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34608267350181490268050897 25956200512636117701038173)
              ·
                refine ⟨9733575192238544137889315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25956200512636117701038173 9733575192238544137889315)
                ·
                  refine ⟨14600362788357816206833973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9733575192238544137889315 14600362788357816206833973)
                  ·
                    refine ⟨1368784011408545269390685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14600362788357816206833973 1368784011408545269390685)
                    ·
                      rfl

theorem cell22_3998546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3998546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998546 prefixEnd_3998546 := by exact prefixLift 3998546
  have htrace : WordTrace (prefixWord ++ tailWord_3998546) baseStart_3998546 baseEnd_3998546 := by
    simpa [prefixWord, tailWord_3998546, baseEnd_3998546] using wordTrace_append hprefix tailTrace_3998546
  have hstable : (prefixWord ++ tailWord_3998546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998546).length < 2 ^ (prefixWord ++ tailWord_3998546).sum := by decide
  have hdescent : baseEnd_3998546 < baseStart_3998546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998559 : List Nat := [1, 1, 2, 3, 1, 3, 1, 10]
def baseStart_3998559 : Nat := 118140960795 + 3998559 * 2 ^ 59
def prefixEnd_3998559 : Nat := 4983230072969 + 3 ^ 40 * 3998559 * 2
def baseEnd_3998559 : Nat := 152087606841579729868405

theorem tailTrace_3998559 : CollatzResearch.WordTrace tailWord_3998559 prefixEnd_3998559 152087606841579729868405 := by
  unfold tailWord_3998559
  simp only [CollatzResearch.WordTrace]
  refine ⟨145839427920911117353902731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97226285280607411569268487 145839427920911117353902731)
  ·
    refine ⟨218759141881366676030854097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145839427920911117353902731 218759141881366676030854097)
    ·
      refine ⟨164069356411025007023140573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218759141881366676030854097 164069356411025007023140573)
      ·
        refine ⟨61526008654134377633677715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164069356411025007023140573 61526008654134377633677715)
        ·
          refine ⟨92289012981201566450516573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61526008654134377633677715 92289012981201566450516573)
          ·
            refine ⟨34608379867950587418943715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92289012981201566450516573 34608379867950587418943715)
            ·
              refine ⟨51912569801925881128415573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34608379867950587418943715 51912569801925881128415573)
              ·
                refine ⟨152087606841579729868405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51912569801925881128415573 152087606841579729868405)
                ·
                  rfl

theorem cell22_3998559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 10].length) (baseStart_3998559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998559 prefixEnd_3998559 := by exact prefixLift 3998559
  have htrace : WordTrace (prefixWord ++ tailWord_3998559) baseStart_3998559 baseEnd_3998559 := by
    simpa [prefixWord, tailWord_3998559, baseEnd_3998559] using wordTrace_append hprefix tailTrace_3998559
  have hstable : (prefixWord ++ tailWord_3998559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998559).length < 2 ^ (prefixWord ++ tailWord_3998559).sum := by decide
  have hdescent : baseEnd_3998559 < baseStart_3998559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998582 : List Nat := [5, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_3998582 : Nat := 118140960795 + 3998582 * 2 ^ 59
def prefixEnd_3998582 : Nat := 4983230072969 + 3 ^ 40 * 3998582 * 2
def baseEnd_3998582 : Nat := 456265444981417725163525

theorem tailTrace_3998582 : CollatzResearch.WordTrace tailWord_3998582 prefixEnd_3998582 456265444981417725163525 := by
  unfold tailWord_3998582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9115016674989237017624375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97226844533218528187993333 9115016674989237017624375)
  ·
    refine ⟨13672525012483855526436563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9115016674989237017624375 13672525012483855526436563)
    ·
      refine ⟨20508787518725783289654845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13672525012483855526436563 20508787518725783289654845)
      ·
        refine ⟨7690795319522168733620567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20508787518725783289654845 7690795319522168733620567)
        ·
          refine ⟨11536192979283253100430851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690795319522168733620567 11536192979283253100430851)
          ·
            refine ⟨17304289468924879650646277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536192979283253100430851 17304289468924879650646277)
            ·
              refine ⟨3244554275423414934496177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17304289468924879650646277 3244554275423414934496177)
              ·
                refine ⟨2433415706567561200872133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244554275423414934496177 2433415706567561200872133)
                ·
                  refine ⟨456265444981417725163525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433415706567561200872133 456265444981417725163525)
                  ·
                    rfl

theorem cell22_3998582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_3998582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998582 prefixEnd_3998582 := by exact prefixLift 3998582
  have htrace : WordTrace (prefixWord ++ tailWord_3998582) baseStart_3998582 baseEnd_3998582 := by
    simpa [prefixWord, tailWord_3998582, baseEnd_3998582] using wordTrace_append hprefix tailTrace_3998582
  have hstable : (prefixWord ++ tailWord_3998582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998582).length < 2 ^ (prefixWord ++ tailWord_3998582).sum := by decide
  have hdescent : baseEnd_3998582 < baseStart_3998582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998610 : List Nat := [3, 2, 3, 2, 2, 1, 3, 6]
def baseStart_3998610 : Nat := 118140960795 + 3998610 * 2 ^ 59
def prefixEnd_3998610 : Nat := 4983230072969 + 3 ^ 40 * 3998610 * 2
def baseEnd_3998610 : Nat := 152089546657385603976721

theorem tailTrace_3998610 : CollatzResearch.WordTrace tailWord_3998610 prefixEnd_3998610 152089546657385603976721 := by
  unfold tailWord_3998610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36460322010931588266002321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97227525362484235376006189 36460322010931588266002321)
  ·
    refine ⟨27345241508198691199501741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36460322010931588266002321 27345241508198691199501741)
    ·
      refine ⟨10254465565574509199813153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27345241508198691199501741 10254465565574509199813153)
      ·
        refine ⟨7690849174180881899859865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10254465565574509199813153 7690849174180881899859865)
        ·
          refine ⟨5768136880635661424894899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7690849174180881899859865 5768136880635661424894899)
          ·
            refine ⟨8652205320953492137342349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768136880635661424894899 8652205320953492137342349)
            ·
              refine ⟨3244576995357559551503381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8652205320953492137342349 3244576995357559551503381)
              ·
                refine ⟨152089546657385603976721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3244576995357559551503381 152089546657385603976721)
                ·
                  rfl

theorem cell22_3998610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_3998610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998610 prefixEnd_3998610 := by exact prefixLift 3998610
  have htrace : WordTrace (prefixWord ++ tailWord_3998610) baseStart_3998610 baseEnd_3998610 := by
    simpa [prefixWord, tailWord_3998610, baseEnd_3998610] using wordTrace_append hprefix tailTrace_3998610
  have hstable : (prefixWord ++ tailWord_3998610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998610).length < 2 ^ (prefixWord ++ tailWord_3998610).sum := by decide
  have hdescent : baseEnd_3998610 < baseStart_3998610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998621 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 7]
def baseStart_3998621 : Nat := 118140960795 + 3998621 * 2 ^ 59
def prefixEnd_3998621 : Nat := 4983230072969 + 3 ^ 40 * 3998621 * 2
def baseEnd_3998621 : Nat := 456269895147090024588485

theorem tailTrace_3998621 : CollatzResearch.WordTrace tailWord_3998621 prefixEnd_3998621 456269895147090024588485 := by
  unfold tailWord_3998621
  simp only [CollatzResearch.WordTrace]
  refine ⟨145841689246686501942659717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97227792831124334628439811 145841689246686501942659717)
  ·
    refine ⟨27345316733753719114248697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145841689246686501942659717 27345316733753719114248697)
    ·
      refine ⟨20508987550315289335686523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27345316733753719114248697 20508987550315289335686523)
      ·
        refine ⟨30763481325472934003529785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20508987550315289335686523 30763481325472934003529785)
        ·
          refine ⟨23072610994104700502647339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30763481325472934003529785 23072610994104700502647339)
          ·
            refine ⟨34608916491157050753971009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23072610994104700502647339 34608916491157050753971009)
            ·
              refine ⟨25956687368367788065478257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34608916491157050753971009 25956687368367788065478257)
              ·
                refine ⟨19467515526275841049108693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25956687368367788065478257 19467515526275841049108693)
                ·
                  refine ⟨456269895147090024588485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19467515526275841049108693 456269895147090024588485)
                  ·
                    rfl

theorem cell22_3998621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_3998621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998621 prefixEnd_3998621 := by exact prefixLift 3998621
  have htrace : WordTrace (prefixWord ++ tailWord_3998621) baseStart_3998621 baseEnd_3998621 := by
    simpa [prefixWord, tailWord_3998621, baseEnd_3998621] using wordTrace_append hprefix tailTrace_3998621
  have hstable : (prefixWord ++ tailWord_3998621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998621).length < 2 ^ (prefixWord ++ tailWord_3998621).sum := by decide
  have hdescent : baseEnd_3998621 < baseStart_3998621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998685 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3998685 : Nat := 118140960795 + 3998685 * 2 ^ 59
def prefixEnd_3998685 : Nat := 4983230072969 + 3 ^ 40 * 3998685 * 2
def baseEnd_3998685 : Nat := 1368831593949195240165259

theorem tailTrace_3998685 : CollatzResearch.WordTrace tailWord_3998685 prefixEnd_3998685 1368831593949195240165259 := by
  unfold tailWord_3998685
  simp only [CollatzResearch.WordTrace]
  refine ⟨145844023518454640872989509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97229349012303093915326339 145844023518454640872989509)
  ·
    refine ⟨27345754409710245163685533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145844023518454640872989509 27345754409710245163685533)
    ·
      refine ⟨10254657903641341936382075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27345754409710245163685533 10254657903641341936382075)
      ·
        refine ⟨15381986855462012904573113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10254657903641341936382075 15381986855462012904573113)
        ·
          refine ⟨11536490141596509678429835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15381986855462012904573113 11536490141596509678429835)
          ·
            refine ⟨17304735212394764517644753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536490141596509678429835 17304735212394764517644753)
            ·
              refine ⟨12978551409296073388233565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17304735212394764517644753 12978551409296073388233565)
              ·
                refine ⟨4866956778486027520587587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12978551409296073388233565 4866956778486027520587587)
                ·
                  refine ⟨7300435167729041280881381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4866956778486027520587587 7300435167729041280881381)
                  ·
                    refine ⟨1368831593949195240165259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7300435167729041280881381 1368831593949195240165259)
                    ·
                      rfl

theorem cell22_3998685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3998685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998685 prefixEnd_3998685 := by exact prefixLift 3998685
  have htrace : WordTrace (prefixWord ++ tailWord_3998685) baseStart_3998685 baseEnd_3998685 := by
    simpa [prefixWord, tailWord_3998685, baseEnd_3998685] using wordTrace_append hprefix tailTrace_3998685
  have hstable : (prefixWord ++ tailWord_3998685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998685).length < 2 ^ (prefixWord ++ tailWord_3998685).sum := by decide
  have hdescent : baseEnd_3998685 < baseStart_3998685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998730 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_3998730 : Nat := 118140960795 + 3998730 * 2 ^ 59
def prefixEnd_3998730 : Nat := 4983230072969 + 3 ^ 40 * 3998730 * 2
def baseEnd_3998730 : Nat := 1368846998368830122790121

theorem tailTrace_3998730 : CollatzResearch.WordTrace tailWord_3998730 prefixEnd_3998730 1368846998368830122790121 := by
  unfold tailWord_3998730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36461416200822903389594411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97230443202194409038918429 36461416200822903389594411)
  ·
    refine ⟨54692124301234355084391617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36461416200822903389594411 54692124301234355084391617)
    ·
      refine ⟨41019093225925766313293713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54692124301234355084391617 41019093225925766313293713)
      ·
        refine ⟨30764319919444324734970285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41019093225925766313293713 30764319919444324734970285)
        ·
          refine ⟨11536619969791621775613857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30764319919444324734970285 11536619969791621775613857)
          ·
            refine ⟨8652464977343716331710393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11536619969791621775613857 8652464977343716331710393)
            ·
              refine ⟨6489348733007787248782795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8652464977343716331710393 6489348733007787248782795)
              ·
                refine ⟨9734023099511680873174193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6489348733007787248782795 9734023099511680873174193)
                ·
                  refine ⟨7300517324633760654880645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9734023099511680873174193 7300517324633760654880645)
                  ·
                    refine ⟨1368846998368830122790121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7300517324633760654880645 1368846998368830122790121)
                    ·
                      rfl

theorem cell22_3998730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_3998730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998730 prefixEnd_3998730 := by exact prefixLift 3998730
  have htrace : WordTrace (prefixWord ++ tailWord_3998730) baseStart_3998730 baseEnd_3998730 := by
    simpa [prefixWord, tailWord_3998730, baseEnd_3998730] using wordTrace_append hprefix tailTrace_3998730
  have hstable : (prefixWord ++ tailWord_3998730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998730).length < 2 ^ (prefixWord ++ tailWord_3998730).sum := by decide
  have hdescent : baseEnd_3998730 < baseStart_3998730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998762 : List Nat := [3, 1, 4, 1, 4, 1, 1, 7]
def baseStart_3998762 : Nat := 118140960795 + 3998762 * 2 ^ 59
def prefixEnd_3998762 : Nat := 4983230072969 + 3 ^ 40 * 3998762 * 2
def baseEnd_3998762 : Nat := 152095328069199189554447

theorem tailTrace_3998762 : CollatzResearch.WordTrace tailWord_3998762 prefixEnd_3998762 152095328069199189554447 := by
  unfold tailWord_3998762
  simp only [CollatzResearch.WordTrace]
  refine ⟨36461707984793920755885635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97231221292783788682361693 36461707984793920755885635)
  ·
    refine ⟨54692561977190881133828453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36461707984793920755885635 54692561977190881133828453)
    ·
      refine ⟨10254855370723290212592835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54692561977190881133828453 10254855370723290212592835)
      ·
        refine ⟨15382283056084935318889253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10254855370723290212592835 15382283056084935318889253)
        ·
          refine ⟨2884178073015925372291735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15382283056084935318889253 2884178073015925372291735)
          ·
            refine ⟨4326267109523888058437603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884178073015925372291735 4326267109523888058437603)
            ·
              refine ⟨6489400664285832087656405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326267109523888058437603 6489400664285832087656405)
              ·
                refine ⟨152095328069199189554447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6489400664285832087656405 152095328069199189554447)
                ·
                  rfl

theorem cell22_3998762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_3998762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998762 prefixEnd_3998762 := by exact prefixLift 3998762
  have htrace : WordTrace (prefixWord ++ tailWord_3998762) baseStart_3998762 baseEnd_3998762 := by
    simpa [prefixWord, tailWord_3998762, baseEnd_3998762] using wordTrace_append hprefix tailTrace_3998762
  have hstable : (prefixWord ++ tailWord_3998762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998762).length < 2 ^ (prefixWord ++ tailWord_3998762).sum := by decide
  have hdescent : baseEnd_3998762 < baseStart_3998762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998824 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 5]
def baseStart_3998824 : Nat := 118140960795 + 3998824 * 2 ^ 59
def prefixEnd_3998824 : Nat := 4983230072969 + 3 ^ 40 * 3998824 * 2
def baseEnd_3998824 : Nat := 456293058829948403646611

theorem tailTrace_3998824 : CollatzResearch.WordTrace tailWord_3998824 prefixEnd_3998824 456293058829948403646611 := by
  unfold tailWord_3998824
  simp only [CollatzResearch.WordTrace]
  refine ⟨72924546632475533806149763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97232728843300711741533017 72924546632475533806149763)
  ·
    refine ⟨109386819948713300709224645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72924546632475533806149763 109386819948713300709224645)
    ·
      refine ⟨20510028740383743882979621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109386819948713300709224645 20510028740383743882979621)
      ·
        refine ⟨3845630388821951978058679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20510028740383743882979621 3845630388821951978058679)
        ·
          refine ⟨5768445583232927967088019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845630388821951978058679 5768445583232927967088019)
          ·
            refine ⟨8652668374849391950632029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768445583232927967088019 8652668374849391950632029)
            ·
              refine ⟨3244750640568521981487011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8652668374849391950632029 3244750640568521981487011)
              ·
                refine ⟨4867125960852782972230517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244750640568521981487011 4867125960852782972230517)
                ·
                  refine ⟨456293058829948403646611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4867125960852782972230517 456293058829948403646611)
                  ·
                    rfl

theorem cell22_3998824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_3998824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998824 prefixEnd_3998824 := by exact prefixLift 3998824
  have htrace : WordTrace (prefixWord ++ tailWord_3998824) baseStart_3998824 baseEnd_3998824 := by
    simpa [prefixWord, tailWord_3998824, baseEnd_3998824] using wordTrace_append hprefix tailTrace_3998824
  have hstable : (prefixWord ++ tailWord_3998824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998824).length < 2 ^ (prefixWord ++ tailWord_3998824).sum := by decide
  have hdescent : baseEnd_3998824 < baseStart_3998824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998833 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_3998833 : Nat := 118140960795 + 3998833 * 2 ^ 59
def prefixEnd_3998833 : Nat := 4983230072969 + 3 ^ 40 * 3998833 * 2
def baseEnd_3998833 : Nat := 1368882257373772187464805

theorem tailTrace_3998833 : CollatzResearch.WordTrace tailWord_3998833 prefixEnd_3998833 1368882257373772187464805 := by
  unfold tailWord_3998833
  simp only [CollatzResearch.WordTrace]
  refine ⟨145849421521918462149377153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97232947681278974766251435 145849421521918462149377153)
  ·
    refine ⟨109387066141438846612032865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145849421521918462149377153 109387066141438846612032865)
    ·
      refine ⟨82040299606079134959024649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109387066141438846612032865 82040299606079134959024649)
      ·
        refine ⟨61530224704559351219268487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82040299606079134959024649 61530224704559351219268487)
        ·
          refine ⟨92295337056839026828902731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61530224704559351219268487 92295337056839026828902731)
          ·
            refine ⟨138443005585258540243354097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92295337056839026828902731 138443005585258540243354097)
            ·
              refine ⟨103832254188943905182515573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138443005585258540243354097 103832254188943905182515573)
              ·
                refine ⟨9734273830213491110860835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103832254188943905182515573 9734273830213491110860835)
                ·
                  refine ⟨14601410745320236666291253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9734273830213491110860835 14601410745320236666291253)
                  ·
                    refine ⟨1368882257373772187464805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14601410745320236666291253 1368882257373772187464805)
                    ·
                      rfl

theorem cell22_3998833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_3998833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998833 prefixEnd_3998833 := by exact prefixLift 3998833
  have htrace : WordTrace (prefixWord ++ tailWord_3998833) baseStart_3998833 baseEnd_3998833 := by
    simpa [prefixWord, tailWord_3998833, baseEnd_3998833] using wordTrace_append hprefix tailTrace_3998833
  have hstable : (prefixWord ++ tailWord_3998833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998833).length < 2 ^ (prefixWord ++ tailWord_3998833).sum := by decide
  have hdescent : baseEnd_3998833 < baseStart_3998833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998848 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_3998848 : Nat := 118140960795 + 3998848 * 2 ^ 59
def prefixEnd_3998848 : Nat := 4983230072969 + 3 ^ 40 * 3998848 * 2
def baseEnd_3998848 : Nat := 1368887392180317148339759

theorem tailTrace_3998848 : CollatzResearch.WordTrace tailWord_3998848 prefixEnd_3998848 1368887392180317148339759 := by
  unfold tailWord_3998848
  simp only [CollatzResearch.WordTrace]
  refine ⟨72924984308432059855586599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97233312411242746474115465 72924984308432059855586599)
  ·
    refine ⟨109387476462648089783379899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72924984308432059855586599 109387476462648089783379899)
    ·
      refine ⟨164081214693972134675069849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109387476462648089783379899 164081214693972134675069849)
      ·
        refine ⟨123060911020479101006302387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164081214693972134675069849 123060911020479101006302387)
        ·
          refine ⟨184591366530718651509453581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123060911020479101006302387 184591366530718651509453581)
          ·
            refine ⟨69221762449019494316045093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184591366530718651509453581 69221762449019494316045093)
            ·
              refine ⟨12979080459191155184258455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69221762449019494316045093 12979080459191155184258455)
              ·
                refine ⟨19468620688786732776387683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12979080459191155184258455 19468620688786732776387683)
                ·
                  refine ⟨29202931033180099164581525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19468620688786732776387683 29202931033180099164581525)
                  ·
                    refine ⟨1368887392180317148339759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29202931033180099164581525 1368887392180317148339759)
                    ·
                      rfl

theorem cell22_3998848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_3998848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998848 prefixEnd_3998848 := by exact prefixLift 3998848
  have htrace : WordTrace (prefixWord ++ tailWord_3998848) baseStart_3998848 baseEnd_3998848 := by
    simpa [prefixWord, tailWord_3998848, baseEnd_3998848] using wordTrace_append hprefix tailTrace_3998848
  have hstable : (prefixWord ++ tailWord_3998848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998848).length < 2 ^ (prefixWord ++ tailWord_3998848).sum := by decide
  have hdescent : baseEnd_3998848 < baseStart_3998848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998852 : List Nat := [2, 3, 2, 1, 2, 2, 3, 3, 4]
def baseStart_3998852 : Nat := 118140960795 + 3998852 * 2 ^ 59
def prefixEnd_3998852 : Nat := 4983230072969 + 3 ^ 40 * 3998852 * 2
def baseEnd_3998852 : Nat := 456296253820687490413249

theorem tailTrace_3998852 : CollatzResearch.WordTrace tailWord_3998852 prefixEnd_3998852 456296253820687490413249 := by
  unfold tailWord_3998852
  simp only [CollatzResearch.WordTrace]
  refine ⟨72925057254424814197159405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97233409672566418929545873 72925057254424814197159405)
  ·
    refine ⟨27346896470409305323934777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72925057254424814197159405 27346896470409305323934777)
    ·
      refine ⟨20510172352806978992951083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27346896470409305323934777 20510172352806978992951083)
      ·
        refine ⟨30765258529210468489426625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20510172352806978992951083 30765258529210468489426625)
        ·
          refine ⟨23073943896907851367069969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30765258529210468489426625 23073943896907851367069969)
          ·
            refine ⟨17305457922680888525302477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23073943896907851367069969 17305457922680888525302477)
            ·
              refine ⟨6489546721005333196988429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17305457922680888525302477 6489546721005333196988429)
              ·
                refine ⟨2433580020376999948870661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6489546721005333196988429 2433580020376999948870661)
                ·
                  refine ⟨456296253820687490413249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433580020376999948870661 456296253820687490413249)
                  ·
                    rfl

theorem cell22_3998852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_3998852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998852 prefixEnd_3998852 := by exact prefixLift 3998852
  have htrace : WordTrace (prefixWord ++ tailWord_3998852) baseStart_3998852 baseEnd_3998852 := by
    simpa [prefixWord, tailWord_3998852, baseEnd_3998852] using wordTrace_append hprefix tailTrace_3998852
  have hstable : (prefixWord ++ tailWord_3998852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998852).length < 2 ^ (prefixWord ++ tailWord_3998852).sum := by decide
  have hdescent : baseEnd_3998852 < baseStart_3998852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998884 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_3998884 : Nat := 118140960795 + 3998884 * 2 ^ 59
def prefixEnd_3998884 : Nat := 4983230072969 + 3 ^ 40 * 3998884 * 2
def baseEnd_3998884 : Nat := 1368899715716025054439649

theorem tailTrace_3998884 : CollatzResearch.WordTrace tailWord_3998884 prefixEnd_3998884 1368899715716025054439649 := by
  unfold tailWord_3998884
  simp only [CollatzResearch.WordTrace]
  refine ⟨72925640822366848929741853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97234187763155798572989137 72925640822366848929741853)
  ·
    refine ⟨27347115308387568348653195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72925640822366848929741853 27347115308387568348653195)
    ·
      refine ⟨41020672962581352522979793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27347115308387568348653195 41020672962581352522979793)
      ·
        refine ⟨30765504721936014392234845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41020672962581352522979793 30765504721936014392234845)
        ·
          refine ⟨11537064270726005397088067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30765504721936014392234845 11537064270726005397088067)
          ·
            refine ⟨17305596406089008095632101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537064270726005397088067 17305596406089008095632101)
            ·
              refine ⟨3244799326141689017931019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17305596406089008095632101 3244799326141689017931019)
              ·
                refine ⟨4867198989212533526896529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244799326141689017931019 4867198989212533526896529)
                ·
                  refine ⟨3650399241909400145172397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4867198989212533526896529 3650399241909400145172397)
                  ·
                    refine ⟨1368899715716025054439649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650399241909400145172397 1368899715716025054439649)
                    ·
                      rfl

theorem cell22_3998884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_3998884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998884 prefixEnd_3998884 := by exact prefixLift 3998884
  have htrace : WordTrace (prefixWord ++ tailWord_3998884) baseStart_3998884 baseEnd_3998884 := by
    simpa [prefixWord, tailWord_3998884, baseEnd_3998884] using wordTrace_append hprefix tailTrace_3998884
  have hstable : (prefixWord ++ tailWord_3998884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998884).length < 2 ^ (prefixWord ++ tailWord_3998884).sum := by decide
  have hdescent : baseEnd_3998884 < baseStart_3998884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998895 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 3, 3]
def baseStart_3998895 : Nat := 118140960795 + 3998895 * 2 ^ 59
def prefixEnd_3998895 : Nat := 4983230072969 + 3 ^ 40 * 3998895 * 2
def baseEnd_3998895 : Nat := 1368903481240824692414615

theorem tailTrace_3998895 : CollatzResearch.WordTrace tailWord_3998895 prefixEnd_3998895 1368903481240824692414615 := by
  unfold tailWord_3998895
  simp only [CollatzResearch.WordTrace]
  refine ⟨145851682847693846738134139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97234455231795897825422759 145851682847693846738134139)
  ·
    refine ⟨218777524271540770107201209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145851682847693846738134139 218777524271540770107201209)
    ·
      refine ⟨164083143203655577580400907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218777524271540770107201209 164083143203655577580400907)
      ·
        refine ⟨246124714805483366370601361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164083143203655577580400907 246124714805483366370601361)
        ·
          refine ⟨184593536104112524777951021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246124714805483366370601361 184593536104112524777951021)
          ·
            refine ⟨69222576039042196791731633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184593536104112524777951021 69222576039042196791731633)
            ·
              refine ⟨51916932029281647593798725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69222576039042196791731633 51916932029281647593798725)
              ·
                refine ⟨9734424755490308923837261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51916932029281647593798725 9734424755490308923837261)
                ·
                  refine ⟨3650409283308865846438973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9734424755490308923837261 3650409283308865846438973)
                  ·
                    refine ⟨1368903481240824692414615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650409283308865846438973 1368903481240824692414615)
                    ·
                      rfl

theorem cell22_3998895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_3998895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998895 prefixEnd_3998895 := by exact prefixLift 3998895
  have htrace : WordTrace (prefixWord ++ tailWord_3998895) baseStart_3998895 baseEnd_3998895 := by
    simpa [prefixWord, tailWord_3998895, baseEnd_3998895] using wordTrace_append hprefix tailTrace_3998895
  have hstable : (prefixWord ++ tailWord_3998895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998895).length < 2 ^ (prefixWord ++ tailWord_3998895).sum := by decide
  have hdescent : baseEnd_3998895 < baseStart_3998895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998914 : List Nat := [3, 5, 1, 1, 3, 9]
def baseStart_3998914 : Nat := 118140960795 + 3998914 * 2 ^ 59
def prefixEnd_3998914 : Nat := 4983230072969 + 3 ^ 40 * 3998914 * 2
def baseEnd_3998914 : Nat := 16900123275668086125797

theorem tailTrace_3998914 : CollatzResearch.WordTrace tailWord_3998914 prefixEnd_3998914 16900123275668086125797 := by
  unfold tailWord_3998914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463093958656253245768949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97234917223083341988717197 36463093958656253245768949)
  ·
    refine ⟨3418415058624023741790839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36463093958656253245768949 3418415058624023741790839)
    ·
      refine ⟨5127622587936035612686259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3418415058624023741790839 5127622587936035612686259)
      ·
        refine ⟨7691433881904053419029389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5127622587936035612686259 7691433881904053419029389)
        ·
          refine ⟨2884287705714020032136021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7691433881904053419029389 2884287705714020032136021)
          ·
            refine ⟨16900123275668086125797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2884287705714020032136021 16900123275668086125797)
            ·
              rfl

theorem cell22_3998914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 9].length) (baseStart_3998914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998914 prefixEnd_3998914 := by exact prefixLift 3998914
  have htrace : WordTrace (prefixWord ++ tailWord_3998914) baseStart_3998914 baseEnd_3998914 := by
    simpa [prefixWord, tailWord_3998914, baseEnd_3998914] using wordTrace_append hprefix tailTrace_3998914
  have hstable : (prefixWord ++ tailWord_3998914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998914).length < 2 ^ (prefixWord ++ tailWord_3998914).sum := by decide
  have hdescent : baseEnd_3998914 < baseStart_3998914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998955 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 3, 4]
def baseStart_3998955 : Nat := 118140960795 + 3998955 * 2 ^ 59
def prefixEnd_3998955 : Nat := 4983230072969 + 3 ^ 40 * 3998955 * 2
def baseEnd_3998955 : Nat := 1368924020467004535914431

theorem tailTrace_3998955 : CollatzResearch.WordTrace tailWord_3998955 prefixEnd_3998955 1368924020467004535914431 := by
  unfold tailWord_3998955
  simp only [CollatzResearch.WordTrace]
  refine ⟨145853871227476476985318319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97235914151650984656878879 145853871227476476985318319)
  ·
    refine ⟨218780806841214715477977479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145853871227476476985318319 218780806841214715477977479)
    ·
      refine ⟨328171210261822073216966219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218780806841214715477977479 328171210261822073216966219)
      ·
        refine ⟨492256815392733109825449329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328171210261822073216966219 492256815392733109825449329)
        ·
          refine ⟨369192611544549832369086997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492256815392733109825449329 369192611544549832369086997)
          ·
            refine ⟨17305903666150773392300953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 369192611544549832369086997 17305903666150773392300953)
            ·
              refine ⟨12979427749613080044225715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17305903666150773392300953 12979427749613080044225715)
              ·
                refine ⟨19469141624419620066338573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12979427749613080044225715 19469141624419620066338573)
                ·
                  refine ⟨7300928109157357524876965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19469141624419620066338573 7300928109157357524876965)
                  ·
                    refine ⟨1368924020467004535914431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7300928109157357524876965 1368924020467004535914431)
                    ·
                      rfl

theorem cell22_3998955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_3998955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998955 prefixEnd_3998955 := by exact prefixLift 3998955
  have htrace : WordTrace (prefixWord ++ tailWord_3998955) baseStart_3998955 baseEnd_3998955 := by
    simpa [prefixWord, tailWord_3998955, baseEnd_3998955] using wordTrace_append hprefix tailTrace_3998955
  have hstable : (prefixWord ++ tailWord_3998955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998955).length < 2 ^ (prefixWord ++ tailWord_3998955).sum := by decide
  have hdescent : baseEnd_3998955 < baseStart_3998955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998987 : List Nat := [1, 1, 1, 1, 5, 3, 2, 4, 4]
def baseStart_3998987 : Nat := 118140960795 + 3998987 * 2 ^ 59
def prefixEnd_3998987 : Nat := 4983230072969 + 3 ^ 40 * 3998987 * 2
def baseEnd_3998987 : Nat := 456311658240322373038111

theorem tailTrace_3998987 : CollatzResearch.WordTrace tailWord_3998987 prefixEnd_3998987 456311658240322373038111 := by
  unfold tailWord_3998987
  simp only [CollatzResearch.WordTrace]
  refine ⟨145855038363360546450483215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97236692242240364300322143 145855038363360546450483215)
  ·
    refine ⟨218782557545040819675724823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145855038363360546450483215 218782557545040819675724823)
    ·
      refine ⟨328173836317561229513587235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218782557545040819675724823 328173836317561229513587235)
      ·
        refine ⟨492260754476341844270380853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328173836317561229513587235 492260754476341844270380853)
        ·
          refine ⟨46149445732157047900348205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492260754476341844270380853 46149445732157047900348205)
          ·
            refine ⟨17306042149558892962630577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46149445732157047900348205 17306042149558892962630577)
            ·
              refine ⟨12979531612169169721972933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17306042149558892962630577 12979531612169169721972933)
              ·
                refine ⟨2433662177281719322869925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12979531612169169721972933 2433662177281719322869925)
                ·
                  refine ⟨456311658240322373038111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433662177281719322869925 456311658240322373038111)
                  ·
                    rfl

theorem cell22_3998987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 4].length) (baseStart_3998987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3998987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3998987 prefixEnd_3998987 := by exact prefixLift 3998987
  have htrace : WordTrace (prefixWord ++ tailWord_3998987) baseStart_3998987 baseEnd_3998987 := by
    simpa [prefixWord, tailWord_3998987, baseEnd_3998987] using wordTrace_append hprefix tailTrace_3998987
  have hstable : (prefixWord ++ tailWord_3998987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998987).length < 2 ^ (prefixWord ++ tailWord_3998987).sum := by decide
  have hdescent : baseEnd_3998987 < baseStart_3998987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999000 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_3999000 : Nat := 118140960795 + 3999000 * 2 ^ 59
def prefixEnd_3999000 : Nat := 4983230072969 + 3 ^ 40 * 3999000 * 2
def baseEnd_3999000 : Nat := 1368939424886639418539293

theorem tailTrace_3999000 : CollatzResearch.WordTrace tailWord_3999000 prefixEnd_3999000 1368939424886639418539293 := by
  unfold tailWord_3999000
  simp only [CollatzResearch.WordTrace]
  refine ⟨72927756256156724835353227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97237008341542299780470969 72927756256156724835353227)
  ·
    refine ⟨109391634384235087253029841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72927756256156724835353227 109391634384235087253029841)
    ·
      refine ⟨82043725788176315439772381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109391634384235087253029841 82043725788176315439772381)
      ·
        refine ⟨30766397170566118289914643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82043725788176315439772381 30766397170566118289914643)
        ·
          refine ⟨46149595755849177434871965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30766397170566118289914643 46149595755849177434871965)
          ·
            refine ⟨17306098408443441538076987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46149595755849177434871965 17306098408443441538076987)
            ·
              refine ⟨25959147612665162307115481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17306098408443441538076987 25959147612665162307115481)
              ·
                refine ⟨19469360709498871730336611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25959147612665162307115481 19469360709498871730336611)
                ·
                  refine ⟨29204041064248307595504917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19469360709498871730336611 29204041064248307595504917)
                  ·
                    refine ⟨1368939424886639418539293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29204041064248307595504917 1368939424886639418539293)
                    ·
                      rfl

theorem cell22_3999000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_3999000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999000 prefixEnd_3999000 := by exact prefixLift 3999000
  have htrace : WordTrace (prefixWord ++ tailWord_3999000) baseStart_3999000 baseEnd_3999000 := by
    simpa [prefixWord, tailWord_3999000, baseEnd_3999000] using wordTrace_append hprefix tailTrace_3999000
  have hstable : (prefixWord ++ tailWord_3999000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999000).length < 2 ^ (prefixWord ++ tailWord_3999000).sum := by decide
  have hdescent : baseEnd_3999000 < baseStart_3999000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999002 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_3999002 : Nat := 118140960795 + 3999002 * 2 ^ 59
def prefixEnd_3999002 : Nat := 4983230072969 + 3 ^ 40 * 3999002 * 2
def baseEnd_3999002 : Nat := 1368940109527512079989287

theorem tailTrace_3999002 : CollatzResearch.WordTrace tailWord_3999002 prefixEnd_3999002 1368940109527512079989287 := by
  unfold tailWord_3999002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463896364576551003069815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97237056972204136008186173 36463896364576551003069815)
  ·
    refine ⟨54695844546864826504604723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36463896364576551003069815 54695844546864826504604723)
    ·
      refine ⟨82043766820297239756907085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54695844546864826504604723 82043766820297239756907085)
      ·
        refine ⟨30766412557611464908840157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82043766820297239756907085 30766412557611464908840157)
        ·
          refine ⟨11537404709104299340815059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30766412557611464908840157 11537404709104299340815059)
          ·
            refine ⟨17306107063656449011222589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537404709104299340815059 17306107063656449011222589)
            ·
              refine ⟨6489790148871168379208471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17306107063656449011222589 6489790148871168379208471)
              ·
                refine ⟨9734685223306752568812707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6489790148871168379208471 9734685223306752568812707)
                ·
                  refine ⟨14602027834960128853219061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9734685223306752568812707 14602027834960128853219061)
                  ·
                    refine ⟨1368940109527512079989287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14602027834960128853219061 1368940109527512079989287)
                    ·
                      rfl

theorem cell22_3999002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_3999002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999002 prefixEnd_3999002 := by exact prefixLift 3999002
  have htrace : WordTrace (prefixWord ++ tailWord_3999002) baseStart_3999002 baseEnd_3999002 := by
    simpa [prefixWord, tailWord_3999002, baseEnd_3999002] using wordTrace_append hprefix tailTrace_3999002
  have hstable : (prefixWord ++ tailWord_3999002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999002).length < 2 ^ (prefixWord ++ tailWord_3999002).sum := by decide
  have hdescent : baseEnd_3999002 < baseStart_3999002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999021 : List Nat := [1, 5, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3999021 : Nat := 118140960795 + 3999021 * 2 ^ 59
def prefixEnd_3999021 : Nat := 4983230072969 + 3 ^ 40 * 3999021 * 2
def baseEnd_3999021 : Nat := 456315537871934121254743

theorem tailTrace_3999021 : CollatzResearch.WordTrace tailWord_3999021 prefixEnd_3999021 456315537871934121254743 := by
  unfold tailWord_3999021
  simp only [CollatzResearch.WordTrace]
  refine ⟨145856278445237370257220917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97237518963491580171480611 145856278445237370257220917)
  ·
    refine ⟨13674026104241003461614461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145856278445237370257220917 13674026104241003461614461)
    ·
      refine ⟨5127759789090376298105423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13674026104241003461614461 5127759789090376298105423)
      ·
        refine ⟨7691639683635564447158135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5127759789090376298105423 7691639683635564447158135)
        ·
          refine ⟨11537459525453346670737203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691639683635564447158135 11537459525453346670737203)
          ·
            refine ⟨17306189288180020006105805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537459525453346670737203 17306189288180020006105805)
            ·
              refine ⟨6489820983067507502289677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17306189288180020006105805 6489820983067507502289677)
              ·
                refine ⟨2433682868650315313358629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6489820983067507502289677 2433682868650315313358629)
                ·
                  refine ⟨456315537871934121254743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433682868650315313358629 456315537871934121254743)
                  ·
                    rfl

theorem cell22_3999021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3999021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999021 prefixEnd_3999021 := by exact prefixLift 3999021
  have htrace : WordTrace (prefixWord ++ tailWord_3999021) baseStart_3999021 baseEnd_3999021 := by
    simpa [prefixWord, tailWord_3999021, baseEnd_3999021] using wordTrace_append hprefix tailTrace_3999021
  have hstable : (prefixWord ++ tailWord_3999021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999021).length < 2 ^ (prefixWord ++ tailWord_3999021).sum := by decide
  have hdescent : baseEnd_3999021 < baseStart_3999021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999053 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3999053 : Nat := 118140960795 + 3999053 * 2 ^ 59
def prefixEnd_3999053 : Nat := 4983230072969 + 3 ^ 40 * 3999053 * 2
def baseEnd_3999053 : Nat := 1368957567869764946964131

theorem tailTrace_3999053 : CollatzResearch.WordTrace tailWord_3999053 prefixEnd_3999053 1368957567869764946964131 := by
  unfold tailWord_3999053
  simp only [CollatzResearch.WordTrace]
  refine ⟨145857445581121439722385813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97238297054080959814923875 145857445581121439722385813)
  ·
    refine ⟨6837067761615067486986835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145857445581121439722385813 6837067761615067486986835)
    ·
      refine ⟨10255601642422601230480253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6837067761615067486986835 10255601642422601230480253)
      ·
        refine ⟨3845850615908475461430095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10255601642422601230480253 3845850615908475461430095)
        ·
          refine ⟨5768775923862713192145143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845850615908475461430095 5768775923862713192145143)
          ·
            refine ⟨8653163885794069788217715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768775923862713192145143 8653163885794069788217715)
            ·
              refine ⟨12979745828691104682326573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8653163885794069788217715 12979745828691104682326573)
              ·
                refine ⟨4867404685759164255872465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12979745828691104682326573 4867404685759164255872465)
                ·
                  refine ⟨3650553514319373191904349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4867404685759164255872465 3650553514319373191904349)
                  ·
                    refine ⟨1368957567869764946964131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650553514319373191904349 1368957567869764946964131)
                    ·
                      rfl

theorem cell22_3999053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3999053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999053 prefixEnd_3999053 := by exact prefixLift 3999053
  have htrace : WordTrace (prefixWord ++ tailWord_3999053) baseStart_3999053 baseEnd_3999053 := by
    simpa [prefixWord, tailWord_3999053, baseEnd_3999053] using wordTrace_append hprefix tailTrace_3999053
  have hstable : (prefixWord ++ tailWord_3999053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999053).length < 2 ^ (prefixWord ++ tailWord_3999053).sum := by decide
  have hdescent : baseEnd_3999053 < baseStart_3999053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999107 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 3, 4]
def baseStart_3999107 : Nat := 118140960795 + 3999107 * 2 ^ 59
def prefixEnd_3999107 : Nat := 4983230072969 + 3 ^ 40 * 3999107 * 2
def baseEnd_3999107 : Nat := 1368976053173326806113965

theorem tailTrace_3999107 : CollatzResearch.WordTrace tailWord_3999107 prefixEnd_3999107 1368976053173326806113965 := by
  unfold tailWord_3999107
  simp only [CollatzResearch.WordTrace]
  refine ⟨145859415122925806944851575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97239610081950537963234383 145859415122925806944851575)
  ·
    refine ⟨218789122684388710417277363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145859415122925806944851575 218789122684388710417277363)
    ·
      refine ⟨328183684026583065625916045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218789122684388710417277363 328183684026583065625916045)
      ·
        refine ⟨123068881509968649609718517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328183684026583065625916045 123068881509968649609718517)
        ·
          refine ⟨11537707641559560900911111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123068881509968649609718517 11537707641559560900911111)
          ·
            refine ⟨17306561462339341351366667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537707641559560900911111 17306561462339341351366667)
            ·
              refine ⟨25959842193509012027050001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17306561462339341351366667 25959842193509012027050001)
              ·
                refine ⟨19469881645131759020287501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25959842193509012027050001 19469881645131759020287501)
                ·
                  refine ⟨7301205616924409632607813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19469881645131759020287501 7301205616924409632607813)
                  ·
                    refine ⟨1368976053173326806113965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7301205616924409632607813 1368976053173326806113965)
                    ·
                      rfl

theorem cell22_3999107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_3999107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999107 prefixEnd_3999107 := by exact prefixLift 3999107
  have htrace : WordTrace (prefixWord ++ tailWord_3999107) baseStart_3999107 baseEnd_3999107 := by
    simpa [prefixWord, tailWord_3999107, baseEnd_3999107] using wordTrace_append hprefix tailTrace_3999107
  have hstable : (prefixWord ++ tailWord_3999107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999107).length < 2 ^ (prefixWord ++ tailWord_3999107).sum := by decide
  have hdescent : baseEnd_3999107 < baseStart_3999107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999124 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3999124 : Nat := 118140960795 + 3999124 * 2 ^ 59
def prefixEnd_3999124 : Nat := 4983230072969 + 3 ^ 40 * 3999124 * 2
def baseEnd_3999124 : Nat := 1368981872620744428438913

theorem tailTrace_3999124 : CollatzResearch.WordTrace tailWord_3999124 prefixEnd_3999124 1368981872620744428438913 := by
  unfold tailWord_3999124
  simp only [CollatzResearch.WordTrace]
  refine ⟨72930017581932109424110213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97240023442576145898813617 72930017581932109424110213)
  ·
    refine ⟨13674378296612270517020665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72930017581932109424110213 13674378296612270517020665)
    ·
      refine ⟨10255783722459202887765499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13674378296612270517020665 10255783722459202887765499)
      ·
        refine ⟨15383675583688804331648249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10255783722459202887765499 15383675583688804331648249)
        ·
          refine ⟨11537756687766603248736187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15383675583688804331648249 11537756687766603248736187)
          ·
            refine ⟨17306635031649904873104281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537756687766603248736187 17306635031649904873104281)
            ·
              refine ⟨12979976273737428654828211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17306635031649904873104281 12979976273737428654828211)
              ·
                refine ⟨19469964410606142982242317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12979976273737428654828211 19469964410606142982242317)
                ·
                  refine ⟨7301236653977303618340869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19469964410606142982242317 7301236653977303618340869)
                  ·
                    refine ⟨1368981872620744428438913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7301236653977303618340869 1368981872620744428438913)
                    ·
                      rfl

theorem cell22_3999124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3999124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999124 prefixEnd_3999124 := by exact prefixLift 3999124
  have htrace : WordTrace (prefixWord ++ tailWord_3999124) baseStart_3999124 baseEnd_3999124 := by
    simpa [prefixWord, tailWord_3999124, baseEnd_3999124] using wordTrace_append hprefix tailTrace_3999124
  have hstable : (prefixWord ++ tailWord_3999124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999124).length < 2 ^ (prefixWord ++ tailWord_3999124).sum := by decide
  have hdescent : baseEnd_3999124 < baseStart_3999124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999139 : List Nat := [1, 1, 1, 4, 1, 3, 4, 3, 4]
def baseStart_3999139 : Nat := 118140960795 + 3999139 * 2 ^ 59
def prefixEnd_3999139 : Nat := 4983230072969 + 3 ^ 40 * 3999139 * 2
def baseEnd_3999139 : Nat := 456329002475763129771289

theorem tailTrace_3999139 : CollatzResearch.WordTrace tailWord_3999139 prefixEnd_3999139 456329002475763129771289 := by
  unfold tailWord_3999139
  simp only [CollatzResearch.WordTrace]
  refine ⟨145860582258809876410016471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97240388172539917606677647 145860582258809876410016471)
  ·
    refine ⟨218790873388214814615024707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145860582258809876410016471 218790873388214814615024707)
    ·
      refine ⟨328186310082322221922537061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218790873388214814615024707 328186310082322221922537061)
      ·
        refine ⟨61534933140435416610475699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328186310082322221922537061 61534933140435416610475699)
        ·
          refine ⟨92302399710653124915713549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61534933140435416610475699 92302399710653124915713549)
          ·
            refine ⟨34613399891494921843392581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92302399710653124915713549 34613399891494921843392581)
            ·
              refine ⟨6490012479655297845636109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34613399891494921843392581 6490012479655297845636109)
              ·
                refine ⟨2433754679870736692113541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6490012479655297845636109 2433754679870736692113541)
                ·
                  refine ⟨456329002475763129771289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433754679870736692113541 456329002475763129771289)
                  ·
                    rfl

theorem cell22_3999139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 4].length) (baseStart_3999139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999139 prefixEnd_3999139 := by exact prefixLift 3999139
  have htrace : WordTrace (prefixWord ++ tailWord_3999139) baseStart_3999139 baseEnd_3999139 := by
    simpa [prefixWord, tailWord_3999139, baseEnd_3999139] using wordTrace_append hprefix tailTrace_3999139
  have hstable : (prefixWord ++ tailWord_3999139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999139).length < 2 ^ (prefixWord ++ tailWord_3999139).sum := by decide
  have hdescent : baseEnd_3999139 < baseStart_3999139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999154 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_3999154 : Nat := 118140960795 + 3999154 * 2 ^ 59
def prefixEnd_3999154 : Nat := 4983230072969 + 3 ^ 40 * 3999154 * 2
def baseEnd_3999154 : Nat := 1368992142233834350188821

theorem tailTrace_3999154 : CollatzResearch.WordTrace tailWord_3999154 prefixEnd_3999154 1368992142233834350188821 := by
  unfold tailWord_3999154
  simp only [CollatzResearch.WordTrace]
  refine ⟨36465282338438883492953129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97240752902503689314541677 36465282338438883492953129)
  ·
    refine ⟨27348961753829162619714847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36465282338438883492953129 27348961753829162619714847)
    ·
      refine ⟨41023442630743743929572271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27348961753829162619714847 41023442630743743929572271)
      ·
        refine ⟨61535163946115615894358407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41023442630743743929572271 61535163946115615894358407)
        ·
          refine ⟨92302745919173423841537611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61535163946115615894358407 92302745919173423841537611)
          ·
            refine ⟨138454118878760135762306417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92302745919173423841537611 138454118878760135762306417)
            ·
              refine ⟨103840589159070101821729813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138454118878760135762306417 103840589159070101821729813)
              ·
                refine ⟨4867527616831411022893585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103840589159070101821729813 4867527616831411022893585)
                ·
                  refine ⟨3650645712623558267170189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4867527616831411022893585 3650645712623558267170189)
                  ·
                    refine ⟨1368992142233834350188821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650645712623558267170189 1368992142233834350188821)
                    ·
                      rfl

theorem cell22_3999154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_3999154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999154 prefixEnd_3999154 := by exact prefixLift 3999154
  have htrace : WordTrace (prefixWord ++ tailWord_3999154) baseStart_3999154 baseEnd_3999154 := by
    simpa [prefixWord, tailWord_3999154, baseEnd_3999154] using wordTrace_append hprefix tailTrace_3999154
  have hstable : (prefixWord ++ tailWord_3999154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999154).length < 2 ^ (prefixWord ++ tailWord_3999154).sum := by decide
  have hdescent : baseEnd_3999154 < baseStart_3999154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999216 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 3, 3]
def baseStart_3999216 : Nat := 118140960795 + 3999216 * 2 ^ 59
def prefixEnd_3999216 : Nat := 4983230072969 + 3 ^ 40 * 3999216 * 2
def baseEnd_3999216 : Nat := 1369013366100886855138631

theorem tailTrace_3999216 : CollatzResearch.WordTrace tailWord_3999216 prefixEnd_3999216 1369013366100886855138631 := by
  unfold tailWord_3999216
  simp only [CollatzResearch.WordTrace]
  refine ⟨72931695339765459280284751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97242260453020612373713001 72931695339765459280284751)
  ·
    refine ⟨109397543009648188920427127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72931695339765459280284751 109397543009648188920427127)
    ·
      refine ⟨164096314514472283380640691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109397543009648188920427127 164096314514472283380640691)
      ·
        refine ⟨246144471771708425070961037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164096314514472283380640691 246144471771708425070961037)
        ·
          refine ⟨92304176914390659401610389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246144471771708425070961037 92304176914390659401610389)
          ·
            refine ⟨4326758292862062159450487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92304176914390659401610389 4326758292862062159450487)
            ·
              refine ⟨6490137439293093239175731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326758292862062159450487 6490137439293093239175731)
              ·
                refine ⟨9735206158939639858763597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490137439293093239175731 9735206158939639858763597)
                ·
                  refine ⟨3650702309602364947036349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9735206158939639858763597 3650702309602364947036349)
                  ·
                    refine ⟨1369013366100886855138631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650702309602364947036349 1369013366100886855138631)
                    ·
                      rfl

theorem cell22_3999216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_3999216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999216 prefixEnd_3999216 := by exact prefixLift 3999216
  have htrace : WordTrace (prefixWord ++ tailWord_3999216) baseStart_3999216 baseEnd_3999216 := by
    simpa [prefixWord, tailWord_3999216, baseEnd_3999216] using wordTrace_append hprefix tailTrace_3999216
  have hstable : (prefixWord ++ tailWord_3999216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999216).length < 2 ^ (prefixWord ++ tailWord_3999216).sum := by decide
  have hdescent : baseEnd_3999216 < baseStart_3999216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999229 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 5]
def baseStart_3999229 : Nat := 118140960795 + 3999229 * 2 ^ 59
def prefixEnd_3999229 : Nat := 4983230072969 + 3 ^ 40 * 3999229 * 2
def baseEnd_3999229 : Nat := 456339272088853051521197

theorem tailTrace_3999229 : CollatzResearch.WordTrace tailWord_3999229 prefixEnd_3999229 456339272088853051521197 := by
  unfold tailWord_3999229
  simp only [CollatzResearch.WordTrace]
  refine ⟨145863864828483821780792741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97242576552322547853861827 145863864828483821780792741)
  ·
    refine ⟨27349474655340716583898639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145863864828483821780792741 27349474655340716583898639)
    ·
      refine ⟨41024211983011074875847959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27349474655340716583898639 41024211983011074875847959)
      ·
        refine ⟨61536317974516612313771939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41024211983011074875847959 61536317974516612313771939)
        ·
          refine ⟨92304476961774918470657909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61536317974516612313771939 92304476961774918470657909)
          ·
            refine ⟨8653544715166398606624179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92304476961774918470657909 8653544715166398606624179)
            ·
              refine ⟨12980317072749597909936269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8653544715166398606624179 12980317072749597909936269)
              ·
                refine ⟨4867618902281099216226101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12980317072749597909936269 4867618902281099216226101)
                ·
                  refine ⟨456339272088853051521197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4867618902281099216226101 456339272088853051521197)
                  ·
                    rfl

theorem cell22_3999229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_3999229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999229 prefixEnd_3999229 := by exact prefixLift 3999229
  have htrace : WordTrace (prefixWord ++ tailWord_3999229) baseStart_3999229 baseEnd_3999229 := by
    simpa [prefixWord, tailWord_3999229, baseEnd_3999229] using wordTrace_append hprefix tailTrace_3999229
  have hstable : (prefixWord ++ tailWord_3999229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999229).length < 2 ^ (prefixWord ++ tailWord_3999229).sum := by decide
  have hdescent : baseEnd_3999229 < baseStart_3999229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999267 : List Nat := [1, 1, 1, 4, 6, 1, 2, 2, 1, 3]
def baseStart_3999267 : Nat := 118140960795 + 3999267 * 2 ^ 59
def prefixEnd_3999267 : Nat := 4983230072969 + 3 ^ 40 * 3999267 * 2
def baseEnd_3999267 : Nat := 1369030824443139722113475

theorem tailTrace_3999267 : CollatzResearch.WordTrace tailWord_3999267 prefixEnd_3999267 1369030824443139722113475 := by
  unfold tailWord_3999267
  simp only [CollatzResearch.WordTrace]
  refine ⟨145865250802346154270676055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97243500534897436180450703 145865250802346154270676055)
  ·
    refine ⟨218797876203519231406014083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145865250802346154270676055 218797876203519231406014083)
    ·
      refine ⟨328196814305278847109021125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218797876203519231406014083 328196814305278847109021125)
      ·
        refine ⟨61536902682239783832941461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328196814305278847109021125 61536902682239783832941461)
        ·
          refine ⟨2884542313229989867169131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61536902682239783832941461 2884542313229989867169131)
          ·
            refine ⟨4326813469844984800753697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884542313229989867169131 4326813469844984800753697)
            ·
              refine ⟨3245110102383738600565273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4326813469844984800753697 3245110102383738600565273)
              ·
                refine ⟨2433832576787803950423955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3245110102383738600565273 2433832576787803950423955)
                ·
                  refine ⟨3650748865181705925635933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433832576787803950423955 3650748865181705925635933)
                  ·
                    refine ⟨1369030824443139722113475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650748865181705925635933 1369030824443139722113475)
                    ·
                      rfl

theorem cell22_3999267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 3].length) (baseStart_3999267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999267 prefixEnd_3999267 := by exact prefixLift 3999267
  have htrace : WordTrace (prefixWord ++ tailWord_3999267) baseStart_3999267 baseEnd_3999267 := by
    simpa [prefixWord, tailWord_3999267, baseEnd_3999267] using wordTrace_append hprefix tailTrace_3999267
  have hstable : (prefixWord ++ tailWord_3999267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999267).length < 2 ^ (prefixWord ++ tailWord_3999267).sum := by decide
  have hdescent : baseEnd_3999267 < baseStart_3999267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999274 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_3999274 : Nat := 118140960795 + 3999274 * 2 ^ 59
def prefixEnd_3999274 : Nat := 4983230072969 + 3 ^ 40 * 3999274 * 2
def baseEnd_3999274 : Nat := 456344406895398012396151

theorem tailTrace_3999274 : CollatzResearch.WordTrace tailWord_3999274 prefixEnd_3999274 456344406895398012396151 := by
  unfold tailWord_3999274
  simp only [CollatzResearch.WordTrace]
  refine ⟨36466376528330198616545219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97243670742213862977453917 36466376528330198616545219)
  ·
    refine ⟨54699564792495297924817829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36466376528330198616545219 54699564792495297924817829)
    ·
      refine ⟨10256168398592868360903343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54699564792495297924817829 10256168398592868360903343)
      ·
        refine ⟨15384252597889302541355015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10256168398592868360903343 15384252597889302541355015)
        ·
          refine ⟨23076378896833953812032523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384252597889302541355015 23076378896833953812032523)
          ·
            refine ⟨34614568345250930718048785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23076378896833953812032523 34614568345250930718048785)
            ·
              refine ⟨25960926258938198038536589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34614568345250930718048785 25960926258938198038536589)
              ·
                refine ⟨9735347347101824264451221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25960926258938198038536589 9735347347101824264451221)
                ·
                  refine ⟨456344406895398012396151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9735347347101824264451221 456344406895398012396151)
                  ·
                    rfl

theorem cell22_3999274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_3999274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999274 prefixEnd_3999274 := by exact prefixLift 3999274
  have htrace : WordTrace (prefixWord ++ tailWord_3999274) baseStart_3999274 baseEnd_3999274 := by
    simpa [prefixWord, tailWord_3999274, baseEnd_3999274] using wordTrace_append hprefix tailTrace_3999274
  have hstable : (prefixWord ++ tailWord_3999274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999274).length < 2 ^ (prefixWord ++ tailWord_3999274).sum := by decide
  have hdescent : baseEnd_3999274 < baseStart_3999274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999289 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_3999289 : Nat := 118140960795 + 3999289 * 2 ^ 59
def prefixEnd_3999289 : Nat := 4983230072969 + 3 ^ 40 * 3999289 * 2
def baseEnd_3999289 : Nat := 1369038355492738998063407

theorem tailTrace_3999289 : CollatzResearch.WordTrace tailWord_3999289 prefixEnd_3999289 1369038355492738998063407 := by
  unfold tailWord_3999289
  simp only [CollatzResearch.WordTrace]
  refine ⟨145866053208266452027976921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97244035472177634685317947 145866053208266452027976921)
  ·
    refine ⟨109399539906199839020982691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145866053208266452027976921 109399539906199839020982691)
    ·
      refine ⟨164099309859299758531474037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109399539906199839020982691 164099309859299758531474037)
      ·
        refine ⟨15384310299309352362325691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164099309859299758531474037 15384310299309352362325691)
        ·
          refine ⟨23076465448964028543488537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384310299309352362325691 23076465448964028543488537)
          ·
            refine ⟨17307349086723021407616403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23076465448964028543488537 17307349086723021407616403)
            ·
              refine ⟨25961023630084532111424605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17307349086723021407616403 25961023630084532111424605)
              ·
                refine ⟨9735383861281699541784227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25961023630084532111424605 9735383861281699541784227)
                ·
                  refine ⟨14603075791922549312676341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9735383861281699541784227 14603075791922549312676341)
                  ·
                    refine ⟨1369038355492738998063407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14603075791922549312676341 1369038355492738998063407)
                    ·
                      rfl

theorem cell22_3999289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_3999289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999289 prefixEnd_3999289 := by exact prefixLift 3999289
  have htrace : WordTrace (prefixWord ++ tailWord_3999289) baseStart_3999289 baseEnd_3999289 := by
    simpa [prefixWord, tailWord_3999289, baseEnd_3999289] using wordTrace_append hprefix tailTrace_3999289
  have hstable : (prefixWord ++ tailWord_3999289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999289).length < 2 ^ (prefixWord ++ tailWord_3999289).sum := by decide
  have hdescent : baseEnd_3999289 < baseStart_3999289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999471 : List Nat := [1, 1, 2, 1, 5, 1, 5, 6]
def baseStart_3999471 : Nat := 118140960795 + 3999471 * 2 ^ 59
def prefixEnd_3999471 : Nat := 4983230072969 + 3 ^ 40 * 3999471 * 2
def baseEnd_3999471 : Nat := 152122295312461243334761

theorem tailTrace_3999471 : CollatzResearch.WordTrace tailWord_3999471 prefixEnd_3999471 152122295312461243334761 := by
  unfold tailWord_3999471
  simp only [CollatzResearch.WordTrace]
  refine ⟨145872691293607097111102267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97248460862404731407401511 145872691293607097111102267)
  ·
    refine ⟨218809036940410645666653401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145872691293607097111102267 218809036940410645666653401)
    ·
      refine ⟨164106777705307984249990051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218809036940410645666653401 164106777705307984249990051)
      ·
        refine ⟨246160166557961976374985077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164106777705307984249990051 246160166557961976374985077)
        ·
          refine ⟨23077515614808935285154851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246160166557961976374985077 23077515614808935285154851)
          ·
            refine ⟨34616273422213402927732277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23077515614808935285154851 34616273422213402927732277)
            ·
              refine ⟨3245275633332506524474901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34616273422213402927732277 3245275633332506524474901)
              ·
                refine ⟨152122295312461243334761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3245275633332506524474901 152122295312461243334761)
                ·
                  rfl

theorem cell22_3999471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 6].length) (baseStart_3999471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999471 prefixEnd_3999471 := by exact prefixLift 3999471
  have htrace : WordTrace (prefixWord ++ tailWord_3999471) baseStart_3999471 baseEnd_3999471 := by
    simpa [prefixWord, tailWord_3999471, baseEnd_3999471] using wordTrace_append hprefix tailTrace_3999471
  have hstable : (prefixWord ++ tailWord_3999471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999471).length < 2 ^ (prefixWord ++ tailWord_3999471).sum := by decide
  have hdescent : baseEnd_3999471 < baseStart_3999471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999473 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 2, 4]
def baseStart_3999473 : Nat := 118140960795 + 3999473 * 2 ^ 59
def prefixEnd_3999473 : Nat := 4983230072969 + 3 ^ 40 * 3999473 * 2
def baseEnd_3999473 : Nat := 1369101342453023851462843

theorem tailTrace_3999473 : CollatzResearch.WordTrace tailWord_3999473 prefixEnd_3999473 1369101342453023851462843 := by
  unfold tailWord_3999473
  simp only [CollatzResearch.WordTrace]
  refine ⟨145872764239599851452675073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97248509493066567635116715 145872764239599851452675073)
  ·
    refine ⟨109404573179699888589506305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145872764239599851452675073 109404573179699888589506305)
    ·
      refine ⟨82053429884774916442129729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109404573179699888589506305 82053429884774916442129729)
      ·
        refine ⟨61540072413581187331597297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82053429884774916442129729 61540072413581187331597297)
        ·
          refine ⟨46155054310185890498697973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61540072413581187331597297 46155054310185890498697973)
          ·
            refine ⟨4327036341579927234252935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46155054310185890498697973 4327036341579927234252935)
            ·
              refine ⟨6490554512369890851379403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327036341579927234252935 6490554512369890851379403)
              ·
                refine ⟨9735831768554836277069105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490554512369890851379403 9735831768554836277069105)
                ·
                  refine ⟨7301873826416127207801829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9735831768554836277069105 7301873826416127207801829)
                  ·
                    refine ⟨1369101342453023851462843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7301873826416127207801829 1369101342453023851462843)
                    ·
                      rfl

theorem cell22_3999473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_3999473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999473 prefixEnd_3999473 := by exact prefixLift 3999473
  have htrace : WordTrace (prefixWord ++ tailWord_3999473) baseStart_3999473 baseEnd_3999473 := by
    simpa [prefixWord, tailWord_3999473, baseEnd_3999473] using wordTrace_append hprefix tailTrace_3999473
  have hstable : (prefixWord ++ tailWord_3999473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999473).length < 2 ^ (prefixWord ++ tailWord_3999473).sum := by decide
  have hdescent : baseEnd_3999473 < baseStart_3999473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999537 : List Nat := [1, 2, 2, 3, 2, 4, 1, 3, 1, 3]
def baseStart_3999537 : Nat := 118140960795 + 3999537 * 2 ^ 59
def prefixEnd_3999537 : Nat := 4983230072969 + 3 ^ 40 * 3999537 * 2
def baseEnd_3999537 : Nat := 1369123250960949017862647

theorem tailTrace_3999537 : CollatzResearch.WordTrace tailWord_3999537 prefixEnd_3999537 1369123250960949017862647 := by
  unfold tailWord_3999537
  simp only [CollatzResearch.WordTrace]
  refine ⟨145875098511367990383004865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97250065674245326922003243 145875098511367990383004865)
  ·
    refine ⟨109406323883525992787253649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145875098511367990383004865 109406323883525992787253649)
    ·
      refine ⟨82054742912644494590440237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109406323883525992787253649 82054742912644494590440237)
      ·
        refine ⟨30770528592241685471415089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82054742912644494590440237 30770528592241685471415089)
        ·
          refine ⟨23077896444181264103561317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30770528592241685471415089 23077896444181264103561317)
          ·
            refine ⟨4327105583283987019417747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23077896444181264103561317 4327105583283987019417747)
            ·
              refine ⟨6490658374925980529126621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327105583283987019417747 6490658374925980529126621)
              ·
                refine ⟨2433996890597242698422483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6490658374925980529126621 2433996890597242698422483)
                ·
                  refine ⟨3650995335895864047633725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433996890597242698422483 3650995335895864047633725)
                  ·
                    refine ⟨1369123250960949017862647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650995335895864047633725 1369123250960949017862647)
                    ·
                      rfl

theorem cell22_3999537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_3999537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999537 prefixEnd_3999537 := by exact prefixLift 3999537
  have htrace : WordTrace (prefixWord ++ tailWord_3999537) baseStart_3999537 baseEnd_3999537 := by
    simpa [prefixWord, tailWord_3999537, baseEnd_3999537] using wordTrace_append hprefix tailTrace_3999537
  have hstable : (prefixWord ++ tailWord_3999537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999537).length < 2 ^ (prefixWord ++ tailWord_3999537).sum := by decide
  have hdescent : baseEnd_3999537 < baseStart_3999537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999580 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3999580 : Nat := 118140960795 + 3999580 * 2 ^ 59
def prefixEnd_3999580 : Nat := 4983230072969 + 3 ^ 40 * 3999580 * 2
def baseEnd_3999580 : Nat := 1369137970739711239037515

theorem tailTrace_3999580 : CollatzResearch.WordTrace tailWord_3999580 prefixEnd_3999580 1369137970739711239037515 := by
  unfold tailWord_3999580
  simp only [CollatzResearch.WordTrace]
  refine ⟨72938333425106104363410097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97251111233474805817880129 72938333425106104363410097)
  ·
    refine ⟨54703750068829578272557573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72938333425106104363410097 54703750068829578272557573)
    ·
      refine ⟨10256953137905545926104545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54703750068829578272557573 10256953137905545926104545)
      ·
        refine ⟨7692714853429159444578409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10256953137905545926104545 7692714853429159444578409)
        ·
          refine ⟨5769536140071869583433807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7692714853429159444578409 5769536140071869583433807)
          ·
            refine ⟨8654304210107804375150711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769536140071869583433807 8654304210107804375150711)
            ·
              refine ⟨12981456315161706562726067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8654304210107804375150711 12981456315161706562726067)
              ·
                refine ⟨19472184472742559844089101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12981456315161706562726067 19472184472742559844089101)
                ·
                  refine ⟨7302069177278459941533413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19472184472742559844089101 7302069177278459941533413)
                  ·
                    refine ⟨1369137970739711239037515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302069177278459941533413 1369137970739711239037515)
                    ·
                      rfl

theorem cell22_3999580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3999580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999580 prefixEnd_3999580 := by exact prefixLift 3999580
  have htrace : WordTrace (prefixWord ++ tailWord_3999580) baseStart_3999580 baseEnd_3999580 := by
    simpa [prefixWord, tailWord_3999580, baseEnd_3999580] using wordTrace_append hprefix tailTrace_3999580
  have hstable : (prefixWord ++ tailWord_3999580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999580).length < 2 ^ (prefixWord ++ tailWord_3999580).sum := by decide
  have hdescent : baseEnd_3999580 < baseStart_3999580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999651 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 7]
def baseStart_3999651 : Nat := 118140960795 + 3999651 * 2 ^ 59
def prefixEnd_3999651 : Nat := 4983230072969 + 3 ^ 40 * 3999651 * 2
def baseEnd_3999651 : Nat := 456387425163563573504099

theorem tailTrace_3999651 : CollatzResearch.WordTrace tailWord_3999651 prefixEnd_3999651 456387425163563573504099 := by
  unfold tailWord_3999651
  simp only [CollatzResearch.WordTrace]
  refine ⟨145879256432954987852654807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97252837621969991901769871 145879256432954987852654807)
  ·
    refine ⟨218818884649432481778982211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145879256432954987852654807 218818884649432481778982211)
    ·
      refine ⟨328228326974148722668473317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218818884649432481778982211 328228326974148722668473317)
      ·
        refine ⟨61542811307652885500338747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328228326974148722668473317 61542811307652885500338747)
        ·
          refine ⟨92314216961479328250508121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61542811307652885500338747 92314216961479328250508121)
          ·
            refine ⟨69235662721109496187881091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92314216961479328250508121 69235662721109496187881091)
            ·
              refine ⟨103853494081664244281821637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69235662721109496187881091 103853494081664244281821637)
              ·
                refine ⟨19472530140312045802841557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103853494081664244281821637 19472530140312045802841557)
                ·
                  refine ⟨456387425163563573504099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19472530140312045802841557 456387425163563573504099)
                  ·
                    rfl

theorem cell22_3999651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_3999651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999651 prefixEnd_3999651 := by exact prefixLift 3999651
  have htrace : WordTrace (prefixWord ++ tailWord_3999651) baseStart_3999651 baseEnd_3999651 := by
    simpa [prefixWord, tailWord_3999651, baseEnd_3999651] using wordTrace_append hprefix tailTrace_3999651
  have hstable : (prefixWord ++ tailWord_3999651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999651).length < 2 ^ (prefixWord ++ tailWord_3999651).sum := by decide
  have hdescent : baseEnd_3999651 < baseStart_3999651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999706 : List Nat := [3, 1, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_3999706 : Nat := 118140960795 + 3999706 * 2 ^ 59
def prefixEnd_3999706 : Nat := 4983230072969 + 3 ^ 40 * 3999706 * 2
def baseEnd_3999706 : Nat := 1369181103114688910387129

theorem tailTrace_3999706 : CollatzResearch.WordTrace tailWord_3999706 prefixEnd_3999706 1369181103114688910387129 := by
  unfold tailWord_3999706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36470315611938933061476743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97254174965170488163937981 36470315611938933061476743)
  ·
    refine ⟨54705473417908399592215115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36470315611938933061476743 54705473417908399592215115)
    ·
      refine ⟨82058210126862599388322673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54705473417908399592215115 82058210126862599388322673)
      ·
        refine ⟨61543657595146949541242005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82058210126862599388322673 61543657595146949541242005)
        ·
          refine ⟨2884858949772513259745719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61543657595146949541242005 2884858949772513259745719)
          ·
            refine ⟨4327288424658769889618579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884858949772513259745719 4327288424658769889618579)
            ·
              refine ⟨6490932636988154834427869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327288424658769889618579 6490932636988154834427869)
              ·
                refine ⟨2434099738870558062910451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6490932636988154834427869 2434099738870558062910451)
                ·
                  refine ⟨3651149608305837094365677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434099738870558062910451 3651149608305837094365677)
                  ·
                    refine ⟨1369181103114688910387129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3651149608305837094365677 1369181103114688910387129)
                    ·
                      rfl

theorem cell22_3999706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_3999706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999706 prefixEnd_3999706 := by exact prefixLift 3999706
  have htrace : WordTrace (prefixWord ++ tailWord_3999706) baseStart_3999706 baseEnd_3999706 := by
    simpa [prefixWord, tailWord_3999706, baseEnd_3999706] using wordTrace_append hprefix tailTrace_3999706
  have hstable : (prefixWord ++ tailWord_3999706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999706).length < 2 ^ (prefixWord ++ tailWord_3999706).sum := by decide
  have hdescent : baseEnd_3999706 < baseStart_3999706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999715 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 1, 4]
def baseStart_3999715 : Nat := 118140960795 + 3999715 * 2 ^ 59
def prefixEnd_3999715 : Nat := 4983230072969 + 3 ^ 40 * 3999715 * 2
def baseEnd_3999715 : Nat := 1369184183998615886912101

theorem tailTrace_3999715 : CollatzResearch.WordTrace tailWord_3999715 prefixEnd_3999715 1369184183998615886912101 := by
  unfold tailWord_3999715
  simp only [CollatzResearch.WordTrace]
  refine ⟨145881590704723126782984599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97254393803148751188656399 145881590704723126782984599)
  ·
    refine ⟨218822386057084690174476899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145881590704723126782984599 218822386057084690174476899)
    ·
      refine ⟨328233579085627035261715349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218822386057084690174476899 328233579085627035261715349)
      ·
        refine ⟨15385949019638767277892907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 328233579085627035261715349 15385949019638767277892907)
        ·
          refine ⟨23078923529458150916839361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15385949019638767277892907 23078923529458150916839361)
          ·
            refine ⟨17309192647093613187629521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23078923529458150916839361 17309192647093613187629521)
            ·
              refine ⟨12981894485320209890722141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17309192647093613187629521 12981894485320209890722141)
              ·
                refine ⟨4868210431995078709020803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12981894485320209890722141 4868210431995078709020803)
                ·
                  refine ⟨7302315647992618063531205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868210431995078709020803 7302315647992618063531205)
                  ·
                    refine ⟨1369184183998615886912101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302315647992618063531205 1369184183998615886912101)
                    ·
                      rfl

theorem cell22_3999715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 4].length) (baseStart_3999715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999715 prefixEnd_3999715 := by exact prefixLift 3999715
  have htrace : WordTrace (prefixWord ++ tailWord_3999715) baseStart_3999715 baseEnd_3999715 := by
    simpa [prefixWord, tailWord_3999715, baseEnd_3999715] using wordTrace_append hprefix tailTrace_3999715
  have hstable : (prefixWord ++ tailWord_3999715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999715).length < 2 ^ (prefixWord ++ tailWord_3999715).sum := by decide
  have hdescent : baseEnd_3999715 < baseStart_3999715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999758 : List Nat := [4, 1, 1, 2, 2, 1, 1, 10]
def baseStart_3999758 : Nat := 118140960795 + 3999758 * 2 ^ 59
def prefixEnd_3999758 : Nat := 4983230072969 + 3 ^ 40 * 3999758 * 2
def baseEnd_3999758 : Nat := 152133211530819789787441

theorem tailTrace_3999758 : CollatzResearch.WordTrace tailWord_3999758 prefixEnd_3999758 152133211530819789787441 := by
  unfold tailWord_3999758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18235394880445918140849991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97255439362378230084533285 18235394880445918140849991)
  ·
    refine ⟨27353092320668877211274987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18235394880445918140849991 27353092320668877211274987)
    ·
      refine ⟨41029638481003315816912481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27353092320668877211274987 41029638481003315816912481)
      ·
        refine ⟨30772228860752486862684361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41029638481003315816912481 30772228860752486862684361)
        ·
          refine ⟨23079171645564365147013271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30772228860752486862684361 23079171645564365147013271)
          ·
            refine ⟨34618757468346547720519907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23079171645564365147013271 34618757468346547720519907)
            ·
              refine ⟨51928136202519821580779861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34618757468346547720519907 51928136202519821580779861)
              ·
                refine ⟨152133211530819789787441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51928136202519821580779861 152133211530819789787441)
                ·
                  rfl

theorem cell22_3999758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_3999758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999758 prefixEnd_3999758 := by exact prefixLift 3999758
  have htrace : WordTrace (prefixWord ++ tailWord_3999758) baseStart_3999758 baseEnd_3999758 := by
    simpa [prefixWord, tailWord_3999758, baseEnd_3999758] using wordTrace_append hprefix tailTrace_3999758
  have hstable : (prefixWord ++ tailWord_3999758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999758).length < 2 ^ (prefixWord ++ tailWord_3999758).sum := by decide
  have hdescent : baseEnd_3999758 < baseStart_3999758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999818 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_3999818 : Nat := 118140960795 + 3999818 * 2 ^ 59
def prefixEnd_3999818 : Nat := 4983230072969 + 3 ^ 40 * 3999818 * 2
def baseEnd_3999818 : Nat := 1369219443003557951586785

theorem tailTrace_3999818 : CollatzResearch.WordTrace tailWord_3999818 prefixEnd_3999818 1369219443003557951586785 := by
  unfold tailWord_3999818
  simp only [CollatzResearch.WordTrace]
  refine ⟨36471336855837493843496027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97256898282233316915989405 36471336855837493843496027)
  ·
    refine ⟨54707005283756240765244041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36471336855837493843496027 54707005283756240765244041)
    ·
      refine ⟨41030253962817180573933031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54707005283756240765244041 41030253962817180573933031)
      ·
        refine ⟨61545380944225770860899547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41030253962817180573933031 61545380944225770860899547)
        ·
          refine ⟨92318071416338656291349321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61545380944225770860899547 92318071416338656291349321)
          ·
            refine ⟨69238553562253992218511991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92318071416338656291349321 69238553562253992218511991)
            ·
              refine ⟨103857830343380988327767987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69238553562253992218511991 103857830343380988327767987)
              ·
                refine ⟨155786745515071482491651981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103857830343380988327767987 155786745515071482491651981)
                ·
                  refine ⟨58420029568151805934369493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155786745515071482491651981 58420029568151805934369493)
                  ·
                    refine ⟨1369219443003557951586785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58420029568151805934369493 1369219443003557951586785)
                    ·
                      rfl

theorem cell22_3999818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_3999818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999818 prefixEnd_3999818 := by exact prefixLift 3999818
  have htrace : WordTrace (prefixWord ++ tailWord_3999818) baseStart_3999818 baseEnd_3999818 := by
    simpa [prefixWord, tailWord_3999818, baseEnd_3999818] using wordTrace_append hprefix tailTrace_3999818
  have hstable : (prefixWord ++ tailWord_3999818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999818).length < 2 ^ (prefixWord ++ tailWord_3999818).sum := by decide
  have hdescent : baseEnd_3999818 < baseStart_3999818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999837 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3999837 : Nat := 118140960795 + 3999837 * 2 ^ 59
def prefixEnd_3999837 : Nat := 4983230072969 + 3 ^ 40 * 3999837 * 2
def baseEnd_3999837 : Nat := 456408649030616078453909

theorem tailTrace_3999837 : CollatzResearch.WordTrace tailWord_3999837 prefixEnd_3999837 456408649030616078453909 := by
  unfold tailWord_3999837
  simp only [CollatzResearch.WordTrace]
  refine ⟨145886040410281141618925765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97257360273520761079283843 145886040410281141618925765)
  ·
    refine ⟨27353632576927714053548581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145886040410281141618925765 27353632576927714053548581)
    ·
      refine ⟨5128806108173946385040359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27353632576927714053548581 5128806108173946385040359)
      ·
        refine ⟨7693209162260919577560539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128806108173946385040359 7693209162260919577560539)
        ·
          refine ⟨11539813743391379366340809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7693209162260919577560539 11539813743391379366340809)
          ·
            refine ⟨8654860307543534524755607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11539813743391379366340809 8654860307543534524755607)
            ·
              refine ⟨12982290461315301787133411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8654860307543534524755607 12982290461315301787133411)
              ·
                refine ⟨19473435691972952680700117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12982290461315301787133411 19473435691972952680700117)
                ·
                  refine ⟨456408649030616078453909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19473435691972952680700117 456408649030616078453909)
                  ·
                    rfl

theorem cell22_3999837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3999837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999837 prefixEnd_3999837 := by exact prefixLift 3999837
  have htrace : WordTrace (prefixWord ++ tailWord_3999837) baseStart_3999837 baseEnd_3999837 := by
    simpa [prefixWord, tailWord_3999837, baseEnd_3999837] using wordTrace_append hprefix tailTrace_3999837
  have hstable : (prefixWord ++ tailWord_3999837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999837).length < 2 ^ (prefixWord ++ tailWord_3999837).sum := by decide
  have hdescent : baseEnd_3999837 < baseStart_3999837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999865 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 6]
def baseStart_3999865 : Nat := 118140960795 + 3999865 * 2 ^ 59
def prefixEnd_3999865 : Nat := 4983230072969 + 3 ^ 40 * 3999865 * 2
def baseEnd_3999865 : Nat := 456411844021355165220547

theorem tailTrace_3999865 : CollatzResearch.WordTrace tailWord_3999865 prefixEnd_3999865 456411844021355165220547 := by
  unfold tailWord_3999865
  simp only [CollatzResearch.WordTrace]
  refine ⟨145887061654179702400945049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97258041102786468267296699 145887061654179702400945049)
  ·
    refine ⟨109415296240634776800708787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145887061654179702400945049 109415296240634776800708787)
    ·
      refine ⟨164122944360952165201063181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109415296240634776800708787 164122944360952165201063181)
      ·
        refine ⟨61546104135357061950398693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164122944360952165201063181 61546104135357061950398693)
        ·
          refine ⟨11539894525379449115699755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61546104135357061950398693 11539894525379449115699755)
          ·
            refine ⟨17309841788069173673549633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11539894525379449115699755 17309841788069173673549633)
            ·
              refine ⟨12982381341051880255162225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17309841788069173673549633 12982381341051880255162225)
              ·
                refine ⟨9736786005788910191371669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12982381341051880255162225 9736786005788910191371669)
                ·
                  refine ⟨456411844021355165220547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9736786005788910191371669 456411844021355165220547)
                  ·
                    rfl

theorem cell22_3999865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_3999865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999865 prefixEnd_3999865 := by exact prefixLift 3999865
  have htrace : WordTrace (prefixWord ++ tailWord_3999865) baseStart_3999865 baseEnd_3999865 := by
    simpa [prefixWord, tailWord_3999865, baseEnd_3999865] using wordTrace_append hprefix tailTrace_3999865
  have hstable : (prefixWord ++ tailWord_3999865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999865).length < 2 ^ (prefixWord ++ tailWord_3999865).sum := by decide
  have hdescent : baseEnd_3999865 < baseStart_3999865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999918 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3999918 : Nat := 118140960795 + 3999918 * 2 ^ 59
def prefixEnd_3999918 : Nat := 4983230072969 + 3 ^ 40 * 3999918 * 2
def baseEnd_3999918 : Nat := 1369253675047191024086479

theorem tailTrace_3999918 : CollatzResearch.WordTrace tailWord_3999918 prefixEnd_3999918 1369253675047191024086479 := by
  unfold tailWord_3999918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18236124340373461556578051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97259329815325128301749605 18236124340373461556578051)
  ·
    refine ⟨27354186510560192334867077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18236124340373461556578051 27354186510560192334867077)
    ·
      refine ⟨5128909970730036062787577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27354186510560192334867077 5128909970730036062787577)
      ·
        refine ⟨3846682478047527047090683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5128909970730036062787577 3846682478047527047090683)
        ·
          refine ⟨5770023717071290570636025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846682478047527047090683 5770023717071290570636025)
          ·
            refine ⟨4327517787803467927977019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5770023717071290570636025 4327517787803467927977019)
            ·
              refine ⟨6491276681705201891965529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327517787803467927977019 6491276681705201891965529)
              ·
                refine ⟨4868457511278901418974147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6491276681705201891965529 4868457511278901418974147)
                ·
                  refine ⟨7302686266918352128461221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868457511278901418974147 7302686266918352128461221)
                  ·
                    refine ⟨1369253675047191024086479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302686266918352128461221 1369253675047191024086479)
                    ·
                      rfl

theorem cell22_3999918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3999918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3999918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3999918 prefixEnd_3999918 := by exact prefixLift 3999918
  have htrace : WordTrace (prefixWord ++ tailWord_3999918) baseStart_3999918 baseEnd_3999918 := by
    simpa [prefixWord, tailWord_3999918, baseEnd_3999918] using wordTrace_append hprefix tailTrace_3999918
  have hstable : (prefixWord ++ tailWord_3999918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999918).length < 2 ^ (prefixWord ++ tailWord_3999918).sum := by decide
  have hdescent : baseEnd_3999918 < baseStart_3999918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000015 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 3, 5]
def baseStart_4000015 : Nat := 118140960795 + 4000015 * 2 ^ 59
def prefixEnd_4000015 : Nat := 4983230072969 + 3 ^ 40 * 4000015 * 2
def baseEnd_4000015 : Nat := 1369286880129515104411181

theorem tailTrace_4000015 : CollatzResearch.WordTrace tailWord_4000015 prefixEnd_4000015 1369286880129515104411181 := by
  unfold tailWord_4000015
  simp only [CollatzResearch.WordTrace]
  refine ⟨145892532603636278018905499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97261688402424185345936999 145892532603636278018905499)
  ·
    refine ⟨218838798905454417028358249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145892532603636278018905499 218838798905454417028358249)
    ·
      refine ⟨164129099179090812771268687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218838798905454417028358249 164129099179090812771268687)
      ·
        refine ⟨246193648768636219156903031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164129099179090812771268687 246193648768636219156903031)
        ·
          refine ⟨369290473152954328735354547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246193648768636219156903031 369290473152954328735354547)
          ·
            refine ⟨553935709729431493103031821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369290473152954328735354547 553935709729431493103031821)
            ·
              refine ⟨207725891148536809913636933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553935709729431493103031821 207725891148536809913636933)
              ·
                refine ⟨38948604590350651858806925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207725891148536809913636933 38948604590350651858806925)
                ·
                  refine ⟨14605726721381494447052597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38948604590350651858806925 14605726721381494447052597)
                  ·
                    refine ⟨1369286880129515104411181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14605726721381494447052597 1369286880129515104411181)
                    ·
                      rfl

theorem cell22_4000015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_4000015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000015 prefixEnd_4000015 := by exact prefixLift 4000015
  have htrace : WordTrace (prefixWord ++ tailWord_4000015) baseStart_4000015 baseEnd_4000015 := by
    simpa [prefixWord, tailWord_4000015, baseEnd_4000015] using wordTrace_append hprefix tailTrace_4000015
  have hstable : (prefixWord ++ tailWord_4000015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000015).length < 2 ^ (prefixWord ++ tailWord_4000015).sum := by decide
  have hdescent : baseEnd_4000015 < baseStart_4000015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000017 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 6]
def baseStart_4000017 : Nat := 118140960795 + 4000017 * 2 ^ 59
def prefixEnd_4000017 : Nat := 4983230072969 + 3 ^ 40 * 4000017 * 2
def baseEnd_4000017 : Nat := 456429188256795921953725

theorem tailTrace_4000017 : CollatzResearch.WordTrace tailWord_4000017 prefixEnd_4000017 456429188256795921953725 := by
  unfold tailWord_4000017
  simp only [CollatzResearch.WordTrace]
  refine ⟨145892605549629032360478305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97261737033086021573652203 145892605549629032360478305)
  ·
    refine ⟨109419454162221774270358729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145892605549629032360478305 109419454162221774270358729)
    ·
      refine ⟨82064590621666330702769047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109419454162221774270358729 82064590621666330702769047)
      ·
        refine ⟨123096885932499496054153571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82064590621666330702769047 123096885932499496054153571)
        ·
          refine ⟨184645328898749244081230357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123096885932499496054153571 184645328898749244081230357)
          ·
            refine ⟨8655249792128870816307673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184645328898749244081230357 8655249792128870816307673)
            ·
              refine ⟨6491437344096653112230755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655249792128870816307673 6491437344096653112230755)
              ·
                refine ⟨9737156016144979668346133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491437344096653112230755 9737156016144979668346133)
                ·
                  refine ⟨456429188256795921953725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9737156016144979668346133 456429188256795921953725)
                  ·
                    rfl

theorem cell22_4000017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_4000017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000017 prefixEnd_4000017 := by exact prefixLift 4000017
  have htrace : WordTrace (prefixWord ++ tailWord_4000017) baseStart_4000017 baseEnd_4000017 := by
    simpa [prefixWord, tailWord_4000017, baseEnd_4000017] using wordTrace_append hprefix tailTrace_4000017
  have hstable : (prefixWord ++ tailWord_4000017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000017).length < 2 ^ (prefixWord ++ tailWord_4000017).sum := by decide
  have hdescent : baseEnd_4000017 < baseStart_4000017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000062 : List Nat := [4, 2, 1, 2, 1, 2, 10]
def baseStart_4000062 : Nat := 118140960795 + 4000062 * 2 ^ 59
def prefixEnd_4000062 : Nat := 4983230072969 + 3 ^ 40 * 4000062 * 2
def baseEnd_4000062 : Nat := 50714924784815653647631

theorem tailTrace_4000062 : CollatzResearch.WordTrace tailWord_4000062 prefixEnd_4000062 50714924784815653647631 := by
  unfold tailWord_4000062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18236780854308250630733305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97262831222977336697244293 18236780854308250630733305)
  ·
    refine ⟨13677585640731187973049979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18236780854308250630733305 13677585640731187973049979)
    ·
      refine ⟨20516378461096781959574969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13677585640731187973049979 20516378461096781959574969)
      ·
        refine ⟨15387283845822586469681227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20516378461096781959574969 15387283845822586469681227)
        ·
          refine ⟨23080925768733879704521841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15387283845822586469681227 23080925768733879704521841)
          ·
            refine ⟨17310694326550409778391381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23080925768733879704521841 17310694326550409778391381)
            ·
              refine ⟨50714924784815653647631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17310694326550409778391381 50714924784815653647631)
              ·
                rfl

theorem cell22_4000062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 10].length) (baseStart_4000062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000062 prefixEnd_4000062 := by exact prefixLift 4000062
  have htrace : WordTrace (prefixWord ++ tailWord_4000062) baseStart_4000062 baseEnd_4000062 := by
    simpa [prefixWord, tailWord_4000062, baseEnd_4000062] using wordTrace_append hprefix tailTrace_4000062
  have hstable : (prefixWord ++ tailWord_4000062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000062).length < 2 ^ (prefixWord ++ tailWord_4000062).sum := by decide
  have hdescent : baseEnd_4000062 < baseStart_4000062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000068 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 6]
def baseStart_4000068 : Nat := 118140960795 + 4000068 * 2 ^ 59
def prefixEnd_4000068 : Nat := 4983230072969 + 3 ^ 40 * 4000068 * 2
def baseEnd_4000068 : Nat := 456435007704213544278673

theorem tailTrace_4000068 : CollatzResearch.WordTrace tailWord_4000068 prefixEnd_4000068 456435007704213544278673 := by
  unfold tailWord_4000068
  simp only [CollatzResearch.WordTrace]
  refine ⟨72947232836222134035292429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97262977114962845380389905 72947232836222134035292429)
  ·
    refine ⟨27355212313583300263234661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72947232836222134035292429 27355212313583300263234661)
    ·
      refine ⟨5129102308796868799356499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27355212313583300263234661 5129102308796868799356499)
      ·
        refine ⟨7693653463195303199034749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129102308796868799356499 7693653463195303199034749)
        ·
          refine ⟨2885120048698238699638031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7693653463195303199034749 2885120048698238699638031)
          ·
            refine ⟨4327680073047358049457047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885120048698238699638031 4327680073047358049457047)
            ·
              refine ⟨6491520109571037074185571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327680073047358049457047 6491520109571037074185571)
              ·
                refine ⟨9737280164356555611278357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491520109571037074185571 9737280164356555611278357)
                ·
                  refine ⟨456435007704213544278673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9737280164356555611278357 456435007704213544278673)
                  ·
                    rfl

theorem cell22_4000068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_4000068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000068 prefixEnd_4000068 := by exact prefixLift 4000068
  have htrace : WordTrace (prefixWord ++ tailWord_4000068) baseStart_4000068 baseEnd_4000068 := by
    simpa [prefixWord, tailWord_4000068, baseEnd_4000068] using wordTrace_append hprefix tailTrace_4000068
  have hstable : (prefixWord ++ tailWord_4000068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000068).length < 2 ^ (prefixWord ++ tailWord_4000068).sum := by decide
  have hdescent : baseEnd_4000068 < baseStart_4000068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000154 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_4000154 : Nat := 118140960795 + 4000154 * 2 ^ 59
def prefixEnd_4000154 : Nat := 4983230072969 + 3 ^ 40 * 4000154 * 2
def baseEnd_4000154 : Nat := 1369334462670165075185755

theorem tailTrace_4000154 : CollatzResearch.WordTrace tailWord_4000154 prefixEnd_4000154 1369334462670165075185755 := by
  unfold tailWord_4000154
  simp only [CollatzResearch.WordTrace]
  refine ⟨36474400587533176189553879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97265068233421803172143677 36474400587533176189553879)
  ·
    refine ⟨54711600881299764284330819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36474400587533176189553879 54711600881299764284330819)
    ·
      refine ⟨82067401321949646426496229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54711600881299764284330819 82067401321949646426496229)
      ·
        refine ⟨15387637747865558704968043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82067401321949646426496229 15387637747865558704968043)
        ·
          refine ⟨23081456621798338057452065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15387637747865558704968043 23081456621798338057452065)
          ·
            refine ⟨17311092466348753543089049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23081456621798338057452065 17311092466348753543089049)
            ·
              refine ⟨12983319349761565157316787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17311092466348753543089049 12983319349761565157316787)
              ·
                refine ⟨19474979024642347735975181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12983319349761565157316787 19474979024642347735975181)
                ·
                  refine ⟨7303117134240880400990693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19474979024642347735975181 7303117134240880400990693)
                  ·
                    refine ⟨1369334462670165075185755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7303117134240880400990693 1369334462670165075185755)
                    ·
                      rfl

theorem cell22_4000154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_4000154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000154 prefixEnd_4000154 := by exact prefixLift 4000154
  have htrace : WordTrace (prefixWord ++ tailWord_4000154) baseStart_4000154 baseEnd_4000154 := by
    simpa [prefixWord, tailWord_4000154, baseEnd_4000154] using wordTrace_append hprefix tailTrace_4000154
  have hstable : (prefixWord ++ tailWord_4000154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000154).length < 2 ^ (prefixWord ++ tailWord_4000154).sum := by decide
  have hdescent : baseEnd_4000154 < baseStart_4000154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000259 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 5]
def baseStart_4000259 : Nat := 118140960795 + 4000259 * 2 ^ 59
def prefixEnd_4000259 : Nat := 4983230072969 + 3 ^ 40 * 4000259 * 2
def baseEnd_4000259 : Nat := 456456802105326600436811

theorem tailTrace_4000259 : CollatzResearch.WordTrace tailWord_4000259 prefixEnd_4000259 456456802105326600436811 := by
  unfold tailWord_4000259
  simp only [CollatzResearch.WordTrace]
  refine ⟨145901432014752307690787831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97267621343168205127191887 145901432014752307690787831)
  ·
    refine ⟨218852148022128461536181747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145901432014752307690787831 218852148022128461536181747)
    ·
      refine ⟨328278222033192692304272621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218852148022128461536181747 328278222033192692304272621)
      ·
        refine ⟨123104333262447259614102233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328278222033192692304272621 123104333262447259614102233)
        ·
          refine ⟨92328249946835444710576675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123104333262447259614102233 92328249946835444710576675)
          ·
            refine ⟨138492374920253167065865013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92328249946835444710576675 138492374920253167065865013)
            ·
              refine ⟨12983660148773734412424845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138492374920253167065865013 12983660148773734412424845)
              ·
                refine ⟨4868872555790150404659317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12983660148773734412424845 4868872555790150404659317)
                ·
                  refine ⟨456456802105326600436811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4868872555790150404659317 456456802105326600436811)
                  ·
                    rfl

theorem cell22_4000259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 5].length) (baseStart_4000259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000259 prefixEnd_4000259 := by exact prefixLift 4000259
  have htrace : WordTrace (prefixWord ++ tailWord_4000259) baseStart_4000259 baseEnd_4000259 := by
    simpa [prefixWord, tailWord_4000259, baseEnd_4000259] using wordTrace_append hprefix tailTrace_4000259
  have hstable : (prefixWord ++ tailWord_4000259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000259).length < 2 ^ (prefixWord ++ tailWord_4000259).sum := by decide
  have hdescent : baseEnd_4000259 < baseStart_4000259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000321 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 6]
def baseStart_4000321 : Nat := 118140960795 + 4000321 * 2 ^ 59
def prefixEnd_4000321 : Nat := 4983230072969 + 3 ^ 40 * 4000321 * 2
def baseEnd_4000321 : Nat := 456463876727677435420081

theorem tailTrace_4000321 : CollatzResearch.WordTrace tailWord_4000321 prefixEnd_4000321 456463876727677435420081 := by
  unfold tailWord_4000321
  simp only [CollatzResearch.WordTrace]
  refine ⟨145903693340527692279544817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97269128893685128186363211 145903693340527692279544817)
  ·
    refine ⟨109427770005395769209658613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145903693340527692279544817 109427770005395769209658613)
    ·
      refine ⟨10258853438005853363405495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109427770005395769209658613 10258853438005853363405495)
      ·
        refine ⟨15388280157008780045108243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10258853438005853363405495 15388280157008780045108243)
        ·
          refine ⟨23082420235513170067662365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15388280157008780045108243 23082420235513170067662365)
          ·
            refine ⟨8655907588317438775373387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23082420235513170067662365 8655907588317438775373387)
            ·
              refine ⟨12983861382476158163060081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8655907588317438775373387 12983861382476158163060081)
              ·
                refine ⟨9737896036857118622295061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12983861382476158163060081 9737896036857118622295061)
                ·
                  refine ⟨456463876727677435420081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9737896036857118622295061 456463876727677435420081)
                  ·
                    rfl

theorem cell22_4000321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_4000321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000321 prefixEnd_4000321 := by exact prefixLift 4000321
  have htrace : WordTrace (prefixWord ++ tailWord_4000321) baseStart_4000321 baseEnd_4000321 := by
    simpa [prefixWord, tailWord_4000321, baseEnd_4000321] using wordTrace_append hprefix tailTrace_4000321
  have hstable : (prefixWord ++ tailWord_4000321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000321).length < 2 ^ (prefixWord ++ tailWord_4000321).sum := by decide
  have hdescent : baseEnd_4000321 < baseStart_4000321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000338 : List Nat := [3, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_4000338 : Nat := 118140960795 + 4000338 * 2 ^ 59
def prefixEnd_4000338 : Nat := 4983230072969 + 3 ^ 40 * 4000338 * 2
def baseEnd_4000338 : Nat := 456465816543483309528397

theorem tailTrace_4000338 : CollatzResearch.WordTrace tailWord_4000338 prefixEnd_4000338 456465816543483309528397 := by
  unfold tailWord_4000338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36476078345366526045728417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97269542254310736121942445 36476078345366526045728417)
  ·
    refine ⟨27357058759024894534296313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36476078345366526045728417 27357058759024894534296313)
    ·
      refine ⟨20517794069268670900722235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27357058759024894534296313 20517794069268670900722235)
      ·
        refine ⟨30776691103903006351083353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20517794069268670900722235 30776691103903006351083353)
        ·
          refine ⟨23082518327927254763312515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30776691103903006351083353 23082518327927254763312515)
          ·
            refine ⟨34623777491890882144968773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23082518327927254763312515 34623777491890882144968773)
            ·
              refine ⟨6491958279729540402181645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34623777491890882144968773 6491958279729540402181645)
              ·
                refine ⟨2434484354898577650818117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6491958279729540402181645 2434484354898577650818117)
                ·
                  refine ⟨456465816543483309528397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434484354898577650818117 456465816543483309528397)
                  ·
                    rfl

theorem cell22_4000338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_4000338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000338 prefixEnd_4000338 := by exact prefixLift 4000338
  have htrace : WordTrace (prefixWord ++ tailWord_4000338) baseStart_4000338 baseEnd_4000338 := by
    simpa [prefixWord, tailWord_4000338, baseEnd_4000338] using wordTrace_append hprefix tailTrace_4000338
  have hstable : (prefixWord ++ tailWord_4000338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000338).length < 2 ^ (prefixWord ++ tailWord_4000338).sum := by decide
  have hdescent : baseEnd_4000338 < baseStart_4000338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000340 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4000340 : Nat := 118140960795 + 4000340 * 2 ^ 59
def prefixEnd_4000340 : Nat := 4983230072969 + 3 ^ 40 * 4000340 * 2
def baseEnd_4000340 : Nat := 1369398134271322590035185

theorem tailTrace_4000340 : CollatzResearch.WordTrace tailWord_4000340 prefixEnd_4000340 1369398134271322590035185 := by
  unfold tailWord_4000340
  simp only [CollatzResearch.WordTrace]
  refine ⟨72952193163729429262243237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97269590884972572349657649 72952193163729429262243237)
  ·
    refine ⟨13678536218199267986670607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72952193163729429262243237 13678536218199267986670607)
    ·
      refine ⟨20517804327298901980005911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13678536218199267986670607 20517804327298901980005911)
      ·
        refine ⟨30776706490948352970008867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20517804327298901980005911 30776706490948352970008867)
        ·
          refine ⟨46165059736422529455013301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30776706490948352970008867 46165059736422529455013301)
          ·
            refine ⟨4327974350289612136407497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46165059736422529455013301 4327974350289612136407497)
            ·
              refine ⟨3245980762717209102305623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4327974350289612136407497 3245980762717209102305623)
              ·
                refine ⟨4868971144075813653458435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245980762717209102305623 4868971144075813653458435)
                ·
                  refine ⟨7303456716113720480187653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868971144075813653458435 7303456716113720480187653)
                  ·
                    refine ⟨1369398134271322590035185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7303456716113720480187653 1369398134271322590035185)
                    ·
                      rfl

theorem cell22_4000340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4000340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000340 prefixEnd_4000340 := by exact prefixLift 4000340
  have htrace : WordTrace (prefixWord ++ tailWord_4000340) baseStart_4000340 baseEnd_4000340 := by
    simpa [prefixWord, tailWord_4000340, baseEnd_4000340] using wordTrace_append hprefix tailTrace_4000340
  have hstable : (prefixWord ++ tailWord_4000340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000340).length < 2 ^ (prefixWord ++ tailWord_4000340).sum := by decide
  have hdescent : baseEnd_4000340 < baseStart_4000340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000353 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 2, 3]
def baseStart_4000353 : Nat := 118140960795 + 4000353 * 2 ^ 59
def prefixEnd_4000353 : Nat := 4983230072969 + 3 ^ 40 * 4000353 * 2
def baseEnd_4000353 : Nat := 1369402584436994889460145

theorem tailTrace_4000353 : CollatzResearch.WordTrace tailWord_4000353 prefixEnd_4000353 1369402584436994889460145 := by
  unfold tailWord_4000353
  simp only [CollatzResearch.WordTrace]
  refine ⟨145904860476411761744709713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97269906984274507829806475 145904860476411761744709713)
  ·
    refine ⟨109428645357308821308532285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145904860476411761744709713 109428645357308821308532285)
    ·
      refine ⟨41035742008990807990699607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109428645357308821308532285 41035742008990807990699607)
      ·
        refine ⟨61553613013486211986049411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41035742008990807990699607 61553613013486211986049411)
        ·
          refine ⟨92330419520229317979074117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61553613013486211986049411 92330419520229317979074117)
          ·
            refine ⟨17311953660042997121076397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92330419520229317979074117 17311953660042997121076397)
            ·
              refine ⟨6491982622516123920403649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17311953660042997121076397 6491982622516123920403649)
              ·
                refine ⟨4868986966887092940302737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6491982622516123920403649 4868986966887092940302737)
                ·
                  refine ⟨3651740225165319705227053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4868986966887092940302737 3651740225165319705227053)
                  ·
                    refine ⟨1369402584436994889460145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3651740225165319705227053 1369402584436994889460145)
                    ·
                      rfl

theorem cell22_4000353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_4000353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000353 prefixEnd_4000353 := by exact prefixLift 4000353
  have htrace : WordTrace (prefixWord ++ tailWord_4000353) baseStart_4000353 baseEnd_4000353 := by
    simpa [prefixWord, tailWord_4000353, baseEnd_4000353] using wordTrace_append hprefix tailTrace_4000353
  have hstable : (prefixWord ++ tailWord_4000353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000353).length < 2 ^ (prefixWord ++ tailWord_4000353).sum := by decide
  have hdescent : baseEnd_4000353 < baseStart_4000353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000370 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_4000370 : Nat := 118140960795 + 4000370 * 2 ^ 59
def prefixEnd_4000370 : Nat := 4983230072969 + 3 ^ 40 * 4000370 * 2
def baseEnd_4000370 : Nat := 1369408403884412511785093

theorem tailTrace_4000370 : CollatzResearch.WordTrace tailWord_4000370 prefixEnd_4000370 1369408403884412511785093 := by
  unfold tailWord_4000370
  simp only [CollatzResearch.WordTrace]
  refine ⟨36476370129337543412019641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97270320344900115765385709 36476370129337543412019641)
  ·
    refine ⟨27357277597003157559014731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36476370129337543412019641 27357277597003157559014731)
    ·
      refine ⟨41035916395504736338522097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27357277597003157559014731 41035916395504736338522097)
      ·
        refine ⟨30776937296628552253891573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41035916395504736338522097 30776937296628552253891573)
        ·
          refine ⟨2885337871558926773802335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30776937296628552253891573 2885337871558926773802335)
          ·
            refine ⟨4328006807338390160703503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885337871558926773802335 4328006807338390160703503)
            ·
              refine ⟨6492010211007585241055255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328006807338390160703503 6492010211007585241055255)
              ·
                refine ⟨9738015316511377861582883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492010211007585241055255 9738015316511377861582883)
                ·
                  refine ⟨14607022974767066792374325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9738015316511377861582883 14607022974767066792374325)
                  ·
                    refine ⟨1369408403884412511785093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14607022974767066792374325 1369408403884412511785093)
                    ·
                      rfl

theorem cell22_4000370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_4000370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000370 prefixEnd_4000370 := by exact prefixLift 4000370
  have htrace : WordTrace (prefixWord ++ tailWord_4000370) baseStart_4000370 baseEnd_4000370 := by
    simpa [prefixWord, tailWord_4000370, baseEnd_4000370] using wordTrace_append hprefix tailTrace_4000370
  have hstable : (prefixWord ++ tailWord_4000370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000370).length < 2 ^ (prefixWord ++ tailWord_4000370).sum := by decide
  have hdescent : baseEnd_4000370 < baseStart_4000370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000466 : List Nat := [3, 2, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_4000466 : Nat := 118140960795 + 4000466 * 2 ^ 59
def prefixEnd_4000466 : Nat := 4983230072969 + 3 ^ 40 * 4000466 * 2
def baseEnd_4000466 : Nat := 1369441266646300261384799

theorem tailTrace_4000466 : CollatzResearch.WordTrace tailWord_4000466 prefixEnd_4000466 1369441266646300261384799 := by
  unfold tailWord_4000466
  simp only [CollatzResearch.WordTrace]
  refine ⟨36477245481250595510893313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97272654616668254695715501 36477245481250595510893313)
  ·
    refine ⟨27357934110937946633169985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36477245481250595510893313 27357934110937946633169985)
    ·
      refine ⟨20518450583203459974877489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27357934110937946633169985 20518450583203459974877489)
      ·
        refine ⟨15388837937402594981158117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20518450583203459974877489 15388837937402594981158117)
        ·
          refine ⟨2885407113262986558967147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15388837937402594981158117 2885407113262986558967147)
          ·
            refine ⟨4328110669894479838450721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885407113262986558967147 4328110669894479838450721)
            ·
              refine ⟨3246083002420859878838041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328110669894479838450721 3246083002420859878838041)
              ·
                refine ⟨2434562251815644909128531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246083002420859878838041 2434562251815644909128531)
                ·
                  refine ⟨3651843377723467363692797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434562251815644909128531 3651843377723467363692797)
                  ·
                    refine ⟨1369441266646300261384799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3651843377723467363692797 1369441266646300261384799)
                    ·
                      rfl

theorem cell22_4000466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_4000466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000466 prefixEnd_4000466 := by exact prefixLift 4000466
  have htrace : WordTrace (prefixWord ++ tailWord_4000466) baseStart_4000466 baseEnd_4000466 := by
    simpa [prefixWord, tailWord_4000466, baseEnd_4000466] using wordTrace_append hprefix tailTrace_4000466
  have hstable : (prefixWord ++ tailWord_4000466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000466).length < 2 ^ (prefixWord ++ tailWord_4000466).sum := by decide
  have hdescent : baseEnd_4000466 < baseStart_4000466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000473 : List Nat := [1, 2, 1, 2, 3, 2, 3, 4, 4]
def baseStart_4000473 : Nat := 118140960795 + 4000473 * 2 ^ 59
def prefixEnd_4000473 : Nat := 4983230072969 + 3 ^ 40 * 4000473 * 2
def baseEnd_4000473 : Nat := 456481220963118192153259

theorem tailTrace_4000473 : CollatzResearch.WordTrace tailWord_4000473 prefixEnd_4000473 456481220963118192153259 := by
  unfold tailWord_4000473
  simp only [CollatzResearch.WordTrace]
  refine ⟨145909237235977022239078073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97272824823984681492718715 145909237235977022239078073)
  ·
    refine ⟨109431927926982766679308555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145909237235977022239078073 109431927926982766679308555)
    ·
      refine ⟨164147891890474150018962833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109431927926982766679308555 164147891890474150018962833)
      ·
        refine ⟨123110918917855612514222125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164147891890474150018962833 123110918917855612514222125)
        ·
          refine ⟨46166594594195854692833297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123110918917855612514222125 46166594594195854692833297)
          ·
            refine ⟨34624945945646891019624973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46166594594195854692833297 34624945945646891019624973)
            ·
              refine ⟨12984354729617584132359365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34624945945646891019624973 12984354729617584132359365)
              ·
                refine ⟨2434566511803297024817381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12984354729617584132359365 2434566511803297024817381)
                ·
                  refine ⟨456481220963118192153259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434566511803297024817381 456481220963118192153259)
                  ·
                    rfl

theorem cell22_4000473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_4000473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000473 prefixEnd_4000473 := by exact prefixLift 4000473
  have htrace : WordTrace (prefixWord ++ tailWord_4000473) baseStart_4000473 baseEnd_4000473 := by
    simpa [prefixWord, tailWord_4000473, baseEnd_4000473] using wordTrace_append hprefix tailTrace_4000473
  have hstable : (prefixWord ++ tailWord_4000473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000473).length < 2 ^ (prefixWord ++ tailWord_4000473).sum := by decide
  have hdescent : baseEnd_4000473 < baseStart_4000473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000623 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 6, 3]
def baseStart_4000623 : Nat := 118140960795 + 4000623 * 2 ^ 59
def prefixEnd_4000623 : Nat := 4983230072969 + 3 ^ 40 * 4000623 * 2
def baseEnd_4000623 : Nat := 1369495010954804185209317

theorem tailTrace_4000623 : CollatzResearch.WordTrace tailWord_4000623 prefixEnd_4000623 1369495010954804185209317 := by
  unfold tailWord_4000623
  simp only [CollatzResearch.WordTrace]
  refine ⟨145914708185433597857038523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97276472123622398571359015 145914708185433597857038523)
  ·
    refine ⟨218872062278150396785557785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145914708185433597857038523 218872062278150396785557785)
    ·
      refine ⟨164154046708612797589168339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218872062278150396785557785 164154046708612797589168339)
      ·
        refine ⟨246231070062919196383752509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164154046708612797589168339 246231070062919196383752509)
        ·
          refine ⟨92336651273594698643907191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246231070062919196383752509 92336651273594698643907191)
          ·
            refine ⟨138504976910392047965860787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92336651273594698643907191 138504976910392047965860787)
            ·
              refine ⟨207757465365588071948791181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138504976910392047965860787 207757465365588071948791181)
              ·
                refine ⟨77909049512095526980796693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207757465365588071948791181 77909049512095526980796693)
                ·
                  refine ⟨3651986695879477827224845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77909049512095526980796693 3651986695879477827224845)
                  ·
                    refine ⟨1369495010954804185209317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3651986695879477827224845 1369495010954804185209317)
                    ·
                      rfl

theorem cell22_4000623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_4000623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000623 prefixEnd_4000623 := by exact prefixLift 4000623
  have htrace : WordTrace (prefixWord ++ tailWord_4000623) baseStart_4000623 baseEnd_4000623 := by
    simpa [prefixWord, tailWord_4000623, baseEnd_4000623] using wordTrace_append hprefix tailTrace_4000623
  have hstable : (prefixWord ++ tailWord_4000623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000623).length < 2 ^ (prefixWord ++ tailWord_4000623).sum := by decide
  have hdescent : baseEnd_4000623 < baseStart_4000623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000698 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_4000698 : Nat := 118140960795 + 4000698 * 2 ^ 59
def prefixEnd_4000698 : Nat := 4983230072969 + 3 ^ 40 * 4000698 * 2
def baseEnd_4000698 : Nat := 456506894995842996528029

theorem tailTrace_4000698 : CollatzResearch.WordTrace tailWord_4000698 prefixEnd_4000698 456506894995842996528029 := by
  unfold tailWord_4000698
  simp only [CollatzResearch.WordTrace]
  refine ⟨36479360915040471416504687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97278295773441257110679165 36479360915040471416504687)
  ·
    refine ⟨54719041372560707124757031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36479360915040471416504687 54719041372560707124757031)
    ·
      refine ⟨82078562058841060687135547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54719041372560707124757031 82078562058841060687135547)
      ·
        refine ⟨123117843088261591030703321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82078562058841060687135547 123117843088261591030703321)
        ·
          refine ⟨92338382316196193273027491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123117843088261591030703321 92338382316196193273027491)
          ·
            refine ⟨138507573474294289909541237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92338382316196193273027491 138507573474294289909541237)
            ·
              refine ⟨12985085013215089679019491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138507573474294289909541237 12985085013215089679019491)
              ·
                refine ⟨19477627519822634518529237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12985085013215089679019491 19477627519822634518529237)
                ·
                  refine ⟨456506894995842996528029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19477627519822634518529237 456506894995842996528029)
                  ·
                    rfl

theorem cell22_4000698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_4000698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000698 prefixEnd_4000698 := by exact prefixLift 4000698
  have htrace : WordTrace (prefixWord ++ tailWord_4000698) baseStart_4000698 baseEnd_4000698 := by
    simpa [prefixWord, tailWord_4000698, baseEnd_4000698] using wordTrace_append hprefix tailTrace_4000698
  have hstable : (prefixWord ++ tailWord_4000698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000698).length < 2 ^ (prefixWord ++ tailWord_4000698).sum := by decide
  have hdescent : baseEnd_4000698 < baseStart_4000698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000702 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_4000702 : Nat := 118140960795 + 4000702 * 2 ^ 59
def prefixEnd_4000702 : Nat := 4983230072969 + 3 ^ 40 * 4000702 * 2
def baseEnd_4000702 : Nat := 1369522054269274312484075

theorem tailTrace_4000702 : CollatzResearch.WordTrace tailWord_4000702 prefixEnd_4000702 1369522054269274312484075 := by
  unfold tailWord_4000702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18239698694018424293645545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97278393034764929566109573 18239698694018424293645545)
  ·
    refine ⟨13679774020513818220234159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18239698694018424293645545 13679774020513818220234159)
    ·
      refine ⟨20519661030770727330351239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13679774020513818220234159 20519661030770727330351239)
      ·
        refine ⟨30779491546156090995526859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20519661030770727330351239 30779491546156090995526859)
        ·
          refine ⟨46169237319234136493290289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30779491546156090995526859 46169237319234136493290289)
          ·
            refine ⟨34626927989425602369967717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46169237319234136493290289 34626927989425602369967717)
            ·
              refine ⟨6492548998017300444368947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34626927989425602369967717 6492548998017300444368947)
              ·
                refine ⟨9738823497025950666553421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492548998017300444368947 9738823497025950666553421)
                ·
                  refine ⟨3652058811384731499957533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9738823497025950666553421 3652058811384731499957533)
                  ·
                    refine ⟨1369522054269274312484075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652058811384731499957533 1369522054269274312484075)
                    ·
                      rfl

theorem cell22_4000702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_4000702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000702 prefixEnd_4000702 := by exact prefixLift 4000702
  have htrace : WordTrace (prefixWord ++ tailWord_4000702) baseStart_4000702 baseEnd_4000702 := by
    simpa [prefixWord, tailWord_4000702, baseEnd_4000702] using wordTrace_append hprefix tailTrace_4000702
  have hstable : (prefixWord ++ tailWord_4000702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000702).length < 2 ^ (prefixWord ++ tailWord_4000702).sum := by decide
  have hdescent : baseEnd_4000702 < baseStart_4000702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000766 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_4000766 : Nat := 118140960795 + 4000766 * 2 ^ 59
def prefixEnd_4000766 : Nat := 4983230072969 + 3 ^ 40 * 4000766 * 2
def baseEnd_4000766 : Nat := 456514654259066492961293

theorem tailTrace_4000766 : CollatzResearch.WordTrace tailWord_4000766 prefixEnd_4000766 456514654259066492961293 := by
  unfold tailWord_4000766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18239990477989441659936769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97279949215943688852996101 18239990477989441659936769)
  ·
    refine ⟨13679992858492081244952577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18239990477989441659936769 13679992858492081244952577)
    ·
      refine ⟨10259994643869060933714433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13679992858492081244952577 10259994643869060933714433)
      ·
        refine ⟨7694995982901795700285825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10259994643869060933714433 7694995982901795700285825)
        ·
          refine ⟨5771246987176346775214369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7694995982901795700285825 5771246987176346775214369)
          ·
            refine ⟨4328435240382260081410777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771246987176346775214369 4328435240382260081410777)
            ·
              refine ⟨3246326430286695061058083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328435240382260081410777 3246326430286695061058083)
              ·
                refine ⟨4869489645430042591587125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246326430286695061058083 4869489645430042591587125)
                ·
                  refine ⟨456514654259066492961293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4869489645430042591587125 456514654259066492961293)
                  ·
                    rfl

theorem cell22_4000766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_4000766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000766 prefixEnd_4000766 := by exact prefixLift 4000766
  have htrace : WordTrace (prefixWord ++ tailWord_4000766) baseStart_4000766 baseEnd_4000766 := by
    simpa [prefixWord, tailWord_4000766, baseEnd_4000766] using wordTrace_append hprefix tailTrace_4000766
  have hstable : (prefixWord ++ tailWord_4000766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000766).length < 2 ^ (prefixWord ++ tailWord_4000766).sum := by decide
  have hdescent : baseEnd_4000766 < baseStart_4000766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000775 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 1, 5]
def baseStart_4000775 : Nat := 118140960795 + 4000775 * 2 ^ 59
def prefixEnd_4000775 : Nat := 4983230072969 + 3 ^ 40 * 4000775 * 2
def baseEnd_4000775 : Nat := 1369547043661126455408851

theorem tailTrace_4000775 : CollatzResearch.WordTrace tailWord_4000775 prefixEnd_4000775 1369547043661126455408851 := by
  unfold tailWord_4000775
  simp only [CollatzResearch.WordTrace]
  refine ⟨145920252080882927816571779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97280168053921951877714519 145920252080882927816571779)
  ·
    refine ⟨218880378121324391724857669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145920252080882927816571779 218880378121324391724857669)
    ·
      refine ⟨41040070897748323448410813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218880378121324391724857669 41040070897748323448410813)
      ·
        refine ⟨15390026586655621293154055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41040070897748323448410813 15390026586655621293154055)
        ·
          refine ⟨23085039879983431939731083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390026586655621293154055 23085039879983431939731083)
          ·
            refine ⟨34627559819975147909596625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23085039879983431939731083 34627559819975147909596625)
            ·
              refine ⟨25970669864981360932197469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34627559819975147909596625 25970669864981360932197469)
              ·
                refine ⟨9739001199368010349574051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25970669864981360932197469 9739001199368010349574051)
                ·
                  refine ⟨14608501799052015524361077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9739001199368010349574051 14608501799052015524361077)
                  ·
                    refine ⟨1369547043661126455408851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14608501799052015524361077 1369547043661126455408851)
                    ·
                      rfl

theorem cell22_4000775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_4000775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000775 prefixEnd_4000775 := by exact prefixLift 4000775
  have htrace : WordTrace (prefixWord ++ tailWord_4000775) baseStart_4000775 baseEnd_4000775 := by
    simpa [prefixWord, tailWord_4000775, baseEnd_4000775] using wordTrace_append hprefix tailTrace_4000775
  have hstable : (prefixWord ++ tailWord_4000775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000775).length < 2 ^ (prefixWord ++ tailWord_4000775).sum := by decide
  have hdescent : baseEnd_4000775 < baseStart_4000775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000822 : List Nat := [5, 1, 2, 1, 1, 2, 3, 7]
def baseStart_4000822 : Nat := 118140960795 + 4000822 * 2 ^ 59
def prefixEnd_4000822 : Nat := 4983230072969 + 3 ^ 40 * 4000822 * 2
def baseEnd_4000822 : Nat := 152173681413514888831523

theorem tailTrace_4000822 : CollatzResearch.WordTrace tailWord_4000822 prefixEnd_4000822 152173681413514888831523 := by
  unfold tailWord_4000822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120122894482040927720795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97281310874475103229021813 9120122894482040927720795)
  ·
    refine ⟨13680184341723061391581193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9120122894482040927720795 13680184341723061391581193)
    ·
      refine ⟨10260138256292296043685895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13680184341723061391581193 10260138256292296043685895)
      ·
        refine ⟨15390207384438444065528843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260138256292296043685895 15390207384438444065528843)
        ·
          refine ⟨23085311076657666098293265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390207384438444065528843 23085311076657666098293265)
          ·
            refine ⟨17313983307493249573719949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23085311076657666098293265 17313983307493249573719949)
            ·
              refine ⟨6492743740309968590144981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17313983307493249573719949 6492743740309968590144981)
              ·
                refine ⟨152173681413514888831523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6492743740309968590144981 152173681413514888831523)
                ·
                  rfl

theorem cell22_4000822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_4000822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000822 prefixEnd_4000822 := by exact prefixLift 4000822
  have htrace : WordTrace (prefixWord ++ tailWord_4000822) baseStart_4000822 baseEnd_4000822 := by
    simpa [prefixWord, tailWord_4000822, baseEnd_4000822] using wordTrace_append hprefix tailTrace_4000822
  have hstable : (prefixWord ++ tailWord_4000822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000822).length < 2 ^ (prefixWord ++ tailWord_4000822).sum := by decide
  have hdescent : baseEnd_4000822 < baseStart_4000822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000865 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_4000865 : Nat := 118140960795 + 4000865 * 2 ^ 59
def prefixEnd_4000865 : Nat := 4983230072969 + 3 ^ 40 * 4000865 * 2
def baseEnd_4000865 : Nat := 1369577852500396220658575

theorem tailTrace_4000865 : CollatzResearch.WordTrace tailWord_4000865 prefixEnd_4000865 1369577852500396220658575 := by
  unfold tailWord_4000865
  simp only [CollatzResearch.WordTrace]
  refine ⟨145923534650556873187348049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97282356433704582124898699 145923534650556873187348049)
  ·
    refine ⟨109442650987917654890511037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145923534650556873187348049 109442650987917654890511037)
    ·
      refine ⟨41040994120469120583941639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109442650987917654890511037 41040994120469120583941639)
      ·
        refine ⟨61561491180703680875912459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41040994120469120583941639 61561491180703680875912459)
        ·
          refine ⟨92342236771055521313868689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61561491180703680875912459 92342236771055521313868689)
          ·
            refine ⟨69256677578291640985401517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92342236771055521313868689 69256677578291640985401517)
            ·
              refine ⟨25971254091859365369525569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69256677578291640985401517 25971254091859365369525569)
              ·
                refine ⟨19478440568894524027144177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25971254091859365369525569 19478440568894524027144177)
                ·
                  refine ⟨14608830426670893020358133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19478440568894524027144177 14608830426670893020358133)
                  ·
                    refine ⟨1369577852500396220658575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14608830426670893020358133 1369577852500396220658575)
                    ·
                      rfl

theorem cell22_4000865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_4000865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000865 prefixEnd_4000865 := by exact prefixLift 4000865
  have htrace : WordTrace (prefixWord ++ tailWord_4000865) baseStart_4000865 baseEnd_4000865 := by
    simpa [prefixWord, tailWord_4000865, baseEnd_4000865] using wordTrace_append hprefix tailTrace_4000865
  have hstable : (prefixWord ++ tailWord_4000865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000865).length < 2 ^ (prefixWord ++ tailWord_4000865).sum := by decide
  have hdescent : baseEnd_4000865 < baseStart_4000865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000912 : List Nat := [2, 1, 1, 1, 1, 1, 4, 7, 4]
def baseStart_4000912 : Nat := 118140960795 + 4000912 * 2 ^ 59
def prefixEnd_4000912 : Nat := 4983230072969 + 3 ^ 40 * 4000912 * 2
def baseEnd_4000912 : Nat := 456531313853634588244477

theorem tailTrace_4000912 : CollatzResearch.WordTrace tailWord_4000912 prefixEnd_4000912 456531313853634588244477 := by
  unfold tailWord_4000912
  simp only [CollatzResearch.WordTrace]
  refine ⟨72962624440693300107154495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97283499254257733476205993 72962624440693300107154495)
  ·
    refine ⟨109443936661039950160731743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72962624440693300107154495 109443936661039950160731743)
    ·
      refine ⟨164165904991559925241097615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109443936661039950160731743 164165904991559925241097615)
      ·
        refine ⟨246248857487339887861646423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164165904991559925241097615 246248857487339887861646423)
        ·
          refine ⟨369373286231009831792469635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246248857487339887861646423 369373286231009831792469635)
          ·
            refine ⟨554059929346514747688704453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369373286231009831792469635 554059929346514747688704453)
            ·
              refine ⟨103886236752471515191632085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 554059929346514747688704453 103886236752471515191632085)
              ·
                refine ⟨2434833673886051137303877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103886236752471515191632085 2434833673886051137303877)
                ·
                  refine ⟨456531313853634588244477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434833673886051137303877 456531313853634588244477)
                  ·
                    rfl

theorem cell22_4000912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_4000912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000912 prefixEnd_4000912 := by exact prefixLift 4000912
  have htrace : WordTrace (prefixWord ++ tailWord_4000912) baseStart_4000912 baseEnd_4000912 := by
    simpa [prefixWord, tailWord_4000912, baseEnd_4000912] using wordTrace_append hprefix tailTrace_4000912
  have hstable : (prefixWord ++ tailWord_4000912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000912).length < 2 ^ (prefixWord ++ tailWord_4000912).sum := by decide
  have hdescent : baseEnd_4000912 < baseStart_4000912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000914 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4000914 : Nat := 118140960795 + 4000914 * 2 ^ 59
def prefixEnd_4000914 : Nat := 4983230072969 + 3 ^ 40 * 4000914 * 2
def baseEnd_4000914 : Nat := 1369594626201776426183425

theorem tailTrace_4000914 : CollatzResearch.WordTrace tailWord_4000914 prefixEnd_4000914 1369594626201776426183425 := by
  unfold tailWord_4000914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36481330456844838638970449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97283547884919569703921197 36481330456844838638970449)
  ·
    refine ⟨27360997842633628979227837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36481330456844838638970449 27360997842633628979227837)
    ·
      refine ⟨10260374190987610867210439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27360997842633628979227837 10260374190987610867210439)
      ·
        refine ⟨15390561286481416300815659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260374190987610867210439 15390561286481416300815659)
        ·
          refine ⟨23085841929722124451223489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390561286481416300815659 23085841929722124451223489)
          ·
            refine ⟨17314381447291593338417617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23085841929722124451223489 17314381447291593338417617)
            ·
              refine ⟨12985786085468695003813213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17314381447291593338417617 12985786085468695003813213)
              ·
                refine ⟨4869669782050760626429955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12985786085468695003813213 4869669782050760626429955)
                ·
                  refine ⟨7304504673076140939644933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869669782050760626429955 7304504673076140939644933)
                  ·
                    refine ⟨1369594626201776426183425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304504673076140939644933 1369594626201776426183425)
                    ·
                      rfl

theorem cell22_4000914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4000914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000914 prefixEnd_4000914 := by exact prefixLift 4000914
  have htrace : WordTrace (prefixWord ++ tailWord_4000914) baseStart_4000914 baseEnd_4000914 := by
    simpa [prefixWord, tailWord_4000914, baseEnd_4000914] using wordTrace_append hprefix tailTrace_4000914
  have hstable : (prefixWord ++ tailWord_4000914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000914).length < 2 ^ (prefixWord ++ tailWord_4000914).sum := by decide
  have hdescent : baseEnd_4000914 < baseStart_4000914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000980 : List Nat := [2, 4, 1, 4, 1, 2, 2, 2, 4]
def baseStart_4000980 : Nat := 118140960795 + 4000980 * 2 ^ 59
def prefixEnd_4000980 : Nat := 4983230072969 + 3 ^ 40 * 4000980 * 2
def baseEnd_4000980 : Nat := 456539073116858084677741

theorem tailTrace_4000980 : CollatzResearch.WordTrace tailWord_4000980 prefixEnd_4000980 456539073116858084677741 := by
  unfold tailWord_4000980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72963864522570123913892197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97285152696760165218522929 72963864522570123913892197)
  ·
    refine ⟨13680724597981898233854787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72963864522570123913892197 13680724597981898233854787)
    ·
      refine ⟨20521086896972847350782181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13680724597981898233854787 20521086896972847350782181)
      ·
        refine ⟨3847703793182408878271659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20521086896972847350782181 3847703793182408878271659)
        ·
          refine ⟨5771555689773613317407489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847703793182408878271659 5771555689773613317407489)
          ·
            refine ⟨4328666767330209988055617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771555689773613317407489 4328666767330209988055617)
            ·
              refine ⟨3246500075497657491041713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328666767330209988055617 3246500075497657491041713)
              ·
                refine ⟨2434875056623243118281285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246500075497657491041713 2434875056623243118281285)
                ·
                  refine ⟨456539073116858084677741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434875056623243118281285 456539073116858084677741)
                  ·
                    rfl

theorem cell22_4000980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_4000980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4000980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4000980 prefixEnd_4000980 := by exact prefixLift 4000980
  have htrace : WordTrace (prefixWord ++ tailWord_4000980) baseStart_4000980 baseEnd_4000980 := by
    simpa [prefixWord, tailWord_4000980, baseEnd_4000980] using wordTrace_append hprefix tailTrace_4000980
  have hstable : (prefixWord ++ tailWord_4000980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000980).length < 2 ^ (prefixWord ++ tailWord_4000980).sum := by decide
  have hdescent : baseEnd_4000980 < baseStart_4000980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001064 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 6]
def baseStart_4001064 : Nat := 118140960795 + 4001064 * 2 ^ 59
def prefixEnd_4001064 : Nat := 4983230072969 + 3 ^ 40 * 4001064 * 2
def baseEnd_4001064 : Nat := 456548658089075344977655

theorem tailTrace_4001064 : CollatzResearch.WordTrace tailWord_4001064 prefixEnd_4001064 456548658089075344977655 := by
  unfold tailWord_4001064
  simp only [CollatzResearch.WordTrace]
  refine ⟨72965396388417965086921123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97287195184557286782561497 72965396388417965086921123)
  ·
    refine ⟨109448094582626947630381685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72965396388417965086921123 109448094582626947630381685)
    ·
      refine ⟨10260758867121276340348283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109448094582626947630381685 10260758867121276340348283)
      ·
        refine ⟨15391138300681914510522425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260758867121276340348283 15391138300681914510522425)
        ·
          refine ⟨11543353725511435882891819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15391138300681914510522425 11543353725511435882891819)
          ·
            refine ⟨17315030588267153824337729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543353725511435882891819 17315030588267153824337729)
            ·
              refine ⟨12986272941200365368253297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17315030588267153824337729 12986272941200365368253297)
              ·
                refine ⟨9739704705900274026189973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12986272941200365368253297 9739704705900274026189973)
                ·
                  refine ⟨456548658089075344977655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9739704705900274026189973 456548658089075344977655)
                  ·
                    rfl

theorem cell22_4001064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_4001064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001064 prefixEnd_4001064 := by exact prefixLift 4001064
  have htrace : WordTrace (prefixWord ++ tailWord_4001064) baseStart_4001064 baseEnd_4001064 := by
    simpa [prefixWord, tailWord_4001064, baseEnd_4001064] using wordTrace_append hprefix tailTrace_4001064
  have hstable : (prefixWord ++ tailWord_4001064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001064).length < 2 ^ (prefixWord ++ tailWord_4001064).sum := by decide
  have hdescent : baseEnd_4001064 < baseStart_4001064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001066 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4001066 : Nat := 118140960795 + 4001066 * 2 ^ 59
def prefixEnd_4001066 : Nat := 4983230072969 + 3 ^ 40 * 4001066 * 2
def baseEnd_4001066 : Nat := 1369646658908098696382959

theorem tailTrace_4001066 : CollatzResearch.WordTrace tailWord_4001066 prefixEnd_4001066 1369646658908098696382959 := by
  unfold tailWord_4001066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36482716430707171128853763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97287243815219123010276701 36482716430707171128853763)
  ·
    refine ⟨54724074646060756693280645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36482716430707171128853763 54724074646060756693280645)
    ·
      refine ⟨10260763996136391879990121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54724074646060756693280645 10260763996136391879990121)
      ·
        refine ⟨7695572997102293909992591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10260763996136391879990121 7695572997102293909992591)
        ·
          refine ⟨11543359495653440864988887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695572997102293909992591 11543359495653440864988887)
          ·
            refine ⟨17315039243480161297483331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543359495653440864988887 17315039243480161297483331)
            ·
              refine ⟨25972558865220241946224997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17315039243480161297483331 25972558865220241946224997)
              ·
                refine ⟨4869854787228795364917187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25972558865220241946224997 4869854787228795364917187)
                ·
                  refine ⟨7304782180843193047375781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869854787228795364917187 7304782180843193047375781)
                  ·
                    refine ⟨1369646658908098696382959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304782180843193047375781 1369646658908098696382959)
                    ·
                      rfl

theorem cell22_4001066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4001066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001066 prefixEnd_4001066 := by exact prefixLift 4001066
  have htrace : WordTrace (prefixWord ++ tailWord_4001066) baseStart_4001066 baseEnd_4001066 := by
    simpa [prefixWord, tailWord_4001066, baseEnd_4001066] using wordTrace_append hprefix tailTrace_4001066
  have hstable : (prefixWord ++ tailWord_4001066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001066).length < 2 ^ (prefixWord ++ tailWord_4001066).sum := by decide
  have hdescent : baseEnd_4001066 < baseStart_4001066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001109 : List Nat := [1, 3, 2, 2, 3, 2, 2, 7]
def baseStart_4001109 : Nat := 118140960795 + 4001109 * 2 ^ 59
def prefixEnd_4001109 : Nat := 4983230072969 + 3 ^ 40 * 4001109 * 2
def baseEnd_4001109 : Nat := 152184597631873435284203

theorem tailTrace_4001109 : CollatzResearch.WordTrace tailWord_4001109 prefixEnd_4001109 152184597631873435284203 := by
  unfold tailWord_4001109
  simp only [CollatzResearch.WordTrace]
  refine ⟨145932434061672902859230381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97288289374448601906153587 145932434061672902859230381)
  ·
    refine ⟨54724662773127338572211393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145932434061672902859230381 54724662773127338572211393)
    ·
      refine ⟨41043497079845503929158545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54724662773127338572211393 41043497079845503929158545)
      ·
        refine ⟨30782622809884127946868909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41043497079845503929158545 30782622809884127946868909)
        ·
          refine ⟨11543483553706547980075841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30782622809884127946868909 11543483553706547980075841)
          ·
            refine ⟨8657612665279910985056881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11543483553706547980075841 8657612665279910985056881)
            ·
              refine ⟨6493209498959933238792661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657612665279910985056881 6493209498959933238792661)
              ·
                refine ⟨152184597631873435284203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6493209498959933238792661 152184597631873435284203)
                ·
                  rfl

theorem cell22_4001109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 7].length) (baseStart_4001109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001109 prefixEnd_4001109 := by exact prefixLift 4001109
  have htrace : WordTrace (prefixWord ++ tailWord_4001109) baseStart_4001109 baseEnd_4001109 := by
    simpa [prefixWord, tailWord_4001109, baseEnd_4001109] using wordTrace_append hprefix tailTrace_4001109
  have hstable : (prefixWord ++ tailWord_4001109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001109).length < 2 ^ (prefixWord ++ tailWord_4001109).sum := by decide
  have hdescent : baseEnd_4001109 < baseStart_4001109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001117 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4001117 : Nat := 118140960795 + 4001117 * 2 ^ 59
def prefixEnd_4001117 : Nat := 4983230072969 + 3 ^ 40 * 4001117 * 2
def baseEnd_4001117 : Nat := 1369664117250351563357803

theorem tailTrace_4001117 : CollatzResearch.WordTrace tailWord_4001117 prefixEnd_4001117 1369664117250351563357803 := by
  unfold tailWord_4001117
  simp only [CollatzResearch.WordTrace]
  refine ⟨145932725845643920225521605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97288483897095946817014403 145932725845643920225521605)
  ·
    refine ⟨27362386096058235042285301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145932725845643920225521605 27362386096058235042285301)
    ·
      refine ⟨2565223696505459535214247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27362386096058235042285301 2565223696505459535214247)
      ·
        refine ⟨3847835544758189302821371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565223696505459535214247 3847835544758189302821371)
        ·
          refine ⟨5771753317137283954232057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847835544758189302821371 5771753317137283954232057)
          ·
            refine ⟨4328814987852962965674043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771753317137283954232057 4328814987852962965674043)
            ·
              refine ⟨6493222481779444448511065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328814987852962965674043 6493222481779444448511065)
              ·
                refine ⟨4869916861334583336383299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6493222481779444448511065 4869916861334583336383299)
                ·
                  refine ⟨7304875292001875004574949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869916861334583336383299 7304875292001875004574949)
                  ·
                    refine ⟨1369664117250351563357803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304875292001875004574949 1369664117250351563357803)
                    ·
                      rfl

theorem cell22_4001117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4001117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001117 prefixEnd_4001117 := by exact prefixLift 4001117
  have htrace : WordTrace (prefixWord ++ tailWord_4001117) baseStart_4001117 baseEnd_4001117 := by
    simpa [prefixWord, tailWord_4001117, baseEnd_4001117] using wordTrace_append hprefix tailTrace_4001117
  have hstable : (prefixWord ++ tailWord_4001117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001117).length < 2 ^ (prefixWord ++ tailWord_4001117).sum := by decide
  have hdescent : baseEnd_4001117 < baseStart_4001117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001137 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 9]
def baseStart_4001137 : Nat := 118140960795 + 4001137 * 2 ^ 59
def prefixEnd_4001137 : Nat := 4983230072969 + 3 ^ 40 * 4001137 * 2
def baseEnd_4001137 : Nat := 456556987886359392619247

theorem tailTrace_4001137 : CollatzResearch.WordTrace tailWord_4001137 prefixEnd_4001137 456556987886359392619247 := by
  unfold tailWord_4001137
  simp only [CollatzResearch.WordTrace]
  refine ⟨145933455305571463641249665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97288970203714309094166443 145933455305571463641249665)
  ·
    refine ⟨109450091479178597730937249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145933455305571463641249665 109450091479178597730937249)
    ·
      refine ⟨82087568609383948298202937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109450091479178597730937249 82087568609383948298202937)
      ·
        refine ⟨61565676457037961223652203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82087568609383948298202937 61565676457037961223652203)
        ·
          refine ⟨92348514685556941835478305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61565676457037961223652203 92348514685556941835478305)
          ·
            refine ⟨69261386014167706376608729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92348514685556941835478305 69261386014167706376608729)
            ·
              refine ⟨51946039510625779782456547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69261386014167706376608729 51946039510625779782456547)
              ·
                refine ⟨77919059265938669673684821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51946039510625779782456547 77919059265938669673684821)
                ·
                  refine ⟨456556987886359392619247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77919059265938669673684821 456556987886359392619247)
                  ·
                    rfl

theorem cell22_4001137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_4001137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001137 prefixEnd_4001137 := by exact prefixLift 4001137
  have htrace : WordTrace (prefixWord ++ tailWord_4001137) baseStart_4001137 baseEnd_4001137 := by
    simpa [prefixWord, tailWord_4001137, baseEnd_4001137] using wordTrace_append hprefix tailTrace_4001137
  have hstable : (prefixWord ++ tailWord_4001137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001137).length < 2 ^ (prefixWord ++ tailWord_4001137).sum := by decide
  have hdescent : baseEnd_4001137 < baseStart_4001137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001152 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_4001152 : Nat := 118140960795 + 4001152 * 2 ^ 59
def prefixEnd_4001152 : Nat := 4983230072969 + 3 ^ 40 * 4001152 * 2
def baseEnd_4001152 : Nat := 1369676098465623138732695

theorem tailTrace_4001152 : CollatzResearch.WordTrace tailWord_4001152 prefixEnd_4001152 1369676098465623138732695 := by
  unfold tailWord_4001152
  simp only [CollatzResearch.WordTrace]
  refine ⟨72967001200258560601522855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97289334933678080802030473 72967001200258560601522855)
  ·
    refine ⟨109450501800387840902284283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72967001200258560601522855 109450501800387840902284283)
    ·
      refine ⟨164175752700581761353426425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109450501800387840902284283 164175752700581761353426425)
      ·
        refine ⟨123131814525436321015069819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164175752700581761353426425 123131814525436321015069819)
        ·
          refine ⟨184697721788154481522604729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123131814525436321015069819 184697721788154481522604729)
          ·
            refine ⟨138523291341115861141953547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184697721788154481522604729 138523291341115861141953547)
            ·
              refine ⟨207784937011673791712930321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138523291341115861141953547 207784937011673791712930321)
              ·
                refine ⟨155838702758755343784697741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207784937011673791712930321 155838702758755343784697741)
                ·
                  refine ⟨58439513534533253919261653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155838702758755343784697741 58439513534533253919261653)
                  ·
                    refine ⟨1369676098465623138732695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58439513534533253919261653 1369676098465623138732695)
                    ·
                      rfl

theorem cell22_4001152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_4001152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001152 prefixEnd_4001152 := by exact prefixLift 4001152
  have htrace : WordTrace (prefixWord ++ tailWord_4001152) baseStart_4001152 baseEnd_4001152 := by
    simpa [prefixWord, tailWord_4001152, baseEnd_4001152] using wordTrace_append hprefix tailTrace_4001152
  have hstable : (prefixWord ++ tailWord_4001152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001152).length < 2 ^ (prefixWord ++ tailWord_4001152).sum := by decide
  have hdescent : baseEnd_4001152 < baseStart_4001152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001184 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_4001184 : Nat := 118140960795 + 4001184 * 2 ^ 59
def prefixEnd_4001184 : Nat := 4983230072969 + 3 ^ 40 * 4001184 * 2
def baseEnd_4001184 : Nat := 1369687052719585721932597

theorem tailTrace_4001184 : CollatzResearch.WordTrace tailWord_4001184 prefixEnd_4001184 1369687052719585721932597 := by
  unfold tailWord_4001184
  simp only [CollatzResearch.WordTrace]
  refine ⟨72967584768200595334105303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97290113024267460445473737 72967584768200595334105303)
  ·
    refine ⟨109451377152300893001157955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72967584768200595334105303 109451377152300893001157955)
    ·
      refine ⟨164177065728451339501736933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109451377152300893001157955 164177065728451339501736933)
      ·
        refine ⟨30783199824084626156575675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164177065728451339501736933 30783199824084626156575675)
        ·
          refine ⟨46174799736126939234863513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30783199824084626156575675 46174799736126939234863513)
          ·
            refine ⟨34631099802095204426147635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46174799736126939234863513 34631099802095204426147635)
            ·
              refine ⟨51946649703142806639221453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34631099802095204426147635 51946649703142806639221453)
              ·
                refine ⟨19479993638678552489708045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51946649703142806639221453 19479993638678552489708045)
                ·
                  refine ⟨7304997614504457183640517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19479993638678552489708045 7304997614504457183640517)
                  ·
                    refine ⟨1369687052719585721932597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304997614504457183640517 1369687052719585721932597)
                    ·
                      rfl

theorem cell22_4001184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_4001184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001184 prefixEnd_4001184 := by exact prefixLift 4001184
  have htrace : WordTrace (prefixWord ++ tailWord_4001184) baseStart_4001184 baseEnd_4001184 := by
    simpa [prefixWord, tailWord_4001184, baseEnd_4001184] using wordTrace_append hprefix tailTrace_4001184
  have hstable : (prefixWord ++ tailWord_4001184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001184).length < 2 ^ (prefixWord ++ tailWord_4001184).sum := by decide
  have hdescent : baseEnd_4001184 < baseStart_4001184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001192 : List Nat := [2, 1, 6, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4001192 : Nat := 118140960795 + 4001192 * 2 ^ 59
def prefixEnd_4001192 : Nat := 4983230072969 + 3 ^ 40 * 4001192 * 2
def baseEnd_4001192 : Nat := 1369689791283076367732573

theorem tailTrace_4001192 : CollatzResearch.WordTrace tailWord_4001192 prefixEnd_4001192 1369689791283076367732573 := by
  unfold tailWord_4001192
  simp only [CollatzResearch.WordTrace]
  refine ⟨72967730660186104017250915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97290307546914805356334553 72967730660186104017250915)
  ·
    refine ⟨109451595990279156025876373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72967730660186104017250915 109451595990279156025876373)
    ·
      refine ⟨5130543562044335438712955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109451595990279156025876373 5130543562044335438712955)
      ·
        refine ⟨7695815343066503158069433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130543562044335438712955 7695815343066503158069433)
        ·
          refine ⟨5771861507299877368552075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7695815343066503158069433 5771861507299877368552075)
          ·
            refine ⟨8657792260949816052828113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771861507299877368552075 8657792260949816052828113)
            ·
              refine ⟨6493344195712362039621085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657792260949816052828113 6493344195712362039621085)
              ·
                refine ⟨2435004073392135764857907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6493344195712362039621085 2435004073392135764857907)
                ·
                  refine ⟨3652506110088203647286861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435004073392135764857907 3652506110088203647286861)
                  ·
                    refine ⟨1369689791283076367732573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652506110088203647286861 1369689791283076367732573)
                    ·
                      rfl

theorem cell22_4001192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4001192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001192 prefixEnd_4001192 := by exact prefixLift 4001192
  have htrace : WordTrace (prefixWord ++ tailWord_4001192) baseStart_4001192 baseEnd_4001192 := by
    simpa [prefixWord, tailWord_4001192, baseEnd_4001192] using wordTrace_append hprefix tailTrace_4001192
  have hstable : (prefixWord ++ tailWord_4001192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001192).length < 2 ^ (prefixWord ++ tailWord_4001192).sum := by decide
  have hdescent : baseEnd_4001192 < baseStart_4001192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001201 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_4001201 : Nat := 118140960795 + 4001201 * 2 ^ 59
def prefixEnd_4001201 : Nat := 4983230072969 + 3 ^ 40 * 4001201 * 2
def baseEnd_4001201 : Nat := 1369692872167003344257545

theorem tailTrace_4001201 : CollatzResearch.WordTrace tailWord_4001201 prefixEnd_4001201 1369692872167003344257545 := by
  unfold tailWord_4001201
  simp only [CollatzResearch.WordTrace]
  refine ⟨145935789577339602571579457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97290526384893068381052971 145935789577339602571579457)
  ·
    refine ⟨109451842183004701928684593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145935789577339602571579457 109451842183004701928684593)
    ·
      refine ⟨82088881637253526446513445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109451842183004701928684593 82088881637253526446513445)
      ·
        refine ⟨15391665306985036208721271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82088881637253526446513445 15391665306985036208721271)
        ·
          refine ⟨23087497960477554313081907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15391665306985036208721271 23087497960477554313081907)
          ·
            refine ⟨34631246940716331469622861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23087497960477554313081907 34631246940716331469622861)
            ·
              refine ⟨12986717602768624301108573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34631246940716331469622861 12986717602768624301108573)
              ·
                refine ⟨4870019101038234112915715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12986717602768624301108573 4870019101038234112915715)
                ·
                  refine ⟨7305028651557351169373573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4870019101038234112915715 7305028651557351169373573)
                  ·
                    refine ⟨1369692872167003344257545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305028651557351169373573 1369692872167003344257545)
                    ·
                      rfl

theorem cell22_4001201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_4001201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001201 prefixEnd_4001201 := by exact prefixLift 4001201
  have htrace : WordTrace (prefixWord ++ tailWord_4001201) baseStart_4001201 baseEnd_4001201 := by
    simpa [prefixWord, tailWord_4001201, baseEnd_4001201] using wordTrace_append hprefix tailTrace_4001201
  have hstable : (prefixWord ++ tailWord_4001201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001201).length < 2 ^ (prefixWord ++ tailWord_4001201).sum := by decide
  have hdescent : baseEnd_4001201 < baseStart_4001201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001216 : List Nat := [2, 1, 1, 2, 3, 1, 4, 4, 4]
def baseStart_4001216 : Nat := 118140960795 + 4001216 * 2 ^ 59
def prefixEnd_4001216 : Nat := 4983230072969 + 3 ^ 40 * 4001216 * 2
def baseEnd_4001216 : Nat := 456566002324516101710833

theorem tailTrace_4001216 : CollatzResearch.WordTrace tailWord_4001216 prefixEnd_4001216 456566002324516101710833 := by
  unfold tailWord_4001216
  simp only [CollatzResearch.WordTrace]
  refine ⟨72968168336142630066687751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97290891114856840088917001 72968168336142630066687751)
  ·
    refine ⟨109452252504213945100031627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72968168336142630066687751 109452252504213945100031627)
    ·
      refine ⟨164178378756320917650047441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109452252504213945100031627 164178378756320917650047441)
      ·
        refine ⟨123133784067240688237535581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164178378756320917650047441 123133784067240688237535581)
        ·
          refine ⟨46175169025215258089075843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123133784067240688237535581 46175169025215258089075843)
          ·
            refine ⟨69262753537822887133613765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46175169025215258089075843 69262753537822887133613765)
            ·
              refine ⟨12986766288341791337552581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69262753537822887133613765 12986766288341791337552581)
              ·
                refine ⟨2435018679064085875791109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12986766288341791337552581 2435018679064085875791109)
                ·
                  refine ⟨456566002324516101710833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435018679064085875791109 456566002324516101710833)
                  ·
                    rfl

theorem cell22_4001216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_4001216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001216 prefixEnd_4001216 := by exact prefixLift 4001216
  have htrace : WordTrace (prefixWord ++ tailWord_4001216) baseStart_4001216 baseEnd_4001216 := by
    simpa [prefixWord, tailWord_4001216, baseEnd_4001216] using wordTrace_append hprefix tailTrace_4001216
  have hstable : (prefixWord ++ tailWord_4001216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001216).length < 2 ^ (prefixWord ++ tailWord_4001216).sum := by decide
  have hdescent : baseEnd_4001216 < baseStart_4001216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001231 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 2, 3]
def baseStart_4001231 : Nat := 118140960795 + 4001231 * 2 ^ 59
def prefixEnd_4001231 : Nat := 4983230072969 + 3 ^ 40 * 4001231 * 2
def baseEnd_4001231 : Nat := 1369703141780093266007453

theorem tailTrace_4001231 : CollatzResearch.WordTrace tailWord_4001231 prefixEnd_4001231 1369703141780093266007453 := by
  unfold tailWord_4001231
  simp only [CollatzResearch.WordTrace]
  refine ⟨145936883767230917695171547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97291255844820611796781031 145936883767230917695171547)
  ·
    refine ⟨218905325650846376542757321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145936883767230917695171547 218905325650846376542757321)
    ·
      refine ⟨164178994238134782407067991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218905325650846376542757321 164178994238134782407067991)
      ·
        refine ⟨246268491357202173610601987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164178994238134782407067991 246268491357202173610601987)
        ·
          refine ⟨369402737035803260415902981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246268491357202173610601987 369402737035803260415902981)
          ·
            refine ⟨69263013194213111327981809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369402737035803260415902981 69263013194213111327981809)
            ·
              refine ⟨51947259895659833495986357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69263013194213111327981809 51947259895659833495986357)
              ·
                refine ⟨4870055615218109390248721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51947259895659833495986357 4870055615218109390248721)
                ·
                  refine ⟨3652541711413582042686541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4870055615218109390248721 3652541711413582042686541)
                  ·
                    refine ⟨1369703141780093266007453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652541711413582042686541 1369703141780093266007453)
                    ·
                      rfl

theorem cell22_4001231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_4001231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001231 prefixEnd_4001231 := by exact prefixLift 4001231
  have htrace : WordTrace (prefixWord ++ tailWord_4001231) baseStart_4001231 baseEnd_4001231 := by
    simpa [prefixWord, tailWord_4001231, baseEnd_4001231] using wordTrace_append hprefix tailTrace_4001231
  have hstable : (prefixWord ++ tailWord_4001231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001231).length < 2 ^ (prefixWord ++ tailWord_4001231).sum := by decide
  have hdescent : baseEnd_4001231 < baseStart_4001231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001274 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_4001274 : Nat := 118140960795 + 4001274 * 2 ^ 59
def prefixEnd_4001274 : Nat := 4983230072969 + 3 ^ 40 * 4001274 * 2
def baseEnd_4001274 : Nat := 1369717861558855487182321

theorem tailTrace_4001274 : CollatzResearch.WordTrace tailWord_4001274 prefixEnd_4001274 1369717861558855487182321 := by
  unfold tailWord_4001274
  simp only [CollatzResearch.WordTrace]
  refine ⟨36484613026518784009746719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97292301404050090692657917 36484613026518784009746719)
  ·
    refine ⟨54726919539778176014620079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36484613026518784009746719 54726919539778176014620079)
    ·
      refine ⟨82090379309667264021930119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54726919539778176014620079 82090379309667264021930119)
      ·
        refine ⟨123135568964500896032895179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82090379309667264021930119 123135568964500896032895179)
        ·
          refine ⟨184703353446751344049342769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123135568964500896032895179 184703353446751344049342769)
          ·
            refine ⟨138527515085063508037007077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184703353446751344049342769 138527515085063508037007077)
            ·
              refine ⟨25973909078449407756938827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138527515085063508037007077 25973909078449407756938827)
              ·
                refine ⟨38960863617674111635408241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25973909078449407756938827 38960863617674111635408241)
                ·
                  refine ⟨29220647713255583726556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38960863617674111635408241 29220647713255583726556181)
                  ·
                    refine ⟨1369717861558855487182321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29220647713255583726556181 1369717861558855487182321)
                    ·
                      rfl

theorem cell22_4001274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_4001274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4001274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4001274 prefixEnd_4001274 := by exact prefixLift 4001274
  have htrace : WordTrace (prefixWord ++ tailWord_4001274) baseStart_4001274 baseEnd_4001274 := by
    simpa [prefixWord, tailWord_4001274, baseEnd_4001274] using wordTrace_append hprefix tailTrace_4001274
  have hstable : (prefixWord ++ tailWord_4001274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001274).length < 2 ^ (prefixWord ++ tailWord_4001274).sum := by decide
  have hdescent : baseEnd_4001274 < baseStart_4001274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
