import V185TrunkScan23Chunk0940

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5569692 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_5569692 : Nat := 118140960795 + 5569692 * 2 ^ 59
def prefixEnd_5569692 : Nat := 4983230072969 + 3 ^ 40 * 5569692 * 2
def baseEnd_5569692 : Nat := 2859929093501727788135459

theorem tailTrace_5569692 : CollatzResearch.WordTrace tailWord_5569692 prefixEnd_5569692 2859929093501727788135459 := by
  unfold tailWord_5569692
  simp only [CollatzResearch.WordTrace]
  refine ⟨101571678068982293253803665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135428904091976391005071553 101571678068982293253803665)
  ·
    refine ⟨76178758551736719940352749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101571678068982293253803665 76178758551736719940352749)
    ·
      refine ⟨28567034456901269977632281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76178758551736719940352749 28567034456901269977632281)
      ·
        refine ⟨21425275842675952483224211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28567034456901269977632281 21425275842675952483224211)
        ·
          refine ⟨32137913764013928724836317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21425275842675952483224211 32137913764013928724836317)
          ·
            refine ⟨12051717661505223271813619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32137913764013928724836317 12051717661505223271813619)
            ·
              refine ⟨18077576492257834907720429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12051717661505223271813619 18077576492257834907720429)
              ·
                refine ⟨6779091184596688090395161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18077576492257834907720429 6779091184596688090395161)
                ·
                  refine ⟨5084318388447516067796371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6779091184596688090395161 5084318388447516067796371)
                  ·
                    refine ⟨7626477582671274101694557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5084318388447516067796371 7626477582671274101694557)
                    ·
                      refine ⟨2859929093501727788135459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626477582671274101694557 2859929093501727788135459)
                      ·
                        rfl

theorem cell23_5569692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_5569692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569692 prefixEnd_5569692 := by exact prefixLift 5569692
  have htrace : WordTrace (prefixWord ++ tailWord_5569692) baseStart_5569692 baseEnd_5569692 := by
    simpa [prefixWord, tailWord_5569692, baseEnd_5569692] using wordTrace_append hprefix tailTrace_5569692
  have hstable : (prefixWord ++ tailWord_5569692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569692).length < 2 ^ (prefixWord ++ tailWord_5569692).sum := by decide
  have hdescent : baseEnd_5569692 < baseStart_5569692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569715 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 6, 2, 2]
def baseStart_5569715 : Nat := 118140960795 + 5569715 * 2 ^ 59
def prefixEnd_5569715 : Nat := 4983230072969 + 3 ^ 40 * 5569715 * 2
def baseEnd_5569715 : Nat := 2859940903556781198147853

theorem tailTrace_5569715 : CollatzResearch.WordTrace tailWord_5569715 prefixEnd_5569715 2859940903556781198147853 := by
  unfold tailWord_5569715
  simp only [CollatzResearch.WordTrace]
  refine ⟨203144195016881261435694599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135429463344587507623796399 203144195016881261435694599)
  ·
    refine ⟨304716292525321892153541899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203144195016881261435694599 304716292525321892153541899)
    ·
      refine ⟨457074438787982838230312849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304716292525321892153541899 457074438787982838230312849)
      ·
        refine ⟨342805829090987128672734637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457074438787982838230312849 342805829090987128672734637)
        ·
          refine ⟨128552185909120173252275489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342805829090987128672734637 128552185909120173252275489)
          ·
            refine ⟨96414139431840129939206617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128552185909120173252275489 96414139431840129939206617)
            ·
              refine ⟨72310604573880097454404963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96414139431840129939206617 72310604573880097454404963)
              ·
                refine ⟨108465906860820146181607445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72310604573880097454404963 108465906860820146181607445)
                ·
                  refine ⟨5084339384100944352262849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108465906860820146181607445 5084339384100944352262849)
                  ·
                    refine ⟨3813254538075708264197137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5084339384100944352262849 3813254538075708264197137)
                    ·
                      refine ⟨2859940903556781198147853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813254538075708264197137 2859940903556781198147853)
                      ·
                        rfl

theorem cell23_5569715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 2, 2].length) (baseStart_5569715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569715 prefixEnd_5569715 := by exact prefixLift 5569715
  have htrace : WordTrace (prefixWord ++ tailWord_5569715) baseStart_5569715 baseEnd_5569715 := by
    simpa [prefixWord, tailWord_5569715, baseEnd_5569715] using wordTrace_append hprefix tailTrace_5569715
  have hstable : (prefixWord ++ tailWord_5569715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569715).length < 2 ^ (prefixWord ++ tailWord_5569715).sum := by decide
  have hdescent : baseEnd_5569715 < baseStart_5569715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569749 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5569749 : Nat := 118140960795 + 5569749 * 2 ^ 59
def prefixEnd_5569749 : Nat := 4983230072969 + 3 ^ 40 * 5569749 * 2
def baseEnd_5569749 : Nat := 2859958361899034065122697

theorem tailTrace_5569749 : CollatzResearch.WordTrace tailWord_5569749 prefixEnd_5569749 2859958361899034065122697 := by
  unfold tailWord_5569749
  simp only [CollatzResearch.WordTrace]
  refine ⟨203145435098758085242432301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135430290065838723494954867 203145435098758085242432301)
  ·
    refine ⟨76179538162034281965912113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203145435098758085242432301 76179538162034281965912113)
    ·
      refine ⟨57134653621525711474434085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76179538162034281965912113 57134653621525711474434085)
      ·
        refine ⟨10712747554036070901456391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57134653621525711474434085 10712747554036070901456391)
        ·
          refine ⟨16069121331054106352184587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10712747554036070901456391 16069121331054106352184587)
          ·
            refine ⟨24103681996581159528276881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16069121331054106352184587 24103681996581159528276881)
            ·
              refine ⟨18077761497435869646207661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24103681996581159528276881 18077761497435869646207661)
              ·
                refine ⟨6779160561538451117327873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18077761497435869646207661 6779160561538451117327873)
                ·
                  refine ⟨5084370421153838337995905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6779160561538451117327873 5084370421153838337995905)
                  ·
                    refine ⟨3813277815865378753496929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5084370421153838337995905 3813277815865378753496929)
                    ·
                      refine ⟨2859958361899034065122697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813277815865378753496929 2859958361899034065122697)
                      ·
                        rfl

theorem cell23_5569749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5569749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569749 prefixEnd_5569749 := by exact prefixLift 5569749
  have htrace : WordTrace (prefixWord ++ tailWord_5569749) baseStart_5569749 baseEnd_5569749 := by
    simpa [prefixWord, tailWord_5569749, baseEnd_5569749] using wordTrace_append hprefix tailTrace_5569749
  have hstable : (prefixWord ++ tailWord_5569749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569749).length < 2 ^ (prefixWord ++ tailWord_5569749).sum := by decide
  have hdescent : baseEnd_5569749 < baseStart_5569749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569768 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 1, 7]
def baseStart_5569768 : Nat := 118140960795 + 5569768 * 2 ^ 59
def prefixEnd_5569768 : Nat := 4983230072969 + 3 ^ 40 * 5569768 * 2
def baseEnd_5569768 : Nat := 953322706010489830261703

theorem tailTrace_5569768 : CollatzResearch.WordTrace tailWord_5569768 prefixEnd_5569768 953322706010489830261703 := by
  unfold tailWord_5569768
  simp only [CollatzResearch.WordTrace]
  refine ⟨101573064042844625743686979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135430752057126167658249305 101573064042844625743686979)
  ·
    refine ⟨152359596064266938615530469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101573064042844625743686979 152359596064266938615530469)
    ·
      refine ⟨28567424262050050990411963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152359596064266938615530469 28567424262050050990411963)
      ·
        refine ⟨42851136393075076485617945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28567424262050050990411963 42851136393075076485617945)
        ·
          refine ⟨32138352294806307364213459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42851136393075076485617945 32138352294806307364213459)
          ·
            refine ⟨48207528442209461046320189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32138352294806307364213459 48207528442209461046320189)
            ·
              refine ⟨18077823165828547892370071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48207528442209461046320189 18077823165828547892370071)
              ·
                refine ⟨27116734748742821838555107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18077823165828547892370071 27116734748742821838555107)
                ·
                  refine ⟨40675102123114232757832661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27116734748742821838555107 40675102123114232757832661)
                  ·
                    refine ⟨953322706010489830261703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40675102123114232757832661 953322706010489830261703)
                    ·
                      rfl

theorem cell23_5569768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_5569768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569768 prefixEnd_5569768 := by exact prefixLift 5569768
  have htrace : WordTrace (prefixWord ++ tailWord_5569768) baseStart_5569768 baseEnd_5569768 := by
    simpa [prefixWord, tailWord_5569768, baseEnd_5569768] using wordTrace_append hprefix tailTrace_5569768
  have hstable : (prefixWord ++ tailWord_5569768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569768).length < 2 ^ (prefixWord ++ tailWord_5569768).sum := by decide
  have hdescent : baseEnd_5569768 < baseStart_5569768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569815 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 3, 4]
def baseStart_5569815 : Nat := 118140960795 + 5569815 * 2 ^ 59
def prefixEnd_5569815 : Nat := 4983230072969 + 3 ^ 40 * 5569815 * 2
def baseEnd_5569815 : Nat := 953330750540743602299131

theorem tailTrace_5569815 : CollatzResearch.WordTrace tailWord_5569815 prefixEnd_5569815 953330750540743602299131 := by
  unfold tailWord_5569815
  simp only [CollatzResearch.WordTrace]
  refine ⟨203147842316518978514334899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135431894877679319009556599 203147842316518978514334899)
  ·
    refine ⟨304721763474778467771502349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203147842316518978514334899 304721763474778467771502349)
    ·
      refine ⟨114270661303041925414313381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304721763474778467771502349 114270661303041925414313381)
      ·
        refine ⟨21425748994320361015183759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114270661303041925414313381 21425748994320361015183759)
        ·
          refine ⟨32138623491480541522775639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21425748994320361015183759 32138623491480541522775639)
          ·
            refine ⟨48207935237220812284163459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32138623491480541522775639 48207935237220812284163459)
            ·
              refine ⟨72311902855831218426245189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48207935237220812284163459 72311902855831218426245189)
              ·
                refine ⟨13558481785468353454920973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72311902855831218426245189 13558481785468353454920973)
                ·
                  refine ⟨5084430669550632545595365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13558481785468353454920973 5084430669550632545595365)
                  ·
                    refine ⟨953330750540743602299131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5084430669550632545595365 953330750540743602299131)
                    ·
                      rfl

theorem cell23_5569815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_5569815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569815 prefixEnd_5569815 := by exact prefixLift 5569815
  have htrace : WordTrace (prefixWord ++ tailWord_5569815) baseStart_5569815 baseEnd_5569815 := by
    simpa [prefixWord, tailWord_5569815, baseEnd_5569815] using wordTrace_append hprefix tailTrace_5569815
  have hstable : (prefixWord ++ tailWord_5569815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569815).length < 2 ^ (prefixWord ++ tailWord_5569815).sum := by decide
  have hdescent : baseEnd_5569815 < baseStart_5569815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569825 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_5569825 : Nat := 118140960795 + 5569825 * 2 ^ 59
def prefixEnd_5569825 : Nat := 4983230072969 + 3 ^ 40 * 5569825 * 2
def baseEnd_5569825 : Nat := 2859997386428775767772347

theorem tailTrace_5569825 : CollatzResearch.WordTrace tailWord_5569825 prefixEnd_5569825 2859997386428775767772347 := by
  unfold tailWord_5569825
  simp only [CollatzResearch.WordTrace]
  refine ⟨203148207046482750222198929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135432138030988500148132619 203148207046482750222198929)
  ·
    refine ⟨152361155284862062666649197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203148207046482750222198929 152361155284862062666649197)
    ·
      refine ⟨57135433231823273499993449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152361155284862062666649197 57135433231823273499993449)
      ·
        refine ⟨42851574923867455124995087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57135433231823273499993449 42851574923867455124995087)
        ·
          refine ⟨64277362385801182687492631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42851574923867455124995087 64277362385801182687492631)
          ·
            refine ⟨96416043578701774031238947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64277362385801182687492631 96416043578701774031238947)
            ·
              refine ⟨144624065368052661046858421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96416043578701774031238947 144624065368052661046858421)
              ·
                refine ⟨13558506128254936973142977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144624065368052661046858421 13558506128254936973142977)
                ·
                  refine ⟨10168879596191202729857233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13558506128254936973142977 10168879596191202729857233)
                  ·
                    refine ⟨7626659697143402047392925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10168879596191202729857233 7626659697143402047392925)
                    ·
                      refine ⟨2859997386428775767772347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626659697143402047392925 2859997386428775767772347)
                      ·
                        rfl

theorem cell23_5569825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_5569825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569825 prefixEnd_5569825 := by exact prefixLift 5569825
  have htrace : WordTrace (prefixWord ++ tailWord_5569825) baseStart_5569825 baseEnd_5569825 := by
    simpa [prefixWord, tailWord_5569825, baseEnd_5569825] using wordTrace_append hprefix tailTrace_5569825
  have hstable : (prefixWord ++ tailWord_5569825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569825).length < 2 ^ (prefixWord ++ tailWord_5569825).sum := by decide
  have hdescent : baseEnd_5569825 < baseStart_5569825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569828 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 10]
def baseStart_5569828 : Nat := 118140960795 + 5569828 * 2 ^ 59
def prefixEnd_5569828 : Nat := 4983230072969 + 3 ^ 40 * 5569828 * 2
def baseEnd_5569828 : Nat := 317777658541193250670537

theorem tailTrace_5569828 : CollatzResearch.WordTrace tailWord_5569828 prefixEnd_5569828 317777658541193250670537 := by
  unfold tailWord_5569828
  simp only [CollatzResearch.WordTrace]
  refine ⟨101574158232735940867279069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135432210976981254489705425 101574158232735940867279069)
  ·
    refine ⟨38090309337275977825229651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101574158232735940867279069 38090309337275977825229651)
    ·
      refine ⟨57135464005913966737844477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38090309337275977825229651 57135464005913966737844477)
      ·
        refine ⟨21425799002217737526691679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57135464005913966737844477 21425799002217737526691679)
        ·
          refine ⟨32138698503326606290037519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21425799002217737526691679 32138698503326606290037519)
          ·
            refine ⟨48208047754989909435056279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32138698503326606290037519 48208047754989909435056279)
            ·
              refine ⟨72312071632484864152584419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48208047754989909435056279 72312071632484864152584419)
              ·
                refine ⟨108468107448727296228876629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72312071632484864152584419 108468107448727296228876629)
                ·
                  refine ⟨317777658541193250670537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 108468107448727296228876629 317777658541193250670537)
                  ·
                    rfl

theorem cell23_5569828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_5569828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569828 prefixEnd_5569828 := by exact prefixLift 5569828
  have htrace : WordTrace (prefixWord ++ tailWord_5569828) baseStart_5569828 baseEnd_5569828 := by
    simpa [prefixWord, tailWord_5569828, baseEnd_5569828] using wordTrace_append hprefix tailTrace_5569828
  have hstable : (prefixWord ++ tailWord_5569828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569828).length < 2 ^ (prefixWord ++ tailWord_5569828).sum := by decide
  have hdescent : baseEnd_5569828 < baseStart_5569828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569842 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_5569842 : Nat := 118140960795 + 5569842 * 2 ^ 59
def prefixEnd_5569842 : Nat := 4983230072969 + 3 ^ 40 * 5569842 * 2
def baseEnd_5569842 : Nat := 2860006115599902201259769

theorem tailTrace_5569842 : CollatzResearch.WordTrace tailWord_5569842 prefixEnd_5569842 2860006115599902201259769 := by
  unfold tailWord_5569842
  simp only [CollatzResearch.WordTrace]
  refine ⟨50787206771855290531391945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135432551391614108083711853 50787206771855290531391945)
  ·
    refine ⟨38090405078891467898543959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50787206771855290531391945 38090405078891467898543959)
    ·
      refine ⟨57135607618337201847815939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38090405078891467898543959 57135607618337201847815939)
      ·
        refine ⟨85703411427505802771723909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57135607618337201847815939 85703411427505802771723909)
        ·
          refine ⟨16069389642657338019698233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85703411427505802771723909 16069389642657338019698233)
          ·
            refine ⟨12052042231993003514773675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16069389642657338019698233 12052042231993003514773675)
            ·
              refine ⟨18078063347989505272160513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12052042231993003514773675 18078063347989505272160513)
              ·
                refine ⟨13558547510992128954120385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18078063347989505272160513 13558547510992128954120385)
                ·
                  refine ⟨10168910633244096715590289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13558547510992128954120385 10168910633244096715590289)
                  ·
                    refine ⟨7626682974933072536692717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10168910633244096715590289 7626682974933072536692717)
                    ·
                      refine ⟨2860006115599902201259769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626682974933072536692717 2860006115599902201259769)
                      ·
                        rfl

theorem cell23_5569842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_5569842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569842 prefixEnd_5569842 := by exact prefixLift 5569842
  have htrace : WordTrace (prefixWord ++ tailWord_5569842) baseStart_5569842 baseEnd_5569842 := by
    simpa [prefixWord, tailWord_5569842, baseEnd_5569842] using wordTrace_append hprefix tailTrace_5569842
  have hstable : (prefixWord ++ tailWord_5569842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569842).length < 2 ^ (prefixWord ++ tailWord_5569842).sum := by decide
  have hdescent : baseEnd_5569842 < baseStart_5569842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569849 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 3, 4]
def baseStart_5569849 : Nat := 118140960795 + 5569849 * 2 ^ 59
def prefixEnd_5569849 : Nat := 4983230072969 + 3 ^ 40 * 5569849 * 2
def baseEnd_5569849 : Nat := 953336569988161224624079

theorem tailTrace_5569849 : CollatzResearch.WordTrace tailWord_5569849 prefixEnd_5569849 953336569988161224624079 := by
  unfold tailWord_5569849
  simp only [CollatzResearch.WordTrace]
  refine ⟨203149082398395802321072601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135432721598930534880715067 203149082398395802321072601)
  ·
    refine ⟨152361811798796851740804451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203149082398395802321072601 152361811798796851740804451)
    ·
      refine ⟨228542717698195277611206677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152361811798796851740804451 228542717698195277611206677)
      ·
        refine ⟨10712939892102903638025313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228542717698195277611206677 10712939892102903638025313)
        ·
          refine ⟨8034704919077177728518985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10712939892102903638025313 8034704919077177728518985)
          ·
            refine ⟨6026028689307883296389239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8034704919077177728518985 6026028689307883296389239)
            ·
              refine ⟨9039043033961824944583859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6026028689307883296389239 9039043033961824944583859)
              ·
                refine ⟨13558564550942737416875789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9039043033961824944583859 13558564550942737416875789)
                ·
                  refine ⟨5084461706603526531328421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13558564550942737416875789 5084461706603526531328421)
                  ·
                    refine ⟨953336569988161224624079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5084461706603526531328421 953336569988161224624079)
                    ·
                      rfl

theorem cell23_5569849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_5569849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569849 prefixEnd_5569849 := by exact prefixLift 5569849
  have htrace : WordTrace (prefixWord ++ tailWord_5569849) baseStart_5569849 baseEnd_5569849 := by
    simpa [prefixWord, tailWord_5569849, baseEnd_5569849] using wordTrace_append hprefix tailTrace_5569849
  have hstable : (prefixWord ++ tailWord_5569849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569849).length < 2 ^ (prefixWord ++ tailWord_5569849).sum := by decide
  have hdescent : baseEnd_5569849 < baseStart_5569849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569865 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 3, 5, 2]
def baseStart_5569865 : Nat := 118140960795 + 5569865 * 2 ^ 59
def prefixEnd_5569865 : Nat := 4983230072969 + 3 ^ 40 * 5569865 * 2
def baseEnd_5569865 : Nat := 2860017925654955611272163

theorem tailTrace_5569865 : CollatzResearch.WordTrace tailWord_5569865 prefixEnd_5569865 2860017925654955611272163 := by
  unfold tailWord_5569865
  simp only [CollatzResearch.WordTrace]
  refine ⟨203149665966337837053655049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135433110644225224702436699 203149665966337837053655049)
  ·
    refine ⟨152362249474753377790241287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203149665966337837053655049 152362249474753377790241287)
    ·
      refine ⟨228543374212130066685361931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152362249474753377790241287 228543374212130066685361931)
      ·
        refine ⟨342815061318195100028042897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228543374212130066685361931 342815061318195100028042897)
        ·
          refine ⟨257111295988646325021032173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342815061318195100028042897 257111295988646325021032173)
          ·
            refine ⟨96416735995742371882887065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257111295988646325021032173 96416735995742371882887065)
            ·
              refine ⟨72312551996806778912165299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96416735995742371882887065 72312551996806778912165299)
              ·
                refine ⟨108468827995210168368247949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72312551996806778912165299 108468827995210168368247949)
                ·
                  refine ⟨40675810498203813138092981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108468827995210168368247949 40675810498203813138092981)
                  ·
                    refine ⟨3813357234206607481696217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40675810498203813138092981 3813357234206607481696217)
                    ·
                      refine ⟨2860017925654955611272163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813357234206607481696217 2860017925654955611272163)
                      ·
                        rfl

theorem cell23_5569865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 5, 2].length) (baseStart_5569865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569865 prefixEnd_5569865 := by exact prefixLift 5569865
  have htrace : WordTrace (prefixWord ++ tailWord_5569865) baseStart_5569865 baseEnd_5569865 := by
    simpa [prefixWord, tailWord_5569865, baseEnd_5569865] using wordTrace_append hprefix tailTrace_5569865
  have hstable : (prefixWord ++ tailWord_5569865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569865).length < 2 ^ (prefixWord ++ tailWord_5569865).sum := by decide
  have hdescent : baseEnd_5569865 < baseStart_5569865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569882 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2]
def baseStart_5569882 : Nat := 118140960795 + 5569882 * 2 ^ 59
def prefixEnd_5569882 : Nat := 4983230072969 + 3 ^ 40 * 5569882 * 2
def baseEnd_5569882 : Nat := 2860026654826082044759585

theorem tailTrace_5569882 : CollatzResearch.WordTrace tailWord_5569882 prefixEnd_5569882 2860026654826082044759585 := by
  unfold tailWord_5569882
  simp only [CollatzResearch.WordTrace]
  refine ⟨50787571501819062239255975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135433524004850832638015933 50787571501819062239255975)
  ·
    refine ⟨76181357252728593358883963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50787571501819062239255975 76181357252728593358883963)
    ·
      refine ⟨114272035879092890038325945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76181357252728593358883963 114272035879092890038325945)
      ·
        refine ⟨85704026909319667528744459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114272035879092890038325945 85704026909319667528744459)
        ·
          refine ⟨128556040363979501293116689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85704026909319667528744459 128556040363979501293116689)
          ·
            refine ⟨96417030272984625969837517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128556040363979501293116689 96417030272984625969837517)
            ·
              refine ⟨36156386352369234738689069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96417030272984625969837517 36156386352369234738689069)
              ·
                refine ⟨13558644882138463027008401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36156386352369234738689069 13558644882138463027008401)
                ·
                  refine ⟨10168983661603847270256301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13558644882138463027008401 10168983661603847270256301)
                  ·
                    refine ⟨3813368873101442726346113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10168983661603847270256301 3813368873101442726346113)
                    ·
                      refine ⟨2860026654826082044759585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813368873101442726346113 2860026654826082044759585)
                      ·
                        rfl

theorem cell23_5569882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_5569882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569882 prefixEnd_5569882 := by exact prefixLift 5569882
  have htrace : WordTrace (prefixWord ++ tailWord_5569882) baseStart_5569882 baseEnd_5569882 := by
    simpa [prefixWord, tailWord_5569882, baseEnd_5569882] using wordTrace_append hprefix tailTrace_5569882
  have hstable : (prefixWord ++ tailWord_5569882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569882).length < 2 ^ (prefixWord ++ tailWord_5569882).sum := by decide
  have hdescent : baseEnd_5569882 < baseStart_5569882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569905 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 4, 4]
def baseStart_5569905 : Nat := 118140960795 + 5569905 * 2 ^ 59
def prefixEnd_5569905 : Nat := 4983230072969 + 3 ^ 40 * 5569905 * 2
def baseEnd_5569905 : Nat := 953346154960378484923993

theorem tailTrace_5569905 : CollatzResearch.WordTrace tailWord_5569905 prefixEnd_5569905 953346154960378484923993 := by
  unfold tailWord_5569905
  simp only [CollatzResearch.WordTrace]
  refine ⟨203151124886192923885111169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135434083257461949256740779 203151124886192923885111169)
  ·
    refine ⟨152363343664644692913833377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203151124886192923885111169 152363343664644692913833377)
    ·
      refine ⟨114272507748483519685375033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152363343664644692913833377 114272507748483519685375033)
      ·
        refine ⟨85704380811362639764031275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114272507748483519685375033 85704380811362639764031275)
        ·
          refine ⟨128556571217043959646046913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85704380811362639764031275 128556571217043959646046913)
          ·
            refine ⟨96417428412782969734535185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128556571217043959646046913 96417428412782969734535185)
            ·
              refine ⟨72313071309587227300901389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96417428412782969734535185 72313071309587227300901389)
              ·
                refine ⟨27117401741095210237838021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72313071309587227300901389 27117401741095210237838021)
                ·
                  refine ⟨5084512826455351919594629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27117401741095210237838021 5084512826455351919594629)
                  ·
                    refine ⟨953346154960378484923993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5084512826455351919594629 953346154960378484923993)
                    ·
                      rfl

theorem cell23_5569905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_5569905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569905 prefixEnd_5569905 := by exact prefixLift 5569905
  have htrace : WordTrace (prefixWord ++ tailWord_5569905) baseStart_5569905 baseEnd_5569905 := by
    simpa [prefixWord, tailWord_5569905, baseEnd_5569905] using wordTrace_append hprefix tailTrace_5569905
  have hstable : (prefixWord ++ tailWord_5569905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569905).length < 2 ^ (prefixWord ++ tailWord_5569905).sum := by decide
  have hdescent : baseEnd_5569905 < baseStart_5569905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569912 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 9, 2, 2]
def baseStart_5569912 : Nat := 118140960795 + 5569912 * 2 ^ 59
def prefixEnd_5569912 : Nat := 4983230072969 + 3 ^ 40 * 5569912 * 2
def baseEnd_5569912 : Nat := 2860042059245716927384447

theorem tailTrace_5569912 : CollatzResearch.WordTrace tailWord_5569912 prefixEnd_5569912 2860042059245716927384447 := by
  unfold tailWord_5569912
  simp only [CollatzResearch.WordTrace]
  refine ⟨101575690098583782040307995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135434253464778376053743993 101575690098583782040307995)
  ·
    refine ⟨152363535147875673060461993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101575690098583782040307995 152363535147875673060461993)
    ·
      refine ⟨114272651360906754795346495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152363535147875673060461993 114272651360906754795346495)
      ·
        refine ⟨171408977041360132193019743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114272651360906754795346495 171408977041360132193019743)
        ·
          refine ⟨257113465562040198289529615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171408977041360132193019743 257113465562040198289529615)
          ·
            refine ⟨385670198343060297434294423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257113465562040198289529615 385670198343060297434294423)
            ·
              refine ⟨578505297514590446151441635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385670198343060297434294423 578505297514590446151441635)
              ·
                refine ⟨867757946271885669227162453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578505297514590446151441635 867757946271885669227162453)
                ·
                  refine ⟨5084519216436830093127905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 867757946271885669227162453 5084519216436830093127905)
                  ·
                    refine ⟨3813389412327622569845929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5084519216436830093127905 3813389412327622569845929)
                    ·
                      refine ⟨2860042059245716927384447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813389412327622569845929 2860042059245716927384447)
                      ·
                        rfl

theorem cell23_5569912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_5569912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569912 prefixEnd_5569912 := by exact prefixLift 5569912
  have htrace : WordTrace (prefixWord ++ tailWord_5569912) baseStart_5569912 baseEnd_5569912 := by
    simpa [prefixWord, tailWord_5569912, baseEnd_5569912] using wordTrace_append hprefix tailTrace_5569912
  have hstable : (prefixWord ++ tailWord_5569912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569912).length < 2 ^ (prefixWord ++ tailWord_5569912).sum := by decide
  have hdescent : baseEnd_5569912 < baseStart_5569912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569915 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 3]
def baseStart_5569915 : Nat := 118140960795 + 5569915 * 2 ^ 59
def prefixEnd_5569915 : Nat := 4983230072969 + 3 ^ 40 * 5569915 * 2
def baseEnd_5569915 : Nat := 2860043599687680415646933

theorem tailTrace_5569915 : CollatzResearch.WordTrace tailWord_5569915 prefixEnd_5569915 2860043599687680415646933 := by
  unfold tailWord_5569915
  simp only [CollatzResearch.WordTrace]
  refine ⟨203151489616156695592975199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135434326410771130395316799 203151489616156695592975199)
  ·
    refine ⟨304727234424235043389462799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203151489616156695592975199 304727234424235043389462799)
    ·
      refine ⟨457090851636352565084194199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304727234424235043389462799 457090851636352565084194199)
      ·
        refine ⟨685636277454528847626291299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457090851636352565084194199 685636277454528847626291299)
        ·
          refine ⟨1028454416181793271439436949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685636277454528847626291299 1028454416181793271439436949)
          ·
            refine ⟨48208800758521559598723607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1028454416181793271439436949 48208800758521559598723607)
            ·
              refine ⟨72313201137782339398085411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48208800758521559598723607 72313201137782339398085411)
              ·
                refine ⟨108469801706673509097128117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72313201137782339398085411 108469801706673509097128117)
                ·
                  refine ⟨10169043910000641477855761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108469801706673509097128117 10169043910000641477855761)
                  ·
                    refine ⟨7626782932500481108391821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10169043910000641477855761 7626782932500481108391821)
                    ·
                      refine ⟨2860043599687680415646933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626782932500481108391821 2860043599687680415646933)
                      ·
                        rfl

theorem cell23_5569915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 3].length) (baseStart_5569915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569915 prefixEnd_5569915 := by exact prefixLift 5569915
  have htrace : WordTrace (prefixWord ++ tailWord_5569915) baseStart_5569915 baseEnd_5569915 := by
    simpa [prefixWord, tailWord_5569915, baseEnd_5569915] using wordTrace_append hprefix tailTrace_5569915
  have hstable : (prefixWord ++ tailWord_5569915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569915).length < 2 ^ (prefixWord ++ tailWord_5569915).sum := by decide
  have hdescent : baseEnd_5569915 < baseStart_5569915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569925 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_5569925 : Nat := 118140960795 + 5569925 * 2 ^ 59
def prefixEnd_5569925 : Nat := 4983230072969 + 3 ^ 40 * 5569925 * 2
def baseEnd_5569925 : Nat := 2860048734494225376521887

theorem tailTrace_5569925 : CollatzResearch.WordTrace tailWord_5569925 prefixEnd_5569925 2860048734494225376521887 := by
  unfold tailWord_5569925
  simp only [CollatzResearch.WordTrace]
  refine ⟨203151854346120467300839229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135434569564080311533892819 203151854346120467300839229)
  ·
    refine ⟨76181945379795175237814711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203151854346120467300839229 76181945379795175237814711)
    ·
      refine ⟨114272918069692762856722067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76181945379795175237814711 114272918069692762856722067)
      ·
        refine ⟨171409377104539144285083101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114272918069692762856722067 171409377104539144285083101)
        ·
          refine ⟨64278516414202179106906163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171409377104539144285083101 64278516414202179106906163)
          ·
            refine ⟨96417774621303268660359245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64278516414202179106906163 96417774621303268660359245)
            ·
              refine ⟨36156665482988725747634717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96417774621303268660359245 36156665482988725747634717)
              ·
                refine ⟨13558749556120772155363019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36156665482988725747634717 13558749556120772155363019)
                ·
                  refine ⟨20338124334181158233044529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13558749556120772155363019 20338124334181158233044529)
                  ·
                    refine ⟨15253593250635868674783397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20338124334181158233044529 15253593250635868674783397)
                    ·
                      refine ⟨2860048734494225376521887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15253593250635868674783397 2860048734494225376521887)
                      ·
                        rfl

theorem cell23_5569925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_5569925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569925 prefixEnd_5569925 := by exact prefixLift 5569925
  have htrace : WordTrace (prefixWord ++ tailWord_5569925) baseStart_5569925 baseEnd_5569925 := by
    simpa [prefixWord, tailWord_5569925, baseEnd_5569925] using wordTrace_append hprefix tailTrace_5569925
  have hstable : (prefixWord ++ tailWord_5569925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569925).length < 2 ^ (prefixWord ++ tailWord_5569925).sum := by decide
  have hdescent : baseEnd_5569925 < baseStart_5569925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569932 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_5569932 : Nat := 118140960795 + 5569932 * 2 ^ 59
def prefixEnd_5569932 : Nat := 4983230072969 + 3 ^ 40 * 5569932 * 2
def baseEnd_5569932 : Nat := 2860052328858806849134355

theorem tailTrace_5569932 : CollatzResearch.WordTrace tailWord_5569932 prefixEnd_5569932 2860052328858806849134355 := by
  unfold tailWord_5569932
  simp only [CollatzResearch.WordTrace]
  refine ⟨101576054828547553748172025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135434739771396738330896033 101576054828547553748172025)
  ·
    refine ⟨76182041121410665311129019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101576054828547553748172025 76182041121410665311129019)
    ·
      refine ⟨114273061682115997966693529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76182041121410665311129019 114273061682115997966693529)
      ·
        refine ⟨85704796261586998475020147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114273061682115997966693529 85704796261586998475020147)
        ·
          refine ⟨128557194392380497712530221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85704796261586998475020147 128557194392380497712530221)
          ·
            refine ⟨48208947897142686642198833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128557194392380497712530221 48208947897142686642198833)
            ·
              refine ⟨36156710922857014981649125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48208947897142686642198833 36156710922857014981649125)
              ·
                refine ⟨6779383298035690309059211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36156710922857014981649125 6779383298035690309059211)
                ·
                  refine ⟨10169074947053535463588817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6779383298035690309059211 10169074947053535463588817)
                  ·
                    refine ⟨7626806210290151597691613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10169074947053535463588817 7626806210290151597691613)
                    ·
                      refine ⟨2860052328858806849134355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626806210290151597691613 2860052328858806849134355)
                      ·
                        rfl

theorem cell23_5569932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_5569932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569932 prefixEnd_5569932 := by exact prefixLift 5569932
  have htrace : WordTrace (prefixWord ++ tailWord_5569932) baseStart_5569932 baseEnd_5569932 := by
    simpa [prefixWord, tailWord_5569932, baseEnd_5569932] using wordTrace_append hprefix tailTrace_5569932
  have hstable : (prefixWord ++ tailWord_5569932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569932).length < 2 ^ (prefixWord ++ tailWord_5569932).sum := by decide
  have hdescent : baseEnd_5569932 < baseStart_5569932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569949 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_5569949 : Nat := 118140960795 + 5569949 * 2 ^ 59
def prefixEnd_5569949 : Nat := 4983230072969 + 3 ^ 40 * 5569949 * 2
def baseEnd_5569949 : Nat := 2860061058029933282621777

theorem tailTrace_5569949 : CollatzResearch.WordTrace tailWord_5569949 prefixEnd_5569949 2860061058029933282621777 := by
  unfold tailWord_5569949
  simp only [CollatzResearch.WordTrace]
  refine ⟨203152729698033519399712901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135435153132022346266475267 203152729698033519399712901)
  ·
    refine ⟨38091136818381284887446169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203152729698033519399712901 38091136818381284887446169)
    ·
      refine ⟨28568352613785963665584627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38091136818381284887446169 28568352613785963665584627)
      ·
        refine ⟨42852528920678945498376941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28568352613785963665584627 42852528920678945498376941)
        ·
          refine ⟨16069698345254604561891353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42852528920678945498376941 16069698345254604561891353)
          ·
            refine ⟨12052273758940953421418515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16069698345254604561891353 12052273758940953421418515)
            ·
              refine ⟨18078410638411430132127773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12052273758940953421418515 18078410638411430132127773)
              ·
                refine ⟨6779403989404286299547915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18078410638411430132127773 6779403989404286299547915)
                ·
                  refine ⟨10169105984106429449321873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6779403989404286299547915 10169105984106429449321873)
                  ·
                    refine ⟨7626829488079822086991405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10169105984106429449321873 7626829488079822086991405)
                    ·
                      refine ⟨2860061058029933282621777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626829488079822086991405 2860061058029933282621777)
                      ·
                        rfl

theorem cell23_5569949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_5569949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569949 prefixEnd_5569949 := by exact prefixLift 5569949
  have htrace : WordTrace (prefixWord ++ tailWord_5569949) baseStart_5569949 baseEnd_5569949 := by
    simpa [prefixWord, tailWord_5569949, baseEnd_5569949] using wordTrace_append hprefix tailTrace_5569949
  have hstable : (prefixWord ++ tailWord_5569949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569949).length < 2 ^ (prefixWord ++ tailWord_5569949).sum := by decide
  have hdescent : baseEnd_5569949 < baseStart_5569949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570065 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_5570065 : Nat := 118140960795 + 5570065 * 2 ^ 59
def prefixEnd_5570065 : Nat := 4983230072969 + 3 ^ 40 * 5570065 * 2
def baseEnd_5570065 : Nat := 2860120621785854828771243

theorem tailTrace_5570065 : CollatzResearch.WordTrace tailWord_5570065 prefixEnd_5570065 2860120621785854828771243 := by
  unfold tailWord_5570065
  simp only [CollatzResearch.WordTrace]
  refine ⟨203156960565613271210935649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135437973710408847473957099 203156960565613271210935649)
  ·
    refine ⟨152367720424209953408201737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203156960565613271210935649 152367720424209953408201737)
    ·
      refine ⟨114275790318157465056151303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152367720424209953408201737 114275790318157465056151303)
      ·
        refine ⟨171413685477236197584226955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114275790318157465056151303 171413685477236197584226955)
        ·
          refine ⟨257120528215854296376340433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171413685477236197584226955 257120528215854296376340433)
          ·
            refine ⟨192840396161890722282255325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257120528215854296376340433 192840396161890722282255325)
            ·
              refine ⟨72315148560709020855845747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192840396161890722282255325 72315148560709020855845747)
              ·
                refine ⟨108472722841063531283768621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72315148560709020855845747 108472722841063531283768621)
                ·
                  refine ⟨40677271065398824231413233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108472722841063531283768621 40677271065398824231413233)
                  ·
                    refine ⟨30507953299049118173559925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40677271065398824231413233 30507953299049118173559925)
                    ·
                      refine ⟨2860120621785854828771243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30507953299049118173559925 2860120621785854828771243)
                      ·
                        rfl

theorem cell23_5570065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_5570065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570065 prefixEnd_5570065 := by exact prefixLift 5570065
  have htrace : WordTrace (prefixWord ++ tailWord_5570065) baseStart_5570065 baseEnd_5570065 := by
    simpa [prefixWord, tailWord_5570065, baseEnd_5570065] using wordTrace_append hprefix tailTrace_5570065
  have hstable : (prefixWord ++ tailWord_5570065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570065).length < 2 ^ (prefixWord ++ tailWord_5570065).sum := by decide
  have hdescent : baseEnd_5570065 < baseStart_5570065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570082 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_5570082 : Nat := 118140960795 + 5570082 * 2 ^ 59
def prefixEnd_5570082 : Nat := 4983230072969 + 3 ^ 40 * 5570082 * 2
def baseEnd_5570082 : Nat := 2860129350956981262258665

theorem tailTrace_5570082 : CollatzResearch.WordTrace tailWord_5570082 prefixEnd_5570082 2860129350956981262258665 := by
  unfold tailWord_5570082
  simp only [CollatzResearch.WordTrace]
  refine ⟨50789395151637920778576125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135438387071034455409536333 50789395151637920778576125)
  ·
    refine ⟨19046023181864220291966047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50789395151637920778576125 19046023181864220291966047)
    ·
      refine ⟨28569034772796330437949071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19046023181864220291966047 28569034772796330437949071)
      ·
        refine ⟨42853552159194495656923607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28569034772796330437949071 42853552159194495656923607)
        ·
          refine ⟨64280328238791743485385411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42853552159194495656923607 64280328238791743485385411)
          ·
            refine ⟨96420492358187615228078117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64280328238791743485385411 96420492358187615228078117)
            ·
              refine ⟨18078842317160177855264647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96420492358187615228078117 18078842317160177855264647)
              ·
                refine ⟨27118263475740266782896971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18078842317160177855264647 27118263475740266782896971)
                ·
                  refine ⟨40677395213610400174345457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27118263475740266782896971 40677395213610400174345457)
                  ·
                    refine ⟨30508046410207800130759093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40677395213610400174345457 30508046410207800130759093)
                    ·
                      refine ⟨2860129350956981262258665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30508046410207800130759093 2860129350956981262258665)
                      ·
                        rfl

theorem cell23_5570082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_5570082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570082 prefixEnd_5570082 := by exact prefixLift 5570082
  have htrace : WordTrace (prefixWord ++ tailWord_5570082) baseStart_5570082 baseEnd_5570082 := by
    simpa [prefixWord, tailWord_5570082, baseEnd_5570082] using wordTrace_append hprefix tailTrace_5570082
  have hstable : (prefixWord ++ tailWord_5570082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570082).length < 2 ^ (prefixWord ++ tailWord_5570082).sum := by decide
  have hdescent : baseEnd_5570082 < baseStart_5570082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570085 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_5570085 : Nat := 118140960795 + 5570085 * 2 ^ 59
def prefixEnd_5570085 : Nat := 4983230072969 + 3 ^ 40 * 5570085 * 2
def baseEnd_5570085 : Nat := 953376963799648250173717

theorem tailTrace_5570085 : CollatzResearch.WordTrace tailWord_5570085 prefixEnd_5570085 953376963799648250173717 := by
  unfold tailWord_5570085
  simp only [CollatzResearch.WordTrace]
  refine ⟨203157690025540814626663709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135438460017027209751109139 203157690025540814626663709)
  ·
    refine ⟨76184133759577805484998891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203157690025540814626663709 76184133759577805484998891)
    ·
      refine ⟨114276200639366708227498337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76184133759577805484998891 114276200639366708227498337)
      ·
        refine ⟨85707150479525031170623753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114276200639366708227498337 85707150479525031170623753)
        ·
          refine ⟨64280362859643773377967815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85707150479525031170623753 64280362859643773377967815)
          ·
            refine ⟨96420544289465660066951723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64280362859643773377967815 96420544289465660066951723)
            ·
              refine ⟨144630816434198490100427585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96420544289465660066951723 144630816434198490100427585)
              ·
                refine ⟨108473112325648867575320689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144630816434198490100427585 108473112325648867575320689)
                ·
                  refine ⟨81354834244236650681490517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108473112325648867575320689 81354834244236650681490517)
                  ·
                    refine ⟨953376963799648250173717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81354834244236650681490517 953376963799648250173717)
                    ·
                      rfl

theorem cell23_5570085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_5570085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570085 prefixEnd_5570085 := by exact prefixLift 5570085
  have htrace : WordTrace (prefixWord ++ tailWord_5570085) baseStart_5570085 baseEnd_5570085 := by
    simpa [prefixWord, tailWord_5570085, baseEnd_5570085] using wordTrace_append hprefix tailTrace_5570085
  have hstable : (prefixWord ++ tailWord_5570085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570085).length < 2 ^ (prefixWord ++ tailWord_5570085).sum := by decide
  have hdescent : baseEnd_5570085 < baseStart_5570085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570109 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_5570109 : Nat := 118140960795 + 5570109 * 2 ^ 59
def prefixEnd_5570109 : Nat := 4983230072969 + 3 ^ 40 * 5570109 * 2
def baseEnd_5570109 : Nat := 2860143214934652656621041

theorem tailTrace_5570109 : CollatzResearch.WordTrace tailWord_5570109 prefixEnd_5570109 2860143214934652656621041 := by
  unfold tailWord_5570109
  simp only [CollatzResearch.WordTrace]
  refine ⟨203158565377453866725537381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135439043584969244483691587 203158565377453866725537381)
  ·
    refine ⟨38092231008272600011038259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203158565377453866725537381 38092231008272600011038259)
    ·
      refine ⟨57138346512408900016557389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38092231008272600011038259 57138346512408900016557389)
      ·
        refine ⟨21426879942153337506209021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57138346512408900016557389 21426879942153337506209021)
        ·
          refine ⟨8035079978307501564828383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21426879942153337506209021 8035079978307501564828383)
          ·
            refine ⟨12052619967461252347242575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8035079978307501564828383 12052619967461252347242575)
            ·
              refine ⟨18078929951191878520863863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12052619967461252347242575 18078929951191878520863863)
              ·
                refine ⟨27118394926787817781295795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18078929951191878520863863 27118394926787817781295795)
                ·
                  refine ⟨40677592390181726671943693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27118394926787817781295795 40677592390181726671943693)
                  ·
                    refine ⟨15254097146318147501978885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40677592390181726671943693 15254097146318147501978885)
                    ·
                      refine ⟨2860143214934652656621041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15254097146318147501978885 2860143214934652656621041)
                      ·
                        rfl

theorem cell23_5570109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_5570109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570109 prefixEnd_5570109 := by exact prefixLift 5570109
  have htrace : WordTrace (prefixWord ++ tailWord_5570109) baseStart_5570109 baseEnd_5570109 := by
    simpa [prefixWord, tailWord_5570109, baseEnd_5570109] using wordTrace_append hprefix tailTrace_5570109
  have hstable : (prefixWord ++ tailWord_5570109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570109).length < 2 ^ (prefixWord ++ tailWord_5570109).sum := by decide
  have hdescent : baseEnd_5570109 < baseStart_5570109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570132 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 8]
def baseStart_5570132 : Nat := 118140960795 + 5570132 * 2 ^ 59
def prefixEnd_5570132 : Nat := 4983230072969 + 3 ^ 40 * 5570132 * 2
def baseEnd_5570132 : Nat := 317795002776634007403715

theorem tailTrace_5570132 : CollatzResearch.WordTrace tailWord_5570132 prefixEnd_5570132 317795002776634007403715 := by
  unfold tailWord_5570132
  simp only [CollatzResearch.WordTrace]
  refine ⟨101579702128185270826812325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135439602837580361102416433 101579702128185270826812325)
  ·
    refine ⟨19046194149034738280027311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101579702128185270826812325 19046194149034738280027311)
    ·
      refine ⟨28569291223552107420040967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19046194149034738280027311 28569291223552107420040967)
      ·
        refine ⟨42853936835328161130061451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28569291223552107420040967 42853936835328161130061451)
        ·
          refine ⟨64280905252992241695092177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42853936835328161130061451 64280905252992241695092177)
          ·
            refine ⟨48210678939744181271319133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64280905252992241695092177 48210678939744181271319133)
            ·
              refine ⟨18079004602404067976744675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48210678939744181271319133 18079004602404067976744675)
              ·
                refine ⟨27118506903606101965117013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18079004602404067976744675 27118506903606101965117013)
                ·
                  refine ⟨317795002776634007403715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27118506903606101965117013 317795002776634007403715)
                  ·
                    rfl

theorem cell23_5570132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_5570132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570132 prefixEnd_5570132 := by exact prefixLift 5570132
  have htrace : WordTrace (prefixWord ++ tailWord_5570132) baseStart_5570132 baseEnd_5570132 := by
    simpa [prefixWord, tailWord_5570132, baseEnd_5570132] using wordTrace_append hprefix tailTrace_5570132
  have hstable : (prefixWord ++ tailWord_5570132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570132).length < 2 ^ (prefixWord ++ tailWord_5570132).sum := by decide
  have hdescent : baseEnd_5570132 < baseStart_5570132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570169 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 1, 5, 2]
def baseStart_5570169 : Nat := 118140960795 + 5570169 * 2 ^ 59
def prefixEnd_5570169 : Nat := 4983230072969 + 3 ^ 40 * 5570169 * 2
def baseEnd_5570169 : Nat := 2860174023773922421870765

theorem tailTrace_5570169 : CollatzResearch.WordTrace tailWord_5570169 prefixEnd_5570169 2860174023773922421870765 := by
  unfold tailWord_5570169
  simp only [CollatzResearch.WordTrace]
  refine ⟨203160753757236496972721561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135440502504824331315147707 203160753757236496972721561)
  ·
    refine ⟨152370565317927372729541171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203160753757236496972721561 152370565317927372729541171)
    ·
      refine ⟨228555847976891059094311757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152370565317927372729541171 228555847976891059094311757)
      ·
        refine ⟨85708442991334147160366909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228555847976891059094311757 85708442991334147160366909)
        ·
          refine ⟨32140666121750305185137591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85708442991334147160366909 32140666121750305185137591)
          ·
            refine ⟨48210999182625457777706387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32140666121750305185137591 48210999182625457777706387)
            ·
              refine ⟨72316498773938186666559581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48210999182625457777706387 72316498773938186666559581)
              ·
                refine ⟨27118687040226819999959843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72316498773938186666559581 27118687040226819999959843)
                ·
                  refine ⟨40678030560340229999939765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27118687040226819999959843 40678030560340229999939765)
                  ·
                    refine ⟨3813565365031896562494353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40678030560340229999939765 3813565365031896562494353)
                    ·
                      refine ⟨2860174023773922421870765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813565365031896562494353 2860174023773922421870765)
                      ·
                        rfl

theorem cell23_5570169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_5570169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570169 prefixEnd_5570169 := by exact prefixLift 5570169
  have htrace : WordTrace (prefixWord ++ tailWord_5570169) baseStart_5570169 baseEnd_5570169 := by
    simpa [prefixWord, tailWord_5570169, baseEnd_5570169] using wordTrace_append hprefix tailTrace_5570169
  have hstable : (prefixWord ++ tailWord_5570169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570169).length < 2 ^ (prefixWord ++ tailWord_5570169).sum := by decide
  have hdescent : baseEnd_5570169 < baseStart_5570169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570186 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_5570186 : Nat := 118140960795 + 5570186 * 2 ^ 59
def prefixEnd_5570186 : Nat := 4983230072969 + 3 ^ 40 * 5570186 * 2
def baseEnd_5570186 : Nat := 2860182752945048855358187

theorem tailTrace_5570186 : CollatzResearch.WordTrace tailWord_5570186 prefixEnd_5570186 2860182752945048855358187 := by
  unfold tailWord_5570186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50790343449543727219022603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135440915865449939250726941 50790343449543727219022603)
  ·
    refine ⟨76185515174315590828533905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50790343449543727219022603 76185515174315590828533905)
    ·
      refine ⟨57139136380736693121400429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76185515174315590828533905 57139136380736693121400429)
      ·
        refine ⟨21427176142776259920525161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57139136380736693121400429 21427176142776259920525161)
        ·
          refine ⟨16070382107082194940393871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21427176142776259920525161 16070382107082194940393871)
          ·
            refine ⟨24105573160623292410590807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16070382107082194940393871 24105573160623292410590807)
            ·
              refine ⟨36158359740934938615886211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24105573160623292410590807 36158359740934938615886211)
              ·
                refine ⟨54237539611402407923829317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36158359740934938615886211 54237539611402407923829317)
                ·
                  refine ⟨10169538677137951485717997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54237539611402407923829317 10169538677137951485717997)
                  ·
                    refine ⟨3813577003926731807144249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10169538677137951485717997 3813577003926731807144249)
                    ·
                      refine ⟨2860182752945048855358187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813577003926731807144249 2860182752945048855358187)
                      ·
                        rfl

theorem cell23_5570186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_5570186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570186 prefixEnd_5570186 := by exact prefixLift 5570186
  have htrace : WordTrace (prefixWord ++ tailWord_5570186) baseStart_5570186 baseEnd_5570186 := by
    simpa [prefixWord, tailWord_5570186, baseEnd_5570186] using wordTrace_append hprefix tailTrace_5570186
  have hstable : (prefixWord ++ tailWord_5570186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570186).length < 2 ^ (prefixWord ++ tailWord_5570186).sum := by decide
  have hdescent : baseEnd_5570186 < baseStart_5570186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570230 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5570230 : Nat := 118140960795 + 5570230 * 2 ^ 59
def prefixEnd_5570230 : Nat := 4983230072969 + 3 ^ 40 * 5570230 * 2
def baseEnd_5570230 : Nat := 953401782031282227735995

theorem tailTrace_5570230 : CollatzResearch.WordTrace tailWord_5570230 prefixEnd_5570230 953401782031282227735995 := by
  unfold tailWord_5570230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697686163125969024418259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135441985740010336260461429 12697686163125969024418259)
  ·
    refine ⟨19046529244688953536627389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12697686163125969024418259 19046529244688953536627389)
    ·
      refine ⟨7142448466758357576235271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19046529244688953536627389 7142448466758357576235271)
      ·
        refine ⟨10713672700137536364352907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142448466758357576235271 10713672700137536364352907)
        ·
          refine ⟨16070509050206304546529361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713672700137536364352907 16070509050206304546529361)
          ·
            refine ⟨12052881787654728409897021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16070509050206304546529361 12052881787654728409897021)
            ·
              refine ⟨4519830670370523153711383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12052881787654728409897021 4519830670370523153711383)
              ·
                refine ⟨6779746005555784730567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4519830670370523153711383 6779746005555784730567075)
                ·
                  refine ⟨10169619008333677095850613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6779746005555784730567075 10169619008333677095850613)
                  ·
                    refine ⟨953401782031282227735995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10169619008333677095850613 953401782031282227735995)
                    ·
                      rfl

theorem cell23_5570230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5570230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570230 prefixEnd_5570230 := by exact prefixLift 5570230
  have htrace : WordTrace (prefixWord ++ tailWord_5570230) baseStart_5570230 baseEnd_5570230 := by
    simpa [prefixWord, tailWord_5570230, baseEnd_5570230] using wordTrace_append hprefix tailTrace_5570230
  have hstable : (prefixWord ++ tailWord_5570230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570230).length < 2 ^ (prefixWord ++ tailWord_5570230).sum := by decide
  have hdescent : baseEnd_5570230 < baseStart_5570230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570236 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_5570236 : Nat := 118140960795 + 5570236 * 2 ^ 59
def prefixEnd_5570236 : Nat := 4983230072969 + 3 ^ 40 * 5570236 * 2
def baseEnd_5570236 : Nat := 2860208426977773659732957

theorem tailTrace_5570236 : CollatzResearch.WordTrace tailWord_5570236 prefixEnd_5570236 2860208426977773659732957 := by
  unfold tailWord_5570236
  simp only [CollatzResearch.WordTrace]
  refine ⟨101581598723996883707705281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135442131631995844943607041 101581598723996883707705281)
  ·
    refine ⟨76186199042997662780778961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101581598723996883707705281 76186199042997662780778961)
    ·
      refine ⟨57139649282248247085584221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76186199042997662780778961 57139649282248247085584221)
      ·
        refine ⟨21427368480843092657094083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57139649282248247085584221 21427368480843092657094083)
        ·
          refine ⟨32141052721264638985641125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21427368480843092657094083 32141052721264638985641125)
          ·
            refine ⟨6026447385237119809807711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32141052721264638985641125 6026447385237119809807711)
            ·
              refine ⟨9039671077855679714711567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6026447385237119809807711 9039671077855679714711567)
              ·
                refine ⟨13559506616783519572067351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9039671077855679714711567 13559506616783519572067351)
                ·
                  refine ⟨20339259925175279358101027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13559506616783519572067351 20339259925175279358101027)
                  ·
                    refine ⟨30508889887762919037151541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20339259925175279358101027 30508889887762919037151541)
                    ·
                      refine ⟨2860208426977773659732957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30508889887762919037151541 2860208426977773659732957)
                      ·
                        rfl

theorem cell23_5570236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_5570236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570236 prefixEnd_5570236 := by exact prefixLift 5570236
  have htrace : WordTrace (prefixWord ++ tailWord_5570236) baseStart_5570236 baseEnd_5570236 := by
    simpa [prefixWord, tailWord_5570236, baseEnd_5570236] using wordTrace_append hprefix tailTrace_5570236
  have hstable : (prefixWord ++ tailWord_5570236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570236).length < 2 ^ (prefixWord ++ tailWord_5570236).sum := by decide
  have hdescent : baseEnd_5570236 < baseStart_5570236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570253 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5570253 : Nat := 118140960795 + 5570253 * 2 ^ 59
def prefixEnd_5570253 : Nat := 4983230072969 + 3 ^ 40 * 5570253 * 2
def baseEnd_5570253 : Nat := 2860217156148900093220379

theorem tailTrace_5570253 : CollatzResearch.WordTrace tailWord_5570253 prefixEnd_5570253 2860217156148900093220379 := by
  unfold tailWord_5570253
  simp only [CollatzResearch.WordTrace]
  refine ⟨203163817488932179318779413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135442544992621452879186275 203163817488932179318779413)
  ·
    refine ⟨9523303944793695905567785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203163817488932179318779413 9523303944793695905567785)
    ·
      refine ⟨7142477958595271929175839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9523303944793695905567785 7142477958595271929175839)
      ·
        refine ⟨10713716937892907893763759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142477958595271929175839 10713716937892907893763759)
        ·
          refine ⟨16070575406839361840645639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713716937892907893763759 16070575406839361840645639)
          ·
            refine ⟨24105863110259042760968459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16070575406839361840645639 24105863110259042760968459)
            ·
              refine ⟨36158794665388564141452689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24105863110259042760968459 36158794665388564141452689)
              ·
                refine ⟨27119095999041423106089517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36158794665388564141452689 27119095999041423106089517)
                ·
                  refine ⟨10169660999640533664783569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27119095999041423106089517 10169660999640533664783569)
                  ·
                    refine ⟨7627245749730400248587677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10169660999640533664783569 7627245749730400248587677)
                    ·
                      refine ⟨2860217156148900093220379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7627245749730400248587677 2860217156148900093220379)
                      ·
                        rfl

theorem cell23_5570253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5570253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570253 prefixEnd_5570253 := by exact prefixLift 5570253
  have htrace : WordTrace (prefixWord ++ tailWord_5570253) baseStart_5570253 baseEnd_5570253 := by
    simpa [prefixWord, tailWord_5570253, baseEnd_5570253] using wordTrace_append hprefix tailTrace_5570253
  have hstable : (prefixWord ++ tailWord_5570253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570253).length < 2 ^ (prefixWord ++ tailWord_5570253).sum := by decide
  have hdescent : baseEnd_5570253 < baseStart_5570253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570266 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_5570266 : Nat := 118140960795 + 5570266 * 2 ^ 59
def prefixEnd_5570266 : Nat := 4983230072969 + 3 ^ 40 * 5570266 * 2
def baseEnd_5570266 : Nat := 2860223831397408542357819

theorem tailTrace_5570266 : CollatzResearch.WordTrace tailWord_5570266 prefixEnd_5570266 2860223831397408542357819 := by
  unfold tailWord_5570266
  simp only [CollatzResearch.WordTrace]
  refine ⟨50791072909471270634750663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135442861091923388359335101 50791072909471270634750663)
  ·
    refine ⟨76186609364206905952125995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50791072909471270634750663 76186609364206905952125995)
    ·
      refine ⟨114279914046310358928188993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76186609364206905952125995 114279914046310358928188993)
      ·
        refine ⟨85709935534732769196141745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114279914046310358928188993 85709935534732769196141745)
        ·
          refine ⟨64282451651049576897106309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85709935534732769196141745 64282451651049576897106309)
          ·
            refine ⟨12052959684571795668207433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64282451651049576897106309 12052959684571795668207433)
            ·
              refine ⟨9039719763428846751155575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12052959684571795668207433 9039719763428846751155575)
              ·
                refine ⟨13559579645143270126733363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9039719763428846751155575 13559579645143270126733363)
                ·
                  refine ⟨20339369467714905190100045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13559579645143270126733363 20339369467714905190100045)
                  ·
                    refine ⟨7627263550393089446287517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20339369467714905190100045 7627263550393089446287517)
                    ·
                      refine ⟨2860223831397408542357819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7627263550393089446287517 2860223831397408542357819)
                      ·
                        rfl

theorem cell23_5570266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_5570266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570266 prefixEnd_5570266 := by exact prefixLift 5570266
  have htrace : WordTrace (prefixWord ++ tailWord_5570266) baseStart_5570266 baseEnd_5570266 := by
    simpa [prefixWord, tailWord_5570266, baseEnd_5570266] using wordTrace_append hprefix tailTrace_5570266
  have hstable : (prefixWord ++ tailWord_5570266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570266).length < 2 ^ (prefixWord ++ tailWord_5570266).sum := by decide
  have hdescent : baseEnd_5570266 < baseStart_5570266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570276 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_5570276 : Nat := 118140960795 + 5570276 * 2 ^ 59
def prefixEnd_5570276 : Nat := 4983230072969 + 3 ^ 40 * 5570276 * 2
def baseEnd_5570276 : Nat := 2860228966203953503232773

theorem tailTrace_5570276 : CollatzResearch.WordTrace tailWord_5570276 prefixEnd_5570276 2860228966203953503232773 := by
  unfold tailWord_5570276
  simp only [CollatzResearch.WordTrace]
  refine ⟨101582328183924427123433341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135443104245232569497911121 101582328183924427123433341)
  ·
    refine ⟨38093373068971660171287503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101582328183924427123433341 38093373068971660171287503)
    ·
      refine ⟨57140059603457490256931255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38093373068971660171287503 57140059603457490256931255)
      ·
        refine ⟨85710089405186235385396883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57140059603457490256931255 85710089405186235385396883)
        ·
          refine ⟨128565134107779353078095325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85710089405186235385396883 128565134107779353078095325)
          ·
            refine ⟨48211925290417257404285747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128565134107779353078095325 48211925290417257404285747)
            ·
              refine ⟨72317887935625886106428621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48211925290417257404285747 72317887935625886106428621)
              ·
                refine ⟨27119207975859707289910733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72317887935625886106428621 27119207975859707289910733)
                ·
                  refine ⟨10169702990947390233716525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27119207975859707289910733 10169702990947390233716525)
                  ·
                    refine ⟨3813638621605271337643697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10169702990947390233716525 3813638621605271337643697)
                    ·
                      refine ⟨2860228966203953503232773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813638621605271337643697 2860228966203953503232773)
                      ·
                        rfl

theorem cell23_5570276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_5570276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570276 prefixEnd_5570276 := by exact prefixLift 5570276
  have htrace : WordTrace (prefixWord ++ tailWord_5570276) baseStart_5570276 baseEnd_5570276 := by
    simpa [prefixWord, tailWord_5570276, baseEnd_5570276] using wordTrace_append hprefix tailTrace_5570276
  have hstable : (prefixWord ++ tailWord_5570276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570276).length < 2 ^ (prefixWord ++ tailWord_5570276).sum := by decide
  have hdescent : baseEnd_5570276 < baseStart_5570276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570339 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 3]
def baseStart_5570339 : Nat := 118140960795 + 5570339 * 2 ^ 59
def prefixEnd_5570339 : Nat := 4983230072969 + 3 ^ 40 * 5570339 * 2
def baseEnd_5570339 : Nat := 2860261315485186756744983

theorem tailTrace_5570339 : CollatzResearch.WordTrace tailWord_5570339 prefixEnd_5570339 2860261315485186756744983 := by
  unfold tailWord_5570339
  simp only [CollatzResearch.WordTrace]
  refine ⟨203166954166620616006410071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135444636111080410670940047 203166954166620616006410071)
  ·
    refine ⟨304750431249930924009615107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203166954166620616006410071 304750431249930924009615107)
    ·
      refine ⟨457125646874896386014422661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304750431249930924009615107 457125646874896386014422661)
      ·
        refine ⟨85711058789043072377704249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 457125646874896386014422661 85711058789043072377704249)
        ·
          refine ⟨64283294091782304283278187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85711058789043072377704249 64283294091782304283278187)
          ·
            refine ⟨96424941137673456424917281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64283294091782304283278187 96424941137673456424917281)
            ·
              refine ⟨72318705853255092318687961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96424941137673456424917281 72318705853255092318687961)
              ·
                refine ⟨54239029389941319239015971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72318705853255092318687961 54239029389941319239015971)
                ·
                  refine ⟨81358544084911978858523957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54239029389941319239015971 81358544084911978858523957)
                  ·
                    refine ⟨7627363507960498017986621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81358544084911978858523957 7627363507960498017986621)
                    ·
                      refine ⟨2860261315485186756744983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7627363507960498017986621 2860261315485186756744983)
                      ·
                        rfl

theorem cell23_5570339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_5570339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570339 prefixEnd_5570339 := by exact prefixLift 5570339
  have htrace : WordTrace (prefixWord ++ tailWord_5570339) baseStart_5570339 baseEnd_5570339 := by
    simpa [prefixWord, tailWord_5570339, baseEnd_5570339] using wordTrace_append hprefix tailTrace_5570339
  have hstable : (prefixWord ++ tailWord_5570339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570339).length < 2 ^ (prefixWord ++ tailWord_5570339).sum := by decide
  have hdescent : baseEnd_5570339 < baseStart_5570339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570374 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5570374 : Nat := 118140960795 + 5570374 * 2 ^ 59
def prefixEnd_5570374 : Nat := 4983230072969 + 3 ^ 40 * 5570374 * 2
def baseEnd_5570374 : Nat := 2860279287308094119807323

theorem tailTrace_5570374 : CollatzResearch.WordTrace tailWord_5570374 prefixEnd_5570374 2860279287308094119807323 := by
  unfold tailWord_5570374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349007210046681780747943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135445487147662544655956117 6349007210046681780747943)
  ·
    refine ⟨9523510815070022671121915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6349007210046681780747943 9523510815070022671121915)
    ·
      refine ⟨14285266222605034006682873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9523510815070022671121915 14285266222605034006682873)
      ·
        refine ⟨10713949666953775505012155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14285266222605034006682873 10713949666953775505012155)
        ·
          refine ⟨16070924500430663257518233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713949666953775505012155 16070924500430663257518233)
          ·
            refine ⟨12053193375322997443138675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16070924500430663257518233 12053193375322997443138675)
            ·
              refine ⟨18079790062984496164708013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12053193375322997443138675 18079790062984496164708013)
              ·
                refine ⟨6779921273619186061765505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18079790062984496164708013 6779921273619186061765505)
                ·
                  refine ⟨5084940955214389546324129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6779921273619186061765505 5084940955214389546324129)
                  ·
                    refine ⟨3813705716410792159743097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5084940955214389546324129 3813705716410792159743097)
                    ·
                      refine ⟨2860279287308094119807323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813705716410792159743097 2860279287308094119807323)
                      ·
                        rfl

theorem cell23_5570374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5570374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570374 prefixEnd_5570374 := by exact prefixLift 5570374
  have htrace : WordTrace (prefixWord ++ tailWord_5570374) baseStart_5570374 baseEnd_5570374 := by
    simpa [prefixWord, tailWord_5570374, baseEnd_5570374] using wordTrace_append hprefix tailTrace_5570374
  have hstable : (prefixWord ++ tailWord_5570374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570374).length < 2 ^ (prefixWord ++ tailWord_5570374).sum := by decide
  have hdescent : baseEnd_5570374 < baseStart_5570374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570430 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5570430 : Nat := 118140960795 + 5570430 * 2 ^ 59
def prefixEnd_5570430 : Nat := 4983230072969 + 3 ^ 40 * 5570430 * 2
def baseEnd_5570430 : Nat := 2860308042224745900707065

theorem tailTrace_5570430 : CollatzResearch.WordTrace tailWord_5570430 prefixEnd_5570430 2860308042224745900707065 := by
  unfold tailWord_5570430
  simp only [CollatzResearch.WordTrace]
  refine ⟨25396284151161367318496593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135446848806193959031981829 25396284151161367318496593)
  ·
    refine ⟨19047213113371025488872445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25396284151161367318496593 19047213113371025488872445)
    ·
      refine ⟨7142704917514134558327167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19047213113371025488872445 7142704917514134558327167)
      ·
        refine ⟨10714057376271201837490751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142704917514134558327167 10714057376271201837490751)
        ·
          refine ⟨16071086064406802756236127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10714057376271201837490751 16071086064406802756236127)
          ·
            refine ⟨24106629096610204134354191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16071086064406802756236127 24106629096610204134354191)
            ·
              refine ⟨36159943644915306201531287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24106629096610204134354191 36159943644915306201531287)
              ·
                refine ⟨54239915467372959302296931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36159943644915306201531287 54239915467372959302296931)
                ·
                  refine ⟨81359873201059438953445397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54239915467372959302296931 81359873201059438953445397)
                  ·
                    refine ⟨3813744056299661200942753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81359873201059438953445397 3813744056299661200942753)
                    ·
                      refine ⟨2860308042224745900707065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813744056299661200942753 2860308042224745900707065)
                      ·
                        rfl

theorem cell23_5570430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5570430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570430 prefixEnd_5570430 := by exact prefixLift 5570430
  have htrace : WordTrace (prefixWord ++ tailWord_5570430) baseStart_5570430 baseEnd_5570430 := by
    simpa [prefixWord, tailWord_5570430, baseEnd_5570430] using wordTrace_append hprefix tailTrace_5570430
  have hstable : (prefixWord ++ tailWord_5570430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570430).length < 2 ^ (prefixWord ++ tailWord_5570430).sum := by decide
  have hdescent : baseEnd_5570430 < baseStart_5570430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570436 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 6]
def baseStart_5570436 : Nat := 118140960795 + 5570436 * 2 ^ 59
def prefixEnd_5570436 : Nat := 4983230072969 + 3 ^ 40 * 5570436 * 2
def baseEnd_5570436 : Nat := 317812347012074764136893

theorem tailTrace_5570436 : CollatzResearch.WordTrace tailWord_5570436 prefixEnd_5570436 317812347012074764136893 := by
  unfold tailWord_5570436
  simp only [CollatzResearch.WordTrace]
  refine ⟨101585246023634600786345581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135446994698179467715127441 101585246023634600786345581)
  ·
    refine ⟨38094467258862975294879593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101585246023634600786345581 38094467258862975294879593)
    ·
      refine ⟨28570850444147231471159695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38094467258862975294879593 28570850444147231471159695)
      ·
        refine ⟨42856275666220847206739543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28570850444147231471159695 42856275666220847206739543)
        ·
          refine ⟨64284413499331270810109315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42856275666220847206739543 64284413499331270810109315)
          ·
            refine ⟨96426620248996906215163973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64284413499331270810109315 96426620248996906215163973)
            ·
              refine ⟨18079991296686919915343245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96426620248996906215163973 18079991296686919915343245)
              ·
                refine ⟨6779996736257594968253717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18079991296686919915343245 6779996736257594968253717)
                ·
                  refine ⟨317812347012074764136893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6779996736257594968253717 317812347012074764136893)
                  ·
                    rfl

theorem cell23_5570436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_5570436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570436 prefixEnd_5570436 := by exact prefixLift 5570436
  have htrace : WordTrace (prefixWord ++ tailWord_5570436) baseStart_5570436 baseEnd_5570436 := by
    simpa [prefixWord, tailWord_5570436, baseEnd_5570436] using wordTrace_append hprefix tailTrace_5570436
  have hstable : (prefixWord ++ tailWord_5570436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570436).length < 2 ^ (prefixWord ++ tailWord_5570436).sum := by decide
  have hdescent : baseEnd_5570436 < baseStart_5570436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570450 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5570450 : Nat := 118140960795 + 5570450 * 2 ^ 59
def prefixEnd_5570450 : Nat := 4983230072969 + 3 ^ 40 * 5570450 * 2
def baseEnd_5570450 : Nat := 2860318311837835822456973

theorem tailTrace_5570450 : CollatzResearch.WordTrace tailWord_5570450 prefixEnd_5570450 2860318311837835822456973 := by
  unfold tailWord_5570450
  simp only [CollatzResearch.WordTrace]
  refine ⟨50792750667304620490925201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135447335112812321309133869 50792750667304620490925201)
  ·
    refine ⟨38094563000478465368193901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50792750667304620490925201 38094563000478465368193901)
    ·
      refine ⟨14285461125179424513072713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38094563000478465368193901 14285461125179424513072713)
      ·
        refine ⟨10714095843884568384804535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14285461125179424513072713 10714095843884568384804535)
        ·
          refine ⟨16071143765826852577206803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10714095843884568384804535 16071143765826852577206803)
          ·
            refine ⟨24106715648740278865810205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16071143765826852577206803 24106715648740278865810205)
            ·
              refine ⟨9040018368277604574678827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24106715648740278865810205 9040018368277604574678827)
              ·
                refine ⟨13560027552416406862018241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9040018368277604574678827 13560027552416406862018241)
                ·
                  refine ⟨10170020664312305146513681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13560027552416406862018241 10170020664312305146513681)
                  ·
                    refine ⟨7627515498234228859885261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10170020664312305146513681 7627515498234228859885261)
                    ·
                      refine ⟨2860318311837835822456973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7627515498234228859885261 2860318311837835822456973)
                      ·
                        rfl

theorem cell23_5570450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5570450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570450 prefixEnd_5570450 := by exact prefixLift 5570450
  have htrace : WordTrace (prefixWord ++ tailWord_5570450) baseStart_5570450 baseEnd_5570450 := by
    simpa [prefixWord, tailWord_5570450, baseEnd_5570450] using wordTrace_append hprefix tailTrace_5570450
  have hstable : (prefixWord ++ tailWord_5570450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570450).length < 2 ^ (prefixWord ++ tailWord_5570450).sum := by decide
  have hdescent : baseEnd_5570450 < baseStart_5570450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570570 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_5570570 : Nat := 118140960795 + 5570570 * 2 ^ 59
def prefixEnd_5570570 : Nat := 4983230072969 + 3 ^ 40 * 5570570 * 2
def baseEnd_5570570 : Nat := 2860379929516375352956421

theorem tailTrace_5570570 : CollatzResearch.WordTrace tailWord_5570570 prefixEnd_5570570 2860379929516375352956421 := by
  unfold tailWord_5570570
  simp only [CollatzResearch.WordTrace]
  refine ⟨50793844857195935614517291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135450252952522494972046109 50793844857195935614517291)
  ·
    refine ⟨76190767285793903421775937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50793844857195935614517291 76190767285793903421775937)
    ·
      refine ⟨57143075464345427566331953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76190767285793903421775937 57143075464345427566331953)
      ·
        refine ⟨42857306598259070674748965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57143075464345427566331953 42857306598259070674748965)
        ·
          refine ⟨8035744987173575751515431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42857306598259070674748965 8035744987173575751515431)
          ·
            refine ⟨12053617480760363627273147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8035744987173575751515431 12053617480760363627273147)
            ·
              refine ⟨18080426221140545440909721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12053617480760363627273147 18080426221140545440909721)
              ·
                refine ⟨13560319665855409080682291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18080426221140545440909721 13560319665855409080682291)
                ·
                  refine ⟨20340479498783113621023437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13560319665855409080682291 20340479498783113621023437)
                  ·
                    refine ⟨7627679812043667607883789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20340479498783113621023437 7627679812043667607883789)
                    ·
                      refine ⟨2860379929516375352956421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7627679812043667607883789 2860379929516375352956421)
                      ·
                        rfl

theorem cell23_5570570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_5570570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570570 prefixEnd_5570570 := by exact prefixLift 5570570
  have htrace : WordTrace (prefixWord ++ tailWord_5570570) baseStart_5570570 baseEnd_5570570 := by
    simpa [prefixWord, tailWord_5570570, baseEnd_5570570] using wordTrace_append hprefix tailTrace_5570570
  have hstable : (prefixWord ++ tailWord_5570570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570570).length < 2 ^ (prefixWord ++ tailWord_5570570).sum := by decide
  have hdescent : baseEnd_5570570 < baseStart_5570570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570610 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_5570610 : Nat := 118140960795 + 5570610 * 2 ^ 59
def prefixEnd_5570610 : Nat := 4983230072969 + 3 ^ 40 * 5570610 * 2
def baseEnd_5570610 : Nat := 2860400468742555196456237

theorem tailTrace_5570610 : CollatzResearch.WordTrace tailWord_5570610 prefixEnd_5570610 2860400468742555196456237 := by
  unfold tailWord_5570610
  simp only [CollatzResearch.WordTrace]
  refine ⟨50794209587159707322381321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135451225565759219526350189 50794209587159707322381321)
  ·
    refine ⟨38095657190369780491785991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50794209587159707322381321 38095657190369780491785991)
    ·
      refine ⟨57143485785554670737678987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38095657190369780491785991 57143485785554670737678987)
      ·
        refine ⟨85715228678332006106518481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57143485785554670737678987 85715228678332006106518481)
        ·
          refine ⟨64286421508749004579888861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85715228678332006106518481 64286421508749004579888861)
          ·
            refine ⟨24107408065780876717458323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64286421508749004579888861 24107408065780876717458323)
            ·
              refine ⟨36161112098671315076187485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24107408065780876717458323 36161112098671315076187485)
              ·
                refine ⟨13560417037001743153570307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36161112098671315076187485 13560417037001743153570307)
                ·
                  refine ⟨20340625555502614730355461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13560417037001743153570307 20340625555502614730355461)
                  ·
                    refine ⟨3813867291656740261941649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20340625555502614730355461 3813867291656740261941649)
                    ·
                      refine ⟨2860400468742555196456237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813867291656740261941649 2860400468742555196456237)
                      ·
                        rfl

theorem cell23_5570610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_5570610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570610 prefixEnd_5570610 := by exact prefixLift 5570610
  have htrace : WordTrace (prefixWord ++ tailWord_5570610) baseStart_5570610 baseEnd_5570610 := by
    simpa [prefixWord, tailWord_5570610, baseEnd_5570610] using wordTrace_append hprefix tailTrace_5570610
  have hstable : (prefixWord ++ tailWord_5570610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570610).length < 2 ^ (prefixWord ++ tailWord_5570610).sum := by decide
  have hdescent : baseEnd_5570610 < baseStart_5570610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570630 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5570630 : Nat := 118140960795 + 5570630 * 2 ^ 59
def prefixEnd_5570630 : Nat := 4983230072969 + 3 ^ 40 * 5570630 * 2
def baseEnd_5570630 : Nat := 2860410738355645118206145

theorem tailTrace_5570630 : CollatzResearch.WordTrace tailWord_5570630 prefixEnd_5570630 2860410738355645118206145 := by
  unfold tailWord_5570630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349298994017699147039167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135451711872377581803502229 6349298994017699147039167)
  ·
    refine ⟨9523948491026548720558751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6349298994017699147039167 9523948491026548720558751)
    ·
      refine ⟨14285922736539823080838127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9523948491026548720558751 14285922736539823080838127)
      ·
        refine ⟨21428884104809734621257191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285922736539823080838127 21428884104809734621257191)
        ·
          refine ⟨32143326157214601931885787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21428884104809734621257191 32143326157214601931885787)
          ·
            refine ⟨48214989235821902897828681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32143326157214601931885787 48214989235821902897828681)
            ·
              refine ⟨36161241926866427173371511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48214989235821902897828681 36161241926866427173371511)
              ·
                refine ⟨54241862890299640760057267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36161241926866427173371511 54241862890299640760057267)
                ·
                  refine ⟨81362794335449461140085901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54241862890299640760057267 81362794335449461140085901)
                  ·
                    refine ⟨30511047875793547927532213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81362794335449461140085901 30511047875793547927532213)
                    ·
                      refine ⟨2860410738355645118206145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30511047875793547927532213 2860410738355645118206145)
                      ·
                        rfl

theorem cell23_5570630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5570630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570630 prefixEnd_5570630 := by exact prefixLift 5570630
  have htrace : WordTrace (prefixWord ++ tailWord_5570630) baseStart_5570630 baseEnd_5570630 := by
    simpa [prefixWord, tailWord_5570630, baseEnd_5570630] using wordTrace_append hprefix tailTrace_5570630
  have hstable : (prefixWord ++ tailWord_5570630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570630).length < 2 ^ (prefixWord ++ tailWord_5570630).sum := by decide
  have hdescent : baseEnd_5570630 < baseStart_5570630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570760 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_5570760 : Nat := 118140960795 + 5570760 * 2 ^ 59
def prefixEnd_5570760 : Nat := 4983230072969 + 3 ^ 40 * 5570760 * 2
def baseEnd_5570760 : Nat := 2860477490840729609580547

theorem tailTrace_5570760 : CollatzResearch.WordTrace tailWord_5570760 prefixEnd_5570760 2860477490840729609580547 := by
  unfold tailWord_5570760
  simp only [CollatzResearch.WordTrace]
  refine ⟨101591154649047702453742867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135454872865396936604990489 101591154649047702453742867)
  ·
    refine ⟨152386731973571553680614301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101591154649047702453742867 152386731973571553680614301)
    ·
      refine ⟨57145024490089332630230363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152386731973571553680614301 57145024490089332630230363)
      ·
        refine ⟨85717536735133998945345545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57145024490089332630230363 85717536735133998945345545)
        ·
          refine ⟨64288152551350499209009159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85717536735133998945345545 64288152551350499209009159)
          ·
            refine ⟨96432228827025748813513739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64288152551350499209009159 96432228827025748813513739)
            ·
              refine ⟨144648343240538623220270609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96432228827025748813513739 144648343240538623220270609)
              ·
                refine ⟨108486257430403967415202957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144648343240538623220270609 108486257430403967415202957)
                ·
                  refine ⟨40682346536401487780701109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108486257430403967415202957 40682346536401487780701109)
                  ·
                    refine ⟨3813969987787639479440729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40682346536401487780701109 3813969987787639479440729)
                    ·
                      refine ⟨2860477490840729609580547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813969987787639479440729 2860477490840729609580547)
                      ·
                        rfl

theorem cell23_5570760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_5570760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570760 prefixEnd_5570760 := by exact prefixLift 5570760
  have htrace : WordTrace (prefixWord ++ tailWord_5570760) baseStart_5570760 baseEnd_5570760 := by
    simpa [prefixWord, tailWord_5570760, baseEnd_5570760] using wordTrace_append hprefix tailTrace_5570760
  have hstable : (prefixWord ++ tailWord_5570760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570760).length < 2 ^ (prefixWord ++ tailWord_5570760).sum := by decide
  have hdescent : baseEnd_5570760 < baseStart_5570760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570770 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_5570770 : Nat := 118140960795 + 5570770 * 2 ^ 59
def prefixEnd_5570770 : Nat := 4983230072969 + 3 ^ 40 * 5570770 * 2
def baseEnd_5570770 : Nat := 953494208549091523485167

theorem tailTrace_5570770 : CollatzResearch.WordTrace tailWord_5570770 prefixEnd_5570770 953494208549091523485167 := by
  unfold tailWord_5570770
  simp only [CollatzResearch.WordTrace]
  refine ⟨50795668507014794153837441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135455116018706117743566509 50795668507014794153837441)
  ·
    refine ⟨38096751380261095615378081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50795668507014794153837441 38096751380261095615378081)
    ·
      refine ⟨28572563535195821711533561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38096751380261095615378081 28572563535195821711533561)
      ·
        refine ⟨21429422651396866283650171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28572563535195821711533561 21429422651396866283650171)
        ·
          refine ⟨32144133977095299425475257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21429422651396866283650171 32144133977095299425475257)
          ·
            refine ⟨24108100482821474569106443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32144133977095299425475257 24108100482821474569106443)
            ·
              refine ⟨36162150724232211853659665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24108100482821474569106443 36162150724232211853659665)
              ·
                refine ⟨27121613043174158890244749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36162150724232211853659665 27121613043174158890244749)
                ·
                  refine ⟨10170604891190309583841781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27121613043174158890244749 10170604891190309583841781)
                  ·
                    refine ⟨953494208549091523485167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10170604891190309583841781 953494208549091523485167)
                    ·
                      rfl

theorem cell23_5570770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_5570770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570770 prefixEnd_5570770 := by exact prefixLift 5570770
  have htrace : WordTrace (prefixWord ++ tailWord_5570770) baseStart_5570770 baseEnd_5570770 := by
    simpa [prefixWord, tailWord_5570770, baseEnd_5570770] using wordTrace_append hprefix tailTrace_5570770
  have hstable : (prefixWord ++ tailWord_5570770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570770).length < 2 ^ (prefixWord ++ tailWord_5570770).sum := by decide
  have hdescent : baseEnd_5570770 < baseStart_5570770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570793 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_5570793 : Nat := 118140960795 + 5570793 * 2 ^ 59
def prefixEnd_5570793 : Nat := 4983230072969 + 3 ^ 40 * 5570793 * 2
def baseEnd_5570793 : Nat := 2860494435702327980467895

theorem tailTrace_5570793 : CollatzResearch.WordTrace tailWord_5570793 prefixEnd_5570793 2860494435702327980467895 := by
  unfold tailWord_5570793
  simp only [CollatzResearch.WordTrace]
  refine ⟨203183512906975851543437033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135455675271317234362291355 203183512906975851543437033)
  ·
    refine ⟨152387634680231888657577775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203183512906975851543437033 152387634680231888657577775)
    ·
      refine ⟨228581452020347832986366663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152387634680231888657577775 228581452020347832986366663)
      ·
        refine ⟨342872178030521749479549995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228581452020347832986366663 342872178030521749479549995)
        ·
          refine ⟨514308267045782624219324993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342872178030521749479549995 514308267045782624219324993)
          ·
            refine ⟨385731200284336968164493745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514308267045782624219324993 385731200284336968164493745)
            ·
              refine ⟨289298400213252726123370309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385731200284336968164493745 289298400213252726123370309)
              ·
                refine ⟨54243450039984886148131933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289298400213252726123370309 54243450039984886148131933)
                ·
                  refine ⟨20341293764994332305549475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54243450039984886148131933 20341293764994332305549475)
                  ·
                    refine ⟨30511940647491498458324213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20341293764994332305549475 30511940647491498458324213)
                    ·
                      refine ⟨2860494435702327980467895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30511940647491498458324213 2860494435702327980467895)
                      ·
                        rfl

theorem cell23_5570793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_5570793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570793 prefixEnd_5570793 := by exact prefixLift 5570793
  have htrace : WordTrace (prefixWord ++ tailWord_5570793) baseStart_5570793 baseEnd_5570793 := by
    simpa [prefixWord, tailWord_5570793, baseEnd_5570793] using wordTrace_append hprefix tailTrace_5570793
  have hstable : (prefixWord ++ tailWord_5570793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570793).length < 2 ^ (prefixWord ++ tailWord_5570793).sum := by decide
  have hdescent : baseEnd_5570793 < baseStart_5570793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570824 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_5570824 : Nat := 118140960795 + 5570824 * 2 ^ 59
def prefixEnd_5570824 : Nat := 4983230072969 + 3 ^ 40 * 5570824 * 2
def baseEnd_5570824 : Nat := 2860510353602617359180253

theorem tailTrace_5570824 : CollatzResearch.WordTrace tailWord_5570824 prefixEnd_5570824 2860510353602617359180253 := by
  unfold tailWord_5570824
  simp only [CollatzResearch.WordTrace]
  refine ⟨101592321784931771918907763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135456429046575695891877017 101592321784931771918907763)
  ·
    refine ⟨152388482677397657878361645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101592321784931771918907763 152388482677397657878361645)
    ·
      refine ⟨57145681004024121704385617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152388482677397657878361645 57145681004024121704385617)
      ·
        refine ⟨42859260753018091278289213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57145681004024121704385617 42859260753018091278289213)
        ·
          refine ⟨16072222782381784229358455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42859260753018091278289213 16072222782381784229358455)
          ·
            refine ⟨24108334173572676344037683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16072222782381784229358455 24108334173572676344037683)
            ·
              refine ⟨36162501260359014516056525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24108334173572676344037683 36162501260359014516056525)
              ·
                refine ⟨13560937972634630443521197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36162501260359014516056525 13560937972634630443521197)
                ·
                  refine ⟨5085351739737986416320449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13560937972634630443521197 5085351739737986416320449)
                  ·
                    refine ⟨3814013804803489812240337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5085351739737986416320449 3814013804803489812240337)
                    ·
                      refine ⟨2860510353602617359180253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814013804803489812240337 2860510353602617359180253)
                      ·
                        rfl

theorem cell23_5570824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_5570824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570824 prefixEnd_5570824 := by exact prefixLift 5570824
  have htrace : WordTrace (prefixWord ++ tailWord_5570824) baseStart_5570824 baseEnd_5570824 := by
    simpa [prefixWord, tailWord_5570824, baseEnd_5570824] using wordTrace_append hprefix tailTrace_5570824
  have hstable : (prefixWord ++ tailWord_5570824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570824).length < 2 ^ (prefixWord ++ tailWord_5570824).sum := by decide
  have hdescent : baseEnd_5570824 < baseStart_5570824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570843 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 2, 7]
def baseStart_5570843 : Nat := 118140960795 + 5570843 * 2 ^ 59
def prefixEnd_5570843 : Nat := 4983230072969 + 3 ^ 40 * 5570843 * 2
def baseEnd_5570843 : Nat := 953506703245017594947555

theorem tailTrace_5570843 : CollatzResearch.WordTrace tailWord_5570843 prefixEnd_5570843 953506703245017594947555 := by
  unfold tailWord_5570843
  simp only [CollatzResearch.WordTrace]
  refine ⟨203185336556794710082757183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135456891037863140055171455 203185336556794710082757183)
  ·
    refine ⟨304778004835192065124135775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203185336556794710082757183 304778004835192065124135775)
    ·
      refine ⟨457167007252788097686203663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304778004835192065124135775 457167007252788097686203663)
      ·
        refine ⟨685750510879182146529305495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457167007252788097686203663 685750510879182146529305495)
        ·
          refine ⟨1028625766318773219793958243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685750510879182146529305495 1028625766318773219793958243)
          ·
            refine ⟨1542938649478159829690937365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028625766318773219793958243 1542938649478159829690937365)
            ·
              refine ⟨72325249194288742016762689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1542938649478159829690937365 72325249194288742016762689)
              ·
                refine ⟨54243936895716556512572017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72325249194288742016762689 54243936895716556512572017)
                ·
                  refine ⟨40682952671787417384429013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54243936895716556512572017 40682952671787417384429013)
                  ·
                    refine ⟨953506703245017594947555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40682952671787417384429013 953506703245017594947555)
                    ·
                      rfl

theorem cell23_5570843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_5570843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570843 prefixEnd_5570843 := by exact prefixLift 5570843
  have htrace : WordTrace (prefixWord ++ tailWord_5570843) baseStart_5570843 baseEnd_5570843 := by
    simpa [prefixWord, tailWord_5570843, baseEnd_5570843] using wordTrace_append hprefix tailTrace_5570843
  have hstable : (prefixWord ++ tailWord_5570843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570843).length < 2 ^ (prefixWord ++ tailWord_5570843).sum := by decide
  have hdescent : baseEnd_5570843 < baseStart_5570843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570847 : List Nat := [1, 1, 2, 4, 3, 3, 2, 7]
def baseStart_5570847 : Nat := 118140960795 + 5570847 * 2 ^ 59
def prefixEnd_5570847 : Nat := 4983230072969 + 3 ^ 40 * 5570847 * 2
def baseEnd_5570847 : Nat := 105945265320654472933061

theorem tailTrace_5570847 : CollatzResearch.WordTrace tailWord_5570847 prefixEnd_5570847 105945265320654472933061 := by
  unfold tailWord_5570847
  simp only [CollatzResearch.WordTrace]
  refine ⟨203185482448780218765902795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135456988299186812510601863 203185482448780218765902795)
  ·
    refine ⟨304778223673170328148854193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203185482448780218765902795 304778223673170328148854193)
    ·
      refine ⟨228583667754877746111640645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304778223673170328148854193 228583667754877746111640645)
      ·
        refine ⟨42859437704039577395932621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228583667754877746111640645 42859437704039577395932621)
        ·
          refine ⟨16072289139014841523474733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42859437704039577395932621 16072289139014841523474733)
          ·
            refine ⟨6027108427130565571303025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16072289139014841523474733 6027108427130565571303025)
            ·
              refine ⟨4520331320347924178477269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6027108427130565571303025 4520331320347924178477269)
              ·
                refine ⟨105945265320654472933061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4520331320347924178477269 105945265320654472933061)
                ·
                  rfl

theorem cell23_5570847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 7].length) (baseStart_5570847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570847 prefixEnd_5570847 := by exact prefixLift 5570847
  have htrace : WordTrace (prefixWord ++ tailWord_5570847) baseStart_5570847 baseEnd_5570847 := by
    simpa [prefixWord, tailWord_5570847, baseEnd_5570847] using wordTrace_append hprefix tailTrace_5570847
  have hstable : (prefixWord ++ tailWord_5570847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570847).length < 2 ^ (prefixWord ++ tailWord_5570847).sum := by decide
  have hdescent : baseEnd_5570847 < baseStart_5570847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570914 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_5570914 : Nat := 118140960795 + 5570914 * 2 ^ 59
def prefixEnd_5570914 : Nat := 4983230072969 + 3 ^ 40 * 5570914 * 2
def baseEnd_5570914 : Nat := 2860556566861522007054839

theorem tailTrace_5570914 : CollatzResearch.WordTrace tailWord_5570914 prefixEnd_5570914 2860556566861522007054839 := by
  unfold tailWord_5570914
  simp only [CollatzResearch.WordTrace]
  refine ⟨50796981534884372302147949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135458617426358326139061197 50796981534884372302147949)
  ·
    refine ⟨19048868075581639613305481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50796981534884372302147949 19048868075581639613305481)
    ·
      refine ⟨14286651056686229709979111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19048868075581639613305481 14286651056686229709979111)
      ·
        refine ⟨21429976585029344564968667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14286651056686229709979111 21429976585029344564968667)
        ·
          refine ⟨32144964877544016847453001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21429976585029344564968667 32144964877544016847453001)
          ·
            refine ⟨24108723658158012635589751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32144964877544016847453001 24108723658158012635589751)
            ·
              refine ⟨36163085487237018953384627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24108723658158012635589751 36163085487237018953384627)
              ·
                refine ⟨54244628230855528430076941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36163085487237018953384627 54244628230855528430076941)
                ·
                  refine ⟨20341735586570823161278853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54244628230855528430076941 20341735586570823161278853)
                  ·
                    refine ⟨3814075422482029342739785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20341735586570823161278853 3814075422482029342739785)
                    ·
                      refine ⟨2860556566861522007054839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814075422482029342739785 2860556566861522007054839)
                      ·
                        rfl

theorem cell23_5570914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_5570914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570914 prefixEnd_5570914 := by exact prefixLift 5570914
  have htrace : WordTrace (prefixWord ++ tailWord_5570914) baseStart_5570914 baseEnd_5570914 := by
    simpa [prefixWord, tailWord_5570914, baseEnd_5570914] using wordTrace_append hprefix tailTrace_5570914
  have hstable : (prefixWord ++ tailWord_5570914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570914).length < 2 ^ (prefixWord ++ tailWord_5570914).sum := by decide
  have hdescent : baseEnd_5570914 < baseStart_5570914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570954 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 7]
def baseStart_5570954 : Nat := 118140960795 + 5570954 * 2 ^ 59
def prefixEnd_5570954 : Nat := 4983230072969 + 3 ^ 40 * 5570954 * 2
def baseEnd_5570954 : Nat := 317841900676411316728295

theorem tailTrace_5570954 : CollatzResearch.WordTrace tailWord_5570954 prefixEnd_5570954 317841900676411316728295 := by
  unfold tailWord_5570954
  simp only [CollatzResearch.WordTrace]
  refine ⟨50797346264848144010011979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135459590039595050693365277 50797346264848144010011979)
  ·
    refine ⟨76196019397272216015017969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50797346264848144010011979 76196019397272216015017969)
    ·
      refine ⟨57147014547954162011263477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76196019397272216015017969 57147014547954162011263477)
      ·
        refine ⟨5357532613870702688555951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57147014547954162011263477 5357532613870702688555951)
        ·
          refine ⟨8036298920806054032833927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357532613870702688555951 8036298920806054032833927)
          ·
            refine ⟨12054448381209081049250891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8036298920806054032833927 12054448381209081049250891)
            ·
              refine ⟨18081672571813621573876337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12054448381209081049250891 18081672571813621573876337)
              ·
                refine ⟨13561254428860216180407253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18081672571813621573876337 13561254428860216180407253)
                ·
                  refine ⟨317841900676411316728295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13561254428860216180407253 317841900676411316728295)
                  ·
                    rfl

theorem cell23_5570954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_5570954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570954 prefixEnd_5570954 := by exact prefixLift 5570954
  have htrace : WordTrace (prefixWord ++ tailWord_5570954) baseStart_5570954 baseEnd_5570954 := by
    simpa [prefixWord, tailWord_5570954, baseEnd_5570954] using wordTrace_append hprefix tailTrace_5570954
  have hstable : (prefixWord ++ tailWord_5570954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570954).length < 2 ^ (prefixWord ++ tailWord_5570954).sum := by decide
  have hdescent : baseEnd_5570954 < baseStart_5570954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5570967 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 2, 5]
def baseStart_5570967 : Nat := 118140960795 + 5570967 * 2 ^ 59
def prefixEnd_5570967 : Nat := 4983230072969 + 3 ^ 40 * 5570967 * 2
def baseEnd_5570967 : Nat := 953527927112070099897365

theorem tailTrace_5570967 : CollatzResearch.WordTrace tailWord_5570967 prefixEnd_5570967 953527927112070099897365 := by
  unfold tailWord_5570967
  simp only [CollatzResearch.WordTrace]
  refine ⟨203189859208345479260271155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135459906138896986173514103 203189859208345479260271155)
  ·
    refine ⟨304784788812518218890406733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203189859208345479260271155 304784788812518218890406733)
    ·
      refine ⟨114294295804694332083902525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304784788812518218890406733 114294295804694332083902525)
      ·
        refine ⟨42860360926760374531463447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114294295804694332083902525 42860360926760374531463447)
        ·
          refine ⟨64290541390140561797195171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42860360926760374531463447 64290541390140561797195171)
          ·
            refine ⟨96435812085210842695792757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64290541390140561797195171 96435812085210842695792757)
            ·
              refine ⟨9040857382988516502730571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96435812085210842695792757 9040857382988516502730571)
              ·
                refine ⟨13561286074482774754095857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9040857382988516502730571 13561286074482774754095857)
                ·
                  refine ⟨10170964555862081065571893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13561286074482774754095857 10170964555862081065571893)
                  ·
                    refine ⟨953527927112070099897365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10170964555862081065571893 953527927112070099897365)
                    ·
                      rfl

theorem cell23_5570967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_5570967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5570967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5570967 prefixEnd_5570967 := by exact prefixLift 5570967
  have htrace : WordTrace (prefixWord ++ tailWord_5570967) baseStart_5570967 baseEnd_5570967 := by
    simpa [prefixWord, tailWord_5570967, baseEnd_5570967] using wordTrace_append hprefix tailTrace_5570967
  have hstable : (prefixWord ++ tailWord_5570967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5570967).length < 2 ^ (prefixWord ++ tailWord_5570967).sum := by decide
  have hdescent : baseEnd_5570967 < baseStart_5570967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5570967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571000 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_5571000 : Nat := 118140960795 + 5571000 * 2 ^ 59
def prefixEnd_5571000 : Nat := 4983230072969 + 3 ^ 40 * 5571000 * 2
def baseEnd_5571000 : Nat := 2860600726197808670579443

theorem tailTrace_5571000 : CollatzResearch.WordTrace tailWord_5571000 prefixEnd_5571000 2860600726197808670579443 := by
  unfold tailWord_5571000
  simp only [CollatzResearch.WordTrace]
  refine ⟨101595531408612962948111227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135460708544817283930814969 101595531408612962948111227)
  ·
    refine ⟨152393297112919444422166841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101595531408612962948111227 152393297112919444422166841)
    ·
      refine ⟨114294972834689583316625131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152393297112919444422166841 114294972834689583316625131)
      ·
        refine ⟨171442459252034374974937697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114294972834689583316625131 171442459252034374974937697)
        ·
          refine ⟨128581844439025781231203273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171442459252034374974937697 128581844439025781231203273)
          ·
            refine ⟨96436383329269335923402455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128581844439025781231203273 96436383329269335923402455)
            ·
              refine ⟨144654574993904003885103683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96436383329269335923402455 144654574993904003885103683)
              ·
                refine ⟨216981862490856005827655525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144654574993904003885103683 216981862490856005827655525)
                ·
                  refine ⟨40684099217035501092685411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216981862490856005827655525 40684099217035501092685411)
                  ·
                    refine ⟨61026148825553251639028117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40684099217035501092685411 61026148825553251639028117)
                    ·
                      refine ⟨2860600726197808670579443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61026148825553251639028117 2860600726197808670579443)
                      ·
                        rfl

theorem cell23_5571000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_5571000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571000 prefixEnd_5571000 := by exact prefixLift 5571000
  have htrace : WordTrace (prefixWord ++ tailWord_5571000) baseStart_5571000 baseEnd_5571000 := by
    simpa [prefixWord, tailWord_5571000, baseEnd_5571000] using wordTrace_append hprefix tailTrace_5571000
  have hstable : (prefixWord ++ tailWord_5571000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571000).length < 2 ^ (prefixWord ++ tailWord_5571000).sum := by decide
  have hdescent : baseEnd_5571000 < baseStart_5571000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571048 : List Nat := [2, 1, 4, 1, 1, 4, 3, 2, 1, 4]
def baseStart_5571048 : Nat := 118140960795 + 5571048 * 2 ^ 59
def prefixEnd_5571048 : Nat := 4983230072969 + 3 ^ 40 * 5571048 * 2
def baseEnd_5571048 : Nat := 953541791089741494259741

theorem tailTrace_5571048 : CollatzResearch.WordTrace tailWord_5571048 prefixEnd_5571048 953541791089741494259741 := by
  unfold tailWord_5571048
  simp only [CollatzResearch.WordTrace]
  refine ⟨101596406760526015046984899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135461875680701353395979865 101596406760526015046984899)
  ·
    refine ⟨152394610140789022570477349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101596406760526015046984899 152394610140789022570477349)
    ·
      refine ⟨28573989401397941731964503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152394610140789022570477349 28573989401397941731964503)
      ·
        refine ⟨42860984102096912597946755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28573989401397941731964503 42860984102096912597946755)
        ·
          refine ⟨64291476153145368896920133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42860984102096912597946755 64291476153145368896920133)
          ·
            refine ⟨12054651778714756668172525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64291476153145368896920133 12054651778714756668172525)
            ·
              refine ⟨4520494417018033750564697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12054651778714756668172525 4520494417018033750564697)
              ·
                refine ⟨3390370812763525312923523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4520494417018033750564697 3390370812763525312923523)
                ·
                  refine ⟨5085556219145287969385285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390370812763525312923523 5085556219145287969385285)
                  ·
                    refine ⟨953541791089741494259741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5085556219145287969385285 953541791089741494259741)
                    ·
                      rfl

theorem cell23_5571048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_5571048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571048 prefixEnd_5571048 := by exact prefixLift 5571048
  have htrace : WordTrace (prefixWord ++ tailWord_5571048) baseStart_5571048 baseEnd_5571048 := by
    simpa [prefixWord, tailWord_5571048, baseEnd_5571048] using wordTrace_append hprefix tailTrace_5571048
  have hstable : (prefixWord ++ tailWord_5571048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571048).length < 2 ^ (prefixWord ++ tailWord_5571048).sum := by decide
  have hdescent : baseEnd_5571048 < baseStart_5571048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571057 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 3, 5]
def baseStart_5571057 : Nat := 118140960795 + 5571057 * 2 ^ 59
def prefixEnd_5571057 : Nat := 4983230072969 + 3 ^ 40 * 5571057 * 2
def baseEnd_5571057 : Nat := 953543331531704982522227

theorem tailTrace_5571057 : CollatzResearch.WordTrace tailWord_5571057 prefixEnd_5571057 953543331531704982522227 := by
  unfold tailWord_5571057
  simp only [CollatzResearch.WordTrace]
  refine ⟨203193141778019424631047425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135462094518679616420698283 203193141778019424631047425)
  ·
    refine ⟨152394856333514568473285569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203193141778019424631047425 152394856333514568473285569)
    ·
      refine ⟨114296142250135926354964177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152394856333514568473285569 114296142250135926354964177)
      ·
        refine ⟨85722106687601944766223133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114296142250135926354964177 85722106687601944766223133)
        ·
          refine ⟨32145790007850729287333675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85722106687601944766223133 32145790007850729287333675)
          ·
            refine ⟨48218685011776093931000513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32145790007850729287333675 48218685011776093931000513)
            ·
              refine ⟨36164013758832070448250385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48218685011776093931000513 36164013758832070448250385)
              ·
                refine ⟨27123010319124052836187789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36164013758832070448250385 27123010319124052836187789)
                ·
                  refine ⟨10171128869671519813570421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27123010319124052836187789 10171128869671519813570421)
                  ·
                    refine ⟨953543331531704982522227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10171128869671519813570421 953543331531704982522227)
                    ·
                      rfl

theorem cell23_5571057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_5571057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571057 prefixEnd_5571057 := by exact prefixLift 5571057
  have htrace : WordTrace (prefixWord ++ tailWord_5571057) baseStart_5571057 baseEnd_5571057 := by
    simpa [prefixWord, tailWord_5571057, baseEnd_5571057] using wordTrace_append hprefix tailTrace_5571057
  have hstable : (prefixWord ++ tailWord_5571057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571057).length < 2 ^ (prefixWord ++ tailWord_5571057).sum := by decide
  have hdescent : baseEnd_5571057 < baseStart_5571057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571061 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 6]
def baseStart_5571061 : Nat := 118140960795 + 5571061 * 2 ^ 59
def prefixEnd_5571061 : Nat := 4983230072969 + 3 ^ 40 * 5571061 * 2
def baseEnd_5571061 : Nat := 317848005390859214657407

theorem tailTrace_5571061 : CollatzResearch.WordTrace tailWord_5571061 prefixEnd_5571061 317848005390859214657407 := by
  unfold tailWord_5571061
  simp only [CollatzResearch.WordTrace]
  refine ⟨203193287670004933314193037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135462191780003288876128691 203193287670004933314193037)
  ·
    refine ⟨76197482876251849992822389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203193287670004933314193037 76197482876251849992822389)
    ·
      refine ⟨7143514019648610936827099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76197482876251849992822389 7143514019648610936827099)
      ·
        refine ⟨10715271029472916405240649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143514019648610936827099 10715271029472916405240649)
        ·
          refine ⟨8036453272104687303930487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10715271029472916405240649 8036453272104687303930487)
          ·
            refine ⟨12054679908157030955895731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8036453272104687303930487 12054679908157030955895731)
            ·
              refine ⟨18082019862235546433843597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12054679908157030955895731 18082019862235546433843597)
              ·
                refine ⟨6780757448338329912691349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18082019862235546433843597 6780757448338329912691349)
                ·
                  refine ⟨317848005390859214657407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6780757448338329912691349 317848005390859214657407)
                  ·
                    rfl

theorem cell23_5571061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_5571061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571061 prefixEnd_5571061 := by exact prefixLift 5571061
  have htrace : WordTrace (prefixWord ++ tailWord_5571061) baseStart_5571061 baseEnd_5571061 := by
    simpa [prefixWord, tailWord_5571061, baseEnd_5571061] using wordTrace_append hprefix tailTrace_5571061
  have hstable : (prefixWord ++ tailWord_5571061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571061).length < 2 ^ (prefixWord ++ tailWord_5571061).sum := by decide
  have hdescent : baseEnd_5571061 < baseStart_5571061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571064 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 4, 3, 2]
def baseStart_5571064 : Nat := 118140960795 + 5571064 * 2 ^ 59
def prefixEnd_5571064 : Nat := 4983230072969 + 3 ^ 40 * 5571064 * 2
def baseEnd_5571064 : Nat := 2860633588959696420179149

theorem tailTrace_5571064 : CollatzResearch.WordTrace tailWord_5571064 prefixEnd_5571064 2860633588959696420179149 := by
  unfold tailWord_5571064
  simp only [CollatzResearch.WordTrace]
  refine ⟨101596698544497032413276123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135462264725996043217701497 101596698544497032413276123)
  ·
    refine ⟨152395047816745548619914185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101596698544497032413276123 152395047816745548619914185)
    ·
      refine ⟨114296285862559161464935639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152395047816745548619914185 114296285862559161464935639)
      ·
        refine ⟨171444428793838742197403459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114296285862559161464935639 171444428793838742197403459)
        ·
          refine ⟨257166643190758113296105189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171444428793838742197403459 257166643190758113296105189)
          ·
            refine ⟨48218745598267146243019723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257166643190758113296105189 48218745598267146243019723)
            ·
              refine ⟨72328118397400719364529585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48218745598267146243019723 72328118397400719364529585)
              ·
                refine ⟨54246088798050539523397189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72328118397400719364529585 54246088798050539523397189)
                ·
                  refine ⟨10171141649634476160636973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54246088798050539523397189 10171141649634476160636973)
                  ·
                    refine ⟨3814178118612928560238865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10171141649634476160636973 3814178118612928560238865)
                    ·
                      refine ⟨2860633588959696420179149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814178118612928560238865 2860633588959696420179149)
                      ·
                        rfl

theorem cell23_5571064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_5571064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571064 prefixEnd_5571064 := by exact prefixLift 5571064
  have htrace : WordTrace (prefixWord ++ tailWord_5571064) baseStart_5571064 baseEnd_5571064 := by
    simpa [prefixWord, tailWord_5571064, baseEnd_5571064] using wordTrace_append hprefix tailTrace_5571064
  have hstable : (prefixWord ++ tailWord_5571064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571064).length < 2 ^ (prefixWord ++ tailWord_5571064).sum := by decide
  have hdescent : baseEnd_5571064 < baseStart_5571064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571167 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_5571167 : Nat := 118140960795 + 5571167 * 2 ^ 59
def prefixEnd_5571167 : Nat := 4983230072969 + 3 ^ 40 * 5571167 * 2
def baseEnd_5571167 : Nat := 2860686477467109517191175

theorem tailTrace_5571167 : CollatzResearch.WordTrace tailWord_5571167 prefixEnd_5571167 2860686477467109517191175 := by
  unfold tailWord_5571167
  simp only [CollatzResearch.WordTrace]
  refine ⟨203197153807620913417551755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135464769205080608945034503 203197153807620913417551755)
  ·
    refine ⟨304795730711431370126327633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203197153807620913417551755 304795730711431370126327633)
    ·
      refine ⟨228596798033573527594745725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304795730711431370126327633 228596798033573527594745725)
      ·
        refine ⟨85723799262590072848029647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228596798033573527594745725 85723799262590072848029647)
        ·
          refine ⟨128585698893885109272044471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85723799262590072848029647 128585698893885109272044471)
          ·
            refine ⟨192878548340827663908066707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128585698893885109272044471 192878548340827663908066707)
            ·
              refine ⟨289317822511241495862100061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192878548340827663908066707 289317822511241495862100061)
              ·
                refine ⟨108494183441715560948287523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289317822511241495862100061 108494183441715560948287523)
                ·
                  refine ⟨162741275162573341422431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108494183441715560948287523 162741275162573341422431285)
                  ·
                    refine ⟨15256994546491250758352933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162741275162573341422431285 15256994546491250758352933)
                    ·
                      refine ⟨2860686477467109517191175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15256994546491250758352933 2860686477467109517191175)
                      ·
                        rfl

theorem cell23_5571167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_5571167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571167 prefixEnd_5571167 := by exact prefixLift 5571167
  have htrace : WordTrace (prefixWord ++ tailWord_5571167) baseStart_5571167 baseEnd_5571167 := by
    simpa [prefixWord, tailWord_5571167, baseEnd_5571167] using wordTrace_append hprefix tailTrace_5571167
  have hstable : (prefixWord ++ tailWord_5571167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571167).length < 2 ^ (prefixWord ++ tailWord_5571167).sum := by decide
  have hdescent : baseEnd_5571167 < baseStart_5571167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571201 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_5571201 : Nat := 118140960795 + 5571201 * 2 ^ 59
def prefixEnd_5571201 : Nat := 4983230072969 + 3 ^ 40 * 5571201 * 2
def baseEnd_5571201 : Nat := 2860703935809362384166019

theorem tailTrace_5571201 : CollatzResearch.WordTrace tailWord_5571201 prefixEnd_5571201 2860703935809362384166019 := by
  unfold tailWord_5571201
  simp only [CollatzResearch.WordTrace]
  refine ⟨203198393889497737224289457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135465595926331824816192971 203198393889497737224289457)
  ·
    refine ⟨152398795417123302918217093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203198393889497737224289457 152398795417123302918217093)
    ·
      refine ⟨28574774140710619297165705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152398795417123302918217093 28574774140710619297165705)
      ·
        refine ⟨21431080605532964472874279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28574774140710619297165705 21431080605532964472874279)
        ·
          refine ⟨32146620908299446709311419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21431080605532964472874279 32146620908299446709311419)
          ·
            refine ⟨48219931362449170063967129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32146620908299446709311419 48219931362449170063967129)
            ·
              refine ⟨36164948521836877547975347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48219931362449170063967129 36164948521836877547975347)
              ·
                refine ⟨54247422782755316321963021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36164948521836877547975347 54247422782755316321963021)
                ·
                  refine ⟨20342783543533243620736133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54247422782755316321963021 20342783543533243620736133)
                  ·
                    refine ⟨3814271914412483178888025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20342783543533243620736133 3814271914412483178888025)
                    ·
                      refine ⟨2860703935809362384166019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814271914412483178888025 2860703935809362384166019)
                      ·
                        rfl

theorem cell23_5571201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_5571201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571201 prefixEnd_5571201 := by exact prefixLift 5571201
  have htrace : WordTrace (prefixWord ++ tailWord_5571201) baseStart_5571201 baseEnd_5571201 := by
    simpa [prefixWord, tailWord_5571201, baseEnd_5571201] using wordTrace_append hprefix tailTrace_5571201
  have hstable : (prefixWord ++ tailWord_5571201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571201).length < 2 ^ (prefixWord ++ tailWord_5571201).sum := by decide
  have hdescent : baseEnd_5571201 < baseStart_5571201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571204 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_5571204 : Nat := 118140960795 + 5571204 * 2 ^ 59
def prefixEnd_5571204 : Nat := 4983230072969 + 3 ^ 40 * 5571204 * 2
def baseEnd_5571204 : Nat := 2860705476251325872428505

theorem tailTrace_5571204 : CollatzResearch.WordTrace tailWord_5571204 prefixEnd_5571204 2860705476251325872428505 := by
  unfold tailWord_5571204
  simp only [CollatzResearch.WordTrace]
  refine ⟨101599251654243434368324333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135465668872324579157765777 101599251654243434368324333)
  ·
    refine ⟨38099719370341287888121625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101599251654243434368324333 38099719370341287888121625)
    ·
      refine ⟨28574789527755965916091219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38099719370341287888121625 28574789527755965916091219)
      ·
        refine ⟨42862184291633948874136829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28574789527755965916091219 42862184291633948874136829)
        ·
          refine ⟨16073319109362730827801311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42862184291633948874136829 16073319109362730827801311)
          ·
            refine ⟨24109978664044096241701967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16073319109362730827801311 24109978664044096241701967)
            ·
              refine ⟨36164967996066144362552951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24109978664044096241701967 36164967996066144362552951)
              ·
                refine ⟨54247451994099216543829427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36164967996066144362552951 54247451994099216543829427)
                ·
                  refine ⟨81371177991148824815744141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54247451994099216543829427 81371177991148824815744141)
                  ·
                    refine ⟨30514191746680809305904053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81371177991148824815744141 30514191746680809305904053)
                    ·
                      refine ⟨2860705476251325872428505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30514191746680809305904053 2860705476251325872428505)
                      ·
                        rfl

theorem cell23_5571204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_5571204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571204 prefixEnd_5571204 := by exact prefixLift 5571204
  have htrace : WordTrace (prefixWord ++ tailWord_5571204) baseStart_5571204 baseEnd_5571204 := by
    simpa [prefixWord, tailWord_5571204, baseEnd_5571204] using wordTrace_append hprefix tailTrace_5571204
  have hstable : (prefixWord ++ tailWord_5571204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571204).length < 2 ^ (prefixWord ++ tailWord_5571204).sum := by decide
  have hdescent : baseEnd_5571204 < baseStart_5571204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571239 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5571239 : Nat := 118140960795 + 5571239 * 2 ^ 59
def prefixEnd_5571239 : Nat := 4983230072969 + 3 ^ 40 * 5571239 * 2
def baseEnd_5571239 : Nat := 2860723448074233235490845

theorem tailTrace_5571239 : CollatzResearch.WordTrace tailWord_5571239 prefixEnd_5571239 2860723448074233235490845 := by
  unfold tailWord_5571239
  simp only [CollatzResearch.WordTrace]
  refine ⟨203199779863360069714172771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135466519908906713142781847 203199779863360069714172771)
  ·
    refine ⟨304799669795040104571259157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203199779863360069714172771 304799669795040104571259157)
    ·
      refine ⟨14287484521642504901777773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 304799669795040104571259157 14287484521642504901777773)
      ·
        refine ⟨5357806695615939338166665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14287484521642504901777773 5357806695615939338166665)
        ·
          refine ⟨4018355021711954503624999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5357806695615939338166665 4018355021711954503624999)
          ·
            refine ⟨6027532532567931755437499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018355021711954503624999 6027532532567931755437499)
            ·
              refine ⟨9041298798851897633156249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027532532567931755437499 9041298798851897633156249)
              ·
                refine ⟨6780974099138923224867187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9041298798851897633156249 6780974099138923224867187)
                ·
                  refine ⟨10171461148708384837300781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6780974099138923224867187 10171461148708384837300781)
                  ·
                    refine ⟨3814297930765644313987793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10171461148708384837300781 3814297930765644313987793)
                    ·
                      refine ⟨2860723448074233235490845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814297930765644313987793 2860723448074233235490845)
                      ·
                        rfl

theorem cell23_5571239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5571239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571239 prefixEnd_5571239 := by exact prefixLift 5571239
  have htrace : WordTrace (prefixWord ++ tailWord_5571239) baseStart_5571239 baseEnd_5571239 := by
    simpa [prefixWord, tailWord_5571239, baseEnd_5571239] using wordTrace_append hprefix tailTrace_5571239
  have hstable : (prefixWord ++ tailWord_5571239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571239).length < 2 ^ (prefixWord ++ tailWord_5571239).sum := by decide
  have hdescent : baseEnd_5571239 < baseStart_5571239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571264 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_5571264 : Nat := 118140960795 + 5571264 * 2 ^ 59
def prefixEnd_5571264 : Nat := 4983230072969 + 3 ^ 40 * 5571264 * 2
def baseEnd_5571264 : Nat := 2860736285090595637678229

theorem tailTrace_5571264 : CollatzResearch.WordTrace tailWord_5571264 prefixEnd_5571264 2860736285090595637678229 := by
  unfold tailWord_5571264
  simp only [CollatzResearch.WordTrace]
  refine ⟨101600345844134749491916423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135467127792179665989221897 101600345844134749491916423)
  ·
    refine ⟨152400518766202124237874635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101600345844134749491916423 152400518766202124237874635)
    ·
      refine ⟨228600778149303186356811953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152400518766202124237874635 228600778149303186356811953)
      ·
        refine ⟨171450583611977389767608965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228600778149303186356811953 171450583611977389767608965)
        ·
          refine ⟨32146984427245760581426681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171450583611977389767608965 32146984427245760581426681)
          ·
            refine ⟨24110238320434320436070011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32146984427245760581426681 24110238320434320436070011)
            ·
              refine ⟨36165357480651480654105017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24110238320434320436070011 36165357480651480654105017)
              ·
                refine ⟨27124018110488610490578763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36165357480651480654105017 27124018110488610490578763)
                ·
                  refine ⟨40686027165732915735868145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27124018110488610490578763 40686027165732915735868145)
                  ·
                    refine ⟨30514520374299686801901109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40686027165732915735868145 30514520374299686801901109)
                    ·
                      refine ⟨2860736285090595637678229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30514520374299686801901109 2860736285090595637678229)
                      ·
                        rfl

theorem cell23_5571264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_5571264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571264 prefixEnd_5571264 := by exact prefixLift 5571264
  have htrace : WordTrace (prefixWord ++ tailWord_5571264) baseStart_5571264 baseEnd_5571264 := by
    simpa [prefixWord, tailWord_5571264, baseEnd_5571264] using wordTrace_append hprefix tailTrace_5571264
  have hstable : (prefixWord ++ tailWord_5571264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571264).length < 2 ^ (prefixWord ++ tailWord_5571264).sum := by decide
  have hdescent : baseEnd_5571264 < baseStart_5571264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571301 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_5571301 : Nat := 118140960795 + 5571301 * 2 ^ 59
def prefixEnd_5571301 : Nat := 4983230072969 + 3 ^ 40 * 5571301 * 2
def baseEnd_5571301 : Nat := 953585094624937330971853

theorem tailTrace_5571301 : CollatzResearch.WordTrace tailWord_5571301 prefixEnd_5571301 953585094624937330971853 := by
  unfold tailWord_5571301
  simp only [CollatzResearch.WordTrace]
  refine ⟨203202041189135454302929757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135468027459423636201953171 203202041189135454302929757)
  ·
    refine ⟨76200765445925795363598659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203202041189135454302929757 76200765445925795363598659)
    ·
      refine ⟨114301148168888693045397989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76200765445925795363598659 114301148168888693045397989)
      ·
        refine ⟨21431465281666629946012123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114301148168888693045397989 21431465281666629946012123)
        ·
          refine ⟨32147197922499944919018185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21431465281666629946012123 32147197922499944919018185)
          ·
            refine ⟨24110398441874958689263639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32147197922499944919018185 24110398441874958689263639)
            ·
              refine ⟨36165597662812438033895459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24110398441874958689263639 36165597662812438033895459)
              ·
                refine ⟨54248396494218657050843189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36165597662812438033895459 54248396494218657050843189)
                ·
                  refine ⟨5085787171332999098516549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54248396494218657050843189 5085787171332999098516549)
                  ·
                    refine ⟨953585094624937330971853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5085787171332999098516549 953585094624937330971853)
                    ·
                      rfl

theorem cell23_5571301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_5571301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571301 prefixEnd_5571301 := by exact prefixLift 5571301
  have htrace : WordTrace (prefixWord ++ tailWord_5571301) baseStart_5571301 baseEnd_5571301 := by
    simpa [prefixWord, tailWord_5571301, baseEnd_5571301] using wordTrace_append hprefix tailTrace_5571301
  have hstable : (prefixWord ++ tailWord_5571301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571301).length < 2 ^ (prefixWord ++ tailWord_5571301).sum := by decide
  have hdescent : baseEnd_5571301 < baseStart_5571301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571311 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 3]
def baseStart_5571311 : Nat := 118140960795 + 5571311 * 2 ^ 59
def prefixEnd_5571311 : Nat := 4983230072969 + 3 ^ 40 * 5571311 * 2
def baseEnd_5571311 : Nat := 2860760418681356953790513

theorem tailTrace_5571311 : CollatzResearch.WordTrace tailWord_5571311 prefixEnd_5571311 2860760418681356953790513 := by
  unfold tailWord_5571311
  simp only [CollatzResearch.WordTrace]
  refine ⟨203202405919099226010793787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135468270612732817340529191 203202405919099226010793787)
  ·
    refine ⟨304803608878648839016190681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203202405919099226010793787 304803608878648839016190681)
    ·
      refine ⟨228602706658986629262143011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304803608878648839016190681 228602706658986629262143011)
      ·
        refine ⟨342904059988479943893214517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228602706658986629262143011 342904059988479943893214517)
        ·
          refine ⟨32147255623919994739988861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 342904059988479943893214517 32147255623919994739988861)
          ·
            refine ⟨12055220858969998027495823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32147255623919994739988861 12055220858969998027495823)
            ·
              refine ⟨18082831288454997041243735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12055220858969998027495823 18082831288454997041243735)
              ·
                refine ⟨27124246932682495561865603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18082831288454997041243735 27124246932682495561865603)
                ·
                  refine ⟨40686370399023743342798405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27124246932682495561865603 40686370399023743342798405)
                  ·
                    refine ⟨7628694449816951876774701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40686370399023743342798405 7628694449816951876774701)
                    ·
                      refine ⟨2860760418681356953790513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7628694449816951876774701 2860760418681356953790513)
                      ·
                        rfl

theorem cell23_5571311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_5571311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571311 prefixEnd_5571311 := by exact prefixLift 5571311
  have htrace : WordTrace (prefixWord ++ tailWord_5571311) baseStart_5571311 baseEnd_5571311 := by
    simpa [prefixWord, tailWord_5571311, baseEnd_5571311] using wordTrace_append hprefix tailTrace_5571311
  have hstable : (prefixWord ++ tailWord_5571311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571311).length < 2 ^ (prefixWord ++ tailWord_5571311).sum := by decide
  have hdescent : baseEnd_5571311 < baseStart_5571311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571335 : List Nat := [1, 1, 4, 4, 1, 1, 2, 4, 1, 4]
def baseStart_5571335 : Nat := 118140960795 + 5571335 * 2 ^ 59
def prefixEnd_5571335 : Nat := 4983230072969 + 3 ^ 40 * 5571335 * 2
def baseEnd_5571335 : Nat := 953590914072354953296801

theorem tailTrace_5571335 : CollatzResearch.WordTrace tailWord_5571335 prefixEnd_5571335 953590914072354953296801 := by
  unfold tailWord_5571335
  simp only [CollatzResearch.WordTrace]
  refine ⟨203203281271012278109667459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135468854180674852073111639 203203281271012278109667459)
  ·
    refine ⟨304804921906518417164501189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203203281271012278109667459 304804921906518417164501189)
    ·
      refine ⟨57150922857472203218343973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304804921906518417164501189 57150922857472203218343973)
      ·
        refine ⟨10715798035776038103439495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57150922857472203218343973 10715798035776038103439495)
        ·
          refine ⟨16073697053664057155159243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10715798035776038103439495 16073697053664057155159243)
          ·
            refine ⟨24110545580496085732738865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16073697053664057155159243 24110545580496085732738865)
            ·
              refine ⟨18082909185372064299554149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24110545580496085732738865 18082909185372064299554149)
              ·
                refine ⟨3390545472257262056166403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18082909185372064299554149 3390545472257262056166403)
                ·
                  refine ⟨5085818208385893084249605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390545472257262056166403 5085818208385893084249605)
                  ·
                    refine ⟨953590914072354953296801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5085818208385893084249605 953590914072354953296801)
                    ·
                      rfl

theorem cell23_5571335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_5571335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571335 prefixEnd_5571335 := by exact prefixLift 5571335
  have htrace : WordTrace (prefixWord ++ tailWord_5571335) baseStart_5571335 baseEnd_5571335 := by
    simpa [prefixWord, tailWord_5571335, baseEnd_5571335] using wordTrace_append hprefix tailTrace_5571335
  have hstable : (prefixWord ++ tailWord_5571335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571335).length < 2 ^ (prefixWord ++ tailWord_5571335).sum := by decide
  have hdescent : baseEnd_5571335 < baseStart_5571335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571368 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_5571368 : Nat := 118140960795 + 5571368 * 2 ^ 59
def prefixEnd_5571368 : Nat := 4983230072969 + 3 ^ 40 * 5571368 * 2
def baseEnd_5571368 : Nat := 2860789687078663230777751

theorem tailTrace_5571368 : CollatzResearch.WordTrace tailWord_5571368 prefixEnd_5571368 2860789687078663230777751 := by
  unfold tailWord_5571368
  simp only [CollatzResearch.WordTrace]
  refine ⟨101602242439946362372809379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135469656586595149830412505 101602242439946362372809379)
  ·
    refine ⟨152403363659919543559214069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101602242439946362372809379 152403363659919543559214069)
    ·
      refine ⟨14287815343117457208676319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152403363659919543559214069 14287815343117457208676319)
      ·
        refine ⟨21431723014676185813014479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14287815343117457208676319 21431723014676185813014479)
        ·
          refine ⟨32147584522014278719521719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21431723014676185813014479 32147584522014278719521719)
          ·
            refine ⟨48221376783021418079282579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32147584522014278719521719 48221376783021418079282579)
            ·
              refine ⟨72332065174532127118923869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48221376783021418079282579 72332065174532127118923869)
              ·
                refine ⟨27124524440449547669596451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72332065174532127118923869 27124524440449547669596451)
                ·
                  refine ⟨40686786660674321504394677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27124524440449547669596451 40686786660674321504394677)
                  ·
                    refine ⟨3814386249438217641037001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40686786660674321504394677 3814386249438217641037001)
                    ·
                      refine ⟨2860789687078663230777751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814386249438217641037001 2860789687078663230777751)
                      ·
                        rfl

theorem cell23_5571368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_5571368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571368 prefixEnd_5571368 := by exact prefixLift 5571368
  have htrace : WordTrace (prefixWord ++ tailWord_5571368) baseStart_5571368 baseEnd_5571368 := by
    simpa [prefixWord, tailWord_5571368, baseEnd_5571368] using wordTrace_append hprefix tailTrace_5571368
  have hstable : (prefixWord ++ tailWord_5571368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571368).length < 2 ^ (prefixWord ++ tailWord_5571368).sum := by decide
  have hdescent : baseEnd_5571368 < baseStart_5571368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571401 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_5571401 : Nat := 118140960795 + 5571401 * 2 ^ 59
def prefixEnd_5571401 : Nat := 4983230072969 + 3 ^ 40 * 5571401 * 2
def baseEnd_5571401 : Nat := 2860806631940261601665099

theorem tailTrace_5571401 : CollatzResearch.WordTrace tailWord_5571401 prefixEnd_5571401 2860806631940261601665099 := by
  unfold tailWord_5571401
  simp only [CollatzResearch.WordTrace]
  refine ⟨203205688488773171381570057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135470458992515447587713371 203205688488773171381570057)
  ·
    refine ⟨152404266366579878536177543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203205688488773171381570057 152404266366579878536177543)
    ·
      refine ⟨228606399549869817804266315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152404266366579878536177543 228606399549869817804266315)
      ·
        refine ⟨342909599324804726706399473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228606399549869817804266315 342909599324804726706399473)
        ·
          refine ⟨257182199493603545029799605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342909599324804726706399473 257182199493603545029799605)
          ·
            refine ⟨24110831202525332346543713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 257182199493603545029799605 24110831202525332346543713)
            ·
              refine ⟨18083123401893999259907785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24110831202525332346543713 18083123401893999259907785)
              ·
                refine ⟨13562342551420499444930839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18083123401893999259907785 13562342551420499444930839)
                ·
                  refine ⟨20343513827130749167396259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13562342551420499444930839 20343513827130749167396259)
                  ·
                    refine ⟨30515270740696123751094389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20343513827130749167396259 30515270740696123751094389)
                    ·
                      refine ⟨2860806631940261601665099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30515270740696123751094389 2860806631940261601665099)
                      ·
                        rfl

theorem cell23_5571401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_5571401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571401 prefixEnd_5571401 := by exact prefixLift 5571401
  have htrace : WordTrace (prefixWord ++ tailWord_5571401) baseStart_5571401 baseEnd_5571401 := by
    simpa [prefixWord, tailWord_5571401, baseEnd_5571401] using wordTrace_append hprefix tailTrace_5571401
  have hstable : (prefixWord ++ tailWord_5571401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571401).length < 2 ^ (prefixWord ++ tailWord_5571401).sum := by decide
  have hdescent : baseEnd_5571401 < baseStart_5571401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571412 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_5571412 : Nat := 118140960795 + 5571412 * 2 ^ 59
def prefixEnd_5571412 : Nat := 4983230072969 + 3 ^ 40 * 5571412 * 2
def baseEnd_5571412 : Nat := 953604093409153686209183

theorem tailTrace_5571412 : CollatzResearch.WordTrace tailWord_5571412 prefixEnd_5571412 953604093409153686209183 := by
  unfold tailWord_5571412
  simp only [CollatzResearch.WordTrace]
  refine ⟨101603044845866660130110245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135470726461155546840146993 101603044845866660130110245)
  ·
    refine ⟨19050570908599998774395671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101603044845866660130110245 19050570908599998774395671)
    ·
      refine ⟨28575856362899998161593507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050570908599998774395671 28575856362899998161593507)
      ·
        refine ⟨42863784544349997242390261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28575856362899998161593507 42863784544349997242390261)
        ·
          refine ⟨4018479801032812241474087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42863784544349997242390261 4018479801032812241474087)
          ·
            refine ⟨6027719701549218362211131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018479801032812241474087 6027719701549218362211131)
            ·
              refine ⟨9041579552323827543316697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027719701549218362211131 9041579552323827543316697)
              ·
                refine ⟨6781184664242870657487523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9041579552323827543316697 6781184664242870657487523)
                ·
                  refine ⟨10171776996364305986231285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6781184664242870657487523 10171776996364305986231285)
                  ·
                    refine ⟨953604093409153686209183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10171776996364305986231285 953604093409153686209183)
                    ·
                      rfl

theorem cell23_5571412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_5571412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571412 prefixEnd_5571412 := by exact prefixLift 5571412
  have htrace : WordTrace (prefixWord ++ tailWord_5571412) baseStart_5571412 baseEnd_5571412 := by
    simpa [prefixWord, tailWord_5571412, baseEnd_5571412] using wordTrace_append hprefix tailTrace_5571412
  have hstable : (prefixWord ++ tailWord_5571412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571412).length < 2 ^ (prefixWord ++ tailWord_5571412).sum := by decide
  have hdescent : baseEnd_5571412 < baseStart_5571412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571415 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_5571415 : Nat := 118140960795 + 5571415 * 2 ^ 59
def prefixEnd_5571415 : Nat := 4983230072969 + 3 ^ 40 * 5571415 * 2
def baseEnd_5571415 : Nat := 2860813820669424546890035

theorem tailTrace_5571415 : CollatzResearch.WordTrace tailWord_5571415 prefixEnd_5571415 2860813820669424546890035 := by
  unfold tailWord_5571415
  simp only [CollatzResearch.WordTrace]
  refine ⟨203206199110722451772579699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135470799407148301181719799 203206199110722451772579699)
  ·
    refine ⟨304809298666083677658869549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203206199110722451772579699 304809298666083677658869549)
    ·
      refine ⟨114303486999781379122076081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304809298666083677658869549 114303486999781379122076081)
      ·
        refine ⟨85727615249836034341557061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114303486999781379122076081 85727615249836034341557061)
        ·
          refine ⟨16073927859344256439041949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85727615249836034341557061 16073927859344256439041949)
          ·
            refine ⟨6027722947254096164640731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16073927859344256439041949 6027722947254096164640731)
            ·
              refine ⟨9041584420881144246961097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027722947254096164640731 9041584420881144246961097)
              ·
                refine ⟨6781188315660858185220823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9041584420881144246961097 6781188315660858185220823)
                ·
                  refine ⟨10171782473491287277831235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6781188315660858185220823 10171782473491287277831235)
                  ·
                    refine ⟨15257673710236930916746853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10171782473491287277831235 15257673710236930916746853)
                    ·
                      refine ⟨2860813820669424546890035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15257673710236930916746853 2860813820669424546890035)
                      ·
                        rfl

theorem cell23_5571415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_5571415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571415 prefixEnd_5571415 := by exact prefixLift 5571415
  have htrace : WordTrace (prefixWord ++ tailWord_5571415) baseStart_5571415 baseEnd_5571415 := by
    simpa [prefixWord, tailWord_5571415, baseEnd_5571415] using wordTrace_append hprefix tailTrace_5571415
  have hstable : (prefixWord ++ tailWord_5571415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571415).length < 2 ^ (prefixWord ++ tailWord_5571415).sum := by decide
  have hdescent : baseEnd_5571415 < baseStart_5571415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571418 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_5571418 : Nat := 118140960795 + 5571418 * 2 ^ 59
def prefixEnd_5571418 : Nat := 4983230072969 + 3 ^ 40 * 5571418 * 2
def baseEnd_5571418 : Nat := 2860815361111388035152521

theorem tailTrace_5571418 : CollatzResearch.WordTrace tailWord_5571418 prefixEnd_5571418 2860815361111388035152521 := by
  unfold tailWord_5571418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50801577132427895821234727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135470872353141055523292605 50801577132427895821234727)
  ·
    refine ⟨76202365698641843731852091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50801577132427895821234727 76202365698641843731852091)
    ·
      refine ⟨114303548547962765597778137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76202365698641843731852091 114303548547962765597778137)
      ·
        refine ⟨85727661410972074198333603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114303548547962765597778137 85727661410972074198333603)
        ·
          refine ⟨128591492116458111297500405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85727661410972074198333603 128591492116458111297500405)
          ·
            refine ⟨12055452385917947934140663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128591492116458111297500405 12055452385917947934140663)
            ·
              refine ⟨18083178578876921901210995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12055452385917947934140663 18083178578876921901210995)
              ·
                refine ⟨27124767868315382851816493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18083178578876921901210995 27124767868315382851816493)
                ·
                  refine ⟨10171787950618268569431185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27124767868315382851816493 10171787950618268569431185)
                  ·
                    refine ⟨7628840962963701427073389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10171787950618268569431185 7628840962963701427073389)
                    ·
                      refine ⟨2860815361111388035152521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7628840962963701427073389 2860815361111388035152521)
                      ·
                        rfl

theorem cell23_5571418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_5571418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571418 prefixEnd_5571418 := by exact prefixLift 5571418
  have htrace : WordTrace (prefixWord ++ tailWord_5571418) baseStart_5571418 baseEnd_5571418 := by
    simpa [prefixWord, tailWord_5571418, baseEnd_5571418] using wordTrace_append hprefix tailTrace_5571418
  have hstable : (prefixWord ++ tailWord_5571418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571418).length < 2 ^ (prefixWord ++ tailWord_5571418).sum := by decide
  have hdescent : baseEnd_5571418 < baseStart_5571418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571428 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_5571428 : Nat := 118140960795 + 5571428 * 2 ^ 59
def prefixEnd_5571428 : Nat := 4983230072969 + 3 ^ 40 * 5571428 * 2
def baseEnd_5571428 : Nat := 2860820495917932996027475

theorem tailTrace_5571428 : CollatzResearch.WordTrace tailWord_5571428 prefixEnd_5571428 2860820495917932996027475 := by
  unfold tailWord_5571428
  simp only [CollatzResearch.WordTrace]
  refine ⟨101603336629837677496401469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135471115506450236661868625 101603336629837677496401469)
  ·
    refine ⟨38101251236189129061150551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101603336629837677496401469 38101251236189129061150551)
    ·
      refine ⟨57151876854283693591725827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38101251236189129061150551 57151876854283693591725827)
      ·
        refine ⟨85727815281425540387588741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57151876854283693591725827 85727815281425540387588741)
        ·
          refine ⟨16073965365267288822672889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85727815281425540387588741 16073965365267288822672889)
          ·
            refine ⟨12055474023950466617004667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16073965365267288822672889 12055474023950466617004667)
            ·
              refine ⟨18083211035925699925507001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12055474023950466617004667 18083211035925699925507001)
              ·
                refine ⟨13562408276944274944130251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18083211035925699925507001 13562408276944274944130251)
                ·
                  refine ⟨20343612415416412416195377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13562408276944274944130251 20343612415416412416195377)
                  ·
                    refine ⟨15257709311562309312146533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20343612415416412416195377 15257709311562309312146533)
                    ·
                      refine ⟨2860820495917932996027475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15257709311562309312146533 2860820495917932996027475)
                      ·
                        rfl

theorem cell23_5571428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_5571428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571428 prefixEnd_5571428 := by exact prefixLift 5571428
  have htrace : WordTrace (prefixWord ++ tailWord_5571428) baseStart_5571428 baseEnd_5571428 := by
    simpa [prefixWord, tailWord_5571428, baseEnd_5571428] using wordTrace_append hprefix tailTrace_5571428
  have hstable : (prefixWord ++ tailWord_5571428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571428).length < 2 ^ (prefixWord ++ tailWord_5571428).sum := by decide
  have hdescent : baseEnd_5571428 < baseStart_5571428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571438 : List Nat := [4, 1, 2, 3, 3, 10]
def baseStart_5571438 : Nat := 118140960795 + 5571438 * 2 ^ 59
def prefixEnd_5571438 : Nat := 4983230072969 + 3 ^ 40 * 5571438 * 2
def baseEnd_5571438 : Nat := 11772944982405259081903

theorem tailTrace_5571438 : CollatzResearch.WordTrace tailWord_5571438 prefixEnd_5571438 11772944982405259081903 := by
  unfold tailWord_5571438
  simp only [CollatzResearch.WordTrace]
  refine ⟨25400879748704890837583371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135471358659759417800444645 25400879748704890837583371)
  ·
    refine ⟨38101319623057336256375057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25400879748704890837583371 38101319623057336256375057)
    ·
      refine ⟨28575989717293002192281293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38101319623057336256375057 28575989717293002192281293)
      ·
        refine ⟨10715996143984875822105485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28575989717293002192281293 10715996143984875822105485)
        ·
          refine ⟨4018498553994328433289557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10715996143984875822105485 4018498553994328433289557)
          ·
            refine ⟨11772944982405259081903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4018498553994328433289557 11772944982405259081903)
            ·
              rfl

theorem cell23_5571438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 10].length) (baseStart_5571438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571438 prefixEnd_5571438 := by exact prefixLift 5571438
  have htrace : WordTrace (prefixWord ++ tailWord_5571438) baseStart_5571438 baseEnd_5571438 := by
    simpa [prefixWord, tailWord_5571438, baseEnd_5571438] using wordTrace_append hprefix tailTrace_5571438
  have hstable : (prefixWord ++ tailWord_5571438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571438).length < 2 ^ (prefixWord ++ tailWord_5571438).sum := by decide
  have hdescent : baseEnd_5571438 < baseStart_5571438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571449 : List Nat := [1, 2, 1, 3, 2, 3, 4, 2, 1, 2, 2]
def baseStart_5571449 : Nat := 118140960795 + 5571449 * 2 ^ 59
def prefixEnd_5571449 : Nat := 4983230072969 + 3 ^ 40 * 5571449 * 2
def baseEnd_5571449 : Nat := 2860831279011677413864879

theorem tailTrace_5571449 : CollatzResearch.WordTrace tailWord_5571449 prefixEnd_5571449 2860831279011677413864879 := by
  unfold tailWord_5571449
  simp only [CollatzResearch.WordTrace]
  refine ⟨203207439192599275579317401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135471626128399517052878267 203207439192599275579317401)
  ·
    refine ⟨152405579394449456684488051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203207439192599275579317401 152405579394449456684488051)
    ·
      refine ⟨228608369091674185026732077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152405579394449456684488051 228608369091674185026732077)
      ·
        refine ⟨85728138409377819385024529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228608369091674185026732077 85728138409377819385024529)
        ·
          refine ⟨64296103807033364538768397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85728138409377819385024529 64296103807033364538768397)
          ·
            refine ⟨24111038927637511702038149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64296103807033364538768397 24111038927637511702038149)
            ·
              refine ⟨4520819798932033444132153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24111038927637511702038149 4520819798932033444132153)
              ·
                refine ⟨3390614849199025083099115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4520819798932033444132153 3390614849199025083099115)
                ·
                  refine ⟨5085922273798537624648673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390614849199025083099115 5085922273798537624648673)
                  ·
                    refine ⟨3814441705348903218486505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5085922273798537624648673 3814441705348903218486505)
                    ·
                      refine ⟨2860831279011677413864879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814441705348903218486505 2860831279011677413864879)
                      ·
                        rfl

theorem cell23_5571449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_5571449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571449 prefixEnd_5571449 := by exact prefixLift 5571449
  have htrace : WordTrace (prefixWord ++ tailWord_5571449) baseStart_5571449 baseEnd_5571449 := by
    simpa [prefixWord, tailWord_5571449, baseEnd_5571449] using wordTrace_append hprefix tailTrace_5571449
  have hstable : (prefixWord ++ tailWord_5571449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571449).length < 2 ^ (prefixWord ++ tailWord_5571449).sum := by decide
  have hdescent : baseEnd_5571449 < baseStart_5571449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571465 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 3]
def baseStart_5571465 : Nat := 118140960795 + 5571465 * 2 ^ 59
def prefixEnd_5571465 : Nat := 4983230072969 + 3 ^ 40 * 5571465 * 2
def baseEnd_5571465 : Nat := 2860839494702149351264805

theorem tailTrace_5571465 : CollatzResearch.WordTrace tailWord_5571465 prefixEnd_5571465 2860839494702149351264805 := by
  unfold tailWord_5571465
  simp only [CollatzResearch.WordTrace]
  refine ⟨203208022760541310311899849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135472015173694206874599899 203208022760541310311899849)
  ·
    refine ⟨152406017070405982733924887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203208022760541310311899849 152406017070405982733924887)
    ·
      refine ⟨228609025605608974100887331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152406017070405982733924887 228609025605608974100887331)
      ·
        refine ⟨342913538408413461151330997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228609025605608974100887331 342913538408413461151330997)
        ·
          refine ⟨32148144225788761982937281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 342913538408413461151330997 32148144225788761982937281)
          ·
            refine ⟨24111108169341571487202961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32148144225788761982937281 24111108169341571487202961)
            ·
              refine ⟨18083331127006178615402221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24111108169341571487202961 18083331127006178615402221)
              ·
                refine ⟨6781249172627316980775833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18083331127006178615402221 6781249172627316980775833)
                ·
                  refine ⟨5085936879470487735581875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6781249172627316980775833 5085936879470487735581875)
                  ·
                    refine ⟨7628905319205731603372813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5085936879470487735581875 7628905319205731603372813)
                    ·
                      refine ⟨2860839494702149351264805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7628905319205731603372813 2860839494702149351264805)
                      ·
                        rfl

theorem cell23_5571465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 3].length) (baseStart_5571465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571465 prefixEnd_5571465 := by exact prefixLift 5571465
  have htrace : WordTrace (prefixWord ++ tailWord_5571465) baseStart_5571465 baseEnd_5571465 := by
    simpa [prefixWord, tailWord_5571465, baseEnd_5571465] using wordTrace_append hprefix tailTrace_5571465
  have hstable : (prefixWord ++ tailWord_5571465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571465).length < 2 ^ (prefixWord ++ tailWord_5571465).sum := by decide
  have hdescent : baseEnd_5571465 < baseStart_5571465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571491 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5]
def baseStart_5571491 : Nat := 118140960795 + 5571491 * 2 ^ 59
def prefixEnd_5571491 : Nat := 4983230072969 + 3 ^ 40 * 5571491 * 2
def baseEnd_5571491 : Nat := 2860852845199166249539685

theorem tailTrace_5571491 : CollatzResearch.WordTrace tailWord_5571491 prefixEnd_5571491 2860852845199166249539685 := by
  unfold tailWord_5571491
  simp only [CollatzResearch.WordTrace]
  refine ⟨203208971058447116752346327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135472647372298077834897551 203208971058447116752346327)
  ·
    refine ⟨304813456587670675128519491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203208971058447116752346327 304813456587670675128519491)
    ·
      refine ⟨457220184881506012692779237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304813456587670675128519491 457220184881506012692779237)
      ·
        refine ⟨85728784665282377379896107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 457220184881506012692779237 85728784665282377379896107)
        ·
          refine ⟨128593176997923566069844161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85728784665282377379896107 128593176997923566069844161)
          ·
            refine ⟨96444882748442674552383121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128593176997923566069844161 96444882748442674552383121)
            ·
              refine ⟨72333662061332005914287341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96444882748442674552383121 72333662061332005914287341)
              ·
                refine ⟨27125123272999502217857753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72333662061332005914287341 27125123272999502217857753)
                ·
                  refine ⟨20343842454749626663393315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27125123272999502217857753 20343842454749626663393315)
                  ·
                    refine ⟨30515763682124439995089973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20343842454749626663393315 30515763682124439995089973)
                    ·
                      refine ⟨2860852845199166249539685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30515763682124439995089973 2860852845199166249539685)
                      ·
                        rfl

theorem cell23_5571491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_5571491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571491 prefixEnd_5571491 := by exact prefixLift 5571491
  have htrace : WordTrace (prefixWord ++ tailWord_5571491) baseStart_5571491 baseEnd_5571491 := by
    simpa [prefixWord, tailWord_5571491, baseEnd_5571491] using wordTrace_append hprefix tailTrace_5571491
  have hstable : (prefixWord ++ tailWord_5571491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571491).length < 2 ^ (prefixWord ++ tailWord_5571491).sum := by decide
  have hdescent : baseEnd_5571491 < baseStart_5571491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571511 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 7]
def baseStart_5571511 : Nat := 118140960795 + 5571511 * 2 ^ 59
def prefixEnd_5571511 : Nat := 4983230072969 + 3 ^ 40 * 5571511 * 2
def baseEnd_5571511 : Nat := 317873679423584019032177

theorem tailTrace_5571511 : CollatzResearch.WordTrace tailWord_5571511 prefixEnd_5571511 317873679423584019032177 := by
  unfold tailWord_5571511
  simp only [CollatzResearch.WordTrace]
  refine ⟨203209700518374660168074387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135473133678916440112049591 203209700518374660168074387)
  ·
    refine ⟨304814550777561990252111581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203209700518374660168074387 304814550777561990252111581)
    ·
      refine ⟨114305456541585746344541843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304814550777561990252111581 114305456541585746344541843)
      ·
        refine ⟨171458184812378619516812765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114305456541585746344541843 171458184812378619516812765)
        ·
          refine ⟨64296819304641982318804787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171458184812378619516812765 64296819304641982318804787)
          ·
            refine ⟨96445228956962973478207181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64296819304641982318804787 96445228956962973478207181)
            ·
              refine ⟨36166960858861115054327693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96445228956962973478207181 36166960858861115054327693)
              ·
                refine ⟨13562610322072918145372885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36166960858861115054327693 13562610322072918145372885)
                ·
                  refine ⟨317873679423584019032177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13562610322072918145372885 317873679423584019032177)
                  ·
                    rfl

theorem cell23_5571511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 7].length) (baseStart_5571511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571511 prefixEnd_5571511 := by exact prefixLift 5571511
  have htrace : WordTrace (prefixWord ++ tailWord_5571511) baseStart_5571511 baseEnd_5571511 := by
    simpa [prefixWord, tailWord_5571511, baseEnd_5571511] using wordTrace_append hprefix tailTrace_5571511
  have hstable : (prefixWord ++ tailWord_5571511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571511).length < 2 ^ (prefixWord ++ tailWord_5571511).sum := by decide
  have hdescent : baseEnd_5571511 < baseStart_5571511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571518 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_5571518 : Nat := 118140960795 + 5571518 * 2 ^ 59
def prefixEnd_5571518 : Nat := 4983230072969 + 3 ^ 40 * 5571518 * 2
def baseEnd_5571518 : Nat := 2860866709176837643902061

theorem tailTrace_5571518 : CollatzResearch.WordTrace tailWord_5571518 prefixEnd_5571518 2860866709176837643902061 := by
  unfold tailWord_5571518
  simp only [CollatzResearch.WordTrace]
  refine ⟨25401244478668662545447401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135473303886232866909052805 25401244478668662545447401)
  ·
    refine ⟨19050933359001496909085551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25401244478668662545447401 19050933359001496909085551)
    ·
      refine ⟨28576400038502245363628327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050933359001496909085551 28576400038502245363628327)
      ·
        refine ⟨42864600057753368045442491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28576400038502245363628327 42864600057753368045442491)
        ·
          refine ⟨64296900086630052068163737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42864600057753368045442491 64296900086630052068163737)
          ·
            refine ⟨48222675064972539051122803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64296900086630052068163737 48222675064972539051122803)
            ·
              refine ⟨72334012597458808576684205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48222675064972539051122803 72334012597458808576684205)
              ·
                refine ⟨27125254724047053216256577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72334012597458808576684205 27125254724047053216256577)
                ·
                  refine ⟨20343941043035289912192433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27125254724047053216256577 20343941043035289912192433)
                  ·
                    refine ⟨15257955782276467434144325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20343941043035289912192433 15257955782276467434144325)
                    ·
                      refine ⟨2860866709176837643902061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15257955782276467434144325 2860866709176837643902061)
                      ·
                        rfl

theorem cell23_5571518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_5571518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571518 prefixEnd_5571518 := by exact prefixLift 5571518
  have htrace : WordTrace (prefixWord ++ tailWord_5571518) baseStart_5571518 baseEnd_5571518 := by
    simpa [prefixWord, tailWord_5571518, baseEnd_5571518] using wordTrace_append hprefix tailTrace_5571518
  have hstable : (prefixWord ++ tailWord_5571518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571518).length < 2 ^ (prefixWord ++ tailWord_5571518).sum := by decide
  have hdescent : baseEnd_5571518 < baseStart_5571518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571545 : List Nat := [1, 2, 1, 2, 5, 1, 3, 3, 5]
def baseStart_5571545 : Nat := 118140960795 + 5571545 * 2 ^ 59
def prefixEnd_5571545 : Nat := 4983230072969 + 3 ^ 40 * 5571545 * 2
def baseEnd_5571545 : Nat := 317875619239389893140493

theorem tailTrace_5571545 : CollatzResearch.WordTrace tailWord_5571545 prefixEnd_5571545 317875619239389893140493 := by
  unfold tailWord_5571545
  simp only [CollatzResearch.WordTrace]
  refine ⟨203210940600251483974812089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135473960400167655983208059 203210940600251483974812089)
  ·
    refine ⟨152408205450188612981109067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203210940600251483974812089 152408205450188612981109067)
    ·
      refine ⟨228612308175282919471663601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152408205450188612981109067 228612308175282919471663601)
      ·
        refine ⟨171459231131462189603747701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228612308175282919471663601 171459231131462189603747701)
        ·
          refine ⟨16074302918574580275351347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171459231131462189603747701 16074302918574580275351347)
          ·
            refine ⟨24111454377861870413027021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16074302918574580275351347 24111454377861870413027021)
            ·
              refine ⟨9041795391698201404885133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24111454377861870413027021 9041795391698201404885133)
              ·
                refine ⟨3390673271886825526831925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9041795391698201404885133 3390673271886825526831925)
                ·
                  refine ⟨317875619239389893140493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3390673271886825526831925 317875619239389893140493)
                  ·
                    rfl

theorem cell23_5571545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 5].length) (baseStart_5571545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571545 prefixEnd_5571545 := by exact prefixLift 5571545
  have htrace : WordTrace (prefixWord ++ tailWord_5571545) baseStart_5571545 baseEnd_5571545 := by
    simpa [prefixWord, tailWord_5571545, baseEnd_5571545] using wordTrace_append hprefix tailTrace_5571545
  have hstable : (prefixWord ++ tailWord_5571545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571545).length < 2 ^ (prefixWord ++ tailWord_5571545).sum := by decide
  have hdescent : baseEnd_5571545 < baseStart_5571545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571561 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_5571561 : Nat := 118140960795 + 5571561 * 2 ^ 59
def prefixEnd_5571561 : Nat := 4983230072969 + 3 ^ 40 * 5571561 * 2
def baseEnd_5571561 : Nat := 2860888788844980975664363

theorem tailTrace_5571561 : CollatzResearch.WordTrace tailWord_5571561 prefixEnd_5571561 2860888788844980975664363 := by
  unfold tailWord_5571561
  simp only [CollatzResearch.WordTrace]
  refine ⟨203211524168193518707394537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135474349445462345804929691 203211524168193518707394537)
  ·
    refine ⟨152408643126145139030545903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203211524168193518707394537 152408643126145139030545903)
    ·
      refine ⟨228612964689217708545818855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152408643126145139030545903 228612964689217708545818855)
      ·
        refine ⟨342919447033826562818728283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228612964689217708545818855 342919447033826562818728283)
        ·
          refine ⟨514379170550739844228092425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342919447033826562818728283 514379170550739844228092425)
          ·
            refine ⟨385784377913054883171069319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514379170550739844228092425 385784377913054883171069319)
            ·
              refine ⟨578676566869582324756603979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385784377913054883171069319 578676566869582324756603979)
              ·
                refine ⟨868014850304373487134905969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578676566869582324756603979 868014850304373487134905969)
                ·
                  refine ⟨651011137728280115351179477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 868014850304373487134905969 651011137728280115351179477)
                  ·
                    refine ⟨15258073540506565203543269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 651011137728280115351179477 15258073540506565203543269)
                    ·
                      refine ⟨2860888788844980975664363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15258073540506565203543269 2860888788844980975664363)
                      ·
                        rfl

theorem cell23_5571561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_5571561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571561 prefixEnd_5571561 := by exact prefixLift 5571561
  have htrace : WordTrace (prefixWord ++ tailWord_5571561) baseStart_5571561 baseEnd_5571561 := by
    simpa [prefixWord, tailWord_5571561, baseEnd_5571561] using wordTrace_append hprefix tailTrace_5571561
  have hstable : (prefixWord ++ tailWord_5571561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571561).length < 2 ^ (prefixWord ++ tailWord_5571561).sum := by decide
  have hdescent : baseEnd_5571561 < baseStart_5571561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571562 : List Nat := [3, 1, 3, 1, 2, 3, 3, 2, 5]
def baseStart_5571562 : Nat := 118140960795 + 5571562 * 2 ^ 59
def prefixEnd_5571562 : Nat := 4983230072969 + 3 ^ 40 * 5571562 * 2
def baseEnd_5571562 : Nat := 317876589147292830194651

theorem tailTrace_5571562 : CollatzResearch.WordTrace tailWord_5571562 prefixEnd_5571562 317876589147292830194651 := by
  unfold tailWord_5571562
  simp only [CollatzResearch.WordTrace]
  refine ⟨50802890160297473969545235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135474373760793263918787293 50802890160297473969545235)
  ·
    refine ⟨76204335240446210954317853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50802890160297473969545235 76204335240446210954317853)
    ·
      refine ⟨28576625715167329107869195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76204335240446210954317853 28576625715167329107869195)
      ·
        refine ⟨42864938572750993661803793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28576625715167329107869195 42864938572750993661803793)
        ·
          refine ⟨32148703929563245246352845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42864938572750993661803793 32148703929563245246352845)
          ·
            refine ⟨12055763973586216967382317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32148703929563245246352845 12055763973586216967382317)
            ·
              refine ⟨4520911490094831362768369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12055763973586216967382317 4520911490094831362768369)
              ·
                refine ⟨3390683617571123522076277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4520911490094831362768369 3390683617571123522076277)
                ·
                  refine ⟨317876589147292830194651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3390683617571123522076277 317876589147292830194651)
                  ·
                    rfl

theorem cell23_5571562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_5571562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571562 prefixEnd_5571562 := by exact prefixLift 5571562
  have htrace : WordTrace (prefixWord ++ tailWord_5571562) baseStart_5571562 baseEnd_5571562 := by
    simpa [prefixWord, tailWord_5571562, baseEnd_5571562] using wordTrace_append hprefix tailTrace_5571562
  have hstable : (prefixWord ++ tailWord_5571562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571562).length < 2 ^ (prefixWord ++ tailWord_5571562).sum := by decide
  have hdescent : baseEnd_5571562 < baseStart_5571562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571595 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 4]
def baseStart_5571595 : Nat := 118140960795 + 5571595 * 2 ^ 59
def prefixEnd_5571595 : Nat := 4983230072969 + 3 ^ 40 * 5571595 * 2
def baseEnd_5571595 : Nat := 2860906247187233842639207

theorem tailTrace_5571595 : CollatzResearch.WordTrace tailWord_5571595 prefixEnd_5571595 2860906247187233842639207 := by
  unfold tailWord_5571595
  simp only [CollatzResearch.WordTrace]
  refine ⟨203212764250070342514132239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135475176166713561676088159 203212764250070342514132239)
  ·
    refine ⟨304819146375105513771198359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203212764250070342514132239 304819146375105513771198359)
    ·
      refine ⟨457228719562658270656797539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304819146375105513771198359 457228719562658270656797539)
      ·
        refine ⟨685843079343987405985196309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457228719562658270656797539 685843079343987405985196309)
        ·
          refine ⟨32148894344249409655556077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 685843079343987405985196309 32148894344249409655556077)
          ·
            refine ⟨12055835379093528620833529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32148894344249409655556077 12055835379093528620833529)
            ·
              refine ⟨9041876534320146465625147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12055835379093528620833529 9041876534320146465625147)
              ·
                refine ⟨13562814801480219698437721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9041876534320146465625147 13562814801480219698437721)
                ·
                  refine ⟨10172111101110164773828291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13562814801480219698437721 10172111101110164773828291)
                  ·
                    refine ⟨15258166651665247160742437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10172111101110164773828291 15258166651665247160742437)
                    ·
                      refine ⟨2860906247187233842639207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15258166651665247160742437 2860906247187233842639207)
                      ·
                        rfl

theorem cell23_5571595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 4].length) (baseStart_5571595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571595 prefixEnd_5571595 := by exact prefixLift 5571595
  have htrace : WordTrace (prefixWord ++ tailWord_5571595) baseStart_5571595 baseEnd_5571595 := by
    simpa [prefixWord, tailWord_5571595, baseEnd_5571595] using wordTrace_append hprefix tailTrace_5571595
  have hstable : (prefixWord ++ tailWord_5571595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571595).length < 2 ^ (prefixWord ++ tailWord_5571595).sum := by decide
  have hdescent : baseEnd_5571595 < baseStart_5571595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571601 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 10]
def baseStart_5571601 : Nat := 118140960795 + 5571601 * 2 ^ 59
def prefixEnd_5571601 : Nat := 4983230072969 + 3 ^ 40 * 5571601 * 2
def baseEnd_5571601 : Nat := 317878814230128979907131

theorem tailTrace_5571601 : CollatzResearch.WordTrace tailWord_5571601 prefixEnd_5571601 317878814230128979907131 := by
  unfold tailWord_5571601
  simp only [CollatzResearch.WordTrace]
  refine ⟨203212983088048605538850657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135475322058699070359233771 203212983088048605538850657)
  ·
    refine ⟨152409737316036454154137993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203212983088048605538850657 152409737316036454154137993)
    ·
      refine ⟨114307302987027340615603495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152409737316036454154137993 114307302987027340615603495)
      ·
        refine ⟨171460954480541010923405243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114307302987027340615603495 171460954480541010923405243)
        ·
          refine ⟨257191431720811516385107865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171460954480541010923405243 257191431720811516385107865)
          ·
            refine ⟨192893573790608637288830899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257191431720811516385107865 192893573790608637288830899)
            ·
              refine ⟨289340360685912955933246349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192893573790608637288830899 289340360685912955933246349)
              ·
                refine ⟨108502635257217358474967381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289340360685912955933246349 108502635257217358474967381)
                ·
                  refine ⟨317878814230128979907131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 108502635257217358474967381 317878814230128979907131)
                  ·
                    rfl

theorem cell23_5571601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 10].length) (baseStart_5571601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571601 prefixEnd_5571601 := by exact prefixLift 5571601
  have htrace : WordTrace (prefixWord ++ tailWord_5571601) baseStart_5571601 baseEnd_5571601 := by
    simpa [prefixWord, tailWord_5571601, baseEnd_5571601] using wordTrace_append hprefix tailTrace_5571601
  have hstable : (prefixWord ++ tailWord_5571601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571601).length < 2 ^ (prefixWord ++ tailWord_5571601).sum := by decide
  have hdescent : baseEnd_5571601 < baseStart_5571601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571615 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 3]
def baseStart_5571615 : Nat := 118140960795 + 5571615 * 2 ^ 59
def prefixEnd_5571615 : Nat := 4983230072969 + 3 ^ 40 * 5571615 * 2
def baseEnd_5571615 : Nat := 2860916516800323764389115

theorem tailTrace_5571615 : CollatzResearch.WordTrace tailWord_5571615 prefixEnd_5571615 2860916516800323764389115 := by
  unfold tailWord_5571615
  simp only [CollatzResearch.WordTrace]
  refine ⟨203213493709997885929860299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135475662473331923953240199 203213493709997885929860299)
  ·
    refine ⟨304820240564996828894790449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203213493709997885929860299 304820240564996828894790449)
    ·
      refine ⟨228615180423747621671092837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304820240564996828894790449 228615180423747621671092837)
      ·
        refine ⟨42865346329452679063329907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228615180423747621671092837 42865346329452679063329907)
        ·
          refine ⟨64298019494179018594994861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42865346329452679063329907 64298019494179018594994861)
          ·
            refine ⟨24111757310317131973123073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64298019494179018594994861 24111757310317131973123073)
            ·
              refine ⟨18083817982737848979842305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24111757310317131973123073 18083817982737848979842305)
              ·
                refine ⟨13562863487053386734881729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18083817982737848979842305 13562863487053386734881729)
                ·
                  refine ⟨10172147615290040051161297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13562863487053386734881729 10172147615290040051161297)
                  ·
                    refine ⟨7629110711467530038370973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10172147615290040051161297 7629110711467530038370973)
                    ·
                      refine ⟨2860916516800323764389115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7629110711467530038370973 2860916516800323764389115)
                      ·
                        rfl

theorem cell23_5571615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_5571615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571615 prefixEnd_5571615 := by exact prefixLift 5571615
  have htrace : WordTrace (prefixWord ++ tailWord_5571615) baseStart_5571615 baseEnd_5571615 := by
    simpa [prefixWord, tailWord_5571615, baseEnd_5571615] using wordTrace_append hprefix tailTrace_5571615
  have hstable : (prefixWord ++ tailWord_5571615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571615).length < 2 ^ (prefixWord ++ tailWord_5571615).sum := by decide
  have hdescent : baseEnd_5571615 < baseStart_5571615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571648 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 3, 5]
def baseStart_5571648 : Nat := 118140960795 + 5571648 * 2 ^ 59
def prefixEnd_5571648 : Nat := 4983230072969 + 3 ^ 40 * 5571648 * 2
def baseEnd_5571648 : Nat := 953644487220640711758821

theorem tailTrace_5571648 : CollatzResearch.WordTrace tailWord_5571648 prefixEnd_5571648 953644487220640711758821 := by
  unfold tailWord_5571648
  simp only [CollatzResearch.WordTrace]
  refine ⟨101607348659439166282905799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135476464879252221710541065 101607348659439166282905799)
  ·
    refine ⟨152411022989158749424358699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101607348659439166282905799 152411022989158749424358699)
    ·
      refine ⟨228616534483738124136538049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152411022989158749424358699 228616534483738124136538049)
      ·
        refine ⟨171462400862803593102403537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228616534483738124136538049 171462400862803593102403537)
        ·
          refine ⟨128596800647102694826802653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171462400862803593102403537 128596800647102694826802653)
          ·
            refine ⟨48223800242663510560050995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128596800647102694826802653 48223800242663510560050995)
            ·
              refine ⟨72335700363995265840076493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48223800242663510560050995 72335700363995265840076493)
              ·
                refine ⟨27125887636498224690028685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72335700363995265840076493 27125887636498224690028685)
                ·
                  refine ⟨10172207863686834258760757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27125887636498224690028685 10172207863686834258760757)
                  ·
                    refine ⟨953644487220640711758821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10172207863686834258760757 953644487220640711758821)
                    ·
                      rfl

theorem cell23_5571648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_5571648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571648 prefixEnd_5571648 := by exact prefixLift 5571648
  have htrace : WordTrace (prefixWord ++ tailWord_5571648) baseStart_5571648 baseEnd_5571648 := by
    simpa [prefixWord, tailWord_5571648, baseEnd_5571648] using wordTrace_append hprefix tailTrace_5571648
  have hstable : (prefixWord ++ tailWord_5571648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571648).length < 2 ^ (prefixWord ++ tailWord_5571648).sum := by decide
  have hdescent : baseEnd_5571648 < baseStart_5571648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571649 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_5571649 : Nat := 118140960795 + 5571649 * 2 ^ 59
def prefixEnd_5571649 : Nat := 4983230072969 + 3 ^ 40 * 5571649 * 2
def baseEnd_5571649 : Nat := 2860933975142576631363959

theorem tailTrace_5571649 : CollatzResearch.WordTrace tailWord_5571649 prefixEnd_5571649 2860933975142576631363959 := by
  unfold tailWord_5571649
  simp only [CollatzResearch.WordTrace]
  refine ⟨203214733791874709736598001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135476489194583139824398667 203214733791874709736598001)
  ·
    refine ⟨152411050343906032302448501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203214733791874709736598001 152411050343906032302448501)
    ·
      refine ⟨14288535969741190528354547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152411050343906032302448501 14288535969741190528354547)
      ·
        refine ⟨21432803954611785792531821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14288535969741190528354547 21432803954611785792531821)
        ·
          refine ⟨8037301482979419672199433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21432803954611785792531821 8037301482979419672199433)
          ·
            refine ⟨6027976112234564754149575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8037301482979419672199433 6027976112234564754149575)
            ·
              refine ⟨9041964168351847131224363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027976112234564754149575 9041964168351847131224363)
              ·
                refine ⟨13562946252527770696836545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9041964168351847131224363 13562946252527770696836545)
                ·
                  refine ⟨10172209689395828022627409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13562946252527770696836545 10172209689395828022627409)
                  ·
                    refine ⟨7629157267046871016970557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10172209689395828022627409 7629157267046871016970557)
                    ·
                      refine ⟨2860933975142576631363959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7629157267046871016970557 2860933975142576631363959)
                      ·
                        rfl

theorem cell23_5571649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_5571649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571649 prefixEnd_5571649 := by exact prefixLift 5571649
  have htrace : WordTrace (prefixWord ++ tailWord_5571649) baseStart_5571649 baseEnd_5571649 := by
    simpa [prefixWord, tailWord_5571649, baseEnd_5571649] using wordTrace_append hprefix tailTrace_5571649
  have hstable : (prefixWord ++ tailWord_5571649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571649).length < 2 ^ (prefixWord ++ tailWord_5571649).sum := by decide
  have hdescent : baseEnd_5571649 < baseStart_5571649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571702 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5571702 : Nat := 118140960795 + 5571702 * 2 ^ 59
def prefixEnd_5571702 : Nat := 4983230072969 + 3 ^ 40 * 5571702 * 2
def baseEnd_5571702 : Nat := 2860961189617264924001215

theorem tailTrace_5571702 : CollatzResearch.WordTrace tailWord_5571702 prefixEnd_5571702 2860961189617264924001215 := by
  unfold tailWord_5571702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12701041678792668736767335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135477777907121799858851573 12701041678792668736767335)
  ·
    refine ⟨19051562518189003105151003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12701041678792668736767335 19051562518189003105151003)
    ·
      refine ⟨28577343777283504657726505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19051562518189003105151003 28577343777283504657726505)
      ·
        refine ⟨21433007832962628493294879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28577343777283504657726505 21433007832962628493294879)
        ·
          refine ⟨32149511749443942739942319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21433007832962628493294879 32149511749443942739942319)
          ·
            refine ⟨48224267624165914109913479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32149511749443942739942319 48224267624165914109913479)
            ·
              refine ⟨72336401436248871164870219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48224267624165914109913479 72336401436248871164870219)
              ·
                refine ⟨108504602154373306747305329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72336401436248871164870219 108504602154373306747305329)
                ·
                  refine ⟨81378451615779980060478997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108504602154373306747305329 81378451615779980060478997)
                  ·
                    refine ⟨3814614919489686565334953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81378451615779980060478997 3814614919489686565334953)
                    ·
                      refine ⟨2860961189617264924001215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814614919489686565334953 2860961189617264924001215)
                      ·
                        rfl

theorem cell23_5571702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5571702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571702 prefixEnd_5571702 := by exact prefixLift 5571702
  have htrace : WordTrace (prefixWord ++ tailWord_5571702) baseStart_5571702 baseEnd_5571702 := by
    simpa [prefixWord, tailWord_5571702, baseEnd_5571702] using wordTrace_append hprefix tailTrace_5571702
  have hstable : (prefixWord ++ tailWord_5571702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571702).length < 2 ^ (prefixWord ++ tailWord_5571702).sum := by decide
  have hdescent : baseEnd_5571702 < baseStart_5571702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571708 : List Nat := [2, 2, 2, 1, 1, 3, 3, 9]
def baseStart_5571708 : Nat := 118140960795 + 5571708 * 2 ^ 59
def prefixEnd_5571708 : Nat := 4983230072969 + 3 ^ 40 * 5571708 * 2
def baseEnd_5571708 : Nat := 105961639648192292612081

theorem tailTrace_5571708 : CollatzResearch.WordTrace tailWord_5571708 prefixEnd_5571708 105961639648192292612081 := by
  unfold tailWord_5571708
  simp only [CollatzResearch.WordTrace]
  refine ⟨101608442849330481406497889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135477923799107308541997185 101608442849330481406497889)
  ·
    refine ⟨76206332136997861054873417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101608442849330481406497889 76206332136997861054873417)
    ·
      refine ⟨57154749102748395791155063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76206332136997861054873417 57154749102748395791155063)
      ·
        refine ⟨85732123654122593686732595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57154749102748395791155063 85732123654122593686732595)
        ·
          refine ⟨128598185481183890530098893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85732123654122593686732595 128598185481183890530098893)
          ·
            refine ⟨48224319555443958948787085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128598185481183890530098893 48224319555443958948787085)
            ·
              refine ⟨18084119833291484605795157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48224319555443958948787085 18084119833291484605795157)
              ·
                refine ⟨105961639648192292612081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18084119833291484605795157 105961639648192292612081)
                ·
                  rfl

theorem cell23_5571708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 9].length) (baseStart_5571708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571708 prefixEnd_5571708 := by exact prefixLift 5571708
  have htrace : WordTrace (prefixWord ++ tailWord_5571708) baseStart_5571708 baseEnd_5571708 := by
    simpa [prefixWord, tailWord_5571708, baseEnd_5571708] using wordTrace_append hprefix tailTrace_5571708
  have hstable : (prefixWord ++ tailWord_5571708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571708).length < 2 ^ (prefixWord ++ tailWord_5571708).sum := by decide
  have hdescent : baseEnd_5571708 < baseStart_5571708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571722 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_5571722 : Nat := 118140960795 + 5571722 * 2 ^ 59
def prefixEnd_5571722 : Nat := 4983230072969 + 3 ^ 40 * 5571722 * 2
def baseEnd_5571722 : Nat := 2860971459230354845751123

theorem tailTrace_5571722 : CollatzResearch.WordTrace tailWord_5571722 prefixEnd_5571722 2860971459230354845751123 := by
  unfold tailWord_5571722
  simp only [CollatzResearch.WordTrace]
  refine ⟨50804349080152560801001355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135478264213740162136003613 50804349080152560801001355)
  ·
    refine ⟨76206523620228841201502033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50804349080152560801001355 76206523620228841201502033)
    ·
      refine ⟨57154892715171630901126525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76206523620228841201502033 57154892715171630901126525)
      ·
        refine ⟨21433084768189361587922447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57154892715171630901126525 21433084768189361587922447)
        ·
          refine ⟨32149627152284042381883671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21433084768189361587922447 32149627152284042381883671)
          ·
            refine ⟨48224440728426063572825507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32149627152284042381883671 48224440728426063572825507)
            ·
              refine ⟨72336661092639095359238261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48224440728426063572825507 72336661092639095359238261)
              ·
                refine ⟨6781561977434915189928587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72336661092639095359238261 6781561977434915189928587)
                ·
                  refine ⟨10172342966152372784892881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6781561977434915189928587 10172342966152372784892881)
                  ·
                    refine ⟨7629257224614279588669661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10172342966152372784892881 7629257224614279588669661)
                    ·
                      refine ⟨2860971459230354845751123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7629257224614279588669661 2860971459230354845751123)
                      ·
                        rfl

theorem cell23_5571722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_5571722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571722 prefixEnd_5571722 := by exact prefixLift 5571722
  have htrace : WordTrace (prefixWord ++ tailWord_5571722) baseStart_5571722 baseEnd_5571722 := by
    simpa [prefixWord, tailWord_5571722, baseEnd_5571722] using wordTrace_append hprefix tailTrace_5571722
  have hstable : (prefixWord ++ tailWord_5571722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571722).length < 2 ^ (prefixWord ++ tailWord_5571722).sum := by decide
  have hdescent : baseEnd_5571722 < baseStart_5571722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571736 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 3, 2, 2]
def baseStart_5571736 : Nat := 118140960795 + 5571736 * 2 ^ 59
def prefixEnd_5571736 : Nat := 4983230072969 + 3 ^ 40 * 5571736 * 2
def baseEnd_5571736 : Nat := 2860978647959517790976059

theorem tailTrace_5571736 : CollatzResearch.WordTrace tailWord_5571736 prefixEnd_5571736 2860978647959517790976059 := by
  unfold tailWord_5571736
  simp only [CollatzResearch.WordTrace]
  refine ⟨101608953471279761797507531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135478604628373015730010041 101608953471279761797507531)
  ·
    refine ⟨152413430206919642696261297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101608953471279761797507531 152413430206919642696261297)
    ·
      refine ⟨114310072655189732022195973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152413430206919642696261297 114310072655189732022195973)
      ·
        refine ⟨21433138622848074754161745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114310072655189732022195973 21433138622848074754161745)
        ·
          refine ⟨16074853967136056065621309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21433138622848074754161745 16074853967136056065621309)
          ·
            refine ⟨6028070237676021024607991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16074853967136056065621309 6028070237676021024607991)
            ·
              refine ⟨9042105356514031536911987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6028070237676021024607991 9042105356514031536911987)
              ·
                refine ⟨13563158034771047305367981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9042105356514031536911987 13563158034771047305367981)
                ·
                  refine ⟨5086184263039142739512993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13563158034771047305367981 5086184263039142739512993)
                  ·
                    refine ⟨3814638197279357054634745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5086184263039142739512993 3814638197279357054634745)
                    ·
                      refine ⟨2860978647959517790976059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814638197279357054634745 2860978647959517790976059)
                      ·
                        rfl

theorem cell23_5571736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_5571736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571736 prefixEnd_5571736 := by exact prefixLift 5571736
  have htrace : WordTrace (prefixWord ++ tailWord_5571736) baseStart_5571736 baseEnd_5571736 := by
    simpa [prefixWord, tailWord_5571736, baseEnd_5571736] using wordTrace_append hprefix tailTrace_5571736
  have hstable : (prefixWord ++ tailWord_5571736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571736).length < 2 ^ (prefixWord ++ tailWord_5571736).sum := by decide
  have hdescent : baseEnd_5571736 < baseStart_5571736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571742 : List Nat := [4, 3, 1, 1, 2, 2, 2, 8]
def baseStart_5571742 : Nat := 118140960795 + 5571742 * 2 ^ 59
def prefixEnd_5571742 : Nat := 4983230072969 + 3 ^ 40 * 5571742 * 2
def baseEnd_5571742 : Nat := 105962286253460917314853

theorem tailTrace_5571742 : CollatzResearch.WordTrace tailWord_5571742 prefixEnd_5571742 105962286253460917314853 := by
  unfold tailWord_5571742
  simp only [CollatzResearch.WordTrace]
  refine ⟨25402265722567223327466685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135478750520358524413155653 25402265722567223327466685)
  ·
    refine ⟨9525849645962708747800007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25402265722567223327466685 9525849645962708747800007)
    ·
      refine ⟨14288774468944063121700011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9525849645962708747800007 14288774468944063121700011)
      ·
        refine ⟨21433161703416094682550017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14288774468944063121700011 21433161703416094682550017)
        ·
          refine ⟨16074871277562071011912513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21433161703416094682550017 16074871277562071011912513)
          ·
            refine ⟨12056153458171553258934385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16074871277562071011912513 12056153458171553258934385)
            ·
              refine ⟨9042115093628664944200789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12056153458171553258934385 9042115093628664944200789)
              ·
                refine ⟨105962286253460917314853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9042115093628664944200789 105962286253460917314853)
                ·
                  rfl

theorem cell23_5571742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_5571742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571742 prefixEnd_5571742 := by exact prefixLift 5571742
  have htrace : WordTrace (prefixWord ++ tailWord_5571742) baseStart_5571742 baseEnd_5571742 := by
    simpa [prefixWord, tailWord_5571742, baseEnd_5571742] using wordTrace_append hprefix tailTrace_5571742
  have hstable : (prefixWord ++ tailWord_5571742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571742).length < 2 ^ (prefixWord ++ tailWord_5571742).sum := by decide
  have hdescent : baseEnd_5571742 < baseStart_5571742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571766 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5571766 : Nat := 118140960795 + 5571766 * 2 ^ 59
def prefixEnd_5571766 : Nat := 4983230072969 + 3 ^ 40 * 5571766 * 2
def baseEnd_5571766 : Nat := 2860994052379152673600921

theorem tailTrace_5571766 : CollatzResearch.WordTrace tailWord_5571766 prefixEnd_5571766 2860994052379152673600921 := by
  unfold tailWord_5571766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12701187570778177419912947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135479334088300559145738101 12701187570778177419912947)
  ·
    refine ⟨19051781356167266129869421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12701187570778177419912947 19051781356167266129869421)
    ·
      refine ⟨7144418008562724798701033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19051781356167266129869421 7144418008562724798701033)
      ·
        refine ⟨5358313506422043599025775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7144418008562724798701033 5358313506422043599025775)
        ·
          refine ⟨8037470259633065398538663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5358313506422043599025775 8037470259633065398538663)
          ·
            refine ⟨12056205389449598097807995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8037470259633065398538663 12056205389449598097807995)
            ·
              refine ⟨18084308084174397146711993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12056205389449598097807995 18084308084174397146711993)
              ·
                refine ⟨13563231063130797860033995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18084308084174397146711993 13563231063130797860033995)
                ·
                  refine ⟨20344846594696196790050993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13563231063130797860033995 20344846594696196790050993)
                  ·
                    refine ⟨15258634946022147592538245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20344846594696196790050993 15258634946022147592538245)
                    ·
                      refine ⟨2860994052379152673600921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15258634946022147592538245 2860994052379152673600921)
                      ·
                        rfl

theorem cell23_5571766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5571766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571766 prefixEnd_5571766 := by exact prefixLift 5571766
  have htrace : WordTrace (prefixWord ++ tailWord_5571766) baseStart_5571766 baseEnd_5571766 := by
    simpa [prefixWord, tailWord_5571766, baseEnd_5571766] using wordTrace_append hprefix tailTrace_5571766
  have hstable : (prefixWord ++ tailWord_5571766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571766).length < 2 ^ (prefixWord ++ tailWord_5571766).sum := by decide
  have hdescent : baseEnd_5571766 < baseStart_5571766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571768 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 3, 8]
def baseStart_5571768 : Nat := 118140960795 + 5571768 * 2 ^ 59
def prefixEnd_5571768 : Nat := 4983230072969 + 3 ^ 40 * 5571768 * 2
def baseEnd_5571768 : Nat := 953665026446820555258637

theorem tailTrace_5571768 : CollatzResearch.WordTrace tailWord_5571768 prefixEnd_5571768 953665026446820555258637 := by
  unfold tailWord_5571768
  simp only [CollatzResearch.WordTrace]
  refine ⟨101609537039221796530089979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135479382718962395373453305 101609537039221796530089979)
  ·
    refine ⟨152414305558832694795134969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101609537039221796530089979 152414305558832694795134969)
    ·
      refine ⟨114310729169124521096351227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152414305558832694795134969 114310729169124521096351227)
      ·
        refine ⟨171466093753686781644526841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114310729169124521096351227 171466093753686781644526841)
        ·
          refine ⟨128599570315265086233395131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171466093753686781644526841 128599570315265086233395131)
          ·
            refine ⟨192899355472897629350092697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128599570315265086233395131 192899355472897629350092697)
            ·
              refine ⟨144674516604673222012569523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192899355472897629350092697 144674516604673222012569523)
              ·
                refine ⟨217011774907009833018854285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144674516604673222012569523 217011774907009833018854285)
                ·
                  refine ⟨81379415590128687382070357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217011774907009833018854285 81379415590128687382070357)
                  ·
                    refine ⟨953665026446820555258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81379415590128687382070357 953665026446820555258637)
                    ·
                      rfl

theorem cell23_5571768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_5571768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571768 prefixEnd_5571768 := by exact prefixLift 5571768
  have htrace : WordTrace (prefixWord ++ tailWord_5571768) baseStart_5571768 baseEnd_5571768 := by
    simpa [prefixWord, tailWord_5571768, baseEnd_5571768] using wordTrace_append hprefix tailTrace_5571768
  have hstable : (prefixWord ++ tailWord_5571768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571768).length < 2 ^ (prefixWord ++ tailWord_5571768).sum := by decide
  have hdescent : baseEnd_5571768 < baseStart_5571768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571809 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_5571809 : Nat := 118140960795 + 5571809 * 2 ^ 59
def prefixEnd_5571809 : Nat := 4983230072969 + 3 ^ 40 * 5571809 * 2
def baseEnd_5571809 : Nat := 2861016132047296005363223

theorem tailTrace_5571809 : CollatzResearch.WordTrace tailWord_5571809 prefixEnd_5571809 2861016132047296005363223 := by
  unfold tailWord_5571809
  simp only [CollatzResearch.WordTrace]
  refine ⟨203220569471295057062422481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135480379647530038041614987 203220569471295057062422481)
  ·
    refine ⟨152415427103471292796816861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203220569471295057062422481 152415427103471292796816861)
    ·
      refine ⟨57155785163801734798806323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152415427103471292796816861 57155785163801734798806323)
      ·
        refine ⟨85733677745702602198209485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57155785163801734798806323 85733677745702602198209485)
        ·
          refine ⟨32150129154638475824328557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85733677745702602198209485 32150129154638475824328557)
          ·
            refine ⟨12056298432989428434123209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32150129154638475824328557 12056298432989428434123209)
            ·
              refine ⟨9042223824742071325592407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12056298432989428434123209 9042223824742071325592407)
              ·
                refine ⟨13563335737113106988388611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9042223824742071325592407 13563335737113106988388611)
                ·
                  refine ⟨20345003605669660482582917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13563335737113106988388611 20345003605669660482582917)
                  ·
                    refine ⟨3814688176063061340484297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20345003605669660482582917 3814688176063061340484297)
                    ·
                      refine ⟨2861016132047296005363223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814688176063061340484297 2861016132047296005363223)
                      ·
                        rfl

theorem cell23_5571809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_5571809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571809 prefixEnd_5571809 := by exact prefixLift 5571809
  have htrace : WordTrace (prefixWord ++ tailWord_5571809) baseStart_5571809 baseEnd_5571809 := by
    simpa [prefixWord, tailWord_5571809, baseEnd_5571809] using wordTrace_append hprefix tailTrace_5571809
  have hstable : (prefixWord ++ tailWord_5571809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571809).length < 2 ^ (prefixWord ++ tailWord_5571809).sum := by decide
  have hdescent : baseEnd_5571809 < baseStart_5571809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571825 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_5571825 : Nat := 118140960795 + 5571825 * 2 ^ 59
def prefixEnd_5571825 : Nat := 4983230072969 + 3 ^ 40 * 5571825 * 2
def baseEnd_5571825 : Nat := 2861024347737767942763149

theorem tailTrace_5571825 : CollatzResearch.WordTrace tailWord_5571825 prefixEnd_5571825 2861024347737767942763149 := by
  unfold tailWord_5571825
  simp only [CollatzResearch.WordTrace]
  refine ⟨203221153039237091795004929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135480768692824727863336619 203221153039237091795004929)
  ·
    refine ⟨152415864779427818846253697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203221153039237091795004929 152415864779427818846253697)
    ·
      refine ⟨114311898584570864134690273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152415864779427818846253697 114311898584570864134690273)
      ·
        refine ⟨85733923938428148101017705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114311898584570864134690273 85733923938428148101017705)
        ·
          refine ⟨64300442953821111075763279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85733923938428148101017705 64300442953821111075763279)
          ·
            refine ⟨96450664430731666613644919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64300442953821111075763279 96450664430731666613644919)
            ·
              refine ⟨144675996646097499920467379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96450664430731666613644919 144675996646097499920467379)
              ·
                refine ⟨217013994969146249880701069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144675996646097499920467379 217013994969146249880701069)
                ·
                  refine ⟨81380248113429843705262901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217013994969146249880701069 81380248113429843705262901)
                  ·
                    refine ⟨7629398260634047847368397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81380248113429843705262901 7629398260634047847368397)
                    ·
                      refine ⟨2861024347737767942763149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7629398260634047847368397 2861024347737767942763149)
                      ·
                        rfl

theorem cell23_5571825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_5571825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571825 prefixEnd_5571825 := by exact prefixLift 5571825
  have htrace : WordTrace (prefixWord ++ tailWord_5571825) baseStart_5571825 baseEnd_5571825 := by
    simpa [prefixWord, tailWord_5571825, baseEnd_5571825] using wordTrace_append hprefix tailTrace_5571825
  have hstable : (prefixWord ++ tailWord_5571825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571825).length < 2 ^ (prefixWord ++ tailWord_5571825).sum := by decide
  have hdescent : baseEnd_5571825 < baseStart_5571825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571845 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_5571845 : Nat := 118140960795 + 5571845 * 2 ^ 59
def prefixEnd_5571845 : Nat := 4983230072969 + 3 ^ 40 * 5571845 * 2
def baseEnd_5571845 : Nat := 953678205783619288171019

theorem tailTrace_5571845 : CollatzResearch.WordTrace tailWord_5571845 prefixEnd_5571845 953678205783619288171019 := by
  unfold tailWord_5571845
  simp only [CollatzResearch.WordTrace]
  refine ⟨203221882499164635210732989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135481254999443090140488659 203221882499164635210732989)
  ·
    refine ⟨76208205937186738204024871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203221882499164635210732989 76208205937186738204024871)
    ·
      refine ⟨114312308905780107306037307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76208205937186738204024871 114312308905780107306037307)
      ·
        refine ⟨171468463358670160959055961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114312308905780107306037307 171468463358670160959055961)
        ·
          refine ⟨128601347519002620719291971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171468463358670160959055961 128601347519002620719291971)
          ·
            refine ⟨192902021278503931078937957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128601347519002620719291971 192902021278503931078937957)
            ·
              refine ⟨36169128989719487077300867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192902021278503931078937957 36169128989719487077300867)
              ·
                refine ⟨54253693484579230615951301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36169128989719487077300867 54253693484579230615951301)
                ·
                  refine ⟨10172567528358605740490869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54253693484579230615951301 10172567528358605740490869)
                  ·
                    refine ⟨953678205783619288171019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10172567528358605740490869 953678205783619288171019)
                    ·
                      rfl

theorem cell23_5571845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_5571845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571845 prefixEnd_5571845 := by exact prefixLift 5571845
  have htrace : WordTrace (prefixWord ++ tailWord_5571845) baseStart_5571845 baseEnd_5571845 := by
    simpa [prefixWord, tailWord_5571845, baseEnd_5571845] using wordTrace_append hprefix tailTrace_5571845
  have hstable : (prefixWord ++ tailWord_5571845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571845).length < 2 ^ (prefixWord ++ tailWord_5571845).sum := by decide
  have hdescent : baseEnd_5571845 < baseStart_5571845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571909 : List Nat := [1, 3, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_5571909 : Nat := 118140960795 + 5571909 * 2 ^ 59
def prefixEnd_5571909 : Nat := 4983230072969 + 3 ^ 40 * 5571909 * 2
def baseEnd_5571909 : Nat := 953689160037581871370921

theorem tailTrace_5571909 : CollatzResearch.WordTrace tailWord_5571909 prefixEnd_5571909 953689160037581871370921 := by
  unfold tailWord_5571909
  simp only [CollatzResearch.WordTrace]
  refine ⟨203224216770932774141062781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135482811180621849427375187 203224216770932774141062781)
  ·
    refine ⟨76209081289099790302898543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203224216770932774141062781 76209081289099790302898543)
    ·
      refine ⟨114313621933649685454347815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76209081289099790302898543 114313621933649685454347815)
      ·
        refine ⟨171470432900474528181521723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114313621933649685454347815 171470432900474528181521723)
        ·
          refine ⟨257205649350711792272282585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171470432900474528181521723 257205649350711792272282585)
          ·
            refine ⟨192904237013033844204211939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257205649350711792272282585 192904237013033844204211939)
            ·
              refine ⟨289356355519550766306317909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192904237013033844204211939 289356355519550766306317909)
              ·
                refine ⟨3390894791244735542652163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 289356355519550766306317909 3390894791244735542652163)
                ·
                  refine ⟨5086342186867103313978245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390894791244735542652163 5086342186867103313978245)
                  ·
                    refine ⟨953689160037581871370921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086342186867103313978245 953689160037581871370921)
                    ·
                      rfl

theorem cell23_5571909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_5571909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571909 prefixEnd_5571909 := by exact prefixLift 5571909
  have htrace : WordTrace (prefixWord ++ tailWord_5571909) baseStart_5571909 baseEnd_5571909 := by
    simpa [prefixWord, tailWord_5571909, baseEnd_5571909] using wordTrace_append hprefix tailTrace_5571909
  have hstable : (prefixWord ++ tailWord_5571909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571909).length < 2 ^ (prefixWord ++ tailWord_5571909).sum := by decide
  have hdescent : baseEnd_5571909 < baseStart_5571909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571945 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_5571945 : Nat := 118140960795 + 5571945 * 2 ^ 59
def prefixEnd_5571945 : Nat := 4983230072969 + 3 ^ 40 * 5571945 * 2
def baseEnd_5571945 : Nat := 2861085965416307473262597

theorem tailTrace_5571945 : CollatzResearch.WordTrace tailWord_5571945 prefixEnd_5571945 2861085965416307473262597 := by
  unfold tailWord_5571945
  simp only [CollatzResearch.WordTrace]
  refine ⟨203225529798802352289373289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135483686532534901526248859 203225529798802352289373289)
  ·
    refine ⟨152419147349101764217029967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203225529798802352289373289 152419147349101764217029967)
    ·
      refine ⟨228628721023652646325544951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152419147349101764217029967 228628721023652646325544951)
      ·
        refine ⟨342943081535478969488317427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228628721023652646325544951 342943081535478969488317427)
        ·
          refine ⟨514414622303218454232476141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342943081535478969488317427 514414622303218454232476141)
          ·
            refine ⟨192905483363706920337178553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514414622303218454232476141 192905483363706920337178553)
            ·
              refine ⟨144679112522780190252883915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192905483363706920337178553 144679112522780190252883915)
              ·
                refine ⟨217018668784170285379325873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144679112522780190252883915 217018668784170285379325873)
                ·
                  refine ⟨162764001588127714034494405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217018668784170285379325873 162764001588127714034494405)
                  ·
                    refine ⟨30518250297773946381467701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162764001588127714034494405 30518250297773946381467701)
                    ·
                      refine ⟨2861085965416307473262597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30518250297773946381467701 2861085965416307473262597)
                      ·
                        rfl

theorem cell23_5571945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_5571945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571945 prefixEnd_5571945 := by exact prefixLift 5571945
  have htrace : WordTrace (prefixWord ++ tailWord_5571945) baseStart_5571945 baseEnd_5571945 := by
    simpa [prefixWord, tailWord_5571945, baseEnd_5571945] using wordTrace_append hprefix tailTrace_5571945
  have hstable : (prefixWord ++ tailWord_5571945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571945).length < 2 ^ (prefixWord ++ tailWord_5571945).sum := by decide
  have hdescent : baseEnd_5571945 < baseStart_5571945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5571959 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 2, 3, 2]
def baseStart_5571959 : Nat := 118140960795 + 5571959 * 2 ^ 59
def prefixEnd_5571959 : Nat := 4983230072969 + 3 ^ 40 * 5571959 * 2
def baseEnd_5571959 : Nat := 2861093154145470418487533

theorem tailTrace_5571959 : CollatzResearch.WordTrace tailWord_5571959 prefixEnd_5571959 2861093154145470418487533 := by
  unfold tailWord_5571959
  simp only [CollatzResearch.WordTrace]
  refine ⟨203226040420751632680382931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135484026947167755120255287 203226040420751632680382931)
  ·
    refine ⟨304839060631127449020574397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203226040420751632680382931 304839060631127449020574397)
    ·
      refine ⟨114314647736672793382715399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304839060631127449020574397 114314647736672793382715399)
      ·
        refine ⟨171471971605009190074073099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114314647736672793382715399 171471971605009190074073099)
        ·
          refine ⟨257207957407513785111109649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171471971605009190074073099 257207957407513785111109649)
          ·
            refine ⟨192905968055635338833332237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257207957407513785111109649 192905968055635338833332237)
            ·
              refine ⟨72339738020863252062499589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192905968055635338833332237 72339738020863252062499589)
              ·
                refine ⟨13563700878911859761718673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72339738020863252062499589 13563700878911859761718673)
                ·
                  refine ⟨10172775659183894821289005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13563700878911859761718673 10172775659183894821289005)
                  ·
                    refine ⟨3814790872193960557983377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10172775659183894821289005 3814790872193960557983377)
                    ·
                      refine ⟨2861093154145470418487533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814790872193960557983377 2861093154145470418487533)
                      ·
                        rfl

theorem cell23_5571959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_5571959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5571959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5571959 prefixEnd_5571959 := by exact prefixLift 5571959
  have htrace : WordTrace (prefixWord ++ tailWord_5571959) baseStart_5571959 baseEnd_5571959 := by
    simpa [prefixWord, tailWord_5571959, baseEnd_5571959] using wordTrace_append hprefix tailTrace_5571959
  have hstable : (prefixWord ++ tailWord_5571959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5571959).length < 2 ^ (prefixWord ++ tailWord_5571959).sum := by decide
  have hdescent : baseEnd_5571959 < baseStart_5571959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5571959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572023 : List Nat := [1, 1, 3, 1, 3, 2, 1, 6, 1, 2, 2]
def baseStart_5572023 : Nat := 118140960795 + 5572023 * 2 ^ 59
def prefixEnd_5572023 : Nat := 4983230072969 + 3 ^ 40 * 5572023 * 2
def baseEnd_5572023 : Nat := 2861126016907358168087239

theorem tailTrace_5572023 : CollatzResearch.WordTrace tailWord_5572023 prefixEnd_5572023 2861126016907358168087239 := by
  unfold tailWord_5572023
  simp only [CollatzResearch.WordTrace]
  refine ⟨203228374692519771610712723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135485583128346514407141815 203228374692519771610712723)
  ·
    refine ⟨304842562038779657416069085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203228374692519771610712723 304842562038779657416069085)
    ·
      refine ⟨114315960764542371531025907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304842562038779657416069085 114315960764542371531025907)
      ·
        refine ⟨171473941146813557296538861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114315960764542371531025907 171473941146813557296538861)
        ·
          refine ⟨64302727930055083986202073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171473941146813557296538861 64302727930055083986202073)
          ·
            refine ⟨48227045947541312989651555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64302727930055083986202073 48227045947541312989651555)
            ·
              refine ⟨72340568921311969484477333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48227045947541312989651555 72340568921311969484477333)
              ·
                refine ⟨3390964168186498569584875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72340568921311969484477333 3390964168186498569584875)
                ·
                  refine ⟨5086446252279747854377313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390964168186498569584875 5086446252279747854377313)
                  ·
                    refine ⟨3814834689209810890782985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5086446252279747854377313 3814834689209810890782985)
                    ·
                      refine ⟨2861126016907358168087239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814834689209810890782985 2861126016907358168087239)
                      ·
                        rfl

theorem cell23_5572023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_5572023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572023 prefixEnd_5572023 := by exact prefixLift 5572023
  have htrace : WordTrace (prefixWord ++ tailWord_5572023) baseStart_5572023 baseEnd_5572023 := by
    simpa [prefixWord, tailWord_5572023, baseEnd_5572023] using wordTrace_append hprefix tailTrace_5572023
  have hstable : (prefixWord ++ tailWord_5572023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572023).length < 2 ^ (prefixWord ++ tailWord_5572023).sum := by decide
  have hdescent : baseEnd_5572023 < baseStart_5572023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572036 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5572036 : Nat := 118140960795 + 5572036 * 2 ^ 59
def prefixEnd_5572036 : Nat := 4983230072969 + 3 ^ 40 * 5572036 * 2
def baseEnd_5572036 : Nat := 2861132692155866617224679

theorem tailTrace_5572036 : CollatzResearch.WordTrace tailWord_5572036 prefixEnd_5572036 2861132692155866617224679 := by
  unfold tailWord_5572036
  simp only [CollatzResearch.WordTrace]
  refine ⟨101614424420736337415467981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135485899227648449887290641 101614424420736337415467981)
  ·
    refine ⟨38105409157776126530800493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101614424420736337415467981 38105409157776126530800493)
    ·
      refine ⟨14289528434166047449050185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38105409157776126530800493 14289528434166047449050185)
      ·
        refine ⟨10717146325624535586787639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14289528434166047449050185 10717146325624535586787639)
        ·
          refine ⟨16075719488436803380181459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10717146325624535586787639 16075719488436803380181459)
          ·
            refine ⟨24113579232655205070272189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16075719488436803380181459 24113579232655205070272189)
            ·
              refine ⟨9042592212245701901352071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24113579232655205070272189 9042592212245701901352071)
              ·
                refine ⟨13563888318368552852028107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9042592212245701901352071 13563888318368552852028107)
                ·
                  refine ⟨20345832477552829278042161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13563888318368552852028107 20345832477552829278042161)
                  ·
                    refine ⟨15259374358164621958531621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20345832477552829278042161 15259374358164621958531621)
                    ·
                      refine ⟨2861132692155866617224679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15259374358164621958531621 2861132692155866617224679)
                      ·
                        rfl

theorem cell23_5572036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5572036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572036 prefixEnd_5572036 := by exact prefixLift 5572036
  have htrace : WordTrace (prefixWord ++ tailWord_5572036) baseStart_5572036 baseEnd_5572036 := by
    simpa [prefixWord, tailWord_5572036, baseEnd_5572036] using wordTrace_append hprefix tailTrace_5572036
  have hstable : (prefixWord ++ tailWord_5572036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572036).length < 2 ^ (prefixWord ++ tailWord_5572036).sum := by decide
  have hdescent : baseEnd_5572036 < baseStart_5572036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572196 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_5572196 : Nat := 118140960795 + 5572196 * 2 ^ 59
def prefixEnd_5572196 : Nat := 4983230072969 + 3 ^ 40 * 5572196 * 2
def baseEnd_5572196 : Nat := 953738283020195330407981

theorem tailTrace_5572196 : CollatzResearch.WordTrace tailWord_5572196 prefixEnd_5572196 953738283020195330407981 := by
  unfold tailWord_5572196
  simp only [CollatzResearch.WordTrace]
  refine ⟨101617342260446511078380221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135489789680595348104506961 101617342260446511078380221)
  ·
    refine ⟨38106503347667441654392583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101617342260446511078380221 38106503347667441654392583)
    ·
      refine ⟨57159755021501162481588875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38106503347667441654392583 57159755021501162481588875)
      ·
        refine ⟨85739632532251743722383313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57159755021501162481588875 85739632532251743722383313)
        ·
          refine ⟨64304724399188807791787485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85739632532251743722383313 64304724399188807791787485)
          ·
            refine ⟨24114271649695802921920307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64304724399188807791787485 24114271649695802921920307)
            ·
              refine ⟨36171407474543704382880461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24114271649695802921920307 36171407474543704382880461)
              ·
                refine ⟨13564277802953889143580173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36171407474543704382880461 13564277802953889143580173)
                ·
                  refine ⟨5086604176107708428842565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13564277802953889143580173 5086604176107708428842565)
                  ·
                    refine ⟨953738283020195330407981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086604176107708428842565 953738283020195330407981)
                    ·
                      rfl

theorem cell23_5572196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_5572196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572196 prefixEnd_5572196 := by exact prefixLift 5572196
  have htrace : WordTrace (prefixWord ++ tailWord_5572196) baseStart_5572196 baseEnd_5572196 := by
    simpa [prefixWord, tailWord_5572196, baseEnd_5572196] using wordTrace_append hprefix tailTrace_5572196
  have hstable : (prefixWord ++ tailWord_5572196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572196).length < 2 ^ (prefixWord ++ tailWord_5572196).sum := by decide
  have hdescent : baseEnd_5572196 < baseStart_5572196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572209 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 6]
def baseStart_5572209 : Nat := 118140960795 + 5572209 * 2 ^ 59
def prefixEnd_5572209 : Nat := 4983230072969 + 3 ^ 40 * 5572209 * 2
def baseEnd_5572209 : Nat := 317913502701010493373487

theorem tailTrace_5572209 : CollatzResearch.WordTrace tailWord_5572209 prefixEnd_5572209 317913502701010493373487 := by
  unfold tailWord_5572209
  simp only [CollatzResearch.WordTrace]
  refine ⟨203235158669845925376983681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135490105779897283584655787 203235158669845925376983681)
  ·
    refine ⟨152426369002384444032737761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203235158669845925376983681 152426369002384444032737761)
    ·
      refine ⟨114319776751788333024553321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152426369002384444032737761 114319776751788333024553321)
      ·
        refine ⟨85739832563841249768414991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114319776751788333024553321 85739832563841249768414991)
        ·
          refine ⟨128609748845761874652622487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85739832563841249768414991 128609748845761874652622487)
          ·
            refine ⟨192914623268642811978933731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128609748845761874652622487 192914623268642811978933731)
            ·
              refine ⟨289371934902964217968400597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192914623268642811978933731 289371934902964217968400597)
              ·
                refine ⟨6782154724288223858634389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 289371934902964217968400597 6782154724288223858634389)
                ·
                  refine ⟨317913502701010493373487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6782154724288223858634389 317913502701010493373487)
                  ·
                    rfl

theorem cell23_5572209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 6].length) (baseStart_5572209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572209 prefixEnd_5572209 := by exact prefixLift 5572209
  have htrace : WordTrace (prefixWord ++ tailWord_5572209) baseStart_5572209 baseEnd_5572209 := by
    simpa [prefixWord, tailWord_5572209, baseEnd_5572209] using wordTrace_append hprefix tailTrace_5572209
  have hstable : (prefixWord ++ tailWord_5572209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572209).length < 2 ^ (prefixWord ++ tailWord_5572209).sum := by decide
  have hdescent : baseEnd_5572209 < baseStart_5572209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572213 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5572213 : Nat := 118140960795 + 5572213 * 2 ^ 59
def prefixEnd_5572213 : Nat := 4983230072969 + 3 ^ 40 * 5572213 * 2
def baseEnd_5572213 : Nat := 953741192743904141570455

theorem tailTrace_5572213 : CollatzResearch.WordTrace tailWord_5572213 prefixEnd_5572213 953741192743904141570455 := by
  unfold tailWord_5572213
  simp only [CollatzResearch.WordTrace]
  refine ⟨203235304561831434060129293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135490203041220956040086195 203235304561831434060129293)
  ·
    refine ⟨76213239210686787772548485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203235304561831434060129293 76213239210686787772548485)
    ·
      refine ⟨14289982352003772707352841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76213239210686787772548485 14289982352003772707352841)
      ·
        refine ⟨10717486764002829530514631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14289982352003772707352841 10717486764002829530514631)
        ·
          refine ⟨16076230146004244295771947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10717486764002829530514631 16076230146004244295771947)
          ·
            refine ⟨24114345219006366443657921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16076230146004244295771947 24114345219006366443657921)
            ·
              refine ⟨18085758914254774832743441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24114345219006366443657921 18085758914254774832743441)
              ·
                refine ⟨13564319185691081124557581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18085758914254774832743441 13564319185691081124557581)
                ·
                  refine ⟨5086619694634155421709093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13564319185691081124557581 5086619694634155421709093)
                  ·
                    refine ⟨953741192743904141570455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086619694634155421709093 953741192743904141570455)
                    ·
                      rfl

theorem cell23_5572213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5572213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572213 prefixEnd_5572213 := by exact prefixLift 5572213
  have htrace : WordTrace (prefixWord ++ tailWord_5572213) baseStart_5572213 baseEnd_5572213 := by
    simpa [prefixWord, tailWord_5572213, baseEnd_5572213] using wordTrace_append hprefix tailTrace_5572213
  have hstable : (prefixWord ++ tailWord_5572213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572213).length < 2 ^ (prefixWord ++ tailWord_5572213).sum := by decide
  have hdescent : baseEnd_5572213 < baseStart_5572213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572219 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 3]
def baseStart_5572219 : Nat := 118140960795 + 5572219 * 2 ^ 59
def prefixEnd_5572219 : Nat := 4983230072969 + 3 ^ 40 * 5572219 * 2
def baseEnd_5572219 : Nat := 2861226659115639401236337

theorem tailTrace_5572219 : CollatzResearch.WordTrace tailWord_5572219 prefixEnd_5572219 2861226659115639401236337 := by
  unfold tailWord_5572219
  simp only [CollatzResearch.WordTrace]
  refine ⟨203235523399809697084847711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135490348933206464723231807 203235523399809697084847711)
  ·
    refine ⟨304853285099714545627271567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203235523399809697084847711 304853285099714545627271567)
    ·
      refine ⟨457279927649571818440907351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304853285099714545627271567 457279927649571818440907351)
      ·
        refine ⟨685919891474357727661361027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457279927649571818440907351 685919891474357727661361027)
        ·
          refine ⟨1028879837211536591492041541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685919891474357727661361027 1028879837211536591492041541)
          ·
            refine ⟨192914969477163110904757789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1028879837211536591492041541 192914969477163110904757789)
            ·
              refine ⟨72343113553936166589284171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192914969477163110904757789 72343113553936166589284171)
              ·
                refine ⟨108514670330904249883926257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72343113553936166589284171 108514670330904249883926257)
                ·
                  refine ⟨81386002748178187412944693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108514670330904249883926257 81386002748178187412944693)
                  ·
                    refine ⟨7629937757641705069963565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81386002748178187412944693 7629937757641705069963565)
                    ·
                      refine ⟨2861226659115639401236337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7629937757641705069963565 2861226659115639401236337)
                      ·
                        rfl

theorem cell23_5572219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 3].length) (baseStart_5572219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572219 prefixEnd_5572219 := by exact prefixLift 5572219
  have htrace : WordTrace (prefixWord ++ tailWord_5572219) baseStart_5572219 baseEnd_5572219 := by
    simpa [prefixWord, tailWord_5572219, baseEnd_5572219] using wordTrace_append hprefix tailTrace_5572219
  have hstable : (prefixWord ++ tailWord_5572219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572219).length < 2 ^ (prefixWord ++ tailWord_5572219).sum := by decide
  have hdescent : baseEnd_5572219 < baseStart_5572219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572286 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_5572286 : Nat := 118140960795 + 5572286 * 2 ^ 59
def prefixEnd_5572286 : Nat := 4983230072969 + 3 ^ 40 * 5572286 * 2
def baseEnd_5572286 : Nat := 953753687439830213032843

theorem tailTrace_5572286 : CollatzResearch.WordTrace tailWord_5572286 prefixEnd_5572286 953753687439830213032843 := by
  unfold tailWord_5572286
  simp only [CollatzResearch.WordTrace]
  refine ⟨25404745886320870940942089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135491978060377978351691141 25404745886320870940942089)
  ·
    refine ⟨19053559414740653205706567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25404745886320870940942089 19053559414740653205706567)
    ·
      refine ⟨28580339122110979808559851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19053559414740653205706567 28580339122110979808559851)
      ·
        refine ⟨42870508683166469712839777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28580339122110979808559851 42870508683166469712839777)
        ·
          refine ⟨32152881512374852284629833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42870508683166469712839777 32152881512374852284629833)
          ·
            refine ⟨24114661134281139213472375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32152881512374852284629833 24114661134281139213472375)
            ·
              refine ⟨36171991701421708820208563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24114661134281139213472375 36171991701421708820208563)
              ·
                refine ⟨54257987552132563230312845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36171991701421708820208563 54257987552132563230312845)
                ·
                  refine ⟨20346745332049711211367317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54257987552132563230312845 20346745332049711211367317)
                  ·
                    refine ⟨953753687439830213032843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20346745332049711211367317 953753687439830213032843)
                    ·
                      rfl

theorem cell23_5572286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_5572286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572286 prefixEnd_5572286 := by exact prefixLift 5572286
  have htrace : WordTrace (prefixWord ++ tailWord_5572286) baseStart_5572286 baseEnd_5572286 := by
    simpa [prefixWord, tailWord_5572286, baseEnd_5572286] using wordTrace_append hprefix tailTrace_5572286
  have hstable : (prefixWord ++ tailWord_5572286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572286).length < 2 ^ (prefixWord ++ tailWord_5572286).sum := by decide
  have hdescent : baseEnd_5572286 < baseStart_5572286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572293 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 5, 2, 2]
def baseStart_5572293 : Nat := 118140960795 + 5572293 * 2 ^ 59
def prefixEnd_5572293 : Nat := 4983230072969 + 3 ^ 40 * 5572293 * 2
def baseEnd_5572293 : Nat := 2861264656684072111710997

theorem tailTrace_5572293 : CollatzResearch.WordTrace tailWord_5572293 prefixEnd_5572293 2861264656684072111710997 := by
  unfold tailWord_5572293
  simp only [CollatzResearch.WordTrace]
  refine ⟨203238222401541607723041533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135492148267694405148694355 203238222401541607723041533)
  ·
    refine ⟨76214333400578102896140575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203238222401541607723041533 76214333400578102896140575)
    ·
      refine ⟨114321500100867154344210863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76214333400578102896140575 114321500100867154344210863)
      ·
        refine ⟨171482250151300731516316295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114321500100867154344210863 171482250151300731516316295)
        ·
          refine ⟨257223375226951097274474443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171482250151300731516316295 257223375226951097274474443)
          ·
            refine ⟨385835062840426645911711665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257223375226951097274474443 385835062840426645911711665)
            ·
              refine ⟨289376297130319984433783749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385835062840426645911711665 289376297130319984433783749)
              ·
                refine ⟨54258055711934997081334453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289376297130319984433783749 54258055711934997081334453)
                ·
                  refine ⟨5086692722993905976375105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54258055711934997081334453 5086692722993905976375105)
                  ·
                    refine ⟨3815019542245429482281329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5086692722993905976375105 3815019542245429482281329)
                    ·
                      refine ⟨2861264656684072111710997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815019542245429482281329 2861264656684072111710997)
                      ·
                        rfl

theorem cell23_5572293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_5572293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572293 prefixEnd_5572293 := by exact prefixLift 5572293
  have htrace : WordTrace (prefixWord ++ tailWord_5572293) baseStart_5572293 baseEnd_5572293 := by
    simpa [prefixWord, tailWord_5572293, baseEnd_5572293] using wordTrace_append hprefix tailTrace_5572293
  have hstable : (prefixWord ++ tailWord_5572293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572293).length < 2 ^ (prefixWord ++ tailWord_5572293).sum := by decide
  have hdescent : baseEnd_5572293 < baseStart_5572293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572329 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 4, 7]
def baseStart_5572329 : Nat := 118140960795 + 5572329 * 2 ^ 59
def prefixEnd_5572329 : Nat := 4983230072969 + 3 ^ 40 * 5572329 * 2
def baseEnd_5572329 : Nat := 953761047329211323620277

theorem tailTrace_5572329 : CollatzResearch.WordTrace tailWord_5572329 prefixEnd_5572329 953761047329211323620277 := by
  unfold tailWord_5572329
  simp only [CollatzResearch.WordTrace]
  refine ⟨203239535429411185871352041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135493023619607457247568027 203239535429411185871352041)
  ·
    refine ⟨152429651572058389403514031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203239535429411185871352041 152429651572058389403514031)
    ·
      refine ⟨228644477358087584105271047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152429651572058389403514031 228644477358087584105271047)
      ·
        refine ⟨342966716037131376157906571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228644477358087584105271047 342966716037131376157906571)
        ·
          refine ⟨514450074055697064236859857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342966716037131376157906571 514450074055697064236859857)
          ·
            refine ⟨385837555541772798177644893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514450074055697064236859857 385837555541772798177644893)
            ·
              refine ⟨144689083328164799316616835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385837555541772798177644893 144689083328164799316616835)
              ·
                refine ⟨217033624992247198974925253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144689083328164799316616835 217033624992247198974925253)
                ·
                  refine ⟨40693804686046349807798485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217033624992247198974925253 40693804686046349807798485)
                  ·
                    refine ⟨953761047329211323620277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40693804686046349807798485 953761047329211323620277)
                    ·
                      rfl

theorem cell23_5572329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_5572329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572329 prefixEnd_5572329 := by exact prefixLift 5572329
  have htrace : WordTrace (prefixWord ++ tailWord_5572329) baseStart_5572329 baseEnd_5572329 := by
    simpa [prefixWord, tailWord_5572329, baseEnd_5572329] using wordTrace_append hprefix tailTrace_5572329
  have hstable : (prefixWord ++ tailWord_5572329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572329).length < 2 ^ (prefixWord ++ tailWord_5572329).sum := by decide
  have hdescent : baseEnd_5572329 < baseStart_5572329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572333 : List Nat := [1, 5, 1, 2, 1, 3, 3, 7]
def baseStart_5572333 : Nat := 118140960795 + 5572333 * 2 ^ 59
def prefixEnd_5572333 : Nat := 4983230072969 + 3 ^ 40 * 5572333 * 2
def baseEnd_5572333 : Nat := 105973525774453776118919

theorem tailTrace_5572333 : CollatzResearch.WordTrace tailWord_5572333 prefixEnd_5572333 105973525774453776118919 := by
  unfold tailWord_5572333
  simp only [CollatzResearch.WordTrace]
  refine ⟨203239681321396694554497653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135493120880931129702998435 203239681321396694554497653)
  ·
    refine ⟨19053720123880940114484155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203239681321396694554497653 19053720123880940114484155)
    ·
      refine ⟨28580580185821410171726233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19053720123880940114484155 28580580185821410171726233)
      ·
        refine ⟨21435435139366057628794675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28580580185821410171726233 21435435139366057628794675)
        ·
          refine ⟨32153152709049086443192013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21435435139366057628794675 32153152709049086443192013)
          ·
            refine ⟨12057432265893407416197005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32153152709049086443192013 12057432265893407416197005)
            ·
              refine ⟨4521537099710027781073877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12057432265893407416197005 4521537099710027781073877)
              ·
                refine ⟨105973525774453776118919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4521537099710027781073877 105973525774453776118919)
                ·
                  rfl

theorem cell23_5572333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 7].length) (baseStart_5572333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572333 prefixEnd_5572333 := by exact prefixLift 5572333
  have htrace : WordTrace (prefixWord ++ tailWord_5572333) baseStart_5572333 baseEnd_5572333 := by
    simpa [prefixWord, tailWord_5572333, baseEnd_5572333] using wordTrace_append hprefix tailTrace_5572333
  have hstable : (prefixWord ++ tailWord_5572333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572333).length < 2 ^ (prefixWord ++ tailWord_5572333).sum := by decide
  have hdescent : baseEnd_5572333 < baseStart_5572333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572366 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5572366 : Nat := 118140960795 + 5572366 * 2 ^ 59
def prefixEnd_5572366 : Nat := 4983230072969 + 3 ^ 40 * 5572366 * 2
def baseEnd_5572366 : Nat := 2861302140771850326098161

theorem tailTrace_5572366 : CollatzResearch.WordTrace tailWord_5572366 prefixEnd_5572366 2861302140771850326098161 := by
  unfold tailWord_5572366
  simp only [CollatzResearch.WordTrace]
  refine ⟨25405110616284642648806119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135493923286851427460299301 25405110616284642648806119)
  ·
    refine ⟨38107665924426963973209179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25405110616284642648806119 38107665924426963973209179)
    ·
      refine ⟨57161498886640445959813769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38107665924426963973209179 57161498886640445959813769)
      ·
        refine ⟨42871124164980334469860327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57161498886640445959813769 42871124164980334469860327)
        ·
          refine ⟨64306686247470501704790491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42871124164980334469860327 64306686247470501704790491)
          ·
            refine ⟨96460029371205752557185737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64306686247470501704790491 96460029371205752557185737)
            ·
              refine ⟨72345022028404314417889303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96460029371205752557185737 72345022028404314417889303)
              ·
                refine ⟨108517533042606471626833955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72345022028404314417889303 108517533042606471626833955)
                ·
                  refine ⟨162776299563909707440250933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108517533042606471626833955 162776299563909707440250933)
                  ·
                    refine ⟨15260278084116535072523525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162776299563909707440250933 15260278084116535072523525)
                    ·
                      refine ⟨2861302140771850326098161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15260278084116535072523525 2861302140771850326098161)
                      ·
                        rfl

theorem cell23_5572366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5572366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572366 prefixEnd_5572366 := by exact prefixLift 5572366
  have htrace : WordTrace (prefixWord ++ tailWord_5572366) baseStart_5572366 baseEnd_5572366 := by
    simpa [prefixWord, tailWord_5572366, baseEnd_5572366] using wordTrace_append hprefix tailTrace_5572366
  have hstable : (prefixWord ++ tailWord_5572366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572366).length < 2 ^ (prefixWord ++ tailWord_5572366).sum := by decide
  have hdescent : baseEnd_5572366 < baseStart_5572366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572376 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 2, 6]
def baseStart_5572376 : Nat := 118140960795 + 5572376 * 2 ^ 59
def prefixEnd_5572376 : Nat := 4983230072969 + 3 ^ 40 * 5572376 * 2
def baseEnd_5572376 : Nat := 953769091859465095657705

theorem tailTrace_5572376 : CollatzResearch.WordTrace tailWord_5572376 prefixEnd_5572376 953769091859465095657705 := by
  unfold tailWord_5572376
  simp only [CollatzResearch.WordTrace]
  refine ⟨101620624830120456449156491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135494166440160608598875321 101620624830120456449156491)
  ·
    refine ⟨152430937245180684673734737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101620624830120456449156491 152430937245180684673734737)
    ·
      refine ⟨114323202933885513505301053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152430937245180684673734737 114323202933885513505301053)
      ·
        refine ⟨42871201100207067564487895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114323202933885513505301053 42871201100207067564487895)
        ·
          refine ⟨64306801650310601346731843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42871201100207067564487895 64306801650310601346731843)
          ·
            refine ⟨96460202475465902020097765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64306801650310601346731843 96460202475465902020097765)
            ·
              refine ⟨18086287964149856628768331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96460202475465902020097765 18086287964149856628768331)
              ·
                refine ⟨27129431946224784943152497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18086287964149856628768331 27129431946224784943152497)
                ·
                  refine ⟨20347073959668588707364373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27129431946224784943152497 20347073959668588707364373)
                  ·
                    refine ⟨953769091859465095657705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20347073959668588707364373 953769091859465095657705)
                    ·
                      rfl

theorem cell23_5572376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_5572376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572376 prefixEnd_5572376 := by exact prefixLift 5572376
  have htrace : WordTrace (prefixWord ++ tailWord_5572376) baseStart_5572376 baseEnd_5572376 := by
    simpa [prefixWord, tailWord_5572376, baseEnd_5572376] using wordTrace_append hprefix tailTrace_5572376
  have hstable : (prefixWord ++ tailWord_5572376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572376).length < 2 ^ (prefixWord ++ tailWord_5572376).sum := by decide
  have hdescent : baseEnd_5572376 < baseStart_5572376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572403 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 5]
def baseStart_5572403 : Nat := 118140960795 + 5572403 * 2 ^ 59
def prefixEnd_5572403 : Nat := 4983230072969 + 3 ^ 40 * 5572403 * 2
def baseEnd_5572403 : Nat := 2861321139556066681335491

theorem tailTrace_5572403 : CollatzResearch.WordTrace tailWord_5572403 prefixEnd_5572403 2861321139556066681335491 := by
  unfold tailWord_5572403
  simp only [CollatzResearch.WordTrace]
  refine ⟨203242234431143096509545863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135494822954095397673030575 203242234431143096509545863)
  ·
    refine ⟨304863351646714644764318795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203242234431143096509545863 304863351646714644764318795)
    ·
      refine ⟨457295027470071967146478193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304863351646714644764318795 457295027470071967146478193)
      ·
        refine ⟨342971270602553975359858645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457295027470071967146478193 342971270602553975359858645)
        ·
          refine ⟨8038389154747358797496687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 342971270602553975359858645 8038389154747358797496687)
          ·
            refine ⟨12057583732121038196245031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8038389154747358797496687 12057583732121038196245031)
            ·
              refine ⟨18086375598181557294367547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12057583732121038196245031 18086375598181557294367547)
              ·
                refine ⟨27129563397272335941551321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18086375598181557294367547 27129563397272335941551321)
                ·
                  refine ⟨20347172547954251956163491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27129563397272335941551321 20347172547954251956163491)
                  ·
                    refine ⟨30520758821931377934245237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20347172547954251956163491 30520758821931377934245237)
                    ·
                      refine ⟨2861321139556066681335491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30520758821931377934245237 2861321139556066681335491)
                      ·
                        rfl

theorem cell23_5572403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_5572403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572403 prefixEnd_5572403 := by exact prefixLift 5572403
  have htrace : WordTrace (prefixWord ++ tailWord_5572403) baseStart_5572403 baseEnd_5572403 := by
    simpa [prefixWord, tailWord_5572403, baseEnd_5572403] using wordTrace_append hprefix tailTrace_5572403
  have hstable : (prefixWord ++ tailWord_5572403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572403).length < 2 ^ (prefixWord ++ tailWord_5572403).sum := by decide
  have hdescent : baseEnd_5572403 < baseStart_5572403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572423 : List Nat := [1, 1, 4, 1, 2, 1, 2, 6, 5]
def baseStart_5572423 : Nat := 118140960795 + 5572423 * 2 ^ 59
def prefixEnd_5572423 : Nat := 4983230072969 + 3 ^ 40 * 5572423 * 2
def baseEnd_5572423 : Nat := 317925712129906289231711

theorem tailTrace_5572423 : CollatzResearch.WordTrace tailWord_5572423 prefixEnd_5572423 317925712129906289231711 := by
  unfold tailWord_5572423
  simp only [CollatzResearch.WordTrace]
  refine ⟨203242963891070639925273923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135495309260713759950182615 203242963891070639925273923)
  ·
    refine ⟨304864445836605959887910885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203242963891070639925273923 304864445836605959887910885)
    ·
      refine ⟨57162083594363617478983291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304864445836605959887910885 57162083594363617478983291)
      ·
        refine ⟨85743125391545426218474937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57162083594363617478983291 85743125391545426218474937)
        ·
          refine ⟨64307344043659069663856203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85743125391545426218474937 64307344043659069663856203)
          ·
            refine ⟨96461016065488604495784305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64307344043659069663856203 96461016065488604495784305)
            ·
              refine ⟨72345762049116453371838229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96461016065488604495784305 72345762049116453371838229)
              ·
                refine ⟨3391207596052333751804917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72345762049116453371838229 3391207596052333751804917)
                ·
                  refine ⟨317925712129906289231711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3391207596052333751804917 317925712129906289231711)
                  ·
                    rfl

theorem cell23_5572423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 5].length) (baseStart_5572423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572423 prefixEnd_5572423 := by exact prefixLift 5572423
  have htrace : WordTrace (prefixWord ++ tailWord_5572423) baseStart_5572423 baseEnd_5572423 := by
    simpa [prefixWord, tailWord_5572423, baseEnd_5572423] using wordTrace_append hprefix tailTrace_5572423
  have hstable : (prefixWord ++ tailWord_5572423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572423).length < 2 ^ (prefixWord ++ tailWord_5572423).sum := by decide
  have hdescent : baseEnd_5572423 < baseStart_5572423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572434 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_5572434 : Nat := 118140960795 + 5572434 * 2 ^ 59
def prefixEnd_5572434 : Nat := 4983230072969 + 3 ^ 40 * 5572434 * 2
def baseEnd_5572434 : Nat := 2861337057456356060047849

theorem tailTrace_5572434 : CollatzResearch.WordTrace tailWord_5572434 prefixEnd_5572434 2861337057456356060047849 := by
  unfold tailWord_5572434
  simp only [CollatzResearch.WordTrace]
  refine ⟨50810841273507697200981089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135495576729353859202616237 50810841273507697200981089)
  ·
    refine ⟨38108130955130772900735817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50810841273507697200981089 38108130955130772900735817)
    ·
      refine ⟨28581098216348079675551863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38108130955130772900735817 28581098216348079675551863)
      ·
        refine ⟨42871647324522119513327795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28581098216348079675551863 42871647324522119513327795)
        ·
          refine ⟨64307470986783179269991693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42871647324522119513327795 64307470986783179269991693)
          ·
            refine ⟨24115301620043692226246885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64307470986783179269991693 24115301620043692226246885)
            ·
              refine ⟨4521619053758192292421291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24115301620043692226246885 4521619053758192292421291)
              ·
                refine ⟨6782428580637288438631937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4521619053758192292421291 6782428580637288438631937)
                ·
                  refine ⟨5086821435477966328973953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6782428580637288438631937 5086821435477966328973953)
                  ·
                    refine ⟨3815116076608474746730465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5086821435477966328973953 3815116076608474746730465)
                    ·
                      refine ⟨2861337057456356060047849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815116076608474746730465 2861337057456356060047849)
                      ·
                        rfl

theorem cell23_5572434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_5572434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572434 prefixEnd_5572434 := by exact prefixLift 5572434
  have htrace : WordTrace (prefixWord ++ tailWord_5572434) baseStart_5572434 baseEnd_5572434 := by
    simpa [prefixWord, tailWord_5572434, baseEnd_5572434] using wordTrace_append hprefix tailTrace_5572434
  have hstable : (prefixWord ++ tailWord_5572434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572434).length < 2 ^ (prefixWord ++ tailWord_5572434).sum := by decide
  have hdescent : baseEnd_5572434 < baseStart_5572434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572473 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_5572473 : Nat := 118140960795 + 5572473 * 2 ^ 59
def prefixEnd_5572473 : Nat := 4983230072969 + 3 ^ 40 * 5572473 * 2
def baseEnd_5572473 : Nat := 2861357083201881407460169

theorem tailTrace_5572473 : CollatzResearch.WordTrace tailWord_5572473 prefixEnd_5572473 2861357083201881407460169 := by
  unfold tailWord_5572473
  simp only [CollatzResearch.WordTrace]
  refine ⟨203244787540889498464594073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135496525027259665643062715 203244787540889498464594073)
  ·
    refine ⟨152433590655667123848445555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203244787540889498464594073 152433590655667123848445555)
    ·
      refine ⟨228650385983500685772668333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152433590655667123848445555 228650385983500685772668333)
      ·
        refine ⟨85743894743812757164750625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228650385983500685772668333 85743894743812757164750625)
        ·
          refine ⟨64307921057859567873562969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85743894743812757164750625 64307921057859567873562969)
          ·
            refine ⟨48230940793394675905172227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64307921057859567873562969 48230940793394675905172227)
            ·
              refine ⟨72346411190092013857758341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48230940793394675905172227 72346411190092013857758341)
              ·
                refine ⟨13564952098142252598329689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72346411190092013857758341 13564952098142252598329689)
                ·
                  refine ⟨10173714073606689448747267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13564952098142252598329689 10173714073606689448747267)
                  ·
                    refine ⟨15260571110410034173120901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10173714073606689448747267 15260571110410034173120901)
                    ·
                      refine ⟨2861357083201881407460169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15260571110410034173120901 2861357083201881407460169)
                      ·
                        rfl

theorem cell23_5572473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_5572473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572473 prefixEnd_5572473 := by exact prefixLift 5572473
  have htrace : WordTrace (prefixWord ++ tailWord_5572473) baseStart_5572473 baseEnd_5572473 := by
    simpa [prefixWord, tailWord_5572473, baseEnd_5572473] using wordTrace_append hprefix tailTrace_5572473
  have hstable : (prefixWord ++ tailWord_5572473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572473).length < 2 ^ (prefixWord ++ tailWord_5572473).sum := by decide
  have hdescent : baseEnd_5572473 < baseStart_5572473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572500 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5572500 : Nat := 118140960795 + 5572500 * 2 ^ 59
def prefixEnd_5572500 : Nat := 4983230072969 + 3 ^ 40 * 5572500 * 2
def baseEnd_5572500 : Nat := 953790315726517600607515

theorem tailTrace_5572500 : CollatzResearch.WordTrace tailWord_5572500 prefixEnd_5572500 953790315726517600607515 := by
  unfold tailWord_5572500
  simp only [CollatzResearch.WordTrace]
  refine ⟨101622886155895841037913477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135497181541194454717217969 101622886155895841037913477)
  ·
    refine ⟨19054291154230470194608777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101622886155895841037913477 19054291154230470194608777)
    ·
      refine ⟨14290718365672852645956583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19054291154230470194608777 14290718365672852645956583)
      ·
        refine ⟨21436077548509278968934875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14290718365672852645956583 21436077548509278968934875)
        ·
          refine ⟨32154116322763918453402313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21436077548509278968934875 32154116322763918453402313)
          ·
            refine ⟨24115587242072938840051735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32154116322763918453402313 24115587242072938840051735)
            ·
              refine ⟨36173380863109408260077603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24115587242072938840051735 36173380863109408260077603)
              ·
                refine ⟨54260071294664112390116405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36173380863109408260077603 54260071294664112390116405)
                ·
                  refine ⟨5086881683874760536573413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54260071294664112390116405 5086881683874760536573413)
                  ·
                    refine ⟨953790315726517600607515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086881683874760536573413 953790315726517600607515)
                    ·
                      rfl

theorem cell23_5572500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5572500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572500 prefixEnd_5572500 := by exact prefixLift 5572500
  have htrace : WordTrace (prefixWord ++ tailWord_5572500) baseStart_5572500 baseEnd_5572500 := by
    simpa [prefixWord, tailWord_5572500, baseEnd_5572500] using wordTrace_append hprefix tailTrace_5572500
  have hstable : (prefixWord ++ tailWord_5572500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572500).length < 2 ^ (prefixWord ++ tailWord_5572500).sum := by decide
  have hdescent : baseEnd_5572500 < baseStart_5572500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572504 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 2, 5]
def baseStart_5572504 : Nat := 118140960795 + 5572504 * 2 ^ 59
def prefixEnd_5572504 : Nat := 4983230072969 + 3 ^ 40 * 5572504 * 2
def baseEnd_5572504 : Nat := 953791000367390262057509

theorem tailTrace_5572504 : CollatzResearch.WordTrace tailWord_5572504 prefixEnd_5572504 953791000367390262057509 := by
  unfold tailWord_5572504
  simp only [CollatzResearch.WordTrace]
  refine ⟨101622959101888595379486283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135497278802518127172648377 101622959101888595379486283)
  ·
    refine ⟨152434438652832893069229425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101622959101888595379486283 152434438652832893069229425)
    ·
      refine ⟨114325828989624669801922069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152434438652832893069229425 114325828989624669801922069)
      ·
        refine ⟨5359023233888656396965097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114325828989624669801922069 5359023233888656396965097)
        ·
          refine ⟨4019267425416492297723823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5359023233888656396965097 4019267425416492297723823)
          ·
            refine ⟨6028901138124738446585735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019267425416492297723823 6028901138124738446585735)
            ·
              refine ⟨9043351707187107669878603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6028901138124738446585735 9043351707187107669878603)
              ·
                refine ⟨13565027560780661504817905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9043351707187107669878603 13565027560780661504817905)
                ·
                  refine ⟨10173770670585496128613429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13565027560780661504817905 10173770670585496128613429)
                  ·
                    refine ⟨953791000367390262057509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10173770670585496128613429 953791000367390262057509)
                    ·
                      rfl

theorem cell23_5572504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_5572504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572504 prefixEnd_5572504 := by exact prefixLift 5572504
  have htrace : WordTrace (prefixWord ++ tailWord_5572504) baseStart_5572504 baseEnd_5572504 := by
    simpa [prefixWord, tailWord_5572504, baseEnd_5572504] using wordTrace_append hprefix tailTrace_5572504
  have hstable : (prefixWord ++ tailWord_5572504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572504).length < 2 ^ (prefixWord ++ tailWord_5572504).sum := by decide
  have hdescent : baseEnd_5572504 < baseStart_5572504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572533 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5572533 : Nat := 118140960795 + 5572533 * 2 ^ 59
def prefixEnd_5572533 : Nat := 4983230072969 + 3 ^ 40 * 5572533 * 2
def baseEnd_5572533 : Nat := 2861387892041151172709893

theorem tailTrace_5572533 : CollatzResearch.WordTrace tailWord_5572533 prefixEnd_5572533 2861387892041151172709893 := by
  unfold tailWord_5572533
  simp only [CollatzResearch.WordTrace]
  refine ⟨203246975920672128711778253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135497983947114752474518835 203246975920672128711778253)
  ·
    refine ⟨76217615970252048266916845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203246975920672128711778253 76217615970252048266916845)
    ·
      refine ⟨28581605988844518100093817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76217615970252048266916845 28581605988844518100093817)
      ·
        refine ⟨21436204491633388575070363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28581605988844518100093817 21436204491633388575070363)
        ·
          refine ⟨32154306737450082862605545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21436204491633388575070363 32154306737450082862605545)
          ·
            refine ⟨24115730053087562146954159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32154306737450082862605545 24115730053087562146954159)
            ·
              refine ⟨36173595079631343220431239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24115730053087562146954159 36173595079631343220431239)
              ·
                refine ⟨54260392619447014830646859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36173595079631343220431239 54260392619447014830646859)
                ·
                  refine ⟨81390588929170522245970289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54260392619447014830646859 81390588929170522245970289)
                  ·
                    refine ⟨61042941696877891684477717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81390588929170522245970289 61042941696877891684477717)
                    ·
                      refine ⟨2861387892041151172709893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61042941696877891684477717 2861387892041151172709893)
                      ·
                        rfl

theorem cell23_5572533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5572533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572533 prefixEnd_5572533 := by exact prefixLift 5572533
  have htrace : WordTrace (prefixWord ++ tailWord_5572533) baseStart_5572533 baseEnd_5572533 := by
    simpa [prefixWord, tailWord_5572533, baseEnd_5572533] using wordTrace_append hprefix tailTrace_5572533
  have hstable : (prefixWord ++ tailWord_5572533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572533).length < 2 ^ (prefixWord ++ tailWord_5572533).sum := by decide
  have hdescent : baseEnd_5572533 < baseStart_5572533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572580 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_5572580 : Nat := 118140960795 + 5572580 * 2 ^ 59
def prefixEnd_5572580 : Nat := 4983230072969 + 3 ^ 40 * 5572580 * 2
def baseEnd_5572580 : Nat := 2861412025631912488822177

theorem tailTrace_5572580 : CollatzResearch.WordTrace tailWord_5572580 prefixEnd_5572580 2861412025631912488822177 := by
  unfold tailWord_5572580
  simp only [CollatzResearch.WordTrace]
  refine ⟨101624345075750927869369597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135499126767667903825826129 101624345075750927869369597)
  ·
    refine ⟨38109129403406597951013599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101624345075750927869369597 38109129403406597951013599)
    ·
      refine ⟨57163694105109896926520399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38109129403406597951013599 57163694105109896926520399)
      ·
        refine ⟨85745541157664845389780599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57163694105109896926520399 85745541157664845389780599)
        ·
          refine ⟨128618311736497268084670899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85745541157664845389780599 128618311736497268084670899)
          ·
            refine ⟨192927467604745902127006349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128618311736497268084670899 192927467604745902127006349)
            ·
              refine ⟨72347800351779713297627381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192927467604745902127006349 72347800351779713297627381)
              ·
                refine ⟨6782606282979348121652567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72347800351779713297627381 6782606282979348121652567)
                ·
                  refine ⟨10173909424469022182478851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6782606282979348121652567 10173909424469022182478851)
                  ·
                    refine ⟨15260864136703533273718277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10173909424469022182478851 15260864136703533273718277)
                    ·
                      refine ⟨2861412025631912488822177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15260864136703533273718277 2861412025631912488822177)
                      ·
                        rfl

theorem cell23_5572580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_5572580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572580 prefixEnd_5572580 := by exact prefixLift 5572580
  have htrace : WordTrace (prefixWord ++ tailWord_5572580) baseStart_5572580 baseEnd_5572580 := by
    simpa [prefixWord, tailWord_5572580, baseEnd_5572580] using wordTrace_append hprefix tailTrace_5572580
  have hstable : (prefixWord ++ tailWord_5572580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572580).length < 2 ^ (prefixWord ++ tailWord_5572580).sum := by decide
  have hdescent : baseEnd_5572580 < baseStart_5572580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572634 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3]
def baseStart_5572634 : Nat := 118140960795 + 5572634 * 2 ^ 59
def prefixEnd_5572634 : Nat := 4983230072969 + 3 ^ 40 * 5572634 * 2
def baseEnd_5572634 : Nat := 2861439753587255277546929

theorem tailTrace_5572634 : CollatzResearch.WordTrace tailWord_5572634 prefixEnd_5572634 2861439753587255277546929 := by
  unfold tailWord_5572634
  simp only [CollatzResearch.WordTrace]
  refine ⟨50812664923326555740301239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135500439795537481974136637 50812664923326555740301239)
  ·
    refine ⟨76218997384989833610451859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50812664923326555740301239 76218997384989833610451859)
    ·
      refine ⟨114328496077484750415677789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76218997384989833610451859 114328496077484750415677789)
      ·
        refine ⟨42873186029056781405879171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114328496077484750415677789 42873186029056781405879171)
        ·
          refine ⟨64309779043585172108818757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42873186029056781405879171 64309779043585172108818757)
          ·
            refine ⟨12058083570672219770403517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64309779043585172108818757 12058083570672219770403517)
            ·
              refine ⟨4521781339002082413901319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12058083570672219770403517 4521781339002082413901319)
              ·
                refine ⟨6782672008503123620851979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4521781339002082413901319 6782672008503123620851979)
                ·
                  refine ⟨10174008012754685431277969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6782672008503123620851979 10174008012754685431277969)
                  ·
                    refine ⟨7630506009566014073458477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10174008012754685431277969 7630506009566014073458477)
                    ·
                      refine ⟨2861439753587255277546929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7630506009566014073458477 2861439753587255277546929)
                      ·
                        rfl

theorem cell23_5572634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_5572634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572634 prefixEnd_5572634 := by exact prefixLift 5572634
  have htrace : WordTrace (prefixWord ++ tailWord_5572634) baseStart_5572634 baseEnd_5572634 := by
    simpa [prefixWord, tailWord_5572634, baseEnd_5572634] using wordTrace_append hprefix tailTrace_5572634
  have hstable : (prefixWord ++ tailWord_5572634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572634).length < 2 ^ (prefixWord ++ tailWord_5572634).sum := by decide
  have hdescent : baseEnd_5572634 < baseStart_5572634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572650 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_5572650 : Nat := 118140960795 + 5572650 * 2 ^ 59
def prefixEnd_5572650 : Nat := 4983230072969 + 3 ^ 40 * 5572650 * 2
def baseEnd_5572650 : Nat := 953815989759242404982285

theorem tailTrace_5572650 : CollatzResearch.WordTrace tailWord_5572650 prefixEnd_5572650 953815989759242404982285 := by
  unfold tailWord_5572650
  simp only [CollatzResearch.WordTrace]
  refine ⟨50812810815312064423446851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135500828840832171795858269 50812810815312064423446851)
  ·
    refine ⟨76219216222968096635170277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50812810815312064423446851 76219216222968096635170277)
    ·
      refine ⟨14291103041806518119094427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76219216222968096635170277 14291103041806518119094427)
      ·
        refine ⟨21436654562709777178641641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14291103041806518119094427 21436654562709777178641641)
        ·
          refine ⟨16077490922032332883981231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21436654562709777178641641 16077490922032332883981231)
          ·
            refine ⟨24116236383048499325971847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16077490922032332883981231 24116236383048499325971847)
            ·
              refine ⟨36174354574572748988957771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24116236383048499325971847 36174354574572748988957771)
              ·
                refine ⟨54261531861859123483436657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36174354574572748988957771 54261531861859123483436657)
                ·
                  refine ⟨40696148896394342612577493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54261531861859123483436657 40696148896394342612577493)
                  ·
                    refine ⟨953815989759242404982285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40696148896394342612577493 953815989759242404982285)
                    ·
                      rfl

theorem cell23_5572650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_5572650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572650 prefixEnd_5572650 := by exact prefixLift 5572650
  have htrace : WordTrace (prefixWord ++ tailWord_5572650) baseStart_5572650 baseEnd_5572650 := by
    simpa [prefixWord, tailWord_5572650, baseEnd_5572650] using wordTrace_append hprefix tailTrace_5572650
  have hstable : (prefixWord ++ tailWord_5572650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572650).length < 2 ^ (prefixWord ++ tailWord_5572650).sum := by decide
  have hdescent : baseEnd_5572650 < baseStart_5572650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572657 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 3, 3, 2]
def baseStart_5572657 : Nat := 118140960795 + 5572657 * 2 ^ 59
def prefixEnd_5572657 : Nat := 4983230072969 + 3 ^ 40 * 5572657 * 2
def baseEnd_5572657 : Nat := 2861451563642308687559323

theorem tailTrace_5572657 : CollatzResearch.WordTrace tailWord_5572657 prefixEnd_5572657 2861451563642308687559323 := by
  unfold tailWord_5572657
  simp only [CollatzResearch.WordTrace]
  refine ⟨203251498572222897889292225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135500999048148598592861483 203251498572222897889292225)
  ·
    refine ⟨152438623929167173416969169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203251498572222897889292225 152438623929167173416969169)
    ·
      refine ⟨114328967946875380062726877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152438623929167173416969169 114328967946875380062726877)
      ·
        refine ⟨42873362980078267523522579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114328967946875380062726877 42873362980078267523522579)
        ·
          refine ⟨64310044470117401285283869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42873362980078267523522579 64310044470117401285283869)
          ·
            refine ⟨24116266676294025481981451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64310044470117401285283869 24116266676294025481981451)
            ·
              refine ⟨36174400014441038222972177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24116266676294025481981451 36174400014441038222972177)
              ·
                refine ⟨27130800010830778667229133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36174400014441038222972177 27130800010830778667229133)
                ·
                  refine ⟨10174050004061542000210925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27130800010830778667229133 10174050004061542000210925)
                  ·
                    refine ⟨3815268751523078250079097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10174050004061542000210925 3815268751523078250079097)
                    ·
                      refine ⟨2861451563642308687559323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815268751523078250079097 2861451563642308687559323)
                      ·
                        rfl

theorem cell23_5572657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_5572657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572657 prefixEnd_5572657 := by exact prefixLift 5572657
  have htrace : WordTrace (prefixWord ++ tailWord_5572657) baseStart_5572657 baseEnd_5572657 := by
    simpa [prefixWord, tailWord_5572657, baseEnd_5572657] using wordTrace_append hprefix tailTrace_5572657
  have hstable : (prefixWord ++ tailWord_5572657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572657).length < 2 ^ (prefixWord ++ tailWord_5572657).sum := by decide
  have hdescent : baseEnd_5572657 < baseStart_5572657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572663 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 1, 8]
def baseStart_5572663 : Nat := 118140960795 + 5572663 * 2 ^ 59
def prefixEnd_5572663 : Nat := 4983230072969 + 3 ^ 40 * 5572663 * 2
def baseEnd_5572663 : Nat := 953818214842078554694765

theorem tailTrace_5572663 : CollatzResearch.WordTrace tailWord_5572663 prefixEnd_5572663 953818214842078554694765 := by
  unfold tailWord_5572663
  simp only [CollatzResearch.WordTrace]
  refine ⟨203251717410201160914010643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135501144940134107276007095 203251717410201160914010643)
  ·
    refine ⟨304877576115301741371015965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203251717410201160914010643 304877576115301741371015965)
    ·
      refine ⟨114329091043238153014130987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304877576115301741371015965 114329091043238153014130987)
      ·
        refine ⟨171493636564857229521196481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114329091043238153014130987 171493636564857229521196481)
        ·
          refine ⟨128620227423642922140897361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171493636564857229521196481 128620227423642922140897361)
          ·
            refine ⟨96465170567732191605673021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128620227423642922140897361 96465170567732191605673021)
            ·
              refine ⟨36174438962899571852127383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96465170567732191605673021 36174438962899571852127383)
              ·
                refine ⟨54261658444349357778191075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36174438962899571852127383 54261658444349357778191075)
                ·
                  refine ⟨81392487666524036667286613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54261658444349357778191075 81392487666524036667286613)
                  ·
                    refine ⟨953818214842078554694765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81392487666524036667286613 953818214842078554694765)
                    ·
                      rfl

theorem cell23_5572663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_5572663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572663 prefixEnd_5572663 := by exact prefixLift 5572663
  have htrace : WordTrace (prefixWord ++ tailWord_5572663) baseStart_5572663 baseEnd_5572663 := by
    simpa [prefixWord, tailWord_5572663, baseEnd_5572663] using wordTrace_append hprefix tailTrace_5572663
  have hstable : (prefixWord ++ tailWord_5572663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572663).length < 2 ^ (prefixWord ++ tailWord_5572663).sum := by decide
  have hdescent : baseEnd_5572663 < baseStart_5572663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572687 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 6, 2, 2]
def baseStart_5572687 : Nat := 118140960795 + 5572687 * 2 ^ 59
def prefixEnd_5572687 : Nat := 4983230072969 + 3 ^ 40 * 5572687 * 2
def baseEnd_5572687 : Nat := 2861466968061943570184185

theorem tailTrace_5572687 : CollatzResearch.WordTrace tailWord_5572687 prefixEnd_5572687 2861466968061943570184185 := by
  unfold tailWord_5572687
  simp only [CollatzResearch.WordTrace]
  refine ⟨203252592762114213012884315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135501728508076142008589543 203252592762114213012884315)
  ·
    refine ⟨304878889143171319519326473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203252592762114213012884315 304878889143171319519326473)
    ·
      refine ⟨228659166857378489639494855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304878889143171319519326473 228659166857378489639494855)
      ·
        refine ⟨342988750286067734459242283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228659166857378489639494855 342988750286067734459242283)
        ·
          refine ⟨514483125429101601688863425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342988750286067734459242283 514483125429101601688863425)
          ·
            refine ⟨385862344071826201266647569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514483125429101601688863425 385862344071826201266647569)
            ·
              refine ⟨289396758053869650949985677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385862344071826201266647569 289396758053869650949985677)
              ·
                refine ⟨108523784270201119106244629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289396758053869650949985677 108523784270201119106244629)
                ·
                  refine ⟨5087052387665677458105217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108523784270201119106244629 5087052387665677458105217)
                  ·
                    refine ⟨3815289290749258093578913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5087052387665677458105217 3815289290749258093578913)
                    ·
                      refine ⟨2861466968061943570184185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815289290749258093578913 2861466968061943570184185)
                      ·
                        rfl

theorem cell23_5572687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 2, 2].length) (baseStart_5572687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572687 prefixEnd_5572687 := by exact prefixLift 5572687
  have htrace : WordTrace (prefixWord ++ tailWord_5572687) baseStart_5572687 baseEnd_5572687 := by
    simpa [prefixWord, tailWord_5572687, baseEnd_5572687] using wordTrace_append hprefix tailTrace_5572687
  have hstable : (prefixWord ++ tailWord_5572687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572687).length < 2 ^ (prefixWord ++ tailWord_5572687).sum := by decide
  have hdescent : baseEnd_5572687 < baseStart_5572687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572703 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_5572703 : Nat := 118140960795 + 5572703 * 2 ^ 59
def prefixEnd_5572703 : Nat := 4983230072969 + 3 ^ 40 * 5572703 * 2
def baseEnd_5572703 : Nat := 2861475183752415507584111

theorem tailTrace_5572703 : CollatzResearch.WordTrace tailWord_5572703 prefixEnd_5572703 2861475183752415507584111 := by
  unfold tailWord_5572703
  simp only [CollatzResearch.WordTrace]
  refine ⟨203253176330056247745466763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135502117553370831830311175 203253176330056247745466763)
  ·
    refine ⟨304879764495084371618200145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203253176330056247745466763 304879764495084371618200145)
    ·
      refine ⟨228659823371313278713650109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304879764495084371618200145 228659823371313278713650109)
      ·
        refine ⟨85747433764242479517618791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228659823371313278713650109 85747433764242479517618791)
        ·
          refine ⟨128621150646363719276428187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85747433764242479517618791 128621150646363719276428187)
          ·
            refine ⟨192931725969545578914642281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128621150646363719276428187 192931725969545578914642281)
            ·
              refine ⟨144698794477159184185981711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192931725969545578914642281 144698794477159184185981711)
              ·
                refine ⟨217048191715738776278972567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144698794477159184185981711 217048191715738776278972567)
                ·
                  refine ⟨325572287573608164418458851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217048191715738776278972567 325572287573608164418458851)
                  ·
                    refine ⟨488358431360412246627688277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 325572287573608164418458851 488358431360412246627688277)
                    ·
                      refine ⟨2861475183752415507584111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 488358431360412246627688277 2861475183752415507584111)
                      ·
                        rfl

theorem cell23_5572703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_5572703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572703 prefixEnd_5572703 := by exact prefixLift 5572703
  have htrace : WordTrace (prefixWord ++ tailWord_5572703) baseStart_5572703 baseEnd_5572703 := by
    simpa [prefixWord, tailWord_5572703, baseEnd_5572703] using wordTrace_append hprefix tailTrace_5572703
  have hstable : (prefixWord ++ tailWord_5572703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572703).length < 2 ^ (prefixWord ++ tailWord_5572703).sum := by decide
  have hdescent : baseEnd_5572703 < baseStart_5572703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572704 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 4, 2, 2]
def baseStart_5572704 : Nat := 118140960795 + 5572704 * 2 ^ 59
def prefixEnd_5572704 : Nat := 4983230072969 + 3 ^ 40 * 5572704 * 2
def baseEnd_5572704 : Nat := 2861475697233070003671607

theorem tailTrace_5572704 : CollatzResearch.WordTrace tailWord_5572704 prefixEnd_5572704 2861475697233070003671607 := by
  unfold tailWord_5572704
  simp only [CollatzResearch.WordTrace]
  refine ⟨101626606401526312458126583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135502141868701749944168777 101626606401526312458126583)
  ·
    refine ⟨152439909602289468687189875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101626606401526312458126583 152439909602289468687189875)
    ·
      refine ⟨228659864403434203030784813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152439909602289468687189875 228659864403434203030784813)
      ·
        refine ⟨85747449151287826136544305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228659864403434203030784813 85747449151287826136544305)
        ·
          refine ⟨64310586863465869602408229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85747449151287826136544305 64310586863465869602408229)
          ·
            refine ⟨12058235036899850550451543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64310586863465869602408229 12058235036899850550451543)
            ·
              refine ⟨18087352555349775825677315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12058235036899850550451543 18087352555349775825677315)
              ·
                refine ⟨27131028833024663738515973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18087352555349775825677315 27131028833024663738515973)
                ·
                  refine ⟨5087067906192124450971745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27131028833024663738515973 5087067906192124450971745)
                  ·
                    refine ⟨3815300929644093338228809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5087067906192124450971745 3815300929644093338228809)
                    ·
                      refine ⟨2861475697233070003671607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815300929644093338228809 2861475697233070003671607)
                      ·
                        rfl

theorem cell23_5572704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_5572704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572704 prefixEnd_5572704 := by exact prefixLift 5572704
  have htrace : WordTrace (prefixWord ++ tailWord_5572704) baseStart_5572704 baseEnd_5572704 := by
    simpa [prefixWord, tailWord_5572704, baseEnd_5572704] using wordTrace_append hprefix tailTrace_5572704
  have hstable : (prefixWord ++ tailWord_5572704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572704).length < 2 ^ (prefixWord ++ tailWord_5572704).sum := by decide
  have hdescent : baseEnd_5572704 < baseStart_5572704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572721 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 2, 2, 2]
def baseStart_5572721 : Nat := 118140960795 + 5572721 * 2 ^ 59
def prefixEnd_5572721 : Nat := 4983230072969 + 3 ^ 40 * 5572721 * 2
def baseEnd_5572721 : Nat := 2861484426404196437159029

theorem tailTrace_5572721 : CollatzResearch.WordTrace tailWord_5572721 prefixEnd_5572721 2861484426404196437159029 := by
  unfold tailWord_5572721
  simp only [CollatzResearch.WordTrace]
  refine ⟨203253832843991036819622017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135502555229327357879748011 203253832843991036819622017)
  ·
    refine ⟨152440374632993277614716513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203253832843991036819622017 152440374632993277614716513)
    ·
      refine ⟨114330280974744958211037385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152440374632993277614716513 114330280974744958211037385)
      ·
        refine ⟨85747710731058718658278039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114330280974744958211037385 85747710731058718658278039)
        ·
          refine ⟨128621566096588077987417059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85747710731058718658278039 128621566096588077987417059)
          ·
            refine ⟨192932349144882116981125589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128621566096588077987417059 192932349144882116981125589)
            ·
              refine ⟨4521851933083174616745131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 192932349144882116981125589 4521851933083174616745131)
              ·
                refine ⟨6782777899624761925117697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4521851933083174616745131 6782777899624761925117697)
                ·
                  refine ⟨5087083424718571443838273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6782777899624761925117697 5087083424718571443838273)
                  ·
                    refine ⟨3815312568538928582878705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5087083424718571443838273 3815312568538928582878705)
                    ·
                      refine ⟨2861484426404196437159029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815312568538928582878705 2861484426404196437159029)
                      ·
                        rfl

theorem cell23_5572721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_5572721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572721 prefixEnd_5572721 := by exact prefixLift 5572721
  have htrace : WordTrace (prefixWord ++ tailWord_5572721) baseStart_5572721 baseEnd_5572721 := by
    simpa [prefixWord, tailWord_5572721, baseEnd_5572721] using wordTrace_append hprefix tailTrace_5572721
  have hstable : (prefixWord ++ tailWord_5572721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572721).length < 2 ^ (prefixWord ++ tailWord_5572721).sum := by decide
  have hdescent : baseEnd_5572721 < baseStart_5572721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572740 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_5572740 : Nat := 118140960795 + 5572740 * 2 ^ 59
def prefixEnd_5572740 : Nat := 4983230072969 + 3 ^ 40 * 5572740 * 2
def baseEnd_5572740 : Nat := 953831394178877287607147

theorem tailTrace_5572740 : CollatzResearch.WordTrace tailWord_5572740 prefixEnd_5572740 953831394178877287607147 := by
  unfold tailWord_5572740
  simp only [CollatzResearch.WordTrace]
  refine ⟨101627262915461101532281837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135503017220614802043042449 101627262915461101532281837)
  ·
    refine ⟨38110223593297913074605689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101627262915461101532281837 38110223593297913074605689)
    ·
      refine ⟨28582667694973434805954267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38110223593297913074605689 28582667694973434805954267)
      ·
        refine ⟨42874001542460152208931401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28582667694973434805954267 42874001542460152208931401)
        ·
          refine ⟨32155501156845114156698551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42874001542460152208931401 32155501156845114156698551)
          ·
            refine ⟨48233251735267671235047827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32155501156845114156698551 48233251735267671235047827)
            ·
              refine ⟨72349877602901506852571741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48233251735267671235047827 72349877602901506852571741)
              ·
                refine ⟨27131204101088065069714403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72349877602901506852571741 27131204101088065069714403)
                ·
                  refine ⟨40696806151632097604571605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27131204101088065069714403 40696806151632097604571605)
                  ·
                    refine ⟨953831394178877287607147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40696806151632097604571605 953831394178877287607147)
                    ·
                      rfl

theorem cell23_5572740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_5572740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572740 prefixEnd_5572740 := by exact prefixLift 5572740
  have htrace : WordTrace (prefixWord ++ tailWord_5572740) baseStart_5572740 baseEnd_5572740 := by
    simpa [prefixWord, tailWord_5572740, baseEnd_5572740] using wordTrace_append hprefix tailTrace_5572740
  have hstable : (prefixWord ++ tailWord_5572740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572740).length < 2 ^ (prefixWord ++ tailWord_5572740).sum := by decide
  have hdescent : baseEnd_5572740 < baseStart_5572740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572744 : List Nat := [2, 1, 3, 4, 1, 1, 3, 3, 5]
def baseStart_5572744 : Nat := 118140960795 + 5572744 * 2 ^ 59
def prefixEnd_5572744 : Nat := 4983230072969 + 3 ^ 40 * 5572744 * 2
def baseEnd_5572744 : Nat := 317944026273249983019047

theorem tailTrace_5572744 : CollatzResearch.WordTrace tailWord_5572744 prefixEnd_5572744 317944026273249983019047 := by
  unfold tailWord_5572744
  simp only [CollatzResearch.WordTrace]
  refine ⟨101627335861453855873854643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135503114481938474498472857 101627335861453855873854643)
  ·
    refine ⟨152441003792180783810781965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101627335861453855873854643 152441003792180783810781965)
    ·
      refine ⟨57165376422067793929043237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152441003792180783810781965 57165376422067793929043237)
      ·
        refine ⟨10718508079137711361695607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57165376422067793929043237 10718508079137711361695607)
        ·
          refine ⟨16077762118706567042543411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10718508079137711361695607 16077762118706567042543411)
          ·
            refine ⟨24116643178059850563815117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16077762118706567042543411 24116643178059850563815117)
            ·
              refine ⟨9043741191772443961430669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24116643178059850563815117 9043741191772443961430669)
              ·
                refine ⟨3391402946914666485536501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9043741191772443961430669 3391402946914666485536501)
                ·
                  refine ⟨317944026273249983019047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3391402946914666485536501 317944026273249983019047)
                  ·
                    rfl

theorem cell23_5572744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 5].length) (baseStart_5572744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572744 prefixEnd_5572744 := by exact prefixLift 5572744
  have htrace : WordTrace (prefixWord ++ tailWord_5572744) baseStart_5572744 baseEnd_5572744 := by
    simpa [prefixWord, tailWord_5572744, baseEnd_5572744] using wordTrace_append hprefix tailTrace_5572744
  have hstable : (prefixWord ++ tailWord_5572744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572744).length < 2 ^ (prefixWord ++ tailWord_5572744).sum := by decide
  have hdescent : baseEnd_5572744 < baseStart_5572744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572767 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5572767 : Nat := 118140960795 + 5572767 * 2 ^ 59
def prefixEnd_5572767 : Nat := 4983230072969 + 3 ^ 40 * 5572767 * 2
def baseEnd_5572767 : Nat := 2861508046514303257183817

theorem tailTrace_5572767 : CollatzResearch.WordTrace tailWord_5572767 prefixEnd_5572767 2861508046514303257183817 := by
  unfold tailWord_5572767
  simp only [CollatzResearch.WordTrace]
  refine ⟨203255510601824386675796555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135503673734549591117197703 203255510601824386675796555)
  ·
    refine ⟨304883265902736580013694833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203255510601824386675796555 304883265902736580013694833)
    ·
      refine ⟨228662449427052435010271125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304883265902736580013694833 228662449427052435010271125)
      ·
        refine ⟨10718552316893082891106459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228662449427052435010271125 10718552316893082891106459)
        ·
          refine ⟨16077828475339624336659689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10718552316893082891106459 16077828475339624336659689)
          ·
            refine ⟨12058371356504718252494767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16077828475339624336659689 12058371356504718252494767)
            ·
              refine ⟨18087557034757077378742151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12058371356504718252494767 18087557034757077378742151)
              ·
                refine ⟨27131335552135616068113227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18087557034757077378742151 27131335552135616068113227)
                ·
                  refine ⟨40697003328203424102169841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27131335552135616068113227 40697003328203424102169841)
                  ·
                    refine ⟨30522752496152568076627381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40697003328203424102169841 30522752496152568076627381)
                    ·
                      refine ⟨2861508046514303257183817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30522752496152568076627381 2861508046514303257183817)
                      ·
                        rfl

theorem cell23_5572767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5572767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572767 prefixEnd_5572767 := by exact prefixLift 5572767
  have htrace : WordTrace (prefixWord ++ tailWord_5572767) baseStart_5572767 baseEnd_5572767 := by
    simpa [prefixWord, tailWord_5572767, baseEnd_5572767] using wordTrace_append hprefix tailTrace_5572767
  have hstable : (prefixWord ++ tailWord_5572767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572767).length < 2 ^ (prefixWord ++ tailWord_5572767).sum := by decide
  have hdescent : baseEnd_5572767 < baseStart_5572767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572814 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_5572814 : Nat := 118140960795 + 5572814 * 2 ^ 59
def prefixEnd_5572814 : Nat := 4983230072969 + 3 ^ 40 * 5572814 * 2
def baseEnd_5572814 : Nat := 2861532180105064573296101

theorem tailTrace_5572814 : CollatzResearch.WordTrace tailWord_5572814 prefixEnd_5572814 2861532180105064573296101 := by
  unfold tailWord_5572814
  simp only [CollatzResearch.WordTrace]
  refine ⟨25407153104081764212844687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135504816555102742468504997 25407153104081764212844687)
  ·
    refine ⟨38110729656122646319267031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25407153104081764212844687 38110729656122646319267031)
    ·
      refine ⟨57166094484183969478900547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38110729656122646319267031 57166094484183969478900547)
      ·
        refine ⟨85749141726275954218350821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57166094484183969478900547 85749141726275954218350821)
        ·
          refine ⟨16077964073676741415940779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85749141726275954218350821 16077964073676741415940779)
          ·
            refine ⟨24116946110515112123911169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16077964073676741415940779 24116946110515112123911169)
            ·
              refine ⟨18087709582886334092933377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24116946110515112123911169 18087709582886334092933377)
              ·
                refine ⟨13565782187164750569700033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18087709582886334092933377 13565782187164750569700033)
                ·
                  refine ⟨10174336640373562927275025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13565782187164750569700033 10174336640373562927275025)
                  ·
                    refine ⟨7630752480280172195456269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10174336640373562927275025 7630752480280172195456269)
                    ·
                      refine ⟨2861532180105064573296101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7630752480280172195456269 2861532180105064573296101)
                      ·
                        rfl

theorem cell23_5572814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_5572814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572814 prefixEnd_5572814 := by exact prefixLift 5572814
  have htrace : WordTrace (prefixWord ++ tailWord_5572814) baseStart_5572814 baseEnd_5572814 := by
    simpa [prefixWord, tailWord_5572814, baseEnd_5572814] using wordTrace_append hprefix tailTrace_5572814
  have hstable : (prefixWord ++ tailWord_5572814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572814).length < 2 ^ (prefixWord ++ tailWord_5572814).sum := by decide
  have hdescent : baseEnd_5572814 < baseStart_5572814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572828 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5572828 : Nat := 118140960795 + 5572828 * 2 ^ 59
def prefixEnd_5572828 : Nat := 4983230072969 + 3 ^ 40 * 5572828 * 2
def baseEnd_5572828 : Nat := 2861539368834227518521037

theorem tailTrace_5572828 : CollatzResearch.WordTrace tailWord_5572828 prefixEnd_5572828 2861539368834227518521037 := by
  unfold tailWord_5572828
  simp only [CollatzResearch.WordTrace]
  refine ⟨101628867727301697046883569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135505156969735596062511425 101628867727301697046883569)
  ·
    refine ⟨76221650795476272785162677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101628867727301697046883569 76221650795476272785162677)
    ·
      refine ⟨7145779762075900573609001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76221650795476272785162677 7145779762075900573609001)
      ·
        refine ⟨5359334821556925430206751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7145779762075900573609001 5359334821556925430206751)
        ·
          refine ⟨8039002232335388145310127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359334821556925430206751 8039002232335388145310127)
          ·
            refine ⟨12058503348503082217965191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8039002232335388145310127 12058503348503082217965191)
            ·
              refine ⟨18087755022754623326947787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12058503348503082217965191 18087755022754623326947787)
              ·
                refine ⟨27131632534131934990421681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18087755022754623326947787 27131632534131934990421681)
                ·
                  refine ⟨20348724400598951242816261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27131632534131934990421681 20348724400598951242816261)
                  ·
                    refine ⟨3815385825112303358028049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20348724400598951242816261 3815385825112303358028049)
                    ·
                      refine ⟨2861539368834227518521037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815385825112303358028049 2861539368834227518521037)
                      ·
                        rfl

theorem cell23_5572828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5572828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572828 prefixEnd_5572828 := by exact prefixLift 5572828
  have htrace : WordTrace (prefixWord ++ tailWord_5572828) baseStart_5572828 baseEnd_5572828 := by
    simpa [prefixWord, tailWord_5572828, baseEnd_5572828] using wordTrace_append hprefix tailTrace_5572828
  have hstable : (prefixWord ++ tailWord_5572828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572828).length < 2 ^ (prefixWord ++ tailWord_5572828).sum := by decide
  have hdescent : baseEnd_5572828 < baseStart_5572828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572844 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_5572844 : Nat := 118140960795 + 5572844 * 2 ^ 59
def prefixEnd_5572844 : Nat := 4983230072969 + 3 ^ 40 * 5572844 * 2
def baseEnd_5572844 : Nat := 2861547584524699455920963

theorem tailTrace_5572844 : CollatzResearch.WordTrace tailWord_5572844 prefixEnd_5572844 2861547584524699455920963 := by
  unfold tailWord_5572844
  simp only [CollatzResearch.WordTrace]
  refine ⟨101629159511272714413174793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135505546015030285884233057 101629159511272714413174793)
  ·
    refine ⟨76221869633454535809881095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101629159511272714413174793 76221869633454535809881095)
    ·
      refine ⟨114332804450181803714821643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76221869633454535809881095 114332804450181803714821643)
      ·
        refine ⟨171499206675272705572232465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114332804450181803714821643 171499206675272705572232465)
        ·
          refine ⟨128624405006454529179174349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171499206675272705572232465 128624405006454529179174349)
          ·
            refine ⟨48234151877420448442190381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128624405006454529179174349 48234151877420448442190381)
            ·
              refine ⟨18087806954032668165821393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48234151877420448442190381 18087806954032668165821393)
              ·
                refine ⟨13565855215524501124366045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18087806954032668165821393 13565855215524501124366045)
                ·
                  refine ⟨5087195705821687921637267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13565855215524501124366045 5087195705821687921637267)
                  ·
                    refine ⟨7630793558732531882455901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087195705821687921637267 7630793558732531882455901)
                    ·
                      refine ⟨2861547584524699455920963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7630793558732531882455901 2861547584524699455920963)
                      ·
                        rfl

theorem cell23_5572844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_5572844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572844 prefixEnd_5572844 := by exact prefixLift 5572844
  have htrace : WordTrace (prefixWord ++ tailWord_5572844) baseStart_5572844 baseEnd_5572844 := by
    simpa [prefixWord, tailWord_5572844, baseEnd_5572844] using wordTrace_append hprefix tailTrace_5572844
  have hstable : (prefixWord ++ tailWord_5572844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572844).length < 2 ^ (prefixWord ++ tailWord_5572844).sum := by decide
  have hdescent : baseEnd_5572844 < baseStart_5572844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572847 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 3, 5]
def baseStart_5572847 : Nat := 118140960795 + 5572847 * 2 ^ 59
def prefixEnd_5572847 : Nat := 4983230072969 + 3 ^ 40 * 5572847 * 2
def baseEnd_5572847 : Nat := 953849708322220981394483

theorem tailTrace_5572847 : CollatzResearch.WordTrace tailWord_5572847 prefixEnd_5572847 953849708322220981394483 := by
  unfold tailWord_5572847
  simp only [CollatzResearch.WordTrace]
  refine ⟨203258428441534560338708795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135505618961023040225805863 203258428441534560338708795)
  ·
    refine ⟨304887642662301840508063193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203258428441534560338708795 304887642662301840508063193)
    ·
      refine ⟨228665731996726380381047395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304887642662301840508063193 228665731996726380381047395)
      ·
        refine ⟨342998597995089570571571093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228665731996726380381047395 342998597995089570571571093)
        ·
          refine ⟨16078059281019823620542395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 342998597995089570571571093 16078059281019823620542395)
          ·
            refine ⟨24117088921529735430813593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16078059281019823620542395 24117088921529735430813593)
            ·
              refine ⟨18087816691147301573110195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24117088921529735430813593 18087816691147301573110195)
              ·
                refine ⟨27131725036720952359665293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18087816691147301573110195 27131725036720952359665293)
                ·
                  refine ⟨10174396888770357134874485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27131725036720952359665293 10174396888770357134874485)
                  ·
                    refine ⟨953849708322220981394483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10174396888770357134874485 953849708322220981394483)
                    ·
                      rfl

theorem cell23_5572847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_5572847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572847 prefixEnd_5572847 := by exact prefixLift 5572847
  have htrace : WordTrace (prefixWord ++ tailWord_5572847) baseStart_5572847 baseEnd_5572847 := by
    simpa [prefixWord, tailWord_5572847, baseEnd_5572847] using wordTrace_append hprefix tailTrace_5572847
  have hstable : (prefixWord ++ tailWord_5572847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572847).length < 2 ^ (prefixWord ++ tailWord_5572847).sum := by decide
  have hdescent : baseEnd_5572847 < baseStart_5572847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572864 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 1, 5]
def baseStart_5572864 : Nat := 118140960795 + 5572864 * 2 ^ 59
def prefixEnd_5572864 : Nat := 4983230072969 + 3 ^ 40 * 5572864 * 2
def baseEnd_5572864 : Nat := 953852618045929792556957

theorem tailTrace_5572864 : CollatzResearch.WordTrace tailWord_5572864 prefixEnd_5572864 953852618045929792556957 := by
  unfold tailWord_5572864
  simp only [CollatzResearch.WordTrace]
  refine ⟨101629524241236486121038823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135506032321648648161385097 101629524241236486121038823)
  ·
    refine ⟨152444286361854729181558235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101629524241236486121038823 152444286361854729181558235)
    ·
      refine ⟨228666429542782093772337353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152444286361854729181558235 228666429542782093772337353)
      ·
        refine ⟨171499822157086570329253015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228666429542782093772337353 171499822157086570329253015)
        ·
          refine ⟨257249733235629855493879523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171499822157086570329253015 257249733235629855493879523)
          ·
            refine ⟨385874599853444783240819285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257249733235629855493879523 385874599853444783240819285)
            ·
              refine ⟨4521967967032556053603351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 385874599853444783240819285 4521967967032556053603351)
              ·
                refine ⟨6782951950548834080405027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4521967967032556053603351 6782951950548834080405027)
                ·
                  refine ⟨10174427925823251120607541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6782951950548834080405027 10174427925823251120607541)
                  ·
                    refine ⟨953852618045929792556957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10174427925823251120607541 953852618045929792556957)
                    ·
                      rfl

theorem cell23_5572864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 5].length) (baseStart_5572864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572864 prefixEnd_5572864 := by exact prefixLift 5572864
  have htrace : WordTrace (prefixWord ++ tailWord_5572864) baseStart_5572864 baseEnd_5572864 := by
    simpa [prefixWord, tailWord_5572864, baseEnd_5572864] using wordTrace_append hprefix tailTrace_5572864
  have hstable : (prefixWord ++ tailWord_5572864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572864).length < 2 ^ (prefixWord ++ tailWord_5572864).sum := by decide
  have hdescent : baseEnd_5572864 < baseStart_5572864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572887 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_5572887 : Nat := 118140960795 + 5572887 * 2 ^ 59
def prefixEnd_5572887 : Nat := 4983230072969 + 3 ^ 40 * 5572887 * 2
def baseEnd_5572887 : Nat := 2861569664192842787683265

theorem tailTrace_5572887 : CollatzResearch.WordTrace tailWord_5572887 prefixEnd_5572887 2861569664192842787683265 := by
  unfold tailWord_5572887
  simp only [CollatzResearch.WordTrace]
  refine ⟨203259887361389647170164915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135506591574259764780109943 203259887361389647170164915)
  ·
    refine ⟨304889831042084470755247373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203259887361389647170164915 304889831042084470755247373)
    ·
      refine ⟨114333686640781676533217765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304889831042084470755247373 114333686640781676533217765)
      ·
        refine ⟨21437566245146564349978331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114333686640781676533217765 21437566245146564349978331)
        ·
          refine ⟨32156349367719846524967497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21437566245146564349978331 32156349367719846524967497)
          ·
            refine ⟨24117262025789884893725623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32156349367719846524967497 24117262025789884893725623)
            ·
              refine ⟨36175893038684827340588435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24117262025789884893725623 36175893038684827340588435)
              ·
                refine ⟨54263839558027241010882653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36175893038684827340588435 54263839558027241010882653)
                ·
                  refine ⟨20348939834260215379080995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54263839558027241010882653 20348939834260215379080995)
                  ·
                    refine ⟨30523409751390323068621493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20348939834260215379080995 30523409751390323068621493)
                    ·
                      refine ⟨2861569664192842787683265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30523409751390323068621493 2861569664192842787683265)
                      ·
                        rfl

theorem cell23_5572887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_5572887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572887 prefixEnd_5572887 := by exact prefixLift 5572887
  have htrace : WordTrace (prefixWord ++ tailWord_5572887) baseStart_5572887 baseEnd_5572887 := by
    simpa [prefixWord, tailWord_5572887, baseEnd_5572887] using wordTrace_append hprefix tailTrace_5572887
  have hstable : (prefixWord ++ tailWord_5572887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572887).length < 2 ^ (prefixWord ++ tailWord_5572887).sum := by decide
  have hdescent : baseEnd_5572887 < baseStart_5572887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572901 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_5572901 : Nat := 118140960795 + 5572901 * 2 ^ 59
def prefixEnd_5572901 : Nat := 4983230072969 + 3 ^ 40 * 5572901 * 2
def baseEnd_5572901 : Nat := 2861576852922005732908201

theorem tailTrace_5572901 : CollatzResearch.WordTrace tailWord_5572901 prefixEnd_5572901 2861576852922005732908201 := by
  unfold tailWord_5572901
  simp only [CollatzResearch.WordTrace]
  refine ⟨203260397983338927561174557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135506931988892618374116371 203260397983338927561174557)
  ·
    refine ⟨76222649243752097835440459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203260397983338927561174557 76222649243752097835440459)
    ·
      refine ⟨114333973865628146753160689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76222649243752097835440459 114333973865628146753160689)
      ·
        refine ⟨85750480399221110064870517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114333973865628146753160689 85750480399221110064870517)
        ·
          refine ⟨8039107537426979068581611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85750480399221110064870517 8039107537426979068581611)
          ·
            refine ⟨12058661306140468602872417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8039107537426979068581611 12058661306140468602872417)
            ·
              refine ⟨9043995979605351452154313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12058661306140468602872417 9043995979605351452154313)
              ·
                refine ⟨6782996984704013589115735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9043995979605351452154313 6782996984704013589115735)
                ·
                  refine ⟨10174495477056020383673603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6782996984704013589115735 10174495477056020383673603)
                  ·
                    refine ⟨15261743215584030575510405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10174495477056020383673603 15261743215584030575510405)
                    ·
                      refine ⟨2861576852922005732908201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15261743215584030575510405 2861576852922005732908201)
                      ·
                        rfl

theorem cell23_5572901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_5572901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572901 prefixEnd_5572901 := by exact prefixLift 5572901
  have htrace : WordTrace (prefixWord ++ tailWord_5572901) baseStart_5572901 baseEnd_5572901 := by
    simpa [prefixWord, tailWord_5572901, baseEnd_5572901] using wordTrace_append hprefix tailTrace_5572901
  have hstable : (prefixWord ++ tailWord_5572901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572901).length < 2 ^ (prefixWord ++ tailWord_5572901).sum := by decide
  have hdescent : baseEnd_5572901 < baseStart_5572901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572921 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5572921 : Nat := 118140960795 + 5572921 * 2 ^ 59
def prefixEnd_5572921 : Nat := 4983230072969 + 3 ^ 40 * 5572921 * 2
def baseEnd_5572921 : Nat := 2861587122535095654658109

theorem tailTrace_5572921 : CollatzResearch.WordTrace tailWord_5572921 prefixEnd_5572921 2861587122535095654658109 := by
  unfold tailWord_5572921
  simp only [CollatzResearch.WordTrace]
  refine ⟨203261127443266470976902617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135507418295510980651268411 203261127443266470976902617)
  ·
    refine ⟨152445845582449853232676963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203261127443266470976902617 152445845582449853232676963)
    ·
      refine ⟨228668768373674779849015445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152445845582449853232676963 228668768373674779849015445)
      ·
        refine ⟨10718848517516005305422599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228668768373674779849015445 10718848517516005305422599)
        ·
          refine ⟨16078272776274007958133899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10718848517516005305422599 16078272776274007958133899)
          ·
            refine ⟨24117409164411011937200849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16078272776274007958133899 24117409164411011937200849)
            ·
              refine ⟨18088056873308258952900637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24117409164411011937200849 18088056873308258952900637)
              ·
                refine ⟨6783021327490597107337739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18088056873308258952900637 6783021327490597107337739)
                ·
                  refine ⟨10174531991235895661006609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6783021327490597107337739 10174531991235895661006609)
                  ·
                    refine ⟨7630898993426921745754957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10174531991235895661006609 7630898993426921745754957)
                    ·
                      refine ⟨2861587122535095654658109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7630898993426921745754957 2861587122535095654658109)
                      ·
                        rfl

theorem cell23_5572921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5572921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572921 prefixEnd_5572921 := by exact prefixLift 5572921
  have htrace : WordTrace (prefixWord ++ tailWord_5572921) baseStart_5572921 baseEnd_5572921 := by
    simpa [prefixWord, tailWord_5572921, baseEnd_5572921] using wordTrace_append hprefix tailTrace_5572921
  have hstable : (prefixWord ++ tailWord_5572921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572921).length < 2 ^ (prefixWord ++ tailWord_5572921).sum := by decide
  have hdescent : baseEnd_5572921 < baseStart_5572921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572935 : List Nat := [1, 1, 4, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_5572935 : Nat := 118140960795 + 5572935 * 2 ^ 59
def prefixEnd_5572935 : Nat := 4983230072969 + 3 ^ 40 * 5572935 * 2
def baseEnd_5572935 : Nat := 2861594311264258599883045

theorem tailTrace_5572935 : CollatzResearch.WordTrace tailWord_5572935 prefixEnd_5572935 2861594311264258599883045 := by
  unfold tailWord_5572935
  simp only [CollatzResearch.WordTrace]
  refine ⟨203261638065215751367912259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135507758710143834245274839 203261638065215751367912259)
  ·
    refine ⟨304892457097823627051868389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203261638065215751367912259 304892457097823627051868389)
    ·
      refine ⟨57167335705841930072225323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304892457097823627051868389 57167335705841930072225323)
      ·
        refine ⟨85751003558762895108337985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57167335705841930072225323 85751003558762895108337985)
        ·
          refine ⟨64313252669072171331253489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85751003558762895108337985 64313252669072171331253489)
          ·
            refine ⟨48234939501804128498440117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64313252669072171331253489 48234939501804128498440117)
            ·
              refine ⟨4522025578294137046728761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48234939501804128498440117 4522025578294137046728761)
              ·
                refine ⟨3391519183720602785046571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522025578294137046728761 3391519183720602785046571)
                ·
                  refine ⟨5087278775580904177569857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391519183720602785046571 5087278775580904177569857)
                  ·
                    refine ⟨3815459081685678133177393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5087278775580904177569857 3815459081685678133177393)
                    ·
                      refine ⟨2861594311264258599883045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815459081685678133177393 2861594311264258599883045)
                      ·
                        rfl

theorem cell23_5572935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_5572935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572935 prefixEnd_5572935 := by exact prefixLift 5572935
  have htrace : WordTrace (prefixWord ++ tailWord_5572935) baseStart_5572935 baseEnd_5572935 := by
    simpa [prefixWord, tailWord_5572935, baseEnd_5572935] using wordTrace_append hprefix tailTrace_5572935
  have hstable : (prefixWord ++ tailWord_5572935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572935).length < 2 ^ (prefixWord ++ tailWord_5572935).sum := by decide
  have hdescent : baseEnd_5572935 < baseStart_5572935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572951 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_5572951 : Nat := 118140960795 + 5572951 * 2 ^ 59
def prefixEnd_5572951 : Nat := 4983230072969 + 3 ^ 40 * 5572951 * 2
def baseEnd_5572951 : Nat := 2861602526954730537282971

theorem tailTrace_5572951 : CollatzResearch.WordTrace tailWord_5572951 prefixEnd_5572951 2861602526954730537282971 := by
  unfold tailWord_5572951
  simp only [CollatzResearch.WordTrace]
  refine ⟨203262221633157786100494707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135508147755438524066996471 203262221633157786100494707)
  ·
    refine ⟨304893332449736679150742061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203262221633157786100494707 304893332449736679150742061)
    ·
      refine ⟨114334999668651254681528273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304893332449736679150742061 114334999668651254681528273)
      ·
        refine ⟨85751249751488441011146205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114334999668651254681528273 85751249751488441011146205)
        ·
          refine ⟨32156718656808165379179827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85751249751488441011146205 32156718656808165379179827)
          ·
            refine ⟨48235077985212248068769741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32156718656808165379179827 48235077985212248068769741)
            ·
              refine ⟨18088154244454593025788653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48235077985212248068769741 18088154244454593025788653)
              ·
                refine ⟨6783057841670472384670745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18088154244454593025788653 6783057841670472384670745)
                ·
                  refine ⟨5087293381252854288503059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6783057841670472384670745 5087293381252854288503059)
                  ·
                    refine ⟨7630940071879281432754589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087293381252854288503059 7630940071879281432754589)
                    ·
                      refine ⟨2861602526954730537282971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7630940071879281432754589 2861602526954730537282971)
                      ·
                        rfl

theorem cell23_5572951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_5572951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572951 prefixEnd_5572951 := by exact prefixLift 5572951
  have htrace : WordTrace (prefixWord ++ tailWord_5572951) baseStart_5572951 baseEnd_5572951 := by
    simpa [prefixWord, tailWord_5572951, baseEnd_5572951] using wordTrace_append hprefix tailTrace_5572951
  have hstable : (prefixWord ++ tailWord_5572951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572951).length < 2 ^ (prefixWord ++ tailWord_5572951).sum := by decide
  have hdescent : baseEnd_5572951 < baseStart_5572951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572997 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 7]
def baseStart_5572997 : Nat := 118140960795 + 5572997 * 2 ^ 59
def prefixEnd_5572997 : Nat := 4983230072969 + 3 ^ 40 * 5572997 * 2
def baseEnd_5572997 : Nat := 317958460784981928589751

theorem tailTrace_5572997 : CollatzResearch.WordTrace tailWord_5572997 prefixEnd_5572997 317958460784981928589751 := by
  unfold tailWord_5572997
  simp only [CollatzResearch.WordTrace]
  refine ⟨203263899390991135956669245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135509266260660757304446163 203263899390991135956669245)
  ·
    refine ⟨76223962271621675983750967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203263899390991135956669245 76223962271621675983750967)
    ·
      refine ⟨114335943407432513975626451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76223962271621675983750967 114335943407432513975626451)
      ·
        refine ⟨171503915111148770963439677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114335943407432513975626451 171503915111148770963439677)
        ·
          refine ⟨64313968166680789111289879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171503915111148770963439677 64313968166680789111289879)
          ·
            refine ⟨96470952250021183666934819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64313968166680789111289879 96470952250021183666934819)
            ·
              refine ⟨144706428375031775500402229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96470952250021183666934819 144706428375031775500402229)
              ·
                refine ⟨13566227660159228953162709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144706428375031775500402229 13566227660159228953162709)
                ·
                  refine ⟨317958460784981928589751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13566227660159228953162709 317958460784981928589751)
                  ·
                    rfl

theorem cell23_5572997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_5572997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572997 prefixEnd_5572997 := by exact prefixLift 5572997
  have htrace : WordTrace (prefixWord ++ tailWord_5572997) baseStart_5572997 baseEnd_5572997 := by
    simpa [prefixWord, tailWord_5572997, baseEnd_5572997] using wordTrace_append hprefix tailTrace_5572997
  have hstable : (prefixWord ++ tailWord_5572997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572997).length < 2 ^ (prefixWord ++ tailWord_5572997).sum := by decide
  have hdescent : baseEnd_5572997 < baseStart_5572997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573004 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_5573004 : Nat := 118140960795 + 5573004 * 2 ^ 59
def prefixEnd_5573004 : Nat := 4983230072969 + 3 ^ 40 * 5573004 * 2
def baseEnd_5573004 : Nat := 2861629741429418829920227

theorem tailTrace_5573004 : CollatzResearch.WordTrace tailWord_5573004 prefixEnd_5573004 2861629741429418829920227 := by
  unfold tailWord_5573004
  simp only [CollatzResearch.WordTrace]
  refine ⟨101632077350982888076087033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135509436467977184101449377 101632077350982888076087033)
  ·
    refine ⟨76224058013237166057065275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101632077350982888076087033 76224058013237166057065275)
    ·
      refine ⟨114336087019855749085597913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76224058013237166057065275 114336087019855749085597913)
      ·
        refine ⟨85752065264891811814198435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114336087019855749085597913 85752065264891811814198435)
        ·
          refine ⟨128628097897337717721297653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85752065264891811814198435 128628097897337717721297653)
          ·
            refine ⟨12058884177875411036371655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128628097897337717721297653 12058884177875411036371655)
            ·
              refine ⟨18088326266813116554557483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12058884177875411036371655 18088326266813116554557483)
              ·
                refine ⟨27132489400219674831836225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18088326266813116554557483 27132489400219674831836225)
                ·
                  refine ⟨20349367050164756123877169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27132489400219674831836225 20349367050164756123877169)
                  ·
                    refine ⟨15262025287623567092907877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20349367050164756123877169 15262025287623567092907877)
                    ·
                      refine ⟨2861629741429418829920227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15262025287623567092907877 2861629741429418829920227)
                      ·
                        rfl

theorem cell23_5573004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_5573004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573004 prefixEnd_5573004 := by exact prefixLift 5573004
  have htrace : WordTrace (prefixWord ++ tailWord_5573004) baseStart_5573004 baseEnd_5573004 := by
    simpa [prefixWord, tailWord_5573004, baseEnd_5573004] using wordTrace_append hprefix tailTrace_5573004
  have hstable : (prefixWord ++ tailWord_5573004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573004).length < 2 ^ (prefixWord ++ tailWord_5573004).sum := by decide
  have hdescent : baseEnd_5573004 < baseStart_5573004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573031 : List Nat := [1, 1, 6, 1, 1, 2, 1, 5, 5]
def baseStart_5573031 : Nat := 118140960795 + 5573031 * 2 ^ 59
def prefixEnd_5573031 : Nat := 4983230072969 + 3 ^ 40 * 5573031 * 2
def baseEnd_5573031 : Nat := 317960400600787802698067

theorem tailTrace_5573031 : CollatzResearch.WordTrace tailWord_5573031 prefixEnd_5573031 317960400600787802698067 := by
  unfold tailWord_5573031
  simp only [CollatzResearch.WordTrace]
  refine ⟨203265139472867959763406947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135510092981911973175604631 203265139472867959763406947)
  ·
    refine ⟨304897709209301939645110421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203265139472867959763406947 304897709209301939645110421)
    ·
      refine ⟨14292080119186028420864551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 304897709209301939645110421 14292080119186028420864551)
      ·
        refine ⟨21438120178779042631296827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14292080119186028420864551 21438120178779042631296827)
        ·
          refine ⟨32157180268168563946945241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21438120178779042631296827 32157180268168563946945241)
          ·
            refine ⟨24117885201126422960208931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32157180268168563946945241 24117885201126422960208931)
            ·
              refine ⟨36176827801689634440313397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24117885201126422960208931 36176827801689634440313397)
              ·
                refine ⟨3391577606408403228779381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36176827801689634440313397 3391577606408403228779381)
                ·
                  refine ⟨317960400600787802698067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3391577606408403228779381 317960400600787802698067)
                  ·
                    rfl

theorem cell23_5573031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 5].length) (baseStart_5573031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573031 prefixEnd_5573031 := by exact prefixLift 5573031
  have htrace : WordTrace (prefixWord ++ tailWord_5573031) baseStart_5573031 baseEnd_5573031 := by
    simpa [prefixWord, tailWord_5573031, baseEnd_5573031] using wordTrace_append hprefix tailTrace_5573031
  have hstable : (prefixWord ++ tailWord_5573031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573031).length < 2 ^ (prefixWord ++ tailWord_5573031).sum := by decide
  have hdescent : baseEnd_5573031 < baseStart_5573031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573054 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_5573054 : Nat := 118140960795 + 5573054 * 2 ^ 59
def prefixEnd_5573054 : Nat := 4983230072969 + 3 ^ 40 * 5573054 * 2
def baseEnd_5573054 : Nat := 2861655415462143634294997

theorem tailTrace_5573054 : CollatzResearch.WordTrace tailWord_5573054 prefixEnd_5573054 2861655415462143634294997 := by
  unfold tailWord_5573054
  simp only [CollatzResearch.WordTrace]
  refine ⟨25408247293973079336436777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135510652234523089794329477 25408247293973079336436777)
  ·
    refine ⟨19056185470479809502327583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25408247293973079336436777 19056185470479809502327583)
    ·
      refine ⟨28584278205719714253491375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19056185470479809502327583 28584278205719714253491375)
      ·
        refine ⟨42876417308579571380237063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28584278205719714253491375 42876417308579571380237063)
        ·
          refine ⟨64314625962869357070355595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42876417308579571380237063 64314625962869357070355595)
          ·
            refine ⟨96471938944304035605533393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64314625962869357070355595 96471938944304035605533393)
            ·
              refine ⟨72353954208228026704150045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96471938944304035605533393 72353954208228026704150045)
              ·
                refine ⟨27132732828085510014056267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72353954208228026704150045 27132732828085510014056267)
                ·
                  refine ⟨40699099242128265021084401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27132732828085510014056267 40699099242128265021084401)
                  ·
                    refine ⟨30524324431596198765813301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40699099242128265021084401 30524324431596198765813301)
                    ·
                      refine ⟨2861655415462143634294997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30524324431596198765813301 2861655415462143634294997)
                      ·
                        rfl

theorem cell23_5573054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_5573054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573054 prefixEnd_5573054 := by exact prefixLift 5573054
  have htrace : WordTrace (prefixWord ++ tailWord_5573054) baseStart_5573054 baseEnd_5573054 := by
    simpa [prefixWord, tailWord_5573054, baseEnd_5573054] using wordTrace_append hprefix tailTrace_5573054
  have hstable : (prefixWord ++ tailWord_5573054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573054).length < 2 ^ (prefixWord ++ tailWord_5573054).sum := by decide
  have hdescent : baseEnd_5573054 < baseStart_5573054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573064 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_5573064 : Nat := 118140960795 + 5573064 * 2 ^ 59
def prefixEnd_5573064 : Nat := 4983230072969 + 3 ^ 40 * 5573064 * 2
def baseEnd_5573064 : Nat := 2861660550268688595169951

theorem tailTrace_5573064 : CollatzResearch.WordTrace tailWord_5573064 prefixEnd_5573064 2861660550268688595169951 := by
  unfold tailWord_5573064
  simp only [CollatzResearch.WordTrace]
  refine ⟨101633171540874203199679123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135510895387832270932905497 101633171540874203199679123)
  ·
    refine ⟨152449757311311304799518685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101633171540874203199679123 152449757311311304799518685)
    ·
      refine ⟨57168658991741739299819507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152449757311311304799518685 57168658991741739299819507)
      ·
        refine ⟨85752988487612608949729261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57168658991741739299819507 85752988487612608949729261)
        ·
          refine ⟨32157370682854728356148473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85752988487612608949729261 32157370682854728356148473)
          ·
            refine ⟨24118028012141046267111355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32157370682854728356148473 24118028012141046267111355)
            ·
              refine ⟨36177042018211569400667033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24118028012141046267111355 36177042018211569400667033)
              ·
                refine ⟨27132781513658677050500275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36177042018211569400667033 27132781513658677050500275)
                ·
                  refine ⟨40699172270488015575750413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27132781513658677050500275 40699172270488015575750413)
                  ·
                    refine ⟨15262189601433005840906405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40699172270488015575750413 15262189601433005840906405)
                    ·
                      refine ⟨2861660550268688595169951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15262189601433005840906405 2861660550268688595169951)
                      ·
                        rfl

theorem cell23_5573064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_5573064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573064 prefixEnd_5573064 := by exact prefixLift 5573064
  have htrace : WordTrace (prefixWord ++ tailWord_5573064) baseStart_5573064 baseEnd_5573064 := by
    simpa [prefixWord, tailWord_5573064, baseEnd_5573064] using wordTrace_append hprefix tailTrace_5573064
  have hstable : (prefixWord ++ tailWord_5573064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573064).length < 2 ^ (prefixWord ++ tailWord_5573064).sum := by decide
  have hdescent : baseEnd_5573064 < baseStart_5573064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573104 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 6]
def baseStart_5573104 : Nat := 118140960795 + 5573104 * 2 ^ 59
def prefixEnd_5573104 : Nat := 4983230072969 + 3 ^ 40 * 5573104 * 2
def baseEnd_5573104 : Nat := 317964565499429826518863

theorem tailTrace_5573104 : CollatzResearch.WordTrace tailWord_5573104 prefixEnd_5573104 317964565499429826518863 := by
  unfold tailWord_5573104
  simp only [CollatzResearch.WordTrace]
  refine ⟨101633901000801746615407183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135511868001068995487209577 101633901000801746615407183)
  ·
    refine ⟨152450851501202619923110775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101633901000801746615407183 152450851501202619923110775)
    ·
      refine ⟨228676277251803929884666163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152450851501202619923110775 228676277251803929884666163)
      ·
        refine ⟨343014415877705894826999245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228676277251803929884666163 343014415877705894826999245)
        ·
          refine ⟨128630405954139710560124717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343014415877705894826999245 128630405954139710560124717)
          ·
            refine ⟨48236402232802391460046769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128630405954139710560124717 48236402232802391460046769)
            ·
              refine ⟨36177301674601793595035077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48236402232802391460046769 36177301674601793595035077)
              ·
                refine ⟨6783244063987836299069077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36177301674601793595035077 6783244063987836299069077)
                ·
                  refine ⟨317964565499429826518863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6783244063987836299069077 317964565499429826518863)
                  ·
                    rfl

theorem cell23_5573104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 6].length) (baseStart_5573104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573104 prefixEnd_5573104 := by exact prefixLift 5573104
  have htrace : WordTrace (prefixWord ++ tailWord_5573104) baseStart_5573104 baseEnd_5573104 := by
    simpa [prefixWord, tailWord_5573104, baseEnd_5573104] using wordTrace_append hprefix tailTrace_5573104
  have hstable : (prefixWord ++ tailWord_5573104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573104).length < 2 ^ (prefixWord ++ tailWord_5573104).sum := by decide
  have hdescent : baseEnd_5573104 < baseStart_5573104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573114 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_5573114 : Nat := 118140960795 + 5573114 * 2 ^ 59
def prefixEnd_5573114 : Nat := 4983230072969 + 3 ^ 40 * 5573114 * 2
def baseEnd_5573114 : Nat := 2861686224301413399544721

theorem tailTrace_5573114 : CollatzResearch.WordTrace tailWord_5573114 prefixEnd_5573114 2861686224301413399544721 := by
  unfold tailWord_5573114
  simp only [CollatzResearch.WordTrace]
  refine ⟨50817041682891816234669599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135512111154378176625785597 50817041682891816234669599)
  ·
    refine ⟨76225562524337724352004399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50817041682891816234669599 76225562524337724352004399)
    ·
      refine ⟨114338343786506586528006599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76225562524337724352004399 114338343786506586528006599)
      ·
        refine ⟨171507515679759879792009899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114338343786506586528006599 171507515679759879792009899)
        ·
          refine ⟨257261273519639819688014849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171507515679759879792009899 257261273519639819688014849)
          ·
            refine ⟨192945955139729864766011137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257261273519639819688014849 192945955139729864766011137)
            ·
              refine ⟨144709466354797398574508353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192945955139729864766011137 144709466354797398574508353)
              ·
                refine ⟨108532099766098048930881265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144709466354797398574508353 108532099766098048930881265)
                ·
                  refine ⟨81399074824573536698160949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108532099766098048930881265 81399074824573536698160949)
                  ·
                    refine ⟨7631163264803769065452589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81399074824573536698160949 7631163264803769065452589)
                    ·
                      refine ⟨2861686224301413399544721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631163264803769065452589 2861686224301413399544721)
                      ·
                        rfl

theorem cell23_5573114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_5573114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573114 prefixEnd_5573114 := by exact prefixLift 5573114
  have htrace : WordTrace (prefixWord ++ tailWord_5573114) baseStart_5573114 baseEnd_5573114 := by
    simpa [prefixWord, tailWord_5573114, baseEnd_5573114] using wordTrace_append hprefix tailTrace_5573114
  have hstable : (prefixWord ++ tailWord_5573114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573114).length < 2 ^ (prefixWord ++ tailWord_5573114).sum := by decide
  have hdescent : baseEnd_5573114 < baseStart_5573114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573121 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 6]
def baseStart_5573121 : Nat := 118140960795 + 5573121 * 2 ^ 59
def prefixEnd_5573121 : Nat := 4983230072969 + 3 ^ 40 * 5573121 * 2
def baseEnd_5573121 : Nat := 317965535407332763573021

theorem tailTrace_5573121 : CollatzResearch.WordTrace tailWord_5573121 prefixEnd_5573121 317965535407332763573021 := by
  unfold tailWord_5573121
  simp only [CollatzResearch.WordTrace]
  refine ⟨203268422042541905134183217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135512281361694603422788811 203268422042541905134183217)
  ·
    refine ⟨152451316531906428850637413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203268422042541905134183217 152451316531906428850637413)
    ·
      refine ⟨28584621849732455409494515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152451316531906428850637413 28584621849732455409494515)
      ·
        refine ⟨42876932774598683114241773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28584621849732455409494515 42876932774598683114241773)
        ·
          refine ⟨16078849790474506167840665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42876932774598683114241773 16078849790474506167840665)
          ·
            refine ⟨12059137342855879625880499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16078849790474506167840665 12059137342855879625880499)
            ·
              refine ⟨18088706014283819438820749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12059137342855879625880499 18088706014283819438820749)
              ·
                refine ⟨6783264755356432289557781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18088706014283819438820749 6783264755356432289557781)
                ·
                  refine ⟨317965535407332763573021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6783264755356432289557781 317965535407332763573021)
                  ·
                    rfl

theorem cell23_5573121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 6].length) (baseStart_5573121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573121 prefixEnd_5573121 := by exact prefixLift 5573121
  have htrace : WordTrace (prefixWord ++ tailWord_5573121) baseStart_5573121 baseEnd_5573121 := by
    simpa [prefixWord, tailWord_5573121, baseEnd_5573121] using wordTrace_append hprefix tailTrace_5573121
  have hstable : (prefixWord ++ tailWord_5573121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573121).length < 2 ^ (prefixWord ++ tailWord_5573121).sum := by decide
  have hdescent : baseEnd_5573121 < baseStart_5573121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573181 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_5573181 : Nat := 118140960795 + 5573181 * 2 ^ 59
def prefixEnd_5573181 : Nat := 4983230072969 + 3 ^ 40 * 5573181 * 2
def baseEnd_5573181 : Nat := 953906875835088212468971

theorem tailTrace_5573181 : CollatzResearch.WordTrace tailWord_5573181 prefixEnd_5573181 953906875835088212468971 := by
  unfold tailWord_5573181
  simp only [CollatzResearch.WordTrace]
  refine ⟨203270610422324535381367397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135513740281549690254244931 203270610422324535381367397)
  ·
    refine ⟨38113239454185850384006387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203270610422324535381367397 38113239454185850384006387)
    ·
      refine ⟨57169859181278775576009581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38113239454185850384006387 57169859181278775576009581)
      ·
        refine ⟨21438697192979540841003593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57169859181278775576009581 21438697192979540841003593)
        ·
          refine ⟨16079022894734655630752695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21438697192979540841003593 16079022894734655630752695)
          ·
            refine ⟨24118534342101983446129043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16079022894734655630752695 24118534342101983446129043)
            ·
              refine ⟨36177801513152975169193565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24118534342101983446129043 36177801513152975169193565)
              ·
                refine ⟨13566675567432365688447587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36177801513152975169193565 13566675567432365688447587)
                ·
                  refine ⟨20350013351148548532671381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13566675567432365688447587 20350013351148548532671381)
                  ·
                    refine ⟨953906875835088212468971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20350013351148548532671381 953906875835088212468971)
                    ·
                      rfl

theorem cell23_5573181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_5573181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573181 prefixEnd_5573181 := by exact prefixLift 5573181
  have htrace : WordTrace (prefixWord ++ tailWord_5573181) baseStart_5573181 baseEnd_5573181 := by
    simpa [prefixWord, tailWord_5573181, baseEnd_5573181] using wordTrace_append hprefix tailTrace_5573181
  have hstable : (prefixWord ++ tailWord_5573181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573181).length < 2 ^ (prefixWord ++ tailWord_5573181).sum := by decide
  have hdescent : baseEnd_5573181 < baseStart_5573181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573182 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5573182 : Nat := 118140960795 + 5573182 * 2 ^ 59
def prefixEnd_5573182 : Nat := 4983230072969 + 3 ^ 40 * 5573182 * 2
def baseEnd_5573182 : Nat := 2861721140985919133494409

theorem tailTrace_5573182 : CollatzResearch.WordTrace tailWord_5573182 prefixEnd_5573182 2861721140985919133494409 := by
  unfold tailWord_5573182
  simp only [CollatzResearch.WordTrace]
  refine ⟨25408830861915114069019225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135513764596880608368102533 25408830861915114069019225)
  ·
    refine ⟨19056623146436335551764419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25408830861915114069019225 19056623146436335551764419)
    ·
      refine ⟨28584934719654503327646629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19056623146436335551764419 28584934719654503327646629)
      ·
        refine ⟨5359675259935219373933743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28584934719654503327646629 5359675259935219373933743)
        ·
          refine ⟨8039512889902829060900615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359675259935219373933743 8039512889902829060900615)
          ·
            refine ⟨12059269334854243591350923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8039512889902829060900615 12059269334854243591350923)
            ·
              refine ⟨18088904002281365387026385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12059269334854243591350923 18088904002281365387026385)
              ·
                refine ⟨13566678001711024040269789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18088904002281365387026385 13566678001711024040269789)
                ·
                  refine ⟨5087504250641634015101171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13566678001711024040269789 5087504250641634015101171)
                  ·
                    refine ⟨7631256375962451022651757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087504250641634015101171 7631256375962451022651757)
                    ·
                      refine ⟨2861721140985919133494409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631256375962451022651757 2861721140985919133494409)
                      ·
                        rfl

theorem cell23_5573182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5573182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573182 prefixEnd_5573182 := by exact prefixLift 5573182
  have htrace : WordTrace (prefixWord ++ tailWord_5573182) baseStart_5573182 baseEnd_5573182 := by
    simpa [prefixWord, tailWord_5573182, baseEnd_5573182] using wordTrace_append hprefix tailTrace_5573182
  have hstable : (prefixWord ++ tailWord_5573182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573182).length < 2 ^ (prefixWord ++ tailWord_5573182).sum := by decide
  have hdescent : baseEnd_5573182 < baseStart_5573182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573184 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_5573184 : Nat := 118140960795 + 5573184 * 2 ^ 59
def prefixEnd_5573184 : Nat := 4983230072969 + 3 ^ 40 * 5573184 * 2
def baseEnd_5573184 : Nat := 2861722167947228125669399

theorem tailTrace_5573184 : CollatzResearch.WordTrace tailWord_5573184 prefixEnd_5573184 2861722167947228125669399 := by
  unfold tailWord_5573184
  simp only [CollatzResearch.WordTrace]
  refine ⟨101635359920656833446863303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135513813227542444595817737 101635359920656833446863303)
  ·
    refine ⟨152453039880985250170294955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101635359920656833446863303 152453039880985250170294955)
    ·
      refine ⟨228679559821477875255442433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152453039880985250170294955 228679559821477875255442433)
      ·
        refine ⟨171509669866108406441581825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228679559821477875255442433 171509669866108406441581825)
        ·
          refine ⟨128632252399581304831186369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171509669866108406441581825 128632252399581304831186369)
          ·
            refine ⟨96474189299685978623389777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128632252399581304831186369 96474189299685978623389777)
            ·
              refine ⟨72355641974764483967542333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96474189299685978623389777 72355641974764483967542333)
              ·
                refine ⟨27133365740536681487828375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72355641974764483967542333 27133365740536681487828375)
                ·
                  refine ⟨40700048610805022231742563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27133365740536681487828375 40700048610805022231742563)
                  ·
                    refine ⟨61050072916207533347613845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40700048610805022231742563 61050072916207533347613845)
                    ·
                      refine ⟨2861722167947228125669399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61050072916207533347613845 2861722167947228125669399)
                      ·
                        rfl

theorem cell23_5573184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_5573184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573184 prefixEnd_5573184 := by exact prefixLift 5573184
  have htrace : WordTrace (prefixWord ++ tailWord_5573184) baseStart_5573184 baseEnd_5573184 := by
    simpa [prefixWord, tailWord_5573184, baseEnd_5573184] using wordTrace_append hprefix tailTrace_5573184
  have hstable : (prefixWord ++ tailWord_5573184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573184).length < 2 ^ (prefixWord ++ tailWord_5573184).sum := by decide
  have hdescent : baseEnd_5573184 < baseStart_5573184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573201 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_5573201 : Nat := 118140960795 + 5573201 * 2 ^ 59
def prefixEnd_5573201 : Nat := 4983230072969 + 3 ^ 40 * 5573201 * 2
def baseEnd_5573201 : Nat := 2861730897118354559156821

theorem tailTrace_5573201 : CollatzResearch.WordTrace tailWord_5573201 prefixEnd_5573201 2861730897118354559156821 := by
  unfold tailWord_5573201
  simp only [CollatzResearch.WordTrace]
  refine ⟨203271339882252078797095457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135514226588168052531396971 203271339882252078797095457)
  ·
    refine ⟨152453504911689059097821593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203271339882252078797095457 152453504911689059097821593)
    ·
      refine ⟨114340128683766794323366195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152453504911689059097821593 114340128683766794323366195)
      ·
        refine ⟨171510193025650191485049293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114340128683766794323366195 171510193025650191485049293)
        ·
          refine ⟨64316322384618821806893485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171510193025650191485049293 64316322384618821806893485)
          ·
            refine ⟨24118620894232058177585057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64316322384618821806893485 24118620894232058177585057)
            ·
              refine ⟨18088965670674043633188793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24118620894232058177585057 18088965670674043633188793)
              ·
                refine ⟨13566724253005532724891595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18088965670674043633188793 13566724253005532724891595)
                ·
                  refine ⟨20350086379508299087337393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13566724253005532724891595 20350086379508299087337393)
                  ·
                    refine ⟨15262564784631224315503045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20350086379508299087337393 15262564784631224315503045)
                    ·
                      refine ⟨2861730897118354559156821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15262564784631224315503045 2861730897118354559156821)
                      ·
                        rfl

theorem cell23_5573201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_5573201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573201 prefixEnd_5573201 := by exact prefixLift 5573201
  have htrace : WordTrace (prefixWord ++ tailWord_5573201) baseStart_5573201 baseEnd_5573201 := by
    simpa [prefixWord, tailWord_5573201, baseEnd_5573201] using wordTrace_append hprefix tailTrace_5573201
  have hstable : (prefixWord ++ tailWord_5573201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573201).length < 2 ^ (prefixWord ++ tailWord_5573201).sum := by decide
  have hdescent : baseEnd_5573201 < baseStart_5573201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573245 : List Nat := [1, 4, 1, 1, 6, 1, 2, 7]
def baseStart_5573245 : Nat := 118140960795 + 5573245 * 2 ^ 59
def prefixEnd_5573245 : Nat := 4983230072969 + 3 ^ 40 * 5573245 * 2
def baseEnd_5573245 : Nat := 105990870009894532852097

theorem tailTrace_5573245 : CollatzResearch.WordTrace tailWord_5573245 prefixEnd_5573245 105990870009894532852097 := by
  unfold tailWord_5573245
  simp only [CollatzResearch.WordTrace]
  refine ⟨203272944694092674311697189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135515296462728449541131459 203272944694092674311697189)
  ·
    refine ⟨38113677130142376433443223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203272944694092674311697189 38113677130142376433443223)
    ·
      refine ⟨57170515695213564650164835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38113677130142376433443223 57170515695213564650164835)
      ·
        refine ⟨85755773542820346975247253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57170515695213564650164835 85755773542820346975247253)
        ·
          refine ⟨4019801884819703764464715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85755773542820346975247253 4019801884819703764464715)
          ·
            refine ⟨6029702827229555646697073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019801884819703764464715 6029702827229555646697073)
            ·
              refine ⟨4522277120422166735022805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6029702827229555646697073 4522277120422166735022805)
              ·
                refine ⟨105990870009894532852097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4522277120422166735022805 105990870009894532852097)
                ·
                  rfl

theorem cell23_5573245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 7].length) (baseStart_5573245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573245 prefixEnd_5573245 := by exact prefixLift 5573245
  have htrace : WordTrace (prefixWord ++ tailWord_5573245) baseStart_5573245 baseEnd_5573245 := by
    simpa [prefixWord, tailWord_5573245, baseEnd_5573245] using wordTrace_append hprefix tailTrace_5573245
  have hstable : (prefixWord ++ tailWord_5573245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573245).length < 2 ^ (prefixWord ++ tailWord_5573245).sum := by decide
  have hdescent : baseEnd_5573245 < baseStart_5573245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573250 : List Nat := [3, 4, 3, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5573250 : Nat := 118140960795 + 5573250 * 2 ^ 59
def prefixEnd_5573250 : Nat := 4983230072969 + 3 ^ 40 * 5573250 * 2
def baseEnd_5573250 : Nat := 2861756057670424867444097

theorem tailTrace_5573250 : CollatzResearch.WordTrace tailWord_5573250 prefixEnd_5573250 2861756057670424867444097 := by
  unfold tailWord_5573250
  simp only [CollatzResearch.WordTrace]
  refine ⟨50818281764768640041407301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135515418039383040110419469 50818281764768640041407301)
  ·
    refine ⟨9528427830894120007763869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50818281764768640041407301 9528427830894120007763869)
    ·
      refine ⟨3573160436585295002911451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9528427830894120007763869 3573160436585295002911451)
      ·
        refine ⟨5359740654877942504367177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3573160436585295002911451 5359740654877942504367177)
        ·
          refine ⟨4019805491158456878275383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5359740654877942504367177 4019805491158456878275383)
          ·
            refine ⟨6029708236737685317413075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019805491158456878275383 6029708236737685317413075)
            ·
              refine ⟨9044562355106527976119613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6029708236737685317413075 9044562355106527976119613)
              ·
                refine ⟨3391710883164947991044855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9044562355106527976119613 3391710883164947991044855)
                ·
                  refine ⟨5087566324747421986567283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391710883164947991044855 5087566324747421986567283)
                  ·
                    refine ⟨7631349487121132979850925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087566324747421986567283 7631349487121132979850925)
                    ·
                      refine ⟨2861756057670424867444097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631349487121132979850925 2861756057670424867444097)
                      ·
                        rfl

theorem cell23_5573250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5573250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573250 prefixEnd_5573250 := by exact prefixLift 5573250
  have htrace : WordTrace (prefixWord ++ tailWord_5573250) baseStart_5573250 baseEnd_5573250 := by
    simpa [prefixWord, tailWord_5573250, baseEnd_5573250] using wordTrace_append hprefix tailTrace_5573250
  have hstable : (prefixWord ++ tailWord_5573250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573250).length < 2 ^ (prefixWord ++ tailWord_5573250).sum := by decide
  have hdescent : baseEnd_5573250 < baseStart_5573250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573278 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5573278 : Nat := 118140960795 + 5573278 * 2 ^ 59
def prefixEnd_5573278 : Nat := 4983230072969 + 3 ^ 40 * 5573278 * 2
def baseEnd_5573278 : Nat := 2861770435128750757893967

theorem tailTrace_5573278 : CollatzResearch.WordTrace tailWord_5573278 prefixEnd_5573278 2861770435128750757893967 := by
  unfold tailWord_5573278
  simp only [CollatzResearch.WordTrace]
  refine ⟨25409268537871640118456061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135516098868648747298432325 25409268537871640118456061)
  ·
    refine ⟨9528475701701865044421023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25409268537871640118456061 9528475701701865044421023)
    ·
      refine ⟨14292713552552797566631535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9528475701701865044421023 14292713552552797566631535)
      ·
        refine ⟨21439070328829196349947303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14292713552552797566631535 21439070328829196349947303)
        ·
          refine ⟨32158605493243794524920955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21439070328829196349947303 32158605493243794524920955)
          ·
            refine ⟨48237908239865691787381433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32158605493243794524920955 48237908239865691787381433)
            ·
              refine ⟨36178431179899268840536075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48237908239865691787381433 36178431179899268840536075)
              ·
                refine ⟨54267646769848903260804113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36178431179899268840536075 54267646769848903260804113)
                ·
                  refine ⟨40700735077386677445603085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54267646769848903260804113 40700735077386677445603085)
                  ·
                    refine ⟨15262775654020004042101157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40700735077386677445603085 15262775654020004042101157)
                    ·
                      refine ⟨2861770435128750757893967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15262775654020004042101157 2861770435128750757893967)
                      ·
                        rfl

theorem cell23_5573278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5573278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573278 prefixEnd_5573278 := by exact prefixLift 5573278
  have htrace : WordTrace (prefixWord ++ tailWord_5573278) baseStart_5573278 baseEnd_5573278 := by
    simpa [prefixWord, tailWord_5573278, baseEnd_5573278] using wordTrace_append hprefix tailTrace_5573278
  have hstable : (prefixWord ++ tailWord_5573278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573278).length < 2 ^ (prefixWord ++ tailWord_5573278).sum := by decide
  have hdescent : baseEnd_5573278 < baseStart_5573278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573335 : List Nat := [1, 1, 3, 2, 1, 4, 4, 2, 5]
def baseStart_5573335 : Nat := 118140960795 + 5573335 * 2 ^ 59
def prefixEnd_5573335 : Nat := 4983230072969 + 3 ^ 40 * 5573335 * 2
def baseEnd_5573335 : Nat := 317977744836228559431245

theorem tailTrace_5573335 : CollatzResearch.WordTrace tailWord_5573335 prefixEnd_5573335 317977744836228559431245 := by
  unfold tailWord_5573335
  simp only [CollatzResearch.WordTrace]
  refine ⟨203276227263766619682473459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135517484842511079788315639 203276227263766619682473459)
  ·
    refine ⟨304914340895649929523710189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203276227263766619682473459 304914340895649929523710189)
    ·
      refine ⟨114342877835868723571391321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304914340895649929523710189 114342877835868723571391321)
      ·
        refine ⟨85757158376901542678543491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114342877835868723571391321 85757158376901542678543491)
        ·
          refine ⟨128635737565352314017815237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85757158376901542678543491 128635737565352314017815237)
          ·
            refine ⟨24119200793503558878340357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128635737565352314017815237 24119200793503558878340357)
            ·
              refine ⟨4522350148781917289688817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24119200793503558878340357 4522350148781917289688817)
              ·
                refine ⟨3391762611586437967266613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522350148781917289688817 3391762611586437967266613)
                ·
                  refine ⟨317977744836228559431245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3391762611586437967266613 317977744836228559431245)
                  ·
                    rfl

theorem cell23_5573335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 5].length) (baseStart_5573335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573335 prefixEnd_5573335 := by exact prefixLift 5573335
  have htrace : WordTrace (prefixWord ++ tailWord_5573335) baseStart_5573335 baseEnd_5573335 := by
    simpa [prefixWord, tailWord_5573335, baseEnd_5573335] using wordTrace_append hprefix tailTrace_5573335
  have hstable : (prefixWord ++ tailWord_5573335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573335).length < 2 ^ (prefixWord ++ tailWord_5573335).sum := by decide
  have hdescent : baseEnd_5573335 < baseStart_5573335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573338 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2]
def baseStart_5573338 : Nat := 118140960795 + 5573338 * 2 ^ 59
def prefixEnd_5573338 : Nat := 4983230072969 + 3 ^ 40 * 5573338 * 2
def baseEnd_5573338 : Nat := 2861801243968020523143691

theorem tailTrace_5573338 : CollatzResearch.WordTrace tailWord_5573338 prefixEnd_5573338 2861801243968020523143691 := by
  unfold tailWord_5573338
  simp only [CollatzResearch.WordTrace]
  refine ⟨50819084170688937798708167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135517557788503834129888445 50819084170688937798708167)
  ·
    refine ⟨76228626256033406698062251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50819084170688937798708167 76228626256033406698062251)
    ·
      refine ⟨114342939384050110047093377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76228626256033406698062251 114342939384050110047093377)
      ·
        refine ⟨85757204538037582535320033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114342939384050110047093377 85757204538037582535320033)
        ·
          refine ⟨64317903403528186901490025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85757204538037582535320033 64317903403528186901490025)
          ·
            refine ⟨48238427552646140176117519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64317903403528186901490025 48238427552646140176117519)
            ·
              refine ⟨72357641328969210264176279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48238427552646140176117519 72357641328969210264176279)
              ·
                refine ⟨108536461993453815396264419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72357641328969210264176279 108536461993453815396264419)
                ·
                  refine ⟨162804692990180723094396629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108536461993453815396264419 162804692990180723094396629)
                  ·
                    refine ⟨3815734991957360697524921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162804692990180723094396629 3815734991957360697524921)
                    ·
                      refine ⟨2861801243968020523143691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815734991957360697524921 2861801243968020523143691)
                      ·
                        rfl

theorem cell23_5573338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_5573338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573338 prefixEnd_5573338 := by exact prefixLift 5573338
  have htrace : WordTrace (prefixWord ++ tailWord_5573338) baseStart_5573338 baseEnd_5573338 := by
    simpa [prefixWord, tailWord_5573338, baseEnd_5573338] using wordTrace_append hprefix tailTrace_5573338
  have hstable : (prefixWord ++ tailWord_5573338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573338).length < 2 ^ (prefixWord ++ tailWord_5573338).sum := by decide
  have hdescent : baseEnd_5573338 < baseStart_5573338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573368 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 1, 6, 2]
def baseStart_5573368 : Nat := 118140960795 + 5573368 * 2 ^ 59
def prefixEnd_5573368 : Nat := 4983230072969 + 3 ^ 40 * 5573368 * 2
def baseEnd_5573368 : Nat := 2861816648387655405768553

theorem tailTrace_5573368 : CollatzResearch.WordTrace tailWord_5573368 prefixEnd_5573368 2861816648387655405768553 := by
  unfold tailWord_5573368
  simp only [CollatzResearch.WordTrace]
  refine ⟨101638715436323533159212379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135518287248431377545616505 101638715436323533159212379)
  ·
    refine ⟨152458073154485299738818569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101638715436323533159212379 152458073154485299738818569)
    ·
      refine ⟨114343554865863974804113927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152458073154485299738818569 114343554865863974804113927)
      ·
        refine ⟨171515332298795962206170891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114343554865863974804113927 171515332298795962206170891)
        ·
          refine ⟨257272998448193943309256337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171515332298795962206170891 257272998448193943309256337)
          ·
            refine ⟨192954748836145457481942253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257272998448193943309256337 192954748836145457481942253)
            ·
              refine ⟨72358030813554546555728345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192954748836145457481942253 72358030813554546555728345)
              ·
                refine ⟨54268523110165909916796259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72358030813554546555728345 54268523110165909916796259)
                ·
                  refine ⟨81402784665248864875194389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54268523110165909916796259 81402784665248864875194389)
                  ·
                    refine ⟨3815755531183540541024737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81402784665248864875194389 3815755531183540541024737)
                    ·
                      refine ⟨2861816648387655405768553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815755531183540541024737 2861816648387655405768553)
                      ·
                        rfl

theorem cell23_5573368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_5573368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573368 prefixEnd_5573368 := by exact prefixLift 5573368
  have htrace : WordTrace (prefixWord ++ tailWord_5573368) baseStart_5573368 baseEnd_5573368 := by
    simpa [prefixWord, tailWord_5573368, baseEnd_5573368] using wordTrace_append hprefix tailTrace_5573368
  have hstable : (prefixWord ++ tailWord_5573368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573368).length < 2 ^ (prefixWord ++ tailWord_5573368).sum := by decide
  have hdescent : baseEnd_5573368 < baseStart_5573368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573381 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_5573381 : Nat := 118140960795 + 5573381 * 2 ^ 59
def prefixEnd_5573381 : Nat := 4983230072969 + 3 ^ 40 * 5573381 * 2
def baseEnd_5573381 : Nat := 2861823323636163854905993

theorem tailTrace_5573381 : CollatzResearch.WordTrace tailWord_5573381 prefixEnd_5573381 2861823323636163854905993 := by
  unfold tailWord_5573381
  simp only [CollatzResearch.WordTrace]
  refine ⟨203277905021599969538647997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135518603347733313025765331 203277905021599969538647997)
  ·
    refine ⟨76229214383099988576992999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203277905021599969538647997 76229214383099988576992999)
    ·
      refine ⟨114343821574649982865489499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76229214383099988576992999 114343821574649982865489499)
      ·
        refine ⟨171515732361974974298234249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114343821574649982865489499 171515732361974974298234249)
        ·
          refine ⟨128636799271481230723675687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171515732361974974298234249 128636799271481230723675687)
          ·
            refine ⟨192955198907221846085513531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128636799271481230723675687 192955198907221846085513531)
            ·
              refine ⟨289432798360832769128270297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192955198907221846085513531 289432798360832769128270297)
              ·
                refine ⟨217074598770624576846202723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289432798360832769128270297 217074598770624576846202723)
                ·
                  refine ⟨325611898155936865269304085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217074598770624576846202723 325611898155936865269304085)
                  ·
                    refine ⟨15263057726059540559498629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 325611898155936865269304085 15263057726059540559498629)
                    ·
                      refine ⟨2861823323636163854905993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15263057726059540559498629 2861823323636163854905993)
                      ·
                        rfl

theorem cell23_5573381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_5573381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573381 prefixEnd_5573381 := by exact prefixLift 5573381
  have htrace : WordTrace (prefixWord ++ tailWord_5573381) baseStart_5573381 baseEnd_5573381 := by
    simpa [prefixWord, tailWord_5573381, baseEnd_5573381] using wordTrace_append hprefix tailTrace_5573381
  have hstable : (prefixWord ++ tailWord_5573381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573381).length < 2 ^ (prefixWord ++ tailWord_5573381).sum := by decide
  have hdescent : baseEnd_5573381 < baseStart_5573381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573388 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_5573388 : Nat := 118140960795 + 5573388 * 2 ^ 59
def prefixEnd_5573388 : Nat := 4983230072969 + 3 ^ 40 * 5573388 * 2
def baseEnd_5573388 : Nat := 2861826918000745327518461

theorem tailTrace_5573388 : CollatzResearch.WordTrace tailWord_5573388 prefixEnd_5573388 2861826918000745327518461 := by
  unfold tailWord_5573388
  simp only [CollatzResearch.WordTrace]
  refine ⟨101639080166287304867076409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135518773555049739822768545 101639080166287304867076409)
  ·
    refine ⟨76229310124715478650307307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101639080166287304867076409 76229310124715478650307307)
    ·
      refine ⟨114343965187073217975460961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76229310124715478650307307 114343965187073217975460961)
      ·
        refine ⟨85757973890304913481595721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114343965187073217975460961 85757973890304913481595721)
        ·
          refine ⟨64318480417728685111196791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85757973890304913481595721 64318480417728685111196791)
          ·
            refine ⟨96477720626593027666795187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64318480417728685111196791 96477720626593027666795187)
            ·
              refine ⟨144716580939889541500192781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96477720626593027666795187 144716580939889541500192781)
              ·
                refine ⟨54268717852458578062572293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144716580939889541500192781 54268717852458578062572293)
                ·
                  refine ⟨10175384597335983386732305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54268717852458578062572293 10175384597335983386732305)
                  ·
                    refine ⟨7631538448001987540049229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10175384597335983386732305 7631538448001987540049229)
                    ·
                      refine ⟨2861826918000745327518461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631538448001987540049229 2861826918000745327518461)
                      ·
                        rfl

theorem cell23_5573388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_5573388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573388 prefixEnd_5573388 := by exact prefixLift 5573388
  have htrace : WordTrace (prefixWord ++ tailWord_5573388) baseStart_5573388 baseEnd_5573388 := by
    simpa [prefixWord, tailWord_5573388, baseEnd_5573388] using wordTrace_append hprefix tailTrace_5573388
  have hstable : (prefixWord ++ tailWord_5573388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573388).length < 2 ^ (prefixWord ++ tailWord_5573388).sum := by decide
  have hdescent : baseEnd_5573388 < baseStart_5573388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573391 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 8]
def baseStart_5573391 : Nat := 118140960795 + 5573391 * 2 ^ 59
def prefixEnd_5573391 : Nat := 4983230072969 + 3 ^ 40 * 5573391 * 2
def baseEnd_5573391 : Nat := 317980939826967646197883

theorem tailTrace_5573391 : CollatzResearch.WordTrace tailWord_5573391 prefixEnd_5573391 317980939826967646197883 := by
  unfold tailWord_5573391
  simp only [CollatzResearch.WordTrace]
  refine ⟨203278269751563741246512027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135518846501042494164341351 203278269751563741246512027)
  ·
    refine ⟨304917404627345611869768041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203278269751563741246512027 304917404627345611869768041)
    ·
      refine ⟨228688053470509208902326031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304917404627345611869768041 228688053470509208902326031)
      ·
        refine ⟨343032080205763813353489047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228688053470509208902326031 343032080205763813353489047)
        ·
          refine ⟨514548120308645720030233571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343032080205763813353489047 514548120308645720030233571)
          ·
            refine ⟨771822180462968580045350357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514548120308645720030233571 771822180462968580045350357)
            ·
              refine ⟨18089582354600826094812899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 771822180462968580045350357 18089582354600826094812899)
              ·
                refine ⟨27134373531901239142219349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18089582354600826094812899 27134373531901239142219349)
                ·
                  refine ⟨317980939826967646197883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27134373531901239142219349 317980939826967646197883)
                  ·
                    rfl

theorem cell23_5573391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 8].length) (baseStart_5573391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573391 prefixEnd_5573391 := by exact prefixLift 5573391
  have htrace : WordTrace (prefixWord ++ tailWord_5573391) baseStart_5573391 baseEnd_5573391 := by
    simpa [prefixWord, tailWord_5573391, baseEnd_5573391] using wordTrace_append hprefix tailTrace_5573391
  have hstable : (prefixWord ++ tailWord_5573391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573391).length < 2 ^ (prefixWord ++ tailWord_5573391).sum := by decide
  have hdescent : baseEnd_5573391 < baseStart_5573391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573395 : List Nat := [1, 1, 1, 2, 1, 3, 3, 6, 1, 4]
def baseStart_5573395 : Nat := 118140960795 + 5573395 * 2 ^ 59
def prefixEnd_5573395 : Nat := 4983230072969 + 3 ^ 40 * 5573395 * 2
def baseEnd_5573395 : Nat := 953943504121775600043643

theorem tailTrace_5573395 : CollatzResearch.WordTrace tailWord_5573395 prefixEnd_5573395 953943504121775600043643 := by
  unfold tailWord_5573395
  simp only [CollatzResearch.WordTrace]
  refine ⟨203278415643549249929657639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135518943762366166619771759 203278415643549249929657639)
  ·
    refine ⟨304917623465323874894486459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203278415643549249929657639 304917623465323874894486459)
    ·
      refine ⟨457376435197985812341729689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304917623465323874894486459 457376435197985812341729689)
      ·
        refine ⟨343032326398489359256297267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457376435197985812341729689 343032326398489359256297267)
        ·
          refine ⟨514548489597734038884445901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343032326398489359256297267 514548489597734038884445901)
          ·
            refine ⟨192955683599150264581667213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514548489597734038884445901 192955683599150264581667213)
            ·
              refine ⟨72358381349681349218125205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192955683599150264581667213 72358381349681349218125205)
              ·
                refine ⟨3391799125766313244599619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72358381349681349218125205 3391799125766313244599619)
                ·
                  refine ⟨5087698688649469866899429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391799125766313244599619 5087698688649469866899429)
                  ·
                    refine ⟨953943504121775600043643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087698688649469866899429 953943504121775600043643)
                    ·
                      rfl

theorem cell23_5573395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 4].length) (baseStart_5573395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573395 prefixEnd_5573395 := by exact prefixLift 5573395
  have htrace : WordTrace (prefixWord ++ tailWord_5573395) baseStart_5573395 baseEnd_5573395 := by
    simpa [prefixWord, tailWord_5573395, baseEnd_5573395] using wordTrace_append hprefix tailTrace_5573395
  have hstable : (prefixWord ++ tailWord_5573395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573395).length < 2 ^ (prefixWord ++ tailWord_5573395).sum := by decide
  have hdescent : baseEnd_5573395 < baseStart_5573395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573411 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6]
def baseStart_5573411 : Nat := 118140960795 + 5573411 * 2 ^ 59
def prefixEnd_5573411 : Nat := 4983230072969 + 3 ^ 40 * 5573411 * 2
def baseEnd_5573411 : Nat := 2861838728055798737530855

theorem tailTrace_5573411 : CollatzResearch.WordTrace tailWord_5573411 prefixEnd_5573411 2861838728055798737530855 := by
  unfold tailWord_5573411
  simp only [CollatzResearch.WordTrace]
  refine ⟨203278999211491284662240087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135519332807660856441493391 203278999211491284662240087)
  ·
    refine ⟨304918498817236926993360131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203278999211491284662240087 304918498817236926993360131)
    ·
      refine ⟨457377748225855390490040197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304918498817236926993360131 457377748225855390490040197)
      ·
        refine ⟨85758327792347885716882537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 457377748225855390490040197 85758327792347885716882537)
        ·
          refine ⟨64318745844260914287661903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85758327792347885716882537 64318745844260914287661903)
          ·
            refine ⟨96478118766391371431492855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64318745844260914287661903 96478118766391371431492855)
            ·
              refine ⟨144717178149587057147239283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96478118766391371431492855 144717178149587057147239283)
              ·
                refine ⟨217075767224380585720858925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144717178149587057147239283 217075767224380585720858925)
                ·
                  refine ⟨81403412709142719645322097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217075767224380585720858925 81403412709142719645322097)
                  ·
                    refine ⟨61052559531857039733991573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81403412709142719645322097 61052559531857039733991573)
                    ·
                      refine ⟨2861838728055798737530855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61052559531857039733991573 2861838728055798737530855)
                      ·
                        rfl

theorem cell23_5573411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_5573411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573411 prefixEnd_5573411 := by exact prefixLift 5573411
  have htrace : WordTrace (prefixWord ++ tailWord_5573411) baseStart_5573411 baseEnd_5573411 := by
    simpa [prefixWord, tailWord_5573411, baseEnd_5573411] using wordTrace_append hprefix tailTrace_5573411
  have hstable : (prefixWord ++ tailWord_5573411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573411).length < 2 ^ (prefixWord ++ tailWord_5573411).sum := by decide
  have hdescent : baseEnd_5573411 < baseStart_5573411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573429 : List Nat := [1, 3, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_5573429 : Nat := 118140960795 + 5573429 * 2 ^ 59
def prefixEnd_5573429 : Nat := 4983230072969 + 3 ^ 40 * 5573429 * 2
def baseEnd_5573429 : Nat := 953949323569193222368591

theorem tailTrace_5573429 : CollatzResearch.WordTrace tailWord_5573429 prefixEnd_5573429 953949323569193222368591 := by
  unfold tailWord_5573429
  simp only [CollatzResearch.WordTrace]
  refine ⟨203279655725426073736395341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135519770483617382490930227 203279655725426073736395341)
  ·
    refine ⟨76229870897034777651148253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203279655725426073736395341 76229870897034777651148253)
    ·
      refine ⟨28586201586388041619180595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76229870897034777651148253 28586201586388041619180595)
      ·
        refine ⟨42879302379582062428770893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28586201586388041619180595 42879302379582062428770893)
        ·
          refine ⟨16079738392343273410789085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42879302379582062428770893 16079738392343273410789085)
          ·
            refine ⟨6029901897128727529045907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16079738392343273410789085 6029901897128727529045907)
            ·
              refine ⟨9044852845693091293568861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6029901897128727529045907 9044852845693091293568861)
              ·
                refine ⟨3391819817134909235088323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9044852845693091293568861 3391819817134909235088323)
                ·
                  refine ⟨5087729725702363852632485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391819817134909235088323 5087729725702363852632485)
                  ·
                    refine ⟨953949323569193222368591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087729725702363852632485 953949323569193222368591)
                    ·
                      rfl

theorem cell23_5573429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_5573429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573429 prefixEnd_5573429 := by exact prefixLift 5573429
  have htrace : WordTrace (prefixWord ++ tailWord_5573429) baseStart_5573429 baseEnd_5573429 := by
    simpa [prefixWord, tailWord_5573429, baseEnd_5573429] using wordTrace_append hprefix tailTrace_5573429
  have hstable : (prefixWord ++ tailWord_5573429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573429).length < 2 ^ (prefixWord ++ tailWord_5573429).sum := by decide
  have hdescent : baseEnd_5573429 < baseStart_5573429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573446 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_5573446 : Nat := 118140960795 + 5573446 * 2 ^ 59
def prefixEnd_5573446 : Nat := 4983230072969 + 3 ^ 40 * 5573446 * 2
def baseEnd_5573446 : Nat := 953952233292902033531065

theorem tailTrace_5573446 : CollatzResearch.WordTrace tailWord_5573446 prefixEnd_5573446 953952233292902033531065 := by
  unfold tailWord_5573446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6352508617698890176242631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135520183844242990426509461 6352508617698890176242631)
  ·
    refine ⟨9528762926548335264363947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6352508617698890176242631 9528762926548335264363947)
    ·
      refine ⟨14293144389822502896545921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9528762926548335264363947 14293144389822502896545921)
      ·
        refine ⟨10719858292366877172409441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14293144389822502896545921 10719858292366877172409441)
        ·
          refine ⟨8039893719275157879307081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10719858292366877172409441 8039893719275157879307081)
          ·
            refine ⟨6029920289456368409480311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8039893719275157879307081 6029920289456368409480311)
            ·
              refine ⟨9044880434184552614220467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6029920289456368409480311 9044880434184552614220467)
              ·
                refine ⟨13567320651276828921330701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9044880434184552614220467 13567320651276828921330701)
                ·
                  refine ⟨5087745244228810845499013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13567320651276828921330701 5087745244228810845499013)
                  ·
                    refine ⟨953952233292902033531065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087745244228810845499013 953952233292902033531065)
                    ·
                      rfl

theorem cell23_5573446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_5573446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573446 prefixEnd_5573446 := by exact prefixLift 5573446
  have htrace : WordTrace (prefixWord ++ tailWord_5573446) baseStart_5573446 baseEnd_5573446 := by
    simpa [prefixWord, tailWord_5573446, baseEnd_5573446] using wordTrace_append hprefix tailTrace_5573446
  have hstable : (prefixWord ++ tailWord_5573446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573446).length < 2 ^ (prefixWord ++ tailWord_5573446).sum := by decide
  have hdescent : baseEnd_5573446 < baseStart_5573446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573452 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_5573452 : Nat := 118140960795 + 5573452 * 2 ^ 59
def prefixEnd_5573452 : Nat := 4983230072969 + 3 ^ 40 * 5573452 * 2
def baseEnd_5573452 : Nat := 2861859780762633077118167

theorem tailTrace_5573452 : CollatzResearch.WordTrace tailWord_5573452 prefixEnd_5573452 2861859780762633077118167 := by
  unfold tailWord_5573452
  simp only [CollatzResearch.WordTrace]
  refine ⟨101640247302171374332241305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135520329736228499109655073 101640247302171374332241305)
  ·
    refine ⟨76230185476628530749180979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101640247302171374332241305 76230185476628530749180979)
    ·
      refine ⟨114345278214942796123771469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76230185476628530749180979 114345278214942796123771469)
      ·
        refine ⟨42879479330603548546414301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114345278214942796123771469 42879479330603548546414301)
        ·
          refine ⟨16079804748976330704905363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42879479330603548546414301 16079804748976330704905363)
          ·
            refine ⟨24119707123464496057358045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16079804748976330704905363 24119707123464496057358045)
            ·
              refine ⟨9044890171299186021509267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24119707123464496057358045 9044890171299186021509267)
              ·
                refine ⟨13567335256948779032263901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9044890171299186021509267 13567335256948779032263901)
                ·
                  refine ⟨5087750721355792137098963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13567335256948779032263901 5087750721355792137098963)
                  ·
                    refine ⟨7631626082033688205648445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087750721355792137098963 7631626082033688205648445)
                    ·
                      refine ⟨2861859780762633077118167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631626082033688205648445 2861859780762633077118167)
                      ·
                        rfl

theorem cell23_5573452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_5573452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573452 prefixEnd_5573452 := by exact prefixLift 5573452
  have htrace : WordTrace (prefixWord ++ tailWord_5573452) baseStart_5573452 baseEnd_5573452 := by
    simpa [prefixWord, tailWord_5573452, baseEnd_5573452] using wordTrace_append hprefix tailTrace_5573452
  have hstable : (prefixWord ++ tailWord_5573452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573452).length < 2 ^ (prefixWord ++ tailWord_5573452).sum := by decide
  have hdescent : baseEnd_5573452 < baseStart_5573452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573475 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 4]
def baseStart_5573475 : Nat := 118140960795 + 5573475 * 2 ^ 59
def prefixEnd_5573475 : Nat := 4983230072969 + 3 ^ 40 * 5573475 * 2
def baseEnd_5573475 : Nat := 2861871590817686487130561

theorem tailTrace_5573475 : CollatzResearch.WordTrace tailWord_5573475 prefixEnd_5573475 2861871590817686487130561 := by
  unfold tailWord_5573475
  simp only [CollatzResearch.WordTrace]
  refine ⟨203281333483259423592569879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135520888988839615728379919 203281333483259423592569879)
  ·
    refine ⟨304922000224889135388854819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203281333483259423592569879 304922000224889135388854819)
    ·
      refine ⟨457383000337333703083282229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304922000224889135388854819 457383000337333703083282229)
      ·
        refine ⟨42879656281625034664057709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 457383000337333703083282229 42879656281625034664057709)
        ·
          refine ⟨16079871105609387999021641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42879656281625034664057709 16079871105609387999021641)
          ·
            refine ⟨12059903329207040999266231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16079871105609387999021641 12059903329207040999266231)
            ·
              refine ⟨18089854993810561498899347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12059903329207040999266231 18089854993810561498899347)
              ·
                refine ⟨27134782490715842248349021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18089854993810561498899347 27134782490715842248349021)
                ·
                  refine ⟨10175543434018440843130883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27134782490715842248349021 10175543434018440843130883)
                  ·
                    refine ⟨15263315151027661264696325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10175543434018440843130883 15263315151027661264696325)
                    ·
                      refine ⟨2861871590817686487130561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15263315151027661264696325 2861871590817686487130561)
                      ·
                        rfl

theorem cell23_5573475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_5573475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573475 prefixEnd_5573475 := by exact prefixLift 5573475
  have htrace : WordTrace (prefixWord ++ tailWord_5573475) baseStart_5573475 baseEnd_5573475 := by
    simpa [prefixWord, tailWord_5573475, baseEnd_5573475] using wordTrace_append hprefix tailTrace_5573475
  have hstable : (prefixWord ++ tailWord_5573475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573475).length < 2 ^ (prefixWord ++ tailWord_5573475).sum := by decide
  have hdescent : baseEnd_5573475 < baseStart_5573475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573488 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_5573488 : Nat := 118140960795 + 5573488 * 2 ^ 59
def prefixEnd_5573488 : Nat := 4983230072969 + 3 ^ 40 * 5573488 * 2
def baseEnd_5573488 : Nat := 2861878266066194936268001

theorem tailTrace_5573488 : CollatzResearch.WordTrace tailWord_5573488 prefixEnd_5573488 2861878266066194936268001 := by
  unfold tailWord_5573488
  simp only [CollatzResearch.WordTrace]
  refine ⟨101640903816106163406396559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135521205088141551208528745 101640903816106163406396559)
  ·
    refine ⟨152461355724159245109594839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101640903816106163406396559 152461355724159245109594839)
    ·
      refine ⟨228692033586238867664392259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152461355724159245109594839 228692033586238867664392259)
      ·
        refine ⟨343038050379358301496588389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228692033586238867664392259 343038050379358301496588389)
        ·
          refine ⟨64319634446129681530610323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343038050379358301496588389 64319634446129681530610323)
          ·
            refine ⟨96479451669194522295915485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64319634446129681530610323 96479451669194522295915485)
            ·
              refine ⟨36179794375947945860968307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96479451669194522295915485 36179794375947945860968307)
              ·
                refine ⟨54269691563921918791452461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36179794375947945860968307 54269691563921918791452461)
                ·
                  refine ⟨20351134336470719546794673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54269691563921918791452461 20351134336470719546794673)
                  ·
                    refine ⟨15263350752353039660096005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20351134336470719546794673 15263350752353039660096005)
                    ·
                      refine ⟨2861878266066194936268001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15263350752353039660096005 2861878266066194936268001)
                      ·
                        rfl

theorem cell23_5573488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_5573488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573488 prefixEnd_5573488 := by exact prefixLift 5573488
  have htrace : WordTrace (prefixWord ++ tailWord_5573488) baseStart_5573488 baseEnd_5573488 := by
    simpa [prefixWord, tailWord_5573488, baseEnd_5573488] using wordTrace_append hprefix tailTrace_5573488
  have hstable : (prefixWord ++ tailWord_5573488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573488).length < 2 ^ (prefixWord ++ tailWord_5573488).sum := by decide
  have hdescent : baseEnd_5573488 < baseStart_5573488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573495 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_5573495 : Nat := 118140960795 + 5573495 * 2 ^ 59
def prefixEnd_5573495 : Nat := 4983230072969 + 3 ^ 40 * 5573495 * 2
def baseEnd_5573495 : Nat := 2861881860430776408880469

theorem tailTrace_5573495 : CollatzResearch.WordTrace tailWord_5573495 prefixEnd_5573495 2861881860430776408880469 := by
  unfold tailWord_5573495
  simp only [CollatzResearch.WordTrace]
  refine ⟨203282062943186967008297939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135521375295457978005531959 203282062943186967008297939)
  ·
    refine ⟨304923094414780450512446909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203282062943186967008297939 304923094414780450512446909)
    ·
      refine ⟨114346160405542668942167591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304923094414780450512446909 114346160405542668942167591)
      ·
        refine ⟨171519240608314003413251387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114346160405542668942167591 171519240608314003413251387)
        ·
          refine ⟨257278860912471005119877081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171519240608314003413251387 257278860912471005119877081)
          ·
            refine ⟨192959145684353253839907811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257278860912471005119877081 192959145684353253839907811)
            ·
              refine ⟨289438718526529880759861717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192959145684353253839907811 289438718526529880759861717)
              ·
                refine ⟨6783719965465544080309259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 289438718526529880759861717 6783719965465544080309259)
                ·
                  refine ⟨10175579948198316120463889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6783719965465544080309259 10175579948198316120463889)
                  ·
                    refine ⟨7631684961148737090347917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10175579948198316120463889 7631684961148737090347917)
                    ·
                      refine ⟨2861881860430776408880469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631684961148737090347917 2861881860430776408880469)
                      ·
                        rfl

theorem cell23_5573495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_5573495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573495 prefixEnd_5573495 := by exact prefixLift 5573495
  have htrace : WordTrace (prefixWord ++ tailWord_5573495) baseStart_5573495 baseEnd_5573495 := by
    simpa [prefixWord, tailWord_5573495, baseEnd_5573495] using wordTrace_append hprefix tailTrace_5573495
  have hstable : (prefixWord ++ tailWord_5573495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573495).length < 2 ^ (prefixWord ++ tailWord_5573495).sum := by decide
  have hdescent : baseEnd_5573495 < baseStart_5573495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573525 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_5573525 : Nat := 118140960795 + 5573525 * 2 ^ 59
def prefixEnd_5573525 : Nat := 4983230072969 + 3 ^ 40 * 5573525 * 2
def baseEnd_5573525 : Nat := 2861897264850411291505331

theorem tailTrace_5573525 : CollatzResearch.WordTrace tailWord_5573525 prefixEnd_5573525 2861897264850411291505331 := by
  unfold tailWord_5573525
  simp only [CollatzResearch.WordTrace]
  refine ⟨203283157133078282131890029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135522104755385521421260019 203283157133078282131890029)
  ·
    refine ⟨76231183924904355799458761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203283157133078282131890029 76231183924904355799458761)
    ·
      refine ⟨57173387943678266849594071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76231183924904355799458761 57173387943678266849594071)
      ·
        refine ⟨85760081915517400274391107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57173387943678266849594071 85760081915517400274391107)
        ·
          refine ⟨128640122873276100411586661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85760081915517400274391107 128640122873276100411586661)
          ·
            refine ⟨24120023038739268827172499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128640122873276100411586661 24120023038739268827172499)
            ·
              refine ⟨36180034558108903240758749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24120023038739268827172499 36180034558108903240758749)
              ·
                refine ⟨13567512959290838715284531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36180034558108903240758749 13567512959290838715284531)
                ·
                  refine ⟨20351269438936258072926797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13567512959290838715284531 20351269438936258072926797)
                  ·
                    refine ⟨7631726039601096777347549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20351269438936258072926797 7631726039601096777347549)
                    ·
                      refine ⟨2861897264850411291505331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631726039601096777347549 2861897264850411291505331)
                      ·
                        rfl

theorem cell23_5573525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_5573525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573525 prefixEnd_5573525 := by exact prefixLift 5573525
  have htrace : WordTrace (prefixWord ++ tailWord_5573525) baseStart_5573525 baseEnd_5573525 := by
    simpa [prefixWord, tailWord_5573525, baseEnd_5573525] using wordTrace_append hprefix tailTrace_5573525
  have hstable : (prefixWord ++ tailWord_5573525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573525).length < 2 ^ (prefixWord ++ tailWord_5573525).sum := by decide
  have hdescent : baseEnd_5573525 < baseStart_5573525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573532 : List Nat := [2, 2, 3, 3, 2, 1, 3, 7]
def baseStart_5573532 : Nat := 118140960795 + 5573532 * 2 ^ 59
def prefixEnd_5573532 : Nat := 4983230072969 + 3 ^ 40 * 5573532 * 2
def baseEnd_5573532 : Nat := 105996328119073806078437

theorem tailTrace_5573532 : CollatzResearch.WordTrace tailWord_5573532 prefixEnd_5573532 105996328119073806078437 := by
  unfold tailWord_5573532
  simp only [CollatzResearch.WordTrace]
  refine ⟨101641706222026461163697425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135522274962701948218263233 101641706222026461163697425)
  ·
    refine ⟨76231279666519845872773069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101641706222026461163697425 76231279666519845872773069)
    ·
      refine ⟨28586729874944942202289901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76231279666519845872773069 28586729874944942202289901)
      ·
        refine ⟨10720023703104353325858713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28586729874944942202289901 10720023703104353325858713)
        ·
          refine ⟨8040017777328264994394035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10720023703104353325858713 8040017777328264994394035)
          ·
            refine ⟨12060026665992397491591053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040017777328264994394035 12060026665992397491591053)
            ·
              refine ⟨4522509999747149059346645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12060026665992397491591053 4522509999747149059346645)
              ·
                refine ⟨105996328119073806078437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4522509999747149059346645 105996328119073806078437)
                ·
                  rfl

theorem cell23_5573532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 7].length) (baseStart_5573532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573532 prefixEnd_5573532 := by exact prefixLift 5573532
  have htrace : WordTrace (prefixWord ++ tailWord_5573532) baseStart_5573532 baseEnd_5573532 := by
    simpa [prefixWord, tailWord_5573532, baseEnd_5573532] using wordTrace_append hprefix tailTrace_5573532
  have hstable : (prefixWord ++ tailWord_5573532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573532).length < 2 ^ (prefixWord ++ tailWord_5573532).sum := by decide
  have hdescent : baseEnd_5573532 < baseStart_5573532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573543 : List Nat := [1, 1, 6, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_5573543 : Nat := 118140960795 + 5573543 * 2 ^ 59
def prefixEnd_5573543 : Nat := 4983230072969 + 3 ^ 40 * 5573543 * 2
def baseEnd_5573543 : Nat := 2861906507502192221080249

theorem tailTrace_5573543 : CollatzResearch.WordTrace tailWord_5573543 prefixEnd_5573543 2861906507502192221080249 := by
  unfold tailWord_5573543
  simp only [CollatzResearch.WordTrace]
  refine ⟨203283813647013071206045283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135522542431342047470696855 203283813647013071206045283)
  ·
    refine ⟨304925720470519606809067925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203283813647013071206045283 304925720470519606809067925)
    ·
      refine ⟨14293393147055606569175059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 304925720470519606809067925 14293393147055606569175059)
      ·
        refine ⟨21440089720583409853762589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14293393147055606569175059 21440089720583409853762589)
        ·
          refine ⟨8040033645218778695160971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21440089720583409853762589 8040033645218778695160971)
          ·
            refine ⟨12060050467828168042741457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040033645218778695160971 12060050467828168042741457)
            ·
              refine ⟨9045037850871126032056093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12060050467828168042741457 9045037850871126032056093)
              ·
                refine ⟨3391889194076672262021035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9045037850871126032056093 3391889194076672262021035)
                ·
                  refine ⟨5087833791115008393031553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391889194076672262021035 5087833791115008393031553)
                  ·
                    refine ⟨3815875343336256294773665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5087833791115008393031553 3815875343336256294773665)
                    ·
                      refine ⟨2861906507502192221080249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815875343336256294773665 2861906507502192221080249)
                      ·
                        rfl

theorem cell23_5573543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_5573543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573543 prefixEnd_5573543 := by exact prefixLift 5573543
  have htrace : WordTrace (prefixWord ++ tailWord_5573543) baseStart_5573543 baseEnd_5573543 := by
    simpa [prefixWord, tailWord_5573543, baseEnd_5573543] using wordTrace_append hprefix tailTrace_5573543
  have hstable : (prefixWord ++ tailWord_5573543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573543).length < 2 ^ (prefixWord ++ tailWord_5573543).sum := by decide
  have hdescent : baseEnd_5573543 < baseStart_5573543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573548 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_5573548 : Nat := 118140960795 + 5573548 * 2 ^ 59
def prefixEnd_5573548 : Nat := 4983230072969 + 3 ^ 40 * 5573548 * 2
def baseEnd_5573548 : Nat := 2861909074905464701517725

theorem tailTrace_5573548 : CollatzResearch.WordTrace tailWord_5573548 prefixEnd_5573548 2861909074905464701517725 := by
  unfold tailWord_5573548
  simp only [CollatzResearch.WordTrace]
  refine ⟨101641998005997478529988649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135522664007996638039984865 101641998005997478529988649)
  ·
    refine ⟨76231498504498108897491487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101641998005997478529988649 76231498504498108897491487)
    ·
      refine ⟨114347247756747163346237231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76231498504498108897491487 114347247756747163346237231)
      ·
        refine ⟨171520871635120745019355847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114347247756747163346237231 171520871635120745019355847)
        ·
          refine ⟨257281307452681117529033771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171520871635120745019355847 257281307452681117529033771)
          ·
            refine ⟨385921961179021676293550657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257281307452681117529033771 385921961179021676293550657)
            ·
              refine ⟨289441470884266257220162993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385921961179021676293550657 289441470884266257220162993)
              ·
                refine ⟨217081103163199692915122245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289441470884266257220162993 217081103163199692915122245)
                ·
                  refine ⟨40702706843099942421585421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217081103163199692915122245 40702706843099942421585421)
                  ·
                    refine ⟨15263515066162478408094533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40702706843099942421585421 15263515066162478408094533)
                    ·
                      refine ⟨2861909074905464701517725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15263515066162478408094533 2861909074905464701517725)
                      ·
                        rfl

theorem cell23_5573548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_5573548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573548 prefixEnd_5573548 := by exact prefixLift 5573548
  have htrace : WordTrace (prefixWord ++ tailWord_5573548) baseStart_5573548 baseEnd_5573548 := by
    simpa [prefixWord, tailWord_5573548, baseEnd_5573548] using wordTrace_append hprefix tailTrace_5573548
  have hstable : (prefixWord ++ tailWord_5573548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573548).length < 2 ^ (prefixWord ++ tailWord_5573548).sum := by decide
  have hdescent : baseEnd_5573548 < baseStart_5573548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573576 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_5573576 : Nat := 118140960795 + 5573576 * 2 ^ 59
def prefixEnd_5573576 : Nat := 4983230072969 + 3 ^ 40 * 5573576 * 2
def baseEnd_5573576 : Nat := 2861923452363790591967597

theorem tailTrace_5573576 : CollatzResearch.WordTrace tailWord_5573576 prefixEnd_5573576 2861923452363790591967597 := by
  unfold tailWord_5573576
  simp only [CollatzResearch.WordTrace]
  refine ⟨101642508627946758920998291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135523344837262345227997721 101642508627946758920998291)
  ·
    refine ⟨152463762941920138381497437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101642508627946758920998291 152463762941920138381497437)
    ·
      refine ⟨57173911103220051893061539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152463762941920138381497437 57173911103220051893061539)
      ·
        refine ⟨85760866654830077839592309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57173911103220051893061539 85760866654830077839592309)
        ·
          refine ⟨8040081248890319797461779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85760866654830077839592309 8040081248890319797461779)
          ·
            refine ⟨12060121873335479696192669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040081248890319797461779 12060121873335479696192669)
            ·
              refine ⟨4522545702500804886072251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12060121873335479696192669 4522545702500804886072251)
              ·
                refine ⟨6783818553751207329108377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522545702500804886072251 6783818553751207329108377)
                ·
                  refine ⟨5087863915313405496831283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6783818553751207329108377 5087863915313405496831283)
                  ·
                    refine ⟨7631795872970108245246925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087863915313405496831283 7631795872970108245246925)
                    ·
                      refine ⟨2861923452363790591967597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631795872970108245246925 2861923452363790591967597)
                      ·
                        rfl

theorem cell23_5573576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_5573576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573576 prefixEnd_5573576 := by exact prefixLift 5573576
  have htrace : WordTrace (prefixWord ++ tailWord_5573576) baseStart_5573576 baseEnd_5573576 := by
    simpa [prefixWord, tailWord_5573576, baseEnd_5573576] using wordTrace_append hprefix tailTrace_5573576
  have hstable : (prefixWord ++ tailWord_5573576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573576).length < 2 ^ (prefixWord ++ tailWord_5573576).sum := by decide
  have hdescent : baseEnd_5573576 < baseStart_5573576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573586 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5573586 : Nat := 118140960795 + 5573586 * 2 ^ 59
def prefixEnd_5573586 : Nat := 4983230072969 + 3 ^ 40 * 5573586 * 2
def baseEnd_5573586 : Nat := 2861928587170335552842551

theorem tailTrace_5573586 : CollatzResearch.WordTrace tailWord_5573586 prefixEnd_5573586 2861928587170335552842551 := by
  unfold tailWord_5573586
  simp only [CollatzResearch.WordTrace]
  refine ⟨50821345496464322387465153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135523587990571526366573741 50821345496464322387465153)
  ·
    refine ⟨38116009122348241790598865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50821345496464322387465153 38116009122348241790598865)
    ·
      refine ⟨28587006841761181342949149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38116009122348241790598865 28587006841761181342949149)
      ·
        refine ⟨10720127565660443003605931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28587006841761181342949149 10720127565660443003605931)
        ·
          refine ⟨16080191348490664505408897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10720127565660443003605931 16080191348490664505408897)
          ·
            refine ⟨12060143511367998379056673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16080191348490664505408897 12060143511367998379056673)
            ·
              refine ⟨9045107633525998784292505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12060143511367998379056673 9045107633525998784292505)
              ·
                refine ⟨6783830725144499088219379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9045107633525998784292505 6783830725144499088219379)
                ·
                  refine ⟨10175746087716748632329069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6783830725144499088219379 10175746087716748632329069)
                  ·
                    refine ⟨3815904782893780737123401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10175746087716748632329069 3815904782893780737123401)
                    ·
                      refine ⟨2861928587170335552842551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815904782893780737123401 2861928587170335552842551)
                      ·
                        rfl

theorem cell23_5573586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5573586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573586 prefixEnd_5573586 := by exact prefixLift 5573586
  have htrace : WordTrace (prefixWord ++ tailWord_5573586) baseStart_5573586 baseEnd_5573586 := by
    simpa [prefixWord, tailWord_5573586, baseEnd_5573586] using wordTrace_append hprefix tailTrace_5573586
  have hstable : (prefixWord ++ tailWord_5573586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573586).length < 2 ^ (prefixWord ++ tailWord_5573586).sum := by decide
  have hdescent : baseEnd_5573586 < baseStart_5573586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573602 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5573602 : Nat := 118140960795 + 5573602 * 2 ^ 59
def prefixEnd_5573602 : Nat := 4983230072969 + 3 ^ 40 * 5573602 * 2
def baseEnd_5573602 : Nat := 2861936802860807490242477

theorem tailTrace_5573602 : CollatzResearch.WordTrace tailWord_5573602 prefixEnd_5573602 2861936802860807490242477 := by
  unfold tailWord_5573602
  simp only [CollatzResearch.WordTrace]
  refine ⟨50821491388449831070610765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135523977035866216188295373 50821491388449831070610765)
  ·
    refine ⟨19058059270668686651479037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50821491388449831070610765 19058059270668686651479037)
    ·
      refine ⟨7146772226500757494304639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19058059270668686651479037 7146772226500757494304639)
      ·
        refine ⟨10720158339751136241456959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7146772226500757494304639 10720158339751136241456959)
        ·
          refine ⟨16080237509626704362185439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10720158339751136241456959 16080237509626704362185439)
          ·
            refine ⟨24120356264440056543278159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16080237509626704362185439 24120356264440056543278159)
            ·
              refine ⟨36180534396660084814917239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24120356264440056543278159 36180534396660084814917239)
              ·
                refine ⟨54270801594990127222375859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36180534396660084814917239 54270801594990127222375859)
                ·
                  refine ⟨81406202392485190833563789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54270801594990127222375859 81406202392485190833563789)
                  ·
                    refine ⟨30527325897181946562586421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81406202392485190833563789 30527325897181946562586421)
                    ·
                      refine ⟨2861936802860807490242477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30527325897181946562586421 2861936802860807490242477)
                      ·
                        rfl

theorem cell23_5573602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5573602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573602 prefixEnd_5573602 := by exact prefixLift 5573602
  have htrace : WordTrace (prefixWord ++ tailWord_5573602) baseStart_5573602 baseEnd_5573602 := by
    simpa [prefixWord, tailWord_5573602, baseEnd_5573602] using wordTrace_append hprefix tailTrace_5573602
  have hstable : (prefixWord ++ tailWord_5573602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573602).length < 2 ^ (prefixWord ++ tailWord_5573602).sum := by decide
  have hdescent : baseEnd_5573602 < baseStart_5573602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573622 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_5573622 : Nat := 118140960795 + 5573622 * 2 ^ 59
def prefixEnd_5573622 : Nat := 4983230072969 + 3 ^ 40 * 5573622 * 2
def baseEnd_5573622 : Nat := 317994119163766379110265

theorem tailTrace_5573622 : CollatzResearch.WordTrace tailWord_5573622 prefixEnd_5573622 317994119163766379110265 := by
  unfold tailWord_5573622
  simp only [CollatzResearch.WordTrace]
  refine ⟨12705418438357929231135695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135524463342484578465447413 12705418438357929231135695)
  ·
    refine ⟨19058127657536893846703543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12705418438357929231135695 19058127657536893846703543)
    ·
      refine ⟨28587191486305340770055315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19058127657536893846703543 28587191486305340770055315)
      ·
        refine ⟨42880787229458011155082973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28587191486305340770055315 42880787229458011155082973)
        ·
          refine ⟨16080295211046754183156115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42880787229458011155082973 16080295211046754183156115)
          ·
            refine ⟨24120442816570131274734173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16080295211046754183156115 24120442816570131274734173)
            ·
              refine ⟨9045166056213799228025315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24120442816570131274734173 9045166056213799228025315)
              ·
                refine ⟨13567749084320698842037973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9045166056213799228025315 13567749084320698842037973)
                ·
                  refine ⟨317994119163766379110265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13567749084320698842037973 317994119163766379110265)
                  ·
                    rfl

theorem cell23_5573622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_5573622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573622 prefixEnd_5573622 := by exact prefixLift 5573622
  have htrace : WordTrace (prefixWord ++ tailWord_5573622) baseStart_5573622 baseEnd_5573622 := by
    simpa [prefixWord, tailWord_5573622, baseEnd_5573622] using wordTrace_append hprefix tailTrace_5573622
  have hstable : (prefixWord ++ tailWord_5573622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573622).length < 2 ^ (prefixWord ++ tailWord_5573622).sum := by decide
  have hdescent : baseEnd_5573622 < baseStart_5573622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573633 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_5573633 : Nat := 118140960795 + 5573633 * 2 ^ 59
def prefixEnd_5573633 : Nat := 4983230072969 + 3 ^ 40 * 5573633 * 2
def baseEnd_5573633 : Nat := 2861952720761096868954835

theorem tailTrace_5573633 : CollatzResearch.WordTrace tailWord_5573633 prefixEnd_5573633 2861952720761096868954835 := by
  unfold tailWord_5573633
  simp only [CollatzResearch.WordTrace]
  refine ⟨203287096216687016576821553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135524730811124677717881035 203287096216687016576821553)
  ·
    refine ⟨152465322162515262432616165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203287096216687016576821553 152465322162515262432616165)
    ·
      refine ⟨28587247905471611706115531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152465322162515262432616165 28587247905471611706115531)
      ·
        refine ⟨42880871858207417559173297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28587247905471611706115531 42880871858207417559173297)
        ·
          refine ⟨32160653893655563169379973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42880871858207417559173297 32160653893655563169379973)
          ·
            refine ⟨6030122605060418094258745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32160653893655563169379973 6030122605060418094258745)
            ·
              refine ⟨4522591953795313570694059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6030122605060418094258745 4522591953795313570694059)
              ·
                refine ⟨6783887930692970356041089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522591953795313570694059 6783887930692970356041089)
                ·
                  refine ⟨5087915948019727767030817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6783887930692970356041089 5087915948019727767030817)
                  ·
                    refine ⟨3815936961014795825273113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5087915948019727767030817 3815936961014795825273113)
                    ·
                      refine ⟨2861952720761096868954835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815936961014795825273113 2861952720761096868954835)
                      ·
                        rfl

theorem cell23_5573633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_5573633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573633 prefixEnd_5573633 := by exact prefixLift 5573633
  have htrace : WordTrace (prefixWord ++ tailWord_5573633) baseStart_5573633 baseEnd_5573633 := by
    simpa [prefixWord, tailWord_5573633, baseEnd_5573633] using wordTrace_append hprefix tailTrace_5573633
  have hstable : (prefixWord ++ tailWord_5573633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573633).length < 2 ^ (prefixWord ++ tailWord_5573633).sum := by decide
  have hdescent : baseEnd_5573633 < baseStart_5573633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573682 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_5573682 : Nat := 118140960795 + 5573682 * 2 ^ 59
def prefixEnd_5573682 : Nat := 4983230072969 + 3 ^ 40 * 5573682 * 2
def baseEnd_5573682 : Nat := 953992627104389059080703

theorem tailTrace_5573682 : CollatzResearch.WordTrace tailWord_5573682 prefixEnd_5573682 953992627104389059080703 := by
  unfold tailWord_5573682
  simp only [CollatzResearch.WordTrace]
  refine ⟨50822220848377374486338825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135525922262339665296903533 50822220848377374486338825)
  ·
    refine ⟨38116665636283030864754119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50822220848377374486338825 38116665636283030864754119)
    ·
      refine ⟨57174998454424546297131179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38116665636283030864754119 57174998454424546297131179)
      ·
        refine ⟨85762497681636819445696769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57174998454424546297131179 85762497681636819445696769)
        ·
          refine ⟨64321873261227614584272577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85762497681636819445696769 64321873261227614584272577)
          ·
            refine ⟨48241404945920710938204433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64321873261227614584272577 48241404945920710938204433)
            ·
              refine ⟨36181053709440533203653325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48241404945920710938204433 36181053709440533203653325)
              ·
                refine ⟨13567895141040199951369997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36181053709440533203653325 13567895141040199951369997)
                ·
                  refine ⟨5087960677890074981763749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13567895141040199951369997 5087960677890074981763749)
                  ·
                    refine ⟨953992627104389059080703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087960677890074981763749 953992627104389059080703)
                    ·
                      rfl

theorem cell23_5573682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_5573682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573682 prefixEnd_5573682 := by exact prefixLift 5573682
  have htrace : WordTrace (prefixWord ++ tailWord_5573682) baseStart_5573682 baseEnd_5573682 := by
    simpa [prefixWord, tailWord_5573682, baseEnd_5573682] using wordTrace_append hprefix tailTrace_5573682
  have hstable : (prefixWord ++ tailWord_5573682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573682).length < 2 ^ (prefixWord ++ tailWord_5573682).sum := by decide
  have hdescent : baseEnd_5573682 < baseStart_5573682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573685 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_5573685 : Nat := 118140960795 + 5573685 * 2 ^ 59
def prefixEnd_5573685 : Nat := 4983230072969 + 3 ^ 40 * 5573685 * 2
def baseEnd_5573685 : Nat := 2861979421755130665504595

theorem tailTrace_5573685 : CollatzResearch.WordTrace tailWord_5573685 prefixEnd_5573685 2861979421755130665504595 := by
  unfold tailWord_5573685
  simp only [CollatzResearch.WordTrace]
  refine ⟨203288992812498629457714509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135525995208332419638476339 203288992812498629457714509)
  ·
    refine ⟨76233372304686986046642941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203288992812498629457714509 76233372304686986046642941)
    ·
      refine ⟨28587514614257619767491103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76233372304686986046642941 28587514614257619767491103)
      ·
        refine ⟨42881271921386429651236655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28587514614257619767491103 42881271921386429651236655)
        ·
          refine ⟨64321907882079644476854983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42881271921386429651236655 64321907882079644476854983)
          ·
            refine ⟨96482861823119466715282475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64321907882079644476854983 96482861823119466715282475)
            ·
              refine ⟨144724292734679200072923713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96482861823119466715282475 144724292734679200072923713)
              ·
                refine ⟨108543219551009400054692785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144724292734679200072923713 108543219551009400054692785)
                ·
                  refine ⟨81407414663257050041019589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108543219551009400054692785 81407414663257050041019589)
                  ·
                    refine ⟨15263890249360696882691173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81407414663257050041019589 15263890249360696882691173)
                    ·
                      refine ⟨2861979421755130665504595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15263890249360696882691173 2861979421755130665504595)
                      ·
                        rfl

theorem cell23_5573685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_5573685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573685 prefixEnd_5573685 := by exact prefixLift 5573685
  have htrace : WordTrace (prefixWord ++ tailWord_5573685) baseStart_5573685 baseEnd_5573685 := by
    simpa [prefixWord, tailWord_5573685, baseEnd_5573685] using wordTrace_append hprefix tailTrace_5573685
  have hstable : (prefixWord ++ tailWord_5573685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573685).length < 2 ^ (prefixWord ++ tailWord_5573685).sum := by decide
  have hdescent : baseEnd_5573685 < baseStart_5573685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573689 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 2, 4, 2]
def baseStart_5573689 : Nat := 118140960795 + 5573689 * 2 ^ 59
def prefixEnd_5573689 : Nat := 4983230072969 + 3 ^ 40 * 5573689 * 2
def baseEnd_5573689 : Nat := 2861981475677748649854577

theorem tailTrace_5573689 : CollatzResearch.WordTrace tailWord_5573689 prefixEnd_5573689 2861981475677748649854577 := by
  unfold tailWord_5573689
  simp only [CollatzResearch.WordTrace]
  refine ⟨203289138704484138140860121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135526092469656092093906747 203289138704484138140860121)
  ·
    refine ⟨152466854028363103605645091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203289138704484138140860121 152466854028363103605645091)
    ·
      refine ⟨228700281042544655408467637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152466854028363103605645091 228700281042544655408467637)
      ·
        refine ⟨21440651347738561444543841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228700281042544655408467637 21440651347738561444543841)
        ·
          refine ⟨16080488510803921083407881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21440651347738561444543841 16080488510803921083407881)
          ·
            refine ⟨12060366383102940812555911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16080488510803921083407881 12060366383102940812555911)
            ·
              refine ⟨18090549574654411218833867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12060366383102940812555911 18090549574654411218833867)
              ·
                refine ⟨27135824361981616828250801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18090549574654411218833867 27135824361981616828250801)
                ·
                  refine ⟨20351868271486212621188101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27135824361981616828250801 20351868271486212621188101)
                  ·
                    refine ⟨3815975300903664866472769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20351868271486212621188101 3815975300903664866472769)
                    ·
                      refine ⟨2861981475677748649854577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3815975300903664866472769 2861981475677748649854577)
                      ·
                        rfl

theorem cell23_5573689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_5573689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573689 prefixEnd_5573689 := by exact prefixLift 5573689
  have htrace : WordTrace (prefixWord ++ tailWord_5573689) baseStart_5573689 baseEnd_5573689 := by
    simpa [prefixWord, tailWord_5573689, baseEnd_5573689] using wordTrace_append hprefix tailTrace_5573689
  have hstable : (prefixWord ++ tailWord_5573689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573689).length < 2 ^ (prefixWord ++ tailWord_5573689).sum := by decide
  have hdescent : baseEnd_5573689 < baseStart_5573689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573705 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 3]
def baseStart_5573705 : Nat := 118140960795 + 5573705 * 2 ^ 59
def prefixEnd_5573705 : Nat := 4983230072969 + 3 ^ 40 * 5573705 * 2
def baseEnd_5573705 : Nat := 2861989691368220587254503

theorem tailTrace_5573705 : CollatzResearch.WordTrace tailWord_5573705 prefixEnd_5573705 2861989691368220587254503 := by
  unfold tailWord_5573705
  simp only [CollatzResearch.WordTrace]
  refine ⟨203289722272426172873442569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135526481514950781915628379 203289722272426172873442569)
  ·
    refine ⟨152467291704319629655081927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203289722272426172873442569 152467291704319629655081927)
    ·
      refine ⟨228700937556479444482622891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152467291704319629655081927 228700937556479444482622891)
      ·
        refine ⟨343051406334719166723934337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228700937556479444482622891 343051406334719166723934337)
        ·
          refine ⟨257288554751039375042950753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343051406334719166723934337 257288554751039375042950753)
          ·
            refine ⟨192966416063279531282213065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257288554751039375042950753 192966416063279531282213065)
            ·
              refine ⟨144724812047459648461659799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192966416063279531282213065 144724812047459648461659799)
              ·
                refine ⟨217087218071189472692489699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144724812047459648461659799 217087218071189472692489699)
                ·
                  refine ⟨325630827106784209038734549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217087218071189472692489699 325630827106784209038734549)
                  ·
                    refine ⟨7631972510315254899345341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 325630827106784209038734549 7631972510315254899345341)
                    ·
                      refine ⟨2861989691368220587254503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631972510315254899345341 2861989691368220587254503)
                      ·
                        rfl

theorem cell23_5573705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_5573705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573705 prefixEnd_5573705 := by exact prefixLift 5573705
  have htrace : WordTrace (prefixWord ++ tailWord_5573705) baseStart_5573705 baseEnd_5573705 := by
    simpa [prefixWord, tailWord_5573705, baseEnd_5573705] using wordTrace_append hprefix tailTrace_5573705
  have hstable : (prefixWord ++ tailWord_5573705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573705).length < 2 ^ (prefixWord ++ tailWord_5573705).sum := by decide
  have hdescent : baseEnd_5573705 < baseStart_5573705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573709 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_5573709 : Nat := 118140960795 + 5573709 * 2 ^ 59
def prefixEnd_5573709 : Nat := 4983230072969 + 3 ^ 40 * 5573709 * 2
def baseEnd_5573709 : Nat := 2861991745290838571604485

theorem tailTrace_5573709 : CollatzResearch.WordTrace tailWord_5573709 prefixEnd_5573709 2861991745290838571604485 := by
  unfold tailWord_5573709
  simp only [CollatzResearch.WordTrace]
  refine ⟨203289868164411681556588181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135526578776274454371058787 203289868164411681556588181)
  ·
    refine ⟨9529212570206797572965071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203289868164411681556588181 9529212570206797572965071)
    ·
      refine ⟨14293818855310196359447607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9529212570206797572965071 14293818855310196359447607)
      ·
        refine ⟨21440728282965294539171411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14293818855310196359447607 21440728282965294539171411)
        ·
          refine ⟨32161092424447941808757117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21440728282965294539171411 32161092424447941808757117)
          ·
            refine ⟨12060409659167978178283919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32161092424447941808757117 12060409659167978178283919)
            ·
              refine ⟨18090614488751967267425879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12060409659167978178283919 18090614488751967267425879)
              ·
                refine ⟨27135921733127950901138819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18090614488751967267425879 27135921733127950901138819)
                ·
                  refine ⟨40703882599691926351708229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27135921733127950901138819 40703882599691926351708229)
                  ·
                    refine ⟨7631977987442236190945293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40703882599691926351708229 7631977987442236190945293)
                    ·
                      refine ⟨2861991745290838571604485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7631977987442236190945293 2861991745290838571604485)
                      ·
                        rfl

theorem cell23_5573709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_5573709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573709 prefixEnd_5573709 := by exact prefixLift 5573709
  have htrace : WordTrace (prefixWord ++ tailWord_5573709) baseStart_5573709 baseEnd_5573709 := by
    simpa [prefixWord, tailWord_5573709, baseEnd_5573709] using wordTrace_append hprefix tailTrace_5573709
  have hstable : (prefixWord ++ tailWord_5573709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573709).length < 2 ^ (prefixWord ++ tailWord_5573709).sum := by decide
  have hdescent : baseEnd_5573709 < baseStart_5573709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573745 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_5573745 : Nat := 118140960795 + 5573745 * 2 ^ 59
def prefixEnd_5573745 : Nat := 4983230072969 + 3 ^ 40 * 5573745 * 2
def baseEnd_5573745 : Nat := 2862010230594400430754319

theorem tailTrace_5573745 : CollatzResearch.WordTrace tailWord_5573745 prefixEnd_5573745 2862010230594400430754319 := by
  unfold tailWord_5573745
  simp only [CollatzResearch.WordTrace]
  refine ⟨203291181192281259704898689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135527454128187506469932459 203291181192281259704898689)
  ·
    refine ⟨152468385894210944778674017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203291181192281259704898689 152468385894210944778674017)
    ·
      refine ⟨114351289420658208584005513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152468385894210944778674017 114351289420658208584005513)
      ·
        refine ⟨85763467065493656438004135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114351289420658208584005513 85763467065493656438004135)
        ·
          refine ⟨128645200598240484657006203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85763467065493656438004135 128645200598240484657006203)
          ·
            refine ⟨192967800897360726985509305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128645200598240484657006203 192967800897360726985509305)
            ·
              refine ⟨144725850673020545239131979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192967800897360726985509305 144725850673020545239131979)
              ·
                refine ⟨217088776009530817858697969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144725850673020545239131979 217088776009530817858697969)
                ·
                  refine ⟨162816582007148113394023477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217088776009530817858697969 162816582007148113394023477)
                  ·
                    refine ⟨15264054563170135630689701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162816582007148113394023477 15264054563170135630689701)
                    ·
                      refine ⟨2862010230594400430754319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15264054563170135630689701 2862010230594400430754319)
                      ·
                        rfl

theorem cell23_5573745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_5573745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573745 prefixEnd_5573745 := by exact prefixLift 5573745
  have htrace : WordTrace (prefixWord ++ tailWord_5573745) baseStart_5573745 baseEnd_5573745 := by
    simpa [prefixWord, tailWord_5573745, baseEnd_5573745] using wordTrace_append hprefix tailTrace_5573745
  have hstable : (prefixWord ++ tailWord_5573745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573745).length < 2 ^ (prefixWord ++ tailWord_5573745).sum := by decide
  have hdescent : baseEnd_5573745 < baseStart_5573745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573779 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 5, 2, 2]
def baseStart_5573779 : Nat := 118140960795 + 5573779 * 2 ^ 59
def prefixEnd_5573779 : Nat := 4983230072969 + 3 ^ 40 * 5573779 * 2
def baseEnd_5573779 : Nat := 2862027688936653297729163

theorem tailTrace_5573779 : CollatzResearch.WordTrace tailWord_5573779 prefixEnd_5573779 2862027688936653297729163 := by
  unfold tailWord_5573779
  simp only [CollatzResearch.WordTrace]
  refine ⟨203292421274158083511636391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135528280849438722341090927 203292421274158083511636391)
  ·
    refine ⟨304938631911237125267454587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203292421274158083511636391 304938631911237125267454587)
    ·
      refine ⟨457407947866855687901181881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304938631911237125267454587 457407947866855687901181881)
      ·
        refine ⟨343055960900141765925886411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457407947866855687901181881 343055960900141765925886411)
        ·
          refine ⟨514583941350212648888829617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343055960900141765925886411 514583941350212648888829617)
          ·
            refine ⟨385937956012659486666622213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514583941350212648888829617 385937956012659486666622213)
            ·
              refine ⟨72363366752373653749991665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 385937956012659486666622213 72363366752373653749991665)
              ·
                refine ⟨54272525064280240312493749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72363366752373653749991665 54272525064280240312493749)
                ·
                  refine ⟨5088049224776272529296289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54272525064280240312493749 5088049224776272529296289)
                  ·
                    refine ⟨3816036918582204396972217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5088049224776272529296289 3816036918582204396972217)
                    ·
                      refine ⟨2862027688936653297729163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816036918582204396972217 2862027688936653297729163)
                      ·
                        rfl

theorem cell23_5573779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 2, 2].length) (baseStart_5573779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573779 prefixEnd_5573779 := by exact prefixLift 5573779
  have htrace : WordTrace (prefixWord ++ tailWord_5573779) baseStart_5573779 baseEnd_5573779 := by
    simpa [prefixWord, tailWord_5573779, baseEnd_5573779] using wordTrace_append hprefix tailTrace_5573779
  have hstable : (prefixWord ++ tailWord_5573779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573779).length < 2 ^ (prefixWord ++ tailWord_5573779).sum := by decide
  have hdescent : baseEnd_5573779 < baseStart_5573779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573789 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_5573789 : Nat := 118140960795 + 5573789 * 2 ^ 59
def prefixEnd_5573789 : Nat := 4983230072969 + 3 ^ 40 * 5573789 * 2
def baseEnd_5573789 : Nat := 954010941247732752868039

theorem tailTrace_5573789 : CollatzResearch.WordTrace tailWord_5573789 prefixEnd_5573789 954010941247732752868039 := by
  unfold tailWord_5573789
  simp only [CollatzResearch.WordTrace]
  refine ⟨203292786004121855219500421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135528524002747903479666947 203292786004121855219500421)
  ·
    refine ⟨38117397375772847853656329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203292786004121855219500421 38117397375772847853656329)
    ·
      refine ⟨28588048031829635890242247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38117397375772847853656329 28588048031829635890242247)
      ·
        refine ⟨42882072047744453835363371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28588048031829635890242247 42882072047744453835363371)
        ·
          refine ⟨64323108071616680753045057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42882072047744453835363371 64323108071616680753045057)
          ·
            refine ⟨48242331053712510564783793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64323108071616680753045057 48242331053712510564783793)
            ·
              refine ⟨36181748290284382923587845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48242331053712510564783793 36181748290284382923587845)
              ·
                refine ⟨6784077804428321798172721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36181748290284382923587845 6784077804428321798172721)
                ·
                  refine ⟨5088058353321241348629541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6784077804428321798172721 5088058353321241348629541)
                  ·
                    refine ⟨954010941247732752868039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088058353321241348629541 954010941247732752868039)
                    ·
                      rfl

theorem cell23_5573789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_5573789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573789 prefixEnd_5573789 := by exact prefixLift 5573789
  have htrace : WordTrace (prefixWord ++ tailWord_5573789) baseStart_5573789 baseEnd_5573789 := by
    simpa [prefixWord, tailWord_5573789, baseEnd_5573789] using wordTrace_append hprefix tailTrace_5573789
  have hstable : (prefixWord ++ tailWord_5573789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573789).length < 2 ^ (prefixWord ++ tailWord_5573789).sum := by decide
  have hdescent : baseEnd_5573789 < baseStart_5573789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573799 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5573799 : Nat := 118140960795 + 5573799 * 2 ^ 59
def prefixEnd_5573799 : Nat := 4983230072969 + 3 ^ 40 * 5573799 * 2
def baseEnd_5573799 : Nat := 2862037958549743219479071

theorem tailTrace_5573799 : CollatzResearch.WordTrace tailWord_5573799 prefixEnd_5573799 2862037958549743219479071 := by
  unfold tailWord_5573799
  simp only [CollatzResearch.WordTrace]
  refine ⟨203293150734085626927364451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135528767156057084618242967 203293150734085626927364451)
  ·
    refine ⟨304939726101128440391046677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203293150734085626927364451 304939726101128440391046677)
    ·
      refine ⟨14294049660990395643330313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 304939726101128440391046677 14294049660990395643330313)
      ·
        refine ⟨10720537245742796732497735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14294049660990395643330313 10720537245742796732497735)
        ·
          refine ⟨16080805868614195098746603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10720537245742796732497735 16080805868614195098746603)
          ·
            refine ⟨24121208802921292648119905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16080805868614195098746603 24121208802921292648119905)
            ·
              refine ⟨18090906602190969486089929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24121208802921292648119905 18090906602190969486089929)
              ·
                refine ⟨13568179951643227114567447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18090906602190969486089929 13568179951643227114567447)
                ·
                  refine ⟨20352269927464840671851171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13568179951643227114567447 20352269927464840671851171)
                  ·
                    refine ⟨30528404891197261007776757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20352269927464840671851171 30528404891197261007776757)
                    ·
                      refine ⟨2862037958549743219479071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30528404891197261007776757 2862037958549743219479071)
                      ·
                        rfl

theorem cell23_5573799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5573799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573799 prefixEnd_5573799 := by exact prefixLift 5573799
  have htrace : WordTrace (prefixWord ++ tailWord_5573799) baseStart_5573799 baseEnd_5573799 := by
    simpa [prefixWord, tailWord_5573799, baseEnd_5573799] using wordTrace_append hprefix tailTrace_5573799
  have hstable : (prefixWord ++ tailWord_5573799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573799).length < 2 ^ (prefixWord ++ tailWord_5573799).sum := by decide
  have hdescent : baseEnd_5573799 < baseStart_5573799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573882 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_5573882 : Nat := 118140960795 + 5573882 * 2 ^ 59
def prefixEnd_5573882 : Nat := 4983230072969 + 3 ^ 40 * 5573882 * 2
def baseEnd_5573882 : Nat := 2862080577444066394741189

theorem tailTrace_5573882 : CollatzResearch.WordTrace tailWord_5573882 prefixEnd_5573882 2862080577444066394741189 := by
  unfold tailWord_5573882
  simp only [CollatzResearch.WordTrace]
  refine ⟨50824044498196233025658975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135530785328523288068423933 50824044498196233025658975)
  ·
    refine ⟨76236066747294349538488463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50824044498196233025658975 76236066747294349538488463)
    ·
      refine ⟨114354100120941524307732695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76236066747294349538488463 114354100120941524307732695)
      ·
        refine ⟨171531150181412286461599043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114354100120941524307732695 171531150181412286461599043)
        ·
          refine ⟨257296725272118429692398565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171531150181412286461599043 257296725272118429692398565)
          ·
            refine ⟨48243135988522205567324731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257296725272118429692398565 48243135988522205567324731)
            ·
              refine ⟨72364703982783308350987097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48243135988522205567324731 72364703982783308350987097)
              ·
                refine ⟨54273527987087481263240323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72364703982783308350987097 54273527987087481263240323)
                ·
                  refine ⟨81410291980631221894860485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54273527987087481263240323 81410291980631221894860485)
                  ·
                    refine ⟨15264429746368354105286341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81410291980631221894860485 15264429746368354105286341)
                    ·
                      refine ⟨2862080577444066394741189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15264429746368354105286341 2862080577444066394741189)
                      ·
                        rfl

theorem cell23_5573882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_5573882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573882 prefixEnd_5573882 := by exact prefixLift 5573882
  have htrace : WordTrace (prefixWord ++ tailWord_5573882) baseStart_5573882 baseEnd_5573882 := by
    simpa [prefixWord, tailWord_5573882, baseEnd_5573882] using wordTrace_append hprefix tailTrace_5573882
  have hstable : (prefixWord ++ tailWord_5573882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573882).length < 2 ^ (prefixWord ++ tailWord_5573882).sum := by decide
  have hdescent : baseEnd_5573882 < baseStart_5573882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573890 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_5573890 : Nat := 118140960795 + 5573890 * 2 ^ 59
def prefixEnd_5573890 : Nat := 4983230072969 + 3 ^ 40 * 5573890 * 2
def baseEnd_5573890 : Nat := 2862084685289302363441153

theorem tailTrace_5573890 : CollatzResearch.WordTrace tailWord_5573890 prefixEnd_5573890 2862084685289302363441153 := by
  unfold tailWord_5573890
  simp only [CollatzResearch.WordTrace]
  refine ⟨50824117444188987367231781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135530979851170632979284749 50824117444188987367231781)
  ·
    refine ⟨9529522020785435131355959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50824117444188987367231781 9529522020785435131355959)
    ·
      refine ⟨14294283031178152697033939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9529522020785435131355959 14294283031178152697033939)
      ·
        refine ⟨21441424546767229045550909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14294283031178152697033939 21441424546767229045550909)
        ·
          refine ⟨8040534205037710892081591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21441424546767229045550909 8040534205037710892081591)
          ·
            refine ⟨12060801307556566338122387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040534205037710892081591 12060801307556566338122387)
            ·
              refine ⟨18091201961334849507183581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12060801307556566338122387 18091201961334849507183581)
              ·
                refine ⟨6784200735500568565193843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18091201961334849507183581 6784200735500568565193843)
                ·
                  refine ⟨10176301103250852847790765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6784200735500568565193843 10176301103250852847790765)
                  ·
                    refine ⟨3816112913719069817921537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10176301103250852847790765 3816112913719069817921537)
                    ·
                      refine ⟨2862084685289302363441153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816112913719069817921537 2862084685289302363441153)
                      ·
                        rfl

theorem cell23_5573890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_5573890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573890 prefixEnd_5573890 := by exact prefixLift 5573890
  have htrace : WordTrace (prefixWord ++ tailWord_5573890) baseStart_5573890 baseEnd_5573890 := by
    simpa [prefixWord, tailWord_5573890, baseEnd_5573890] using wordTrace_append hprefix tailTrace_5573890
  have hstable : (prefixWord ++ tailWord_5573890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573890).length < 2 ^ (prefixWord ++ tailWord_5573890).sum := by decide
  have hdescent : baseEnd_5573890 < baseStart_5573890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573920 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 1, 4, 2]
def baseStart_5573920 : Nat := 118140960795 + 5573920 * 2 ^ 59
def prefixEnd_5573920 : Nat := 4983230072969 + 3 ^ 40 * 5573920 * 2
def baseEnd_5573920 : Nat := 2862100089708937246066015

theorem tailTrace_5573920 : CollatzResearch.WordTrace tailWord_5573920 prefixEnd_5573920 2862100089708937246066015 := by
  unfold tailWord_5573920
  simp only [CollatzResearch.WordTrace]
  refine ⟨101648781983323632296259607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135531709311098176395012809 101648781983323632296259607)
  ·
    refine ⟨152473172974985448444389411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101648781983323632296259607 152473172974985448444389411)
    ·
      refine ⟨228709759462478172666584117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152473172974985448444389411 228709759462478172666584117)
      ·
        refine ⟨21441539949607328687492261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228709759462478172666584117 21441539949607328687492261)
        ·
          refine ⟨4020288740551374128904799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21441539949607328687492261 4020288740551374128904799)
          ·
            refine ⟨6030433110827061193357199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020288740551374128904799 6030433110827061193357199)
            ·
              refine ⟨9045649666240591790035799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6030433110827061193357199 9045649666240591790035799)
              ·
                refine ⟨13568474499360887685053699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9045649666240591790035799 13568474499360887685053699)
                ·
                  refine ⟨20352711749041331527580549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13568474499360887685053699 20352711749041331527580549)
                  ·
                    refine ⟨3816133452945249661421353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20352711749041331527580549 3816133452945249661421353)
                    ·
                      refine ⟨2862100089708937246066015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816133452945249661421353 2862100089708937246066015)
                      ·
                        rfl

theorem cell23_5573920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_5573920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573920 prefixEnd_5573920 := by exact prefixLift 5573920
  have htrace : WordTrace (prefixWord ++ tailWord_5573920) baseStart_5573920 baseEnd_5573920 := by
    simpa [prefixWord, tailWord_5573920, baseEnd_5573920] using wordTrace_append hprefix tailTrace_5573920
  have hstable : (prefixWord ++ tailWord_5573920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573920).length < 2 ^ (prefixWord ++ tailWord_5573920).sum := by decide
  have hdescent : baseEnd_5573920 < baseStart_5573920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573932 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_5573932 : Nat := 118140960795 + 5573932 * 2 ^ 59
def prefixEnd_5573932 : Nat := 4983230072969 + 3 ^ 40 * 5573932 * 2
def baseEnd_5573932 : Nat := 2862106251476791199115959

theorem tailTrace_5573932 : CollatzResearch.WordTrace tailWord_5573932 prefixEnd_5573932 2862106251476791199115959 := by
  unfold tailWord_5573932
  simp only [CollatzResearch.WordTrace]
  refine ⟨101649000821301895320978025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135532001095069193761304033 101649000821301895320978025)
  ·
    refine ⟨76236750615976421490733519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101649000821301895320978025 76236750615976421490733519)
    ·
      refine ⟨114355125923964632236100279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76236750615976421490733519 114355125923964632236100279)
      ·
        refine ⟨171532688885946948354150419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114355125923964632236100279 171532688885946948354150419)
        ·
          refine ⟨257299033328920422531225629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171532688885946948354150419 257299033328920422531225629)
          ·
            refine ⟨96487137498345158449209611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257299033328920422531225629 96487137498345158449209611)
            ·
              refine ⟨144730706247517737673814417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96487137498345158449209611 144730706247517737673814417)
              ·
                refine ⟨108548029685638303255360813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144730706247517737673814417 108548029685638303255360813)
                ·
                  refine ⟨40705511132114363720760305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108548029685638303255360813 40705511132114363720760305)
                  ·
                    refine ⟨30529133349085772790570229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40705511132114363720760305 30529133349085772790570229)
                    ·
                      refine ⟨2862106251476791199115959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30529133349085772790570229 2862106251476791199115959)
                      ·
                        rfl

theorem cell23_5573932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_5573932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573932 prefixEnd_5573932 := by exact prefixLift 5573932
  have htrace : WordTrace (prefixWord ++ tailWord_5573932) baseStart_5573932 baseEnd_5573932 := by
    simpa [prefixWord, tailWord_5573932, baseEnd_5573932] using wordTrace_append hprefix tailTrace_5573932
  have hstable : (prefixWord ++ tailWord_5573932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573932).length < 2 ^ (prefixWord ++ tailWord_5573932).sum := by decide
  have hdescent : baseEnd_5573932 < baseStart_5573932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573956 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5573956 : Nat := 118140960795 + 5573956 * 2 ^ 59
def prefixEnd_5573956 : Nat := 4983230072969 + 3 ^ 40 * 5573956 * 2
def baseEnd_5573956 : Nat := 954039525004166368405283

theorem tailTrace_5573956 : CollatzResearch.WordTrace tailWord_5573956 prefixEnd_5573956 954039525004166368405283 := by
  unfold tailWord_5573956
  simp only [CollatzResearch.WordTrace]
  refine ⟨101649438497258421370414861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135532584663011228493886481 101649438497258421370414861)
  ·
    refine ⟨38118539436471908013905573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101649438497258421370414861 38118539436471908013905573)
    ·
      refine ⟨7147226144338482752607295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38118539436471908013905573 7147226144338482752607295)
      ·
        refine ⟨10720839216507724128910943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7147226144338482752607295 10720839216507724128910943)
        ·
          refine ⟨16081258824761586193366415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10720839216507724128910943 16081258824761586193366415)
          ·
            refine ⟨24121888237142379290049623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16081258824761586193366415 24121888237142379290049623)
            ·
              refine ⟨36182832355713568935074435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24121888237142379290049623 36182832355713568935074435)
              ·
                refine ⟨54274248533570353402611653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36182832355713568935074435 54274248533570353402611653)
                ·
                  refine ⟨10176421600044441262989685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54274248533570353402611653 10176421600044441262989685)
                  ·
                    refine ⟨954039525004166368405283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10176421600044441262989685 954039525004166368405283)
                    ·
                      rfl

theorem cell23_5573956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5573956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573956 prefixEnd_5573956 := by exact prefixLift 5573956
  have htrace : WordTrace (prefixWord ++ tailWord_5573956) baseStart_5573956 baseEnd_5573956 := by
    simpa [prefixWord, tailWord_5573956, baseEnd_5573956] using wordTrace_append hprefix tailTrace_5573956
  have hstable : (prefixWord ++ tailWord_5573956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573956).length < 2 ^ (prefixWord ++ tailWord_5573956).sum := by decide
  have hdescent : baseEnd_5573956 < baseStart_5573956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573959 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_5573959 : Nat := 118140960795 + 5573959 * 2 ^ 59
def prefixEnd_5573959 : Nat := 4983230072969 + 3 ^ 40 * 5573959 * 2
def baseEnd_5573959 : Nat := 2862120115454462593478335

theorem tailTrace_5573959 : CollatzResearch.WordTrace tailWord_5573959 prefixEnd_5573959 2862120115454462593478335 := by
  unfold tailWord_5573959
  simp only [CollatzResearch.WordTrace]
  refine ⟨203298986413505974253188931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135532657609003982835459287 203298986413505974253188931)
  ·
    refine ⟨304948479620258961379783397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203298986413505974253188931 304948479620258961379783397)
    ·
      refine ⟨57177839928798555258709387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304948479620258961379783397 57177839928798555258709387)
      ·
        refine ⟨85766759893197832888064081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57177839928798555258709387 85766759893197832888064081)
        ·
          refine ⟨64325069919898374666048061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85766759893197832888064081 64325069919898374666048061)
          ·
            refine ⟨24121901219961890499768023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64325069919898374666048061 24121901219961890499768023)
            ·
              refine ⟨36182851829942835749652035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24121901219961890499768023 36182851829942835749652035)
              ·
                refine ⟨54274277744914253624478053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36182851829942835749652035 54274277744914253624478053)
                ·
                  refine ⟨10176427077171422554589635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54274277744914253624478053 10176427077171422554589635)
                  ·
                    refine ⟨15264640615757133831884453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10176427077171422554589635 15264640615757133831884453)
                    ·
                      refine ⟨2862120115454462593478335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15264640615757133831884453 2862120115454462593478335)
                      ·
                        rfl

theorem cell23_5573959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_5573959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573959 prefixEnd_5573959 := by exact prefixLift 5573959
  have htrace : WordTrace (prefixWord ++ tailWord_5573959) baseStart_5573959 baseEnd_5573959 := by
    simpa [prefixWord, tailWord_5573959, baseEnd_5573959] using wordTrace_append hprefix tailTrace_5573959
  have hstable : (prefixWord ++ tailWord_5573959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573959).length < 2 ^ (prefixWord ++ tailWord_5573959).sum := by decide
  have hdescent : baseEnd_5573959 < baseStart_5573959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573986 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5573986 : Nat := 118140960795 + 5573986 * 2 ^ 59
def prefixEnd_5573986 : Nat := 4983230072969 + 3 ^ 40 * 5573986 * 2
def baseEnd_5573986 : Nat := 954044659810711329280237

theorem tailTrace_5573986 : CollatzResearch.WordTrace tailWord_5573986 prefixEnd_5573986 954044659810711329280237 := by
  unfold tailWord_5573986
  simp only [CollatzResearch.WordTrace]
  refine ⟨50824992796102039466105453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135533314122938771909614541 50824992796102039466105453)
  ·
    refine ⟨19059372298538264799789545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50824992796102039466105453 19059372298538264799789545)
    ·
      refine ⟨14294529223903698599842159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19059372298538264799789545 14294529223903698599842159)
      ·
        refine ⟨21441793835855547899763239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14294529223903698599842159 21441793835855547899763239)
        ·
          refine ⟨32162690753783321849644859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21441793835855547899763239 32162690753783321849644859)
          ·
            refine ⟨48244036130674982774467289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32162690753783321849644859 48244036130674982774467289)
            ·
              refine ⟨36183027098006237080850467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48244036130674982774467289 36183027098006237080850467)
              ·
                refine ⟨54274540647009355621275701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36183027098006237080850467 54274540647009355621275701)
                ·
                  refine ⟨5088238185657127089494597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54274540647009355621275701 5088238185657127089494597)
                  ·
                    refine ⟨954044659810711329280237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088238185657127089494597 954044659810711329280237)
                    ·
                      rfl

theorem cell23_5573986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5573986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573986 prefixEnd_5573986 := by exact prefixLift 5573986
  have htrace : WordTrace (prefixWord ++ tailWord_5573986) baseStart_5573986 baseEnd_5573986 := by
    simpa [prefixWord, tailWord_5573986, baseEnd_5573986] using wordTrace_append hprefix tailTrace_5573986
  have hstable : (prefixWord ++ tailWord_5573986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573986).length < 2 ^ (prefixWord ++ tailWord_5573986).sum := by decide
  have hdescent : baseEnd_5573986 < baseStart_5573986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5573996 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_5573996 : Nat := 118140960795 + 5573996 * 2 ^ 59
def prefixEnd_5573996 : Nat := 4983230072969 + 3 ^ 40 * 5573996 * 2
def baseEnd_5573996 : Nat := 2862139114238678948715665

theorem tailTrace_5573996 : CollatzResearch.WordTrace tailWord_5573996 prefixEnd_5573996 2862139114238678948715665 := by
  unfold tailWord_5573996
  simp only [CollatzResearch.WordTrace]
  refine ⟨101650167957185964786142921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135533557276247953048190561 101650167957185964786142921)
  ·
    refine ⟨76237625967889473589607191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101650167957185964786142921 76237625967889473589607191)
    ·
      refine ⟨114356438951834210384410787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76237625967889473589607191 114356438951834210384410787)
      ·
        refine ⟨171534658427751315576616181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114356438951834210384410787 171534658427751315576616181)
        ·
          refine ⟨16081374227601685835307767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171534658427751315576616181 16081374227601685835307767)
          ·
            refine ⟨24122061341402528752961651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16081374227601685835307767 24122061341402528752961651)
            ·
              refine ⟨36183092012103793129442477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24122061341402528752961651 36183092012103793129442477)
              ·
                refine ⟨13568659504538922423540929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36183092012103793129442477 13568659504538922423540929)
                ·
                  refine ⟨10176494628404191817655697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13568659504538922423540929 10176494628404191817655697)
                  ·
                    refine ⟨7632370971303143863241773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10176494628404191817655697 7632370971303143863241773)
                    ·
                      refine ⟨2862139114238678948715665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7632370971303143863241773 2862139114238678948715665)
                      ·
                        rfl

theorem cell23_5573996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_5573996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5573996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5573996 prefixEnd_5573996 := by exact prefixLift 5573996
  have htrace : WordTrace (prefixWord ++ tailWord_5573996) baseStart_5573996 baseEnd_5573996 := by
    simpa [prefixWord, tailWord_5573996, baseEnd_5573996] using wordTrace_append hprefix tailTrace_5573996
  have hstable : (prefixWord ++ tailWord_5573996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5573996).length < 2 ^ (prefixWord ++ tailWord_5573996).sum := by decide
  have hdescent : baseEnd_5573996 < baseStart_5573996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5573996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574020 : List Nat := [2, 3, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_5574020 : Nat := 118140960795 + 5574020 * 2 ^ 59
def prefixEnd_5574020 : Nat := 4983230072969 + 3 ^ 40 * 5574020 * 2
def baseEnd_5574020 : Nat := 954050479258128951605185

theorem tailTrace_5574020 : CollatzResearch.WordTrace tailWord_5574020 prefixEnd_5574020 954050479258128951605185 := by
  unfold tailWord_5574020
  simp only [CollatzResearch.WordTrace]
  refine ⟨101650605633142490835579757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135534140844189987780773009 101650605633142490835579757)
  ·
    refine ⟨38118977112428434063342409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101650605633142490835579757 38118977112428434063342409)
    ·
      refine ⟨28589232834321325547506807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38118977112428434063342409 28589232834321325547506807)
      ·
        refine ⟨42883849251481988321260211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28589232834321325547506807 42883849251481988321260211)
        ·
          refine ⟨64325773877222982481890317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42883849251481988321260211 64325773877222982481890317)
          ·
            refine ⟨24122165203958618430708869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64325773877222982481890317 24122165203958618430708869)
            ·
              refine ⟨4522905975742240955757913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24122165203958618430708869 4522905975742240955757913)
              ·
                refine ⟨3392179481806680716818435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522905975742240955757913 3392179481806680716818435)
                ·
                  refine ⟨5088269222710021075227653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392179481806680716818435 5088269222710021075227653)
                  ·
                    refine ⟨954050479258128951605185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088269222710021075227653 954050479258128951605185)
                    ·
                      rfl

theorem cell23_5574020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_5574020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574020 prefixEnd_5574020 := by exact prefixLift 5574020
  have htrace : WordTrace (prefixWord ++ tailWord_5574020) baseStart_5574020 baseEnd_5574020 := by
    simpa [prefixWord, tailWord_5574020, baseEnd_5574020] using wordTrace_append hprefix tailTrace_5574020
  have hstable : (prefixWord ++ tailWord_5574020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574020).length < 2 ^ (prefixWord ++ tailWord_5574020).sum := by decide
  have hdescent : baseEnd_5574020 < baseStart_5574020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574079 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_5574079 : Nat := 118140960795 + 5574079 * 2 ^ 59
def prefixEnd_5574079 : Nat := 4983230072969 + 3 ^ 40 * 5574079 * 2
def baseEnd_5574079 : Nat := 2862181733133002123977783

theorem tailTrace_5574079 : CollatzResearch.WordTrace tailWord_5574079 prefixEnd_5574079 2862181733133002123977783 := by
  unfold tailWord_5574079
  simp only [CollatzResearch.WordTrace]
  refine ⟨203303363173071234747557291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135535575448714156498371527 203303363173071234747557291)
  ·
    refine ⟨304955044759606852121335937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203303363173071234747557291 304955044759606852121335937)
    ·
      refine ⟨228716283569705139091001953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304955044759606852121335937 228716283569705139091001953)
      ·
        refine ⟨171537212677278854318251465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228716283569705139091001953 171537212677278854318251465)
        ·
          refine ⟨128652909507959140738688599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171537212677278854318251465 128652909507959140738688599)
          ·
            refine ⟨192979364261938711108032899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128652909507959140738688599 192979364261938711108032899)
            ·
              refine ⟨289469046392908066662049349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192979364261938711108032899 289469046392908066662049349)
              ·
                refine ⟨54275446198670262499134253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289469046392908066662049349 54275446198670262499134253)
                ·
                  refine ⟨20353292324501348437175345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54275446198670262499134253 20353292324501348437175345)
                  ·
                    refine ⟨15264969243376011327881509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20353292324501348437175345 15264969243376011327881509)
                    ·
                      refine ⟨2862181733133002123977783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15264969243376011327881509 2862181733133002123977783)
                      ·
                        rfl

theorem cell23_5574079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_5574079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574079 prefixEnd_5574079 := by exact prefixLift 5574079
  have htrace : WordTrace (prefixWord ++ tailWord_5574079) baseStart_5574079 baseEnd_5574079 := by
    simpa [prefixWord, tailWord_5574079, baseEnd_5574079] using wordTrace_append hprefix tailTrace_5574079
  have hstable : (prefixWord ++ tailWord_5574079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574079).length < 2 ^ (prefixWord ++ tailWord_5574079).sum := by decide
  have hdescent : baseEnd_5574079 < baseStart_5574079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574083 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 3, 2, 2]
def baseStart_5574083 : Nat := 118140960795 + 5574083 * 2 ^ 59
def prefixEnd_5574083 : Nat := 4983230072969 + 3 ^ 40 * 5574083 * 2
def baseEnd_5574083 : Nat := 2862183787055620108327765

theorem tailTrace_5574083 : CollatzResearch.WordTrace tailWord_5574083 prefixEnd_5574083 2862183787055620108327765 := by
  unfold tailWord_5574083
  simp only [CollatzResearch.WordTrace]
  refine ⟨203303509065056743430702903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135535672710037828953801935 203303509065056743430702903)
  ·
    refine ⟨304955263597585115146054355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203303509065056743430702903 304955263597585115146054355)
    ·
      refine ⟨457432895396377672719081533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304955263597585115146054355 457432895396377672719081533)
      ·
        refine ⟨171537335773641627269655575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457432895396377672719081533 171537335773641627269655575)
        ·
          refine ⟨257306003660462440904483363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171537335773641627269655575 257306003660462440904483363)
          ·
            refine ⟨385959005490693661356725045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257306003660462440904483363 385959005490693661356725045)
            ·
              refine ⟨36183656764752530752192973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 385959005490693661356725045 36183656764752530752192973)
              ·
                refine ⟨13568871286782199032072365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36183656764752530752192973 13568871286782199032072365)
                ·
                  refine ⟨5088326732543324637027137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13568871286782199032072365 5088326732543324637027137)
                  ·
                    refine ⟨3816245049407493477770353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5088326732543324637027137 3816245049407493477770353)
                    ·
                      refine ⟨2862183787055620108327765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816245049407493477770353 2862183787055620108327765)
                      ·
                        rfl

theorem cell23_5574083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_5574083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574083 prefixEnd_5574083 := by exact prefixLift 5574083
  have htrace : WordTrace (prefixWord ++ tailWord_5574083) baseStart_5574083 baseEnd_5574083 := by
    simpa [prefixWord, tailWord_5574083, baseEnd_5574083] using wordTrace_append hprefix tailTrace_5574083
  have hstable : (prefixWord ++ tailWord_5574083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574083).length < 2 ^ (prefixWord ++ tailWord_5574083).sum := by decide
  have hdescent : baseEnd_5574083 < baseStart_5574083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574100 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_5574100 : Nat := 118140960795 + 5574100 * 2 ^ 59
def prefixEnd_5574100 : Nat := 4983230072969 + 3 ^ 40 * 5574100 * 2
def baseEnd_5574100 : Nat := 2862192516226746541815187

theorem tailTrace_5574100 : CollatzResearch.WordTrace tailWord_5574100 prefixEnd_5574100 2862192516226746541815187 := by
  unfold tailWord_5574100
  simp only [CollatzResearch.WordTrace]
  refine ⟨101652064552997577667035877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135536086070663436889381169 101652064552997577667035877)
  ·
    refine ⟨19059762103687045812569227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101652064552997577667035877 19059762103687045812569227)
    ·
      refine ⟨28589643155530568718853841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19059762103687045812569227 28589643155530568718853841)
      ·
        refine ⟨21442232366647926539140381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28589643155530568718853841 21442232366647926539140381)
        ·
          refine ⟨8040837137492972452177643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21442232366647926539140381 8040837137492972452177643)
          ·
            refine ⟨12061255706239458678266465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040837137492972452177643 12061255706239458678266465)
            ·
              refine ⟨9045941779679594008699849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12061255706239458678266465 9045941779679594008699849)
              ·
                refine ⟨6784456334759695506524887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9045941779679594008699849 6784456334759695506524887)
                ·
                  refine ⟨10176684502139543259787331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6784456334759695506524887 10176684502139543259787331)
                  ·
                    refine ⟨15265026753209314889680997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10176684502139543259787331 15265026753209314889680997)
                    ·
                      refine ⟨2862192516226746541815187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15265026753209314889680997 2862192516226746541815187)
                      ·
                        rfl

theorem cell23_5574100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_5574100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574100 prefixEnd_5574100 := by exact prefixLift 5574100
  have htrace : WordTrace (prefixWord ++ tailWord_5574100) baseStart_5574100 baseEnd_5574100 := by
    simpa [prefixWord, tailWord_5574100, baseEnd_5574100] using wordTrace_append hprefix tailTrace_5574100
  have hstable : (prefixWord ++ tailWord_5574100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574100).length < 2 ^ (prefixWord ++ tailWord_5574100).sum := by decide
  have hdescent : baseEnd_5574100 < baseStart_5574100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574106 : List Nat := [3, 1, 1, 2, 3, 2, 4, 7]
def baseStart_5574106 : Nat := 118140960795 + 5574106 * 2 ^ 59
def prefixEnd_5574106 : Nat := 4983230072969 + 3 ^ 40 * 5574106 * 2
def baseEnd_5574106 : Nat := 106007244337432352531117

theorem tailTrace_5574106 : CollatzResearch.WordTrace tailWord_5574106 prefixEnd_5574106 106007244337432352531117 := by
  unfold tailWord_5574106
  simp only [CollatzResearch.WordTrace]
  refine ⟨50826086985993354589697543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135536231962648945572526781 50826086985993354589697543)
  ·
    refine ⟨76239130478990031884546315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50826086985993354589697543 76239130478990031884546315)
    ·
      refine ⟨114358695718485047826819473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76239130478990031884546315 114358695718485047826819473)
      ·
        refine ⟨85769021788863785870114605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114358695718485047826819473 85769021788863785870114605)
        ·
          refine ⟨32163383170823919701292977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85769021788863785870114605 32163383170823919701292977)
          ·
            refine ⟨24122537378117939775969733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32163383170823919701292977 24122537378117939775969733)
            ·
              refine ⟨4522975758397113707994325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24122537378117939775969733 4522975758397113707994325)
              ·
                refine ⟨106007244337432352531117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4522975758397113707994325 106007244337432352531117)
                ·
                  rfl

theorem cell23_5574106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_5574106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574106 prefixEnd_5574106 := by exact prefixLift 5574106
  have htrace : WordTrace (prefixWord ++ tailWord_5574106) baseStart_5574106 baseEnd_5574106 := by
    simpa [prefixWord, tailWord_5574106, baseEnd_5574106] using wordTrace_append hprefix tailTrace_5574106
  have hstable : (prefixWord ++ tailWord_5574106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574106).length < 2 ^ (prefixWord ++ tailWord_5574106).sum := by decide
  have hdescent : baseEnd_5574106 < baseStart_5574106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574116 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_5574116 : Nat := 118140960795 + 5574116 * 2 ^ 59
def prefixEnd_5574116 : Nat := 4983230072969 + 3 ^ 40 * 5574116 * 2
def baseEnd_5574116 : Nat := 2862200731917218479215113

theorem tailTrace_5574116 : CollatzResearch.WordTrace tailWord_5574116 prefixEnd_5574116 2862200731917218479215113 := by
  unfold tailWord_5574116
  simp only [CollatzResearch.WordTrace]
  refine ⟨101652356336968595033327101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135536475115958126711102801 101652356336968595033327101)
  ·
    refine ⟨38119633626363223137497663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101652356336968595033327101 38119633626363223137497663)
    ·
      refine ⟨57179450439544834706246495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38119633626363223137497663 57179450439544834706246495)
      ·
        refine ⟨85769175659317252059369743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57179450439544834706246495 85769175659317252059369743)
        ·
          refine ⟨128653763488975878089054615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85769175659317252059369743 128653763488975878089054615)
          ·
            refine ⟨192980645233463817133581923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128653763488975878089054615 192980645233463817133581923)
            ·
              refine ⟨289470967850195725700372885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192980645233463817133581923 289470967850195725700372885)
              ·
                refine ⟨13568951617977924642204979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 289470967850195725700372885 13568951617977924642204979)
                ·
                  refine ⟨20353427426966886963307469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13568951617977924642204979 20353427426966886963307469)
                  ·
                    refine ⟨7632535285112582611240301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20353427426966886963307469 7632535285112582611240301)
                    ·
                      refine ⟨2862200731917218479215113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7632535285112582611240301 2862200731917218479215113)
                      ·
                        rfl

theorem cell23_5574116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_5574116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574116 prefixEnd_5574116 := by exact prefixLift 5574116
  have htrace : WordTrace (prefixWord ++ tailWord_5574116) baseStart_5574116 baseEnd_5574116 := by
    simpa [prefixWord, tailWord_5574116, baseEnd_5574116] using wordTrace_append hprefix tailTrace_5574116
  have hstable : (prefixWord ++ tailWord_5574116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574116).length < 2 ^ (prefixWord ++ tailWord_5574116).sum := by decide
  have hdescent : baseEnd_5574116 < baseStart_5574116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574139 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4]
def baseStart_5574139 : Nat := 118140960795 + 5574139 * 2 ^ 59
def prefixEnd_5574139 : Nat := 4983230072969 + 3 ^ 40 * 5574139 * 2
def baseEnd_5574139 : Nat := 2862212541972271889227507

theorem tailTrace_5574139 : CollatzResearch.WordTrace tailWord_5574139 prefixEnd_5574139 2862212541972271889227507 := by
  unfold tailWord_5574139
  simp only [CollatzResearch.WordTrace]
  refine ⟨203305551552853864994741471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135537034368569243329827647 203305551552853864994741471)
  ·
    refine ⟨304958327329280797492112207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203305551552853864994741471 304958327329280797492112207)
    ·
      refine ⟨457437490993921196238168311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304958327329280797492112207 457437490993921196238168311)
      ·
        refine ⟨686156236490881794357252467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457437490993921196238168311 686156236490881794357252467)
        ·
          refine ⟨1029234354736322691535878701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686156236490881794357252467 1029234354736322691535878701)
          ·
            refine ⟨385962883026121009325954513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1029234354736322691535878701 385962883026121009325954513)
            ·
              refine ⟨289472162269590756994465885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385962883026121009325954513 289472162269590756994465885)
              ·
                refine ⟨108552060851096533872924707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289472162269590756994465885 108552060851096533872924707)
                ·
                  refine ⟨162828091276644800809387061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108552060851096533872924707 162828091276644800809387061)
                  ·
                    refine ⟨15265133557185450075880037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162828091276644800809387061 15265133557185450075880037)
                    ·
                      refine ⟨2862212541972271889227507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15265133557185450075880037 2862212541972271889227507)
                      ·
                        rfl

theorem cell23_5574139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_5574139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574139 prefixEnd_5574139 := by exact prefixLift 5574139
  have htrace : WordTrace (prefixWord ++ tailWord_5574139) baseStart_5574139 baseEnd_5574139 := by
    simpa [prefixWord, tailWord_5574139, baseEnd_5574139] using wordTrace_append hprefix tailTrace_5574139
  have hstable : (prefixWord ++ tailWord_5574139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574139).length < 2 ^ (prefixWord ++ tailWord_5574139).sum := by decide
  have hdescent : baseEnd_5574139 < baseStart_5574139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574149 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_5574149 : Nat := 118140960795 + 5574149 * 2 ^ 59
def prefixEnd_5574149 : Nat := 4983230072969 + 3 ^ 40 * 5574149 * 2
def baseEnd_5574149 : Nat := 954072558926272283367487

theorem tailTrace_5574149 : CollatzResearch.WordTrace tailWord_5574149 prefixEnd_5574149 954072558926272283367487 := by
  unfold tailWord_5574149
  simp only [CollatzResearch.WordTrace]
  refine ⟨203305916282817636702605501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135537277521878424468403667 203305916282817636702605501)
  ·
    refine ⟨76239718606056613763477063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203305916282817636702605501 76239718606056613763477063)
    ·
      refine ⟨114359577909084920645215595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76239718606056613763477063 114359577909084920645215595)
      ·
        refine ⟨171539366863627380967823393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114359577909084920645215595 171539366863627380967823393)
        ·
          refine ⟨128654525147720535725867545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171539366863627380967823393 128654525147720535725867545)
          ·
            refine ⟨96490893860790401794400659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128654525147720535725867545 96490893860790401794400659)
            ·
              refine ⟨144736340791185602691600989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96490893860790401794400659 144736340791185602691600989)
              ·
                refine ⟨54276127796694601009350371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144736340791185602691600989 54276127796694601009350371)
                ·
                  refine ⟨81414191695041901514025557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54276127796694601009350371 81414191695041901514025557)
                  ·
                    refine ⟨954072558926272283367487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81414191695041901514025557 954072558926272283367487)
                    ·
                      rfl

theorem cell23_5574149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_5574149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574149 prefixEnd_5574149 := by exact prefixLift 5574149
  have htrace : WordTrace (prefixWord ++ tailWord_5574149) baseStart_5574149 baseEnd_5574149 := by
    simpa [prefixWord, tailWord_5574149, baseEnd_5574149] using wordTrace_append hprefix tailTrace_5574149
  have hstable : (prefixWord ++ tailWord_5574149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574149).length < 2 ^ (prefixWord ++ tailWord_5574149).sum := by decide
  have hdescent : baseEnd_5574149 < baseStart_5574149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574177 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_5574177 : Nat := 118140960795 + 5574177 * 2 ^ 59
def prefixEnd_5574177 : Nat := 4983230072969 + 3 ^ 40 * 5574177 * 2
def baseEnd_5574177 : Nat := 2862232054237142740552333

theorem tailTrace_5574177 : CollatzResearch.WordTrace tailWord_5574177 prefixEnd_5574177 2862232054237142740552333 := by
  unfold tailWord_5574177
  simp only [CollatzResearch.WordTrace]
  refine ⟨203306937526716197484624785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135537958351144131656416523 203306937526716197484624785)
  ·
    refine ⟨152480203145037148113468589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203306937526716197484624785 152480203145037148113468589)
    ·
      refine ⟨57180076179388930542550721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152480203145037148113468589 57180076179388930542550721)
      ·
        refine ⟨42885057134541697906913041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57180076179388930542550721 42885057134541697906913041)
        ·
          refine ⟨32163792850906273430184781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42885057134541697906913041 32163792850906273430184781)
          ·
            refine ⟨12061422319089852536319293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32163792850906273430184781 12061422319089852536319293)
            ·
              refine ⟨4523033369658694701119735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12061422319089852536319293 4523033369658694701119735)
              ·
                refine ⟨6784550054488042051679603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4523033369658694701119735 6784550054488042051679603)
                ·
                  refine ⟨10176825081732063077519405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6784550054488042051679603 10176825081732063077519405)
                  ·
                    refine ⟨3816309405649523654069777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10176825081732063077519405 3816309405649523654069777)
                    ·
                      refine ⟨2862232054237142740552333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816309405649523654069777 2862232054237142740552333)
                      ·
                        rfl

theorem cell23_5574177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_5574177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574177 prefixEnd_5574177 := by exact prefixLift 5574177
  have htrace : WordTrace (prefixWord ++ tailWord_5574177) baseStart_5574177 baseEnd_5574177 := by
    simpa [prefixWord, tailWord_5574177, baseEnd_5574177] using wordTrace_append hprefix tailTrace_5574177
  have hstable : (prefixWord ++ tailWord_5574177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574177).length < 2 ^ (prefixWord ++ tailWord_5574177).sum := by decide
  have hdescent : baseEnd_5574177 < baseStart_5574177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574283 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 3]
def baseStart_5574283 : Nat := 118140960795 + 5574283 * 2 ^ 59
def prefixEnd_5574283 : Nat := 4983230072969 + 3 ^ 40 * 5574283 * 2
def baseEnd_5574283 : Nat := 2862286483186519325826845

theorem tailTrace_5574283 : CollatzResearch.WordTrace tailWord_5574283 prefixEnd_5574283 2862286483186519325826845 := by
  unfold tailWord_5574283
  simp only [CollatzResearch.WordTrace]
  refine ⟨203310803664332177587983503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135540535776221451725322335 203310803664332177587983503)
  ·
    refine ⟨304966205496498266381975255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203310803664332177587983503 304966205496498266381975255)
    ·
      refine ⟨457449308244747399572962883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304966205496498266381975255 457449308244747399572962883)
      ·
        refine ⟨686173962367121099359444325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457449308244747399572962883 686173962367121099359444325)
        ·
          refine ⟨128657617943835206129895811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 686173962367121099359444325 128657617943835206129895811)
          ·
            refine ⟨192986426915752809194843717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128657617943835206129895811 192986426915752809194843717)
            ·
              refine ⟨36184955046703651724033197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192986426915752809194843717 36184955046703651724033197)
              ·
                refine ⟨13569358142513869396512449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36184955046703651724033197 13569358142513869396512449)
                ·
                  refine ⟨10177018606885402047384337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13569358142513869396512449 10177018606885402047384337)
                  ·
                    refine ⟨7632763955164051535538253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10177018606885402047384337 7632763955164051535538253)
                    ·
                      refine ⟨2862286483186519325826845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7632763955164051535538253 2862286483186519325826845)
                      ·
                        rfl

theorem cell23_5574283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 3].length) (baseStart_5574283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574283 prefixEnd_5574283 := by exact prefixLift 5574283
  have htrace : WordTrace (prefixWord ++ tailWord_5574283) baseStart_5574283 baseEnd_5574283 := by
    simpa [prefixWord, tailWord_5574283, baseEnd_5574283] using wordTrace_append hprefix tailTrace_5574283
  have hstable : (prefixWord ++ tailWord_5574283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574283).length < 2 ^ (prefixWord ++ tailWord_5574283).sum := by decide
  have hdescent : baseEnd_5574283 < baseStart_5574283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574307 : List Nat := [1, 1, 1, 4, 1, 1, 7, 2, 1, 4]
def baseStart_5574307 : Nat := 118140960795 + 5574307 * 2 ^ 59
def prefixEnd_5574307 : Nat := 4983230072969 + 3 ^ 40 * 5574307 * 2
def baseEnd_5574307 : Nat := 954099602240742410642245

theorem tailTrace_5574307 : CollatzResearch.WordTrace tailWord_5574307 prefixEnd_5574307 954099602240742410642245 := by
  unfold tailWord_5574307
  simp only [CollatzResearch.WordTrace]
  refine ⟨203311679016245229686857175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135541119344163486457904783 203311679016245229686857175)
  ·
    refine ⟨304967518524367844530285763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203311679016245229686857175 304967518524367844530285763)
    ·
      refine ⟨457451277786551766795428645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304967518524367844530285763 457451277786551766795428645)
      ·
        refine ⟨85772114584978456274142871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 457451277786551766795428645 85772114584978456274142871)
        ·
          refine ⟨128658171877467684411214307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85772114584978456274142871 128658171877467684411214307)
          ·
            refine ⟨192987257816201526616821461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128658171877467684411214307 192987257816201526616821461)
            ·
              refine ⟨4523138855067223280081753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 192987257816201526616821461 4523138855067223280081753)
              ·
                refine ⟨3392354141300417460061315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523138855067223280081753 3392354141300417460061315)
                ·
                  refine ⟨5088531211950626190091973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392354141300417460061315 5088531211950626190091973)
                  ·
                    refine ⟨954099602240742410642245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088531211950626190091973 954099602240742410642245)
                    ·
                      rfl

theorem cell23_5574307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 4].length) (baseStart_5574307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574307 prefixEnd_5574307 := by exact prefixLift 5574307
  have htrace : WordTrace (prefixWord ++ tailWord_5574307) baseStart_5574307 baseEnd_5574307 := by
    simpa [prefixWord, tailWord_5574307, baseEnd_5574307] using wordTrace_append hprefix tailTrace_5574307
  have hstable : (prefixWord ++ tailWord_5574307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574307).length < 2 ^ (prefixWord ++ tailWord_5574307).sum := by decide
  have hdescent : baseEnd_5574307 < baseStart_5574307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574333 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_5574333 : Nat := 118140960795 + 5574333 * 2 ^ 59
def prefixEnd_5574333 : Nat := 4983230072969 + 3 ^ 40 * 5574333 * 2
def baseEnd_5574333 : Nat := 954104052406414710067205

theorem tailTrace_5574333 : CollatzResearch.WordTrace tailWord_5574333 prefixEnd_5574333 954104052406414710067205 := by
  unfold tailWord_5574333
  simp only [CollatzResearch.WordTrace]
  refine ⟨203312627314151036127303653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135541751542767357418202435 203312627314151036127303653)
  ·
    refine ⟨38121117621403319273869435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203312627314151036127303653 38121117621403319273869435)
    ·
      refine ⟨57181676432104978910804153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38121117621403319273869435 57181676432104978910804153)
      ·
        refine ⟨42886257324078734183103115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57181676432104978910804153 42886257324078734183103115)
        ·
          refine ⟨64329385986118101274654673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42886257324078734183103115 64329385986118101274654673)
          ·
            refine ⟨48247039489588575955991005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64329385986118101274654673 48247039489588575955991005)
            ·
              refine ⟨18092639808595715983496627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48247039489588575955991005 18092639808595715983496627)
              ·
                refine ⟨27138959712893573975244941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18092639808595715983496627 27138959712893573975244941)
                ·
                  refine ⟨10177109892335090240716853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27138959712893573975244941 10177109892335090240716853)
                  ·
                    refine ⟨954104052406414710067205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10177109892335090240716853 954104052406414710067205)
                    ·
                      rfl

theorem cell23_5574333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_5574333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574333 prefixEnd_5574333 := by exact prefixLift 5574333
  have htrace : WordTrace (prefixWord ++ tailWord_5574333) baseStart_5574333 baseEnd_5574333 := by
    simpa [prefixWord, tailWord_5574333, baseEnd_5574333] using wordTrace_append hprefix tailTrace_5574333
  have hstable : (prefixWord ++ tailWord_5574333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574333).length < 2 ^ (prefixWord ++ tailWord_5574333).sum := by decide
  have hdescent : baseEnd_5574333 < baseStart_5574333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574373 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5574373 : Nat := 118140960795 + 5574373 * 2 ^ 59
def prefixEnd_5574373 : Nat := 4983230072969 + 3 ^ 40 * 5574373 * 2
def baseEnd_5574373 : Nat := 2862332696445423973701431

theorem tailTrace_5574373 : CollatzResearch.WordTrace tailWord_5574373 prefixEnd_5574373 2862332696445423973701431 := by
  unfold tailWord_5574373
  simp only [CollatzResearch.WordTrace]
  refine ⟨203314086234006122958759773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135542724156004081972506515 203314086234006122958759773)
  ·
    refine ⟨76242782337752296109534915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203314086234006122958759773 76242782337752296109534915)
    ·
      refine ⟨114364173506628444164302373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76242782337752296109534915 114364173506628444164302373)
      ·
        refine ⟨21443282532492833280806695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114364173506628444164302373 21443282532492833280806695)
        ·
          refine ⟨32164923798739249921210043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21443282532492833280806695 32164923798739249921210043)
          ·
            refine ⟨48247385698108874881815065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32164923798739249921210043 48247385698108874881815065)
            ·
              refine ⟨36185539273581656161361299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48247385698108874881815065 36185539273581656161361299)
              ·
                refine ⟨54278308910372484242041949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36185539273581656161361299 54278308910372484242041949)
                ·
                  refine ⟨20354365841389681590765731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54278308910372484242041949 20354365841389681590765731)
                  ·
                    refine ⟨30531548762084522386148597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20354365841389681590765731 30531548762084522386148597)
                    ·
                      refine ⟨2862332696445423973701431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30531548762084522386148597 2862332696445423973701431)
                      ·
                        rfl

theorem cell23_5574373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5574373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574373 prefixEnd_5574373 := by exact prefixLift 5574373
  have htrace : WordTrace (prefixWord ++ tailWord_5574373) baseStart_5574373 baseEnd_5574373 := by
    simpa [prefixWord, tailWord_5574373, baseEnd_5574373] using wordTrace_append hprefix tailTrace_5574373
  have hstable : (prefixWord ++ tailWord_5574373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574373).length < 2 ^ (prefixWord ++ tailWord_5574373).sum := by decide
  have hdescent : baseEnd_5574373 < baseStart_5574373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574380 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_5574380 : Nat := 118140960795 + 5574380 * 2 ^ 59
def prefixEnd_5574380 : Nat := 4983230072969 + 3 ^ 40 * 5574380 * 2
def baseEnd_5574380 : Nat := 954112096936668482104633

theorem tailTrace_5574380 : CollatzResearch.WordTrace tailWord_5574380 prefixEnd_5574380 954112096936668482104633 := by
  unfold tailWord_5574380
  simp only [CollatzResearch.WordTrace]
  refine ⟨101657170772490381577132297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135542894363320508769509729 101657170772490381577132297)
  ·
    refine ⟨76242878079367786182849223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101657170772490381577132297 76242878079367786182849223)
    ·
      refine ⟨114364317119051679274273835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76242878079367786182849223 114364317119051679274273835)
      ·
        refine ⟨171546475678577518911410753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114364317119051679274273835 171546475678577518911410753)
        ·
          refine ⟨128659856758933139183558065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171546475678577518911410753 128659856758933139183558065)
          ·
            refine ⟨96494892569199854387668549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128659856758933139183558065 96494892569199854387668549)
            ·
              refine ⟨18092792356724972697687853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96494892569199854387668549 18092792356724972697687853)
              ·
                refine ⟨6784797133771864761632945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18092792356724972697687853 6784797133771864761632945)
                ·
                  refine ⟨5088597850328898571224709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6784797133771864761632945 5088597850328898571224709)
                  ·
                    refine ⟨954112096936668482104633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088597850328898571224709 954112096936668482104633)
                    ·
                      rfl

theorem cell23_5574380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_5574380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574380 prefixEnd_5574380 := by exact prefixLift 5574380
  have htrace : WordTrace (prefixWord ++ tailWord_5574380) baseStart_5574380 baseEnd_5574380 := by
    simpa [prefixWord, tailWord_5574380, baseEnd_5574380] using wordTrace_append hprefix tailTrace_5574380
  have hstable : (prefixWord ++ tailWord_5574380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574380).length < 2 ^ (prefixWord ++ tailWord_5574380).sum := by decide
  have hdescent : baseEnd_5574380 < baseStart_5574380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574404 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_5574404 : Nat := 118140960795 + 5574404 * 2 ^ 59
def prefixEnd_5574404 : Nat := 4983230072969 + 3 ^ 40 * 5574404 * 2
def baseEnd_5574404 : Nat := 2862348614345713352413789

theorem tailTrace_5574404 : CollatzResearch.WordTrace tailWord_5574404 prefixEnd_5574404 2862348614345713352413789 := by
  unfold tailWord_5574404
  simp only [CollatzResearch.WordTrace]
  refine ⟨101657608448446907626569133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135543477931262543502092177 101657608448446907626569133)
  ·
    refine ⟨38121603168167590359963425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101657608448446907626569133 38121603168167590359963425)
    ·
      refine ⟨28591202376125692769972569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38121603168167590359963425 28591202376125692769972569)
      ·
        refine ⟨21443401782094269577479427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28591202376125692769972569 21443401782094269577479427)
        ·
          refine ⟨32165102673141404366219141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21443401782094269577479427 32165102673141404366219141)
          ·
            refine ⟨6030956751214013318666089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32165102673141404366219141 6030956751214013318666089)
            ·
              refine ⟨4523217563410509988999567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6030956751214013318666089 4523217563410509988999567)
              ·
                refine ⟨6784826345115764983499351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4523217563410509988999567 6784826345115764983499351)
                ·
                  refine ⟨10177239517673647475249027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6784826345115764983499351 10177239517673647475249027)
                  ·
                    refine ⟨15265859276510471212873541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10177239517673647475249027 15265859276510471212873541)
                    ·
                      refine ⟨2862348614345713352413789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15265859276510471212873541 2862348614345713352413789)
                      ·
                        rfl

theorem cell23_5574404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_5574404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574404 prefixEnd_5574404 := by exact prefixLift 5574404
  have htrace : WordTrace (prefixWord ++ tailWord_5574404) baseStart_5574404 baseEnd_5574404 := by
    simpa [prefixWord, tailWord_5574404, baseEnd_5574404] using wordTrace_append hprefix tailTrace_5574404
  have hstable : (prefixWord ++ tailWord_5574404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574404).length < 2 ^ (prefixWord ++ tailWord_5574404).sum := by decide
  have hdescent : baseEnd_5574404 < baseStart_5574404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574437 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_5574437 : Nat := 118140960795 + 5574437 * 2 ^ 59
def prefixEnd_5574437 : Nat := 4983230072969 + 3 ^ 40 * 5574437 * 2
def baseEnd_5574437 : Nat := 2862365559207311723301137

theorem tailTrace_5574437 : CollatzResearch.WordTrace tailWord_5574437 prefixEnd_5574437 2862365559207311723301137 := by
  unfold tailWord_5574437
  simp only [CollatzResearch.WordTrace]
  refine ⟨203316420505774261889089565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135544280337182841259393043 203316420505774261889089565)
  ·
    refine ⟨76243657689665348208408587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203316420505774261889089565 76243657689665348208408587)
    ·
      refine ⟨114365486534498022312612881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76243657689665348208408587 114365486534498022312612881)
      ·
        refine ⟨85774114900873516734459661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114365486534498022312612881 85774114900873516734459661)
        ·
          refine ⟨32165293087827568775422373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85774114900873516734459661 32165293087827568775422373)
          ·
            refine ⟨6030992453967669145391695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32165293087827568775422373 6030992453967669145391695)
            ·
              refine ⟨9046488680951503718087543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6030992453967669145391695 9046488680951503718087543)
              ·
                refine ⟨13569733021427255577131315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9046488680951503718087543 13569733021427255577131315)
                ·
                  refine ⟨20354599532140883365696973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13569733021427255577131315 20354599532140883365696973)
                  ·
                    refine ⟨7632974824552831262136365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20354599532140883365696973 7632974824552831262136365)
                    ·
                      refine ⟨2862365559207311723301137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7632974824552831262136365 2862365559207311723301137)
                      ·
                        rfl

theorem cell23_5574437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_5574437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574437 prefixEnd_5574437 := by exact prefixLift 5574437
  have htrace : WordTrace (prefixWord ++ tailWord_5574437) baseStart_5574437 baseEnd_5574437 := by
    simpa [prefixWord, tailWord_5574437, baseEnd_5574437] using wordTrace_append hprefix tailTrace_5574437
  have hstable : (prefixWord ++ tailWord_5574437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574437).length < 2 ^ (prefixWord ++ tailWord_5574437).sum := by decide
  have hdescent : baseEnd_5574437 < baseStart_5574437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574454 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5574454 : Nat := 118140960795 + 5574454 * 2 ^ 59
def prefixEnd_5574454 : Nat := 4983230072969 + 3 ^ 40 * 5574454 * 2
def baseEnd_5574454 : Nat := 2862374288378438156788559

theorem tailTrace_5574454 : CollatzResearch.WordTrace tailWord_5574454 prefixEnd_5574454 2862374288378438156788559 := by
  unfold tailWord_5574454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707315034169542112028651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135544693697808449194972277 12707315034169542112028651)
  ·
    refine ⟨19060972551254313168042977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12707315034169542112028651 19060972551254313168042977)
    ·
      refine ⟨14295729413440734876032233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19060972551254313168042977 14295729413440734876032233)
      ·
        refine ⟨10721797060080551157024175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14295729413440734876032233 10721797060080551157024175)
        ·
          refine ⟨16082695590120826735536263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10721797060080551157024175 16082695590120826735536263)
          ·
            refine ⟨24124043385181240103304395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16082695590120826735536263 24124043385181240103304395)
            ·
              refine ⟨36186065077771860154956593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24124043385181240103304395 36186065077771860154956593)
              ·
                refine ⟨27139548808328895116217445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36186065077771860154956593 27139548808328895116217445)
                ·
                  refine ⟨5088665401561667834290771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27139548808328895116217445 5088665401561667834290771)
                  ·
                    refine ⟨7632998102342501751436157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5088665401561667834290771 7632998102342501751436157)
                    ·
                      refine ⟨2862374288378438156788559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7632998102342501751436157 2862374288378438156788559)
                      ·
                        rfl

theorem cell23_5574454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5574454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574454 prefixEnd_5574454 := by exact prefixLift 5574454
  have htrace : WordTrace (prefixWord ++ tailWord_5574454) baseStart_5574454 baseEnd_5574454 := by
    simpa [prefixWord, tailWord_5574454, baseEnd_5574454] using wordTrace_append hprefix tailTrace_5574454
  have hstable : (prefixWord ++ tailWord_5574454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574454).length < 2 ^ (prefixWord ++ tailWord_5574454).sum := by decide
  have hdescent : baseEnd_5574454 < baseStart_5574454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574517 : List Nat := [1, 3, 4, 1, 1, 1, 2, 5, 5]
def baseStart_5574517 : Nat := 118140960795 + 5574517 * 2 ^ 59
def prefixEnd_5574517 : Nat := 4983230072969 + 3 ^ 40 * 5574517 * 2
def baseEnd_5574517 : Nat := 318045181962185712255641

theorem tailTrace_5574517 : CollatzResearch.WordTrace tailWord_5574517 prefixEnd_5574517 318045181962185712255641 := by
  unfold tailWord_5574517
  simp only [CollatzResearch.WordTrace]
  refine ⟨203319338345484435552001805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135546225563656290368001203 203319338345484435552001805)
  ·
    refine ⟨76244751879556663332000677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203319338345484435552001805 76244751879556663332000677)
    ·
      refine ⟨14295890977416874374750127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76244751879556663332000677 14295890977416874374750127)
      ·
        refine ⟨21443836466125311562125191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14295890977416874374750127 21443836466125311562125191)
        ·
          refine ⟨32165754699187967343187787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21443836466125311562125191 32165754699187967343187787)
          ·
            refine ⟨48248632048781951014781681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32165754699187967343187787 48248632048781951014781681)
            ·
              refine ⟨36186474036586463261086261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48248632048781951014781681 36186474036586463261086261)
              ·
                refine ⟨3392481940929980930726837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36186474036586463261086261 3392481940929980930726837)
                ·
                  refine ⟨318045181962185712255641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3392481940929980930726837 318045181962185712255641)
                  ·
                    rfl

theorem cell23_5574517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_5574517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574517 prefixEnd_5574517 := by exact prefixLift 5574517
  have htrace : WordTrace (prefixWord ++ tailWord_5574517) baseStart_5574517 baseEnd_5574517 := by
    simpa [prefixWord, tailWord_5574517, baseEnd_5574517] using wordTrace_append hprefix tailTrace_5574517
  have hstable : (prefixWord ++ tailWord_5574517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574517).length < 2 ^ (prefixWord ++ tailWord_5574517).sum := by decide
  have hdescent : baseEnd_5574517 < baseStart_5574517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574567 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5574567 : Nat := 118140960795 + 5574567 * 2 ^ 59
def prefixEnd_5574567 : Nat := 4983230072969 + 3 ^ 40 * 5574567 * 2
def baseEnd_5574567 : Nat := 2862432311692396214675539

theorem tailTrace_5574567 : CollatzResearch.WordTrace tailWord_5574567 prefixEnd_5574567 2862432311692396214675539 := by
  unfold tailWord_5574567
  simp only [CollatzResearch.WordTrace]
  refine ⟨203321161995303294091321955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135547441330202196060881303 203321161995303294091321955)
  ·
    refine ⟨304981742992954941136982933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203321161995303294091321955 304981742992954941136982933)
    ·
      refine ⟨14296019202794762865796075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 304981742992954941136982933 14296019202794762865796075)
      ·
        refine ⟨21444028804192144298694113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14296019202794762865796075 21444028804192144298694113)
        ·
          refine ⟨16083021603144108224020585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21444028804192144298694113 16083021603144108224020585)
          ·
            refine ⟨12062266202358081168015439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16083021603144108224020585 12062266202358081168015439)
            ·
              refine ⟨18093399303537121752023159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12062266202358081168015439 18093399303537121752023159)
              ·
                refine ⟨27140098955305682628034739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18093399303537121752023159 27140098955305682628034739)
                ·
                  refine ⟨40710148432958523942052109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27140098955305682628034739 40710148432958523942052109)
                  ·
                    refine ⟨15266305662359446478269541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40710148432958523942052109 15266305662359446478269541)
                    ·
                      refine ⟨2862432311692396214675539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15266305662359446478269541 2862432311692396214675539)
                      ·
                        rfl

theorem cell23_5574567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5574567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574567 prefixEnd_5574567 := by exact prefixLift 5574567
  have htrace : WordTrace (prefixWord ++ tailWord_5574567) baseStart_5574567 baseEnd_5574567 := by
    simpa [prefixWord, tailWord_5574567, baseEnd_5574567] using wordTrace_append hprefix tailTrace_5574567
  have hstable : (prefixWord ++ tailWord_5574567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574567).length < 2 ^ (prefixWord ++ tailWord_5574567).sum := by decide
  have hdescent : baseEnd_5574567 < baseStart_5574567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574607 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 6]
def baseStart_5574607 : Nat := 118140960795 + 5574607 * 2 ^ 59
def prefixEnd_5574607 : Nat := 4983230072969 + 3 ^ 40 * 5574607 * 2
def baseEnd_5574607 : Nat := 318050316768730673130595

theorem tailTrace_5574607 : CollatzResearch.WordTrace tailWord_5574607 prefixEnd_5574607 318050316768730673130595 := by
  unfold tailWord_5574607
  simp only [CollatzResearch.WordTrace]
  refine ⟨203322620915158380922778075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135548413943438920615185383 203322620915158380922778075)
  ·
    refine ⟨304983931372737571384167113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203322620915158380922778075 304983931372737571384167113)
    ·
      refine ⟨228737948529553178538125335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304983931372737571384167113 228737948529553178538125335)
      ·
        refine ⟨343106922794329767807188003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228737948529553178538125335 343106922794329767807188003)
        ·
          refine ⟨514660384191494651710782005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343106922794329767807188003 514660384191494651710782005)
          ·
            refine ⟨48249411017952623597885813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 514660384191494651710782005 48249411017952623597885813)
            ·
              refine ⟨4523382282933058462301795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48249411017952623597885813 4523382282933058462301795)
              ·
                refine ⟨6785073424399587693452693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4523382282933058462301795 6785073424399587693452693)
                ·
                  refine ⟨318050316768730673130595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6785073424399587693452693 318050316768730673130595)
                  ·
                    rfl

theorem cell23_5574607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 6].length) (baseStart_5574607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574607 prefixEnd_5574607 := by exact prefixLift 5574607
  have htrace : WordTrace (prefixWord ++ tailWord_5574607) baseStart_5574607 baseEnd_5574607 := by
    simpa [prefixWord, tailWord_5574607, baseEnd_5574607] using wordTrace_append hprefix tailTrace_5574607
  have hstable : (prefixWord ++ tailWord_5574607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574607).length < 2 ^ (prefixWord ++ tailWord_5574607).sum := by decide
  have hdescent : baseEnd_5574607 < baseStart_5574607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574657 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_5574657 : Nat := 118140960795 + 5574657 * 2 ^ 59
def prefixEnd_5574657 : Nat := 4983230072969 + 3 ^ 40 * 5574657 * 2
def baseEnd_5574657 : Nat := 2862478524951300862550125

theorem tailTrace_5574657 : CollatzResearch.WordTrace tailWord_5574657 prefixEnd_5574657 2862478524951300862550125 := by
  unfold tailWord_5574657
  simp only [CollatzResearch.WordTrace]
  refine ⟨203324444564977239462098225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135549629709984826308065483 203324444564977239462098225)
  ·
    refine ⟨152493333423732929596573669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203324444564977239462098225 152493333423732929596573669)
    ·
      refine ⟨28592500016949924299357563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152493333423732929596573669 28592500016949924299357563)
      ·
        refine ⟨42888750025424886449036345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28592500016949924299357563 42888750025424886449036345)
        ·
          refine ⟨32166562519068664836777259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42888750025424886449036345 32166562519068664836777259)
          ·
            refine ⟨48249843778602997255165889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32166562519068664836777259 48249843778602997255165889)
            ·
              refine ⟨36187382833952247941374417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48249843778602997255165889 36187382833952247941374417)
              ·
                refine ⟨27140537125464185956030813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36187382833952247941374417 27140537125464185956030813)
                ·
                  refine ⟨10177701422049069733511555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27140537125464185956030813 10177701422049069733511555)
                  ·
                    refine ⟨15266552133073604600267333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10177701422049069733511555 15266552133073604600267333)
                    ·
                      refine ⟨2862478524951300862550125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15266552133073604600267333 2862478524951300862550125)
                      ·
                        rfl

theorem cell23_5574657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_5574657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574657 prefixEnd_5574657 := by exact prefixLift 5574657
  have htrace : WordTrace (prefixWord ++ tailWord_5574657) baseStart_5574657 baseEnd_5574657 := by
    simpa [prefixWord, tailWord_5574657, baseEnd_5574657] using wordTrace_append hprefix tailTrace_5574657
  have hstable : (prefixWord ++ tailWord_5574657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574657).length < 2 ^ (prefixWord ++ tailWord_5574657).sum := by decide
  have hdescent : baseEnd_5574657 < baseStart_5574657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574680 : List Nat := [2, 1, 2, 3, 2, 1, 1, 11]
def baseStart_5574680 : Nat := 118140960795 + 5574680 * 2 ^ 59
def prefixEnd_5574680 : Nat := 4983230072969 + 3 ^ 40 * 5574680 * 2
def baseEnd_5574680 : Nat := 106018160555790898983797

theorem tailTrace_5574680 : CollatzResearch.WordTrace tailWord_5574680 prefixEnd_5574680 106018160555790898983797 := by
  unfold tailWord_5574680
  simp only [CollatzResearch.WordTrace]
  refine ⟨101662641721946957195092747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135550188962595942926790329 101662641721946957195092747)
  ·
    refine ⟨152493962582920435792639121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101662641721946957195092747 152493962582920435792639121)
    ·
      refine ⟨114370471937190326844479341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152493962582920435792639121 114370471937190326844479341)
      ·
        refine ⟨42888926976446372566679753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114370471937190326844479341 42888926976446372566679753)
        ·
          refine ⟨32166695232334779425009815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42888926976446372566679753 32166695232334779425009815)
          ·
            refine ⟨48250042848502169137514723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32166695232334779425009815 48250042848502169137514723)
            ·
              refine ⟨72375064272753253706272085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48250042848502169137514723 72375064272753253706272085)
              ·
                refine ⟨106018160555790898983797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 72375064272753253706272085 106018160555790898983797)
                ·
                  rfl

theorem cell23_5574680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 11].length) (baseStart_5574680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574680 prefixEnd_5574680 := by exact prefixLift 5574680
  have htrace : WordTrace (prefixWord ++ tailWord_5574680) baseStart_5574680 baseEnd_5574680 := by
    simpa [prefixWord, tailWord_5574680, baseEnd_5574680] using wordTrace_append hprefix tailTrace_5574680
  have hstable : (prefixWord ++ tailWord_5574680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574680).length < 2 ^ (prefixWord ++ tailWord_5574680).sum := by decide
  have hdescent : baseEnd_5574680 < baseStart_5574680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574687 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_5574687 : Nat := 118140960795 + 5574687 * 2 ^ 59
def prefixEnd_5574687 : Nat := 4983230072969 + 3 ^ 40 * 5574687 * 2
def baseEnd_5574687 : Nat := 2862493929370935745174987

theorem tailTrace_5574687 : CollatzResearch.WordTrace tailWord_5574687 prefixEnd_5574687 2862493929370935745174987 := by
  unfold tailWord_5574687
  simp only [CollatzResearch.WordTrace]
  refine ⟨203325538754868554585690315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135550359169912369723793543 203325538754868554585690315)
  ·
    refine ⟨304988308132302831878535473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203325538754868554585690315 304988308132302831878535473)
    ·
      refine ⟨228741231099227123908901605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304988308132302831878535473 228741231099227123908901605)
      ·
        refine ⟨42888980831105085732919051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228741231099227123908901605 42888980831105085732919051)
        ·
          refine ⟨64333471246657628599378577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42888980831105085732919051 64333471246657628599378577)
          ·
            refine ⟨48250103434993221449533933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64333471246657628599378577 48250103434993221449533933)
            ·
              refine ⟨18093788788122458043575225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48250103434993221449533933 18093788788122458043575225)
              ·
                refine ⟨13570341591091843532681419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18093788788122458043575225 13570341591091843532681419)
                ·
                  refine ⟨20355512386637765299022129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13570341591091843532681419 20355512386637765299022129)
                  ·
                    refine ⟨15266634289978323974266597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20355512386637765299022129 15266634289978323974266597)
                    ·
                      refine ⟨2862493929370935745174987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15266634289978323974266597 2862493929370935745174987)
                      ·
                        rfl

theorem cell23_5574687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_5574687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574687 prefixEnd_5574687 := by exact prefixLift 5574687
  have htrace : WordTrace (prefixWord ++ tailWord_5574687) baseStart_5574687 baseEnd_5574687 := by
    simpa [prefixWord, tailWord_5574687, baseEnd_5574687] using wordTrace_append hprefix tailTrace_5574687
  have hstable : (prefixWord ++ tailWord_5574687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574687).length < 2 ^ (prefixWord ++ tailWord_5574687).sum := by decide
  have hdescent : baseEnd_5574687 < baseStart_5574687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574700 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_5574700 : Nat := 118140960795 + 5574700 * 2 ^ 59
def prefixEnd_5574700 : Nat := 4983230072969 + 3 ^ 40 * 5574700 * 2
def baseEnd_5574700 : Nat := 2862500604619444194312427

theorem tailTrace_5574700 : CollatzResearch.WordTrace tailWord_5574700 prefixEnd_5574700 2862500604619444194312427 := by
  unfold tailWord_5574700
  simp only [CollatzResearch.WordTrace]
  refine ⟨101663006451910728902956777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135550675269214305203942369 101663006451910728902956777)
  ·
    refine ⟨76247254838933046677217583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101663006451910728902956777 76247254838933046677217583)
    ·
      refine ⟨114370882258399570015826375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76247254838933046677217583 114370882258399570015826375)
      ·
        refine ⟨171556323387599355023739563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114370882258399570015826375 171556323387599355023739563)
        ·
          refine ⟨257334485081399032535609345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171556323387599355023739563 257334485081399032535609345)
          ·
            refine ⟨193000863811049274401707009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257334485081399032535609345 193000863811049274401707009)
            ·
              refine ⟨144750647858286955801280257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193000863811049274401707009 144750647858286955801280257)
              ·
                refine ⟨108562985893715216850960193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144750647858286955801280257 108562985893715216850960193)
                ·
                  refine ⟨81422239420286412638220145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108562985893715216850960193 81422239420286412638220145)
                  ·
                    refine ⟨61066679565214809478665109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81422239420286412638220145 61066679565214809478665109)
                    ·
                      refine ⟨2862500604619444194312427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61066679565214809478665109 2862500604619444194312427)
                      ·
                        rfl

theorem cell23_5574700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_5574700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574700 prefixEnd_5574700 := by exact prefixLift 5574700
  have htrace : WordTrace (prefixWord ++ tailWord_5574700) baseStart_5574700 baseEnd_5574700 := by
    simpa [prefixWord, tailWord_5574700, baseEnd_5574700] using wordTrace_append hprefix tailTrace_5574700
  have hstable : (prefixWord ++ tailWord_5574700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574700).length < 2 ^ (prefixWord ++ tailWord_5574700).sum := by decide
  have hdescent : baseEnd_5574700 < baseStart_5574700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574742 : List Nat := [5, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_5574742 : Nat := 118140960795 + 5574742 * 2 ^ 59
def prefixEnd_5574742 : Nat := 4983230072969 + 3 ^ 40 * 5574742 * 2
def baseEnd_5574742 : Nat := 2862522170806933029987235

theorem tailTrace_5574742 : CollatzResearch.WordTrace tailWord_5574742 prefixEnd_5574742 2862522170806933029987235 := by
  unfold tailWord_5574742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707971548104331186183905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135551696513112865985961653 12707971548104331186183905)
  ·
    refine ⟨9530978661078248389637929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12707971548104331186183905 9530978661078248389637929)
    ·
      refine ⟨7148233995808686292228447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9530978661078248389637929 7148233995808686292228447)
      ·
        refine ⟨10722350993713029438342671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148233995808686292228447 10722350993713029438342671)
        ·
          refine ⟨16083526490569544157514007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10722350993713029438342671 16083526490569544157514007)
          ·
            refine ⟨24125289735854316236271011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16083526490569544157514007 24125289735854316236271011)
            ·
              refine ⟨36187934603781474354406517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24125289735854316236271011 36187934603781474354406517)
              ·
                refine ⟨3392618869104513220725611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36187934603781474354406517 3392618869104513220725611)
                ·
                  refine ⟨5088928303656769831088417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392618869104513220725611 5088928303656769831088417)
                  ·
                    refine ⟨3816696227742577373316313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5088928303656769831088417 3816696227742577373316313)
                    ·
                      refine ⟨2862522170806933029987235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816696227742577373316313 2862522170806933029987235)
                      ·
                        rfl

theorem cell23_5574742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_5574742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574742 prefixEnd_5574742 := by exact prefixLift 5574742
  have htrace : WordTrace (prefixWord ++ tailWord_5574742) baseStart_5574742 baseEnd_5574742 := by
    simpa [prefixWord, tailWord_5574742, baseEnd_5574742] using wordTrace_append hprefix tailTrace_5574742
  have hstable : (prefixWord ++ tailWord_5574742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574742).length < 2 ^ (prefixWord ++ tailWord_5574742).sum := by decide
  have hdescent : baseEnd_5574742 < baseStart_5574742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574757 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_5574757 : Nat := 118140960795 + 5574757 * 2 ^ 59
def prefixEnd_5574757 : Nat := 4983230072969 + 3 ^ 40 * 5574757 * 2
def baseEnd_5574757 : Nat := 954176624338916823766555

theorem tailTrace_5574757 : CollatzResearch.WordTrace tailWord_5574757 prefixEnd_5574757 954176624338916823766555 := by
  unfold tailWord_5574757
  simp only [CollatzResearch.WordTrace]
  refine ⟨203328091864614956540738525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135552061243076637693825683 203328091864614956540738525)
  ·
    refine ⟨76248034449230608702776947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203328091864614956540738525 76248034449230608702776947)
    ·
      refine ⟨114372051673845913054165421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76248034449230608702776947 114372051673845913054165421)
      ·
        refine ⟨42889519377692217395312033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114372051673845913054165421 42889519377692217395312033)
        ·
          refine ⟨32167139533269163046484025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42889519377692217395312033 32167139533269163046484025)
          ·
            refine ⟨24125354649951872284863019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32167139533269163046484025 24125354649951872284863019)
            ·
              refine ⟨36188031974927808427294529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24125354649951872284863019 36188031974927808427294529)
              ·
                refine ⟨27141023981195856320470897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36188031974927808427294529 27141023981195856320470897)
                ·
                  refine ⟨20355767985896892240353173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27141023981195856320470897 20355767985896892240353173)
                  ·
                    refine ⟨954176624338916823766555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20355767985896892240353173 954176624338916823766555)
                    ·
                      rfl

theorem cell23_5574757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_5574757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574757 prefixEnd_5574757 := by exact prefixLift 5574757
  have htrace : WordTrace (prefixWord ++ tailWord_5574757) baseStart_5574757 baseEnd_5574757 := by
    simpa [prefixWord, tailWord_5574757, baseEnd_5574757] using wordTrace_append hprefix tailTrace_5574757
  have hstable : (prefixWord ++ tailWord_5574757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574757).length < 2 ^ (prefixWord ++ tailWord_5574757).sum := by decide
  have hdescent : baseEnd_5574757 < baseStart_5574757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574774 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_5574774 : Nat := 118140960795 + 5574774 * 2 ^ 59
def prefixEnd_5574774 : Nat := 4983230072969 + 3 ^ 40 * 5574774 * 2
def baseEnd_5574774 : Nat := 954179534062625634929029

theorem tailTrace_5574774 : CollatzResearch.WordTrace tailWord_5574774 prefixEnd_5574774 954179534062625634929029 := by
  unfold tailWord_5574774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12708044494097085527756711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135552474603702245629404917 12708044494097085527756711)
  ·
    refine ⟨19062066741145628291635067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12708044494097085527756711 19062066741145628291635067)
    ·
      refine ⟨28593100111718442437452601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19062066741145628291635067 28593100111718442437452601)
      ·
        refine ⟨21444825083788831828089451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28593100111718442437452601 21444825083788831828089451)
        ·
          refine ⟨32167237625683247742134177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21444825083788831828089451 32167237625683247742134177)
          ·
            refine ⟨24125428219262435806600633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32167237625683247742134177 24125428219262435806600633)
            ·
              refine ⟨18094071164446826854950475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24125428219262435806600633 18094071164446826854950475)
              ·
                refine ⟨27141106746670240282425713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18094071164446826854950475 27141106746670240282425713)
                ·
                  refine ⟨20355830060002680211819285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27141106746670240282425713 20355830060002680211819285)
                  ·
                    refine ⟨954179534062625634929029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20355830060002680211819285 954179534062625634929029)
                    ·
                      rfl

theorem cell23_5574774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_5574774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574774 prefixEnd_5574774 := by exact prefixLift 5574774
  have htrace : WordTrace (prefixWord ++ tailWord_5574774) baseStart_5574774 baseEnd_5574774 := by
    simpa [prefixWord, tailWord_5574774, baseEnd_5574774] using wordTrace_append hprefix tailTrace_5574774
  have hstable : (prefixWord ++ tailWord_5574774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574774).length < 2 ^ (prefixWord ++ tailWord_5574774).sum := by decide
  have hdescent : baseEnd_5574774 < baseStart_5574774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574781 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_5574781 : Nat := 118140960795 + 5574781 * 2 ^ 59
def prefixEnd_5574781 : Nat := 4983230072969 + 3 ^ 40 * 5574781 * 2
def baseEnd_5574781 : Nat := 2862542196552458377399555

theorem tailTrace_5574781 : CollatzResearch.WordTrace tailWord_5574781 prefixEnd_5574781 2862542196552458377399555 := by
  unfold tailWord_5574781
  simp only [CollatzResearch.WordTrace]
  refine ⟨203328967216528008639612197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135552644811018672426408131 203328967216528008639612197)
  ·
    refine ⟨38124181353099001619927287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203328967216528008639612197 38124181353099001619927287)
    ·
      refine ⟨57186272029648502429890931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38124181353099001619927287 57186272029648502429890931)
      ·
        refine ⟨85779408044472753644836397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57186272029648502429890931 85779408044472753644836397)
        ·
          refine ⟨32167278016677282616813649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85779408044472753644836397 32167278016677282616813649)
          ·
            refine ⟨24125458512507961962610237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32167278016677282616813649 24125458512507961962610237)
            ·
              refine ⟨9047046942190485735978839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24125458512507961962610237 9047046942190485735978839)
              ·
                refine ⟨13570570413285728603968259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9047046942190485735978839 13570570413285728603968259)
                ·
                  refine ⟨20355855619928592905952389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13570570413285728603968259 20355855619928592905952389)
                  ·
                    refine ⟨3816722928736611169866073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20355855619928592905952389 3816722928736611169866073)
                    ·
                      refine ⟨2862542196552458377399555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816722928736611169866073 2862542196552458377399555)
                      ·
                        rfl

theorem cell23_5574781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_5574781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574781 prefixEnd_5574781 := by exact prefixLift 5574781
  have htrace : WordTrace (prefixWord ++ tailWord_5574781) baseStart_5574781 baseEnd_5574781 := by
    simpa [prefixWord, tailWord_5574781, baseEnd_5574781] using wordTrace_append hprefix tailTrace_5574781
  have hstable : (prefixWord ++ tailWord_5574781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574781).length < 2 ^ (prefixWord ++ tailWord_5574781).sum := by decide
  have hdescent : baseEnd_5574781 < baseStart_5574781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574787 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 7]
def baseStart_5574787 : Nat := 118140960795 + 5574787 * 2 ^ 59
def prefixEnd_5574787 : Nat := 4983230072969 + 3 ^ 40 * 5574787 * 2
def baseEnd_5574787 : Nat := 318060586381820594880503

theorem tailTrace_5574787 : CollatzResearch.WordTrace tailWord_5574787 prefixEnd_5574787 318060586381820594880503 := by
  unfold tailWord_5574787
  simp only [CollatzResearch.WordTrace]
  refine ⟨203329186054506271664330615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135552790703004181109553743 203329186054506271664330615)
  ·
    refine ⟨304993779081759407496495923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203329186054506271664330615 304993779081759407496495923)
    ·
      refine ⟨457490668622639111244743885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304993779081759407496495923 457490668622639111244743885)
      ·
        refine ⟨171559000733489666716778957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457490668622639111244743885 171559000733489666716778957)
        ·
          refine ⟨64334625275058625018792109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171559000733489666716778957 64334625275058625018792109)
          ·
            refine ⟨24125484478146984382047041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64334625275058625018792109 24125484478146984382047041)
            ·
              refine ⟨18094113358610238286535281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24125484478146984382047041 18094113358610238286535281)
              ·
                refine ⟨13570585018957678714901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18094113358610238286535281 13570585018957678714901461)
                ·
                  refine ⟨318060586381820594880503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13570585018957678714901461 318060586381820594880503)
                  ·
                    rfl

theorem cell23_5574787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 7].length) (baseStart_5574787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574787 prefixEnd_5574787 := by exact prefixLift 5574787
  have htrace : WordTrace (prefixWord ++ tailWord_5574787) baseStart_5574787 baseEnd_5574787 := by
    simpa [prefixWord, tailWord_5574787, baseEnd_5574787] using wordTrace_append hprefix tailTrace_5574787
  have hstable : (prefixWord ++ tailWord_5574787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574787).length < 2 ^ (prefixWord ++ tailWord_5574787).sum := by decide
  have hdescent : baseEnd_5574787 < baseStart_5574787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574821 : List Nat := [1, 3, 1, 2, 1, 3, 5, 2, 5]
def baseStart_5574821 : Nat := 118140960795 + 5574821 * 2 ^ 59
def prefixEnd_5574821 : Nat := 4983230072969 + 3 ^ 40 * 5574821 * 2
def baseEnd_5574821 : Nat := 318062526197626468988819

theorem tailTrace_5574821 : CollatzResearch.WordTrace tailWord_5574821 prefixEnd_5574821 318062526197626468988819 := by
  unfold tailWord_5574821
  simp only [CollatzResearch.WordTrace]
  refine ⟨203330426136383095471068317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135553617424255396980712211 203330426136383095471068317)
  ·
    refine ⟨76248909801143660801650619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203330426136383095471068317 76248909801143660801650619)
    ·
      refine ⟨114373364701715491202475929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76248909801143660801650619 114373364701715491202475929)
      ·
        refine ⟨85780023526286618401856947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114373364701715491202475929 85780023526286618401856947)
        ·
          refine ⟨128670035289429927602785421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85780023526286618401856947 128670035289429927602785421)
          ·
            refine ⟨48251263233536222851044533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128670035289429927602785421 48251263233536222851044533)
            ·
              refine ⟨4523555928144020892285425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48251263233536222851044533 4523555928144020892285425)
              ·
                refine ⟨3392666946108015669214069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523555928144020892285425 3392666946108015669214069)
                ·
                  refine ⟨318062526197626468988819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3392666946108015669214069 318062526197626468988819)
                  ·
                    rfl

theorem cell23_5574821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_5574821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574821 prefixEnd_5574821 := by exact prefixLift 5574821
  have htrace : WordTrace (prefixWord ++ tailWord_5574821) baseStart_5574821 baseEnd_5574821 := by
    simpa [prefixWord, tailWord_5574821, baseEnd_5574821] using wordTrace_append hprefix tailTrace_5574821
  have hstable : (prefixWord ++ tailWord_5574821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574821).length < 2 ^ (prefixWord ++ tailWord_5574821).sum := by decide
  have hdescent : baseEnd_5574821 < baseStart_5574821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574836 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5574836 : Nat := 118140960795 + 5574836 * 2 ^ 59
def prefixEnd_5574836 : Nat := 4983230072969 + 3 ^ 40 * 5574836 * 2
def baseEnd_5574836 : Nat := 2862570437988455662211803

theorem tailTrace_5574836 : CollatzResearch.WordTrace tailWord_5574836 prefixEnd_5574836 2862570437988455662211803 := by
  unfold tailWord_5574836
  simp only [CollatzResearch.WordTrace]
  refine ⟨101665486615664376516432181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135553982154219168688576241 101665486615664376516432181)
  ·
    refine ⟨9531139370218535298415517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101665486615664376516432181 9531139370218535298415517)
    ·
      refine ⟨3574177263831950736905819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9531139370218535298415517 3574177263831950736905819)
      ·
        refine ⟨5361265895747926105358729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574177263831950736905819 5361265895747926105358729)
        ·
          refine ⟨4020949421810944579019047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5361265895747926105358729 4020949421810944579019047)
          ·
            refine ⟨6031424132716416868528571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020949421810944579019047 6031424132716416868528571)
            ·
              refine ⟨9047136199074625302792857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031424132716416868528571 9047136199074625302792857)
              ·
                refine ⟨6785352149305968977094643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9047136199074625302792857 6785352149305968977094643)
                ·
                  refine ⟨10178028223958953465641965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6785352149305968977094643 10178028223958953465641965)
                  ·
                    refine ⟨3816760583984607549615737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10178028223958953465641965 3816760583984607549615737)
                    ·
                      refine ⟨2862570437988455662211803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816760583984607549615737 2862570437988455662211803)
                      ·
                        rfl

theorem cell23_5574836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5574836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574836 prefixEnd_5574836 := by exact prefixLift 5574836
  have htrace : WordTrace (prefixWord ++ tailWord_5574836) baseStart_5574836 baseEnd_5574836 := by
    simpa [prefixWord, tailWord_5574836, baseEnd_5574836] using wordTrace_append hprefix tailTrace_5574836
  have hstable : (prefixWord ++ tailWord_5574836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574836).length < 2 ^ (prefixWord ++ tailWord_5574836).sum := by decide
  have hdescent : baseEnd_5574836 < baseStart_5574836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574908 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_5574908 : Nat := 118140960795 + 5574908 * 2 ^ 59
def prefixEnd_5574908 : Nat := 4983230072969 + 3 ^ 40 * 5574908 * 2
def baseEnd_5574908 : Nat := 2862607408595579380511471

theorem tailTrace_5574908 : CollatzResearch.WordTrace tailWord_5574908 prefixEnd_5574908 2862607408595579380511471 := by
  unfold tailWord_5574908
  simp only [CollatzResearch.WordTrace]
  refine ⟨101666799643533954664742689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135555732858045272886323585 101666799643533954664742689)
  ·
    refine ⟨76250099732650465998557017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101666799643533954664742689 76250099732650465998557017)
    ·
      refine ⟨57187574799487849498917763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76250099732650465998557017 57187574799487849498917763)
      ·
        refine ⟨85781362199231774248376645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57187574799487849498917763 85781362199231774248376645)
        ·
          refine ⟨16084005412355957671570621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85781362199231774248376645 16084005412355957671570621)
          ·
            refine ⟨6031502029633484126838983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16084005412355957671570621 6031502029633484126838983)
            ·
              refine ⟨9047253044450226190258475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031502029633484126838983 9047253044450226190258475)
              ·
                refine ⟨13570879566675339285387713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9047253044450226190258475 13570879566675339285387713)
                ·
                  refine ⟨10178159675006504464040785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13570879566675339285387713 10178159675006504464040785)
                  ·
                    refine ⟨7633619756254878348030589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10178159675006504464040785 7633619756254878348030589)
                    ·
                      refine ⟨2862607408595579380511471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7633619756254878348030589 2862607408595579380511471)
                      ·
                        rfl

theorem cell23_5574908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_5574908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574908 prefixEnd_5574908 := by exact prefixLift 5574908
  have htrace : WordTrace (prefixWord ++ tailWord_5574908) baseStart_5574908 baseEnd_5574908 := by
    simpa [prefixWord, tailWord_5574908, baseEnd_5574908] using wordTrace_append hprefix tailTrace_5574908
  have hstable : (prefixWord ++ tailWord_5574908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574908).length < 2 ^ (prefixWord ++ tailWord_5574908).sum := by decide
  have hdescent : baseEnd_5574908 < baseStart_5574908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574931 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 2, 3, 2]
def baseStart_5574931 : Nat := 118140960795 + 5574931 * 2 ^ 59
def prefixEnd_5574931 : Nat := 4983230072969 + 3 ^ 40 * 5574931 * 2
def baseEnd_5574931 : Nat := 2862619218650632790523865

theorem tailTrace_5574931 : CollatzResearch.WordTrace tailWord_5574931 prefixEnd_5574931 2862619218650632790523865 := by
  unfold tailWord_5574931
  simp only [CollatzResearch.WordTrace]
  refine ⟨203334438165984584257572647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135556292110656389505048431 203334438165984584257572647)
  ·
    refine ⟨305001657248976876386358971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203334438165984584257572647 305001657248976876386358971)
    ·
      refine ⟨457502485873465314579538457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305001657248976876386358971 457502485873465314579538457)
      ·
        refine ⟨343126864405098985934653843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457502485873465314579538457 343126864405098985934653843)
        ·
          refine ⟨514690296607648478901980765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343126864405098985934653843 514690296607648478901980765)
          ·
            refine ⟨193008861227868179588242787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514690296607648478901980765 193008861227868179588242787)
            ·
              refine ⟨289513291841802269382364181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193008861227868179588242787 289513291841802269382364181)
              ·
                refine ⟨13570935555084481377298321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 289513291841802269382364181 13570935555084481377298321)
                ·
                  refine ⟨10178201666313361032973741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13570935555084481377298321 10178201666313361032973741)
                  ·
                    refine ⟨3816825624867510387365153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10178201666313361032973741 3816825624867510387365153)
                    ·
                      refine ⟨2862619218650632790523865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816825624867510387365153 2862619218650632790523865)
                      ·
                        rfl

theorem cell23_5574931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3, 2].length) (baseStart_5574931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574931 prefixEnd_5574931 := by exact prefixLift 5574931
  have htrace : WordTrace (prefixWord ++ tailWord_5574931) baseStart_5574931 baseEnd_5574931 := by
    simpa [prefixWord, tailWord_5574931, baseEnd_5574931] using wordTrace_append hprefix tailTrace_5574931
  have hstable : (prefixWord ++ tailWord_5574931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574931).length < 2 ^ (prefixWord ++ tailWord_5574931).sum := by decide
  have hdescent : baseEnd_5574931 < baseStart_5574931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5574937 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 12]
def baseStart_5574937 : Nat := 118140960795 + 5574937 * 2 ^ 59
def prefixEnd_5574937 : Nat := 4983230072969 + 3 ^ 40 * 5574937 * 2
def baseEnd_5574937 : Nat := 954207433178186589016279

theorem tailTrace_5574937 : CollatzResearch.WordTrace tailWord_5574937 prefixEnd_5574937 954207433178186589016279 := by
  unfold tailWord_5574937
  simp only [CollatzResearch.WordTrace]
  refine ⟨203334657003962847282291065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135556438002641898188194043 203334657003962847282291065)
  ·
    refine ⟨152500992752972135461718299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203334657003962847282291065 152500992752972135461718299)
    ·
      refine ⟨228751489129458203192577449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152500992752972135461718299 228751489129458203192577449)
      ·
        refine ⟨171563616847093652394433087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228751489129458203192577449 171563616847093652394433087)
        ·
          refine ⟨257345425270640478591649631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171563616847093652394433087 257345425270640478591649631)
          ·
            refine ⟨386018137905960717887474447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257345425270640478591649631 386018137905960717887474447)
            ·
              refine ⟨579027206858941076831211671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386018137905960717887474447 579027206858941076831211671)
              ·
                refine ⟨868540810288411615246817507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579027206858941076831211671 868540810288411615246817507)
                ·
                  refine ⟨1302811215432617422870226261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868540810288411615246817507 1302811215432617422870226261)
                  ·
                    refine ⟨954207433178186589016279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1302811215432617422870226261 954207433178186589016279)
                    ·
                      rfl

theorem cell23_5574937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_5574937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5574937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5574937 prefixEnd_5574937 := by exact prefixLift 5574937
  have htrace : WordTrace (prefixWord ++ tailWord_5574937) baseStart_5574937 baseEnd_5574937 := by
    simpa [prefixWord, tailWord_5574937, baseEnd_5574937] using wordTrace_append hprefix tailTrace_5574937
  have hstable : (prefixWord ++ tailWord_5574937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5574937).length < 2 ^ (prefixWord ++ tailWord_5574937).sum := by decide
  have hdescent : baseEnd_5574937 < baseStart_5574937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5574937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575011 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 3]
def baseStart_5575011 : Nat := 118140960795 + 5575011 * 2 ^ 59
def prefixEnd_5575011 : Nat := 4983230072969 + 3 ^ 40 * 5575011 * 2
def baseEnd_5575011 : Nat := 2862660297102992477523497

theorem tailTrace_5575011 : CollatzResearch.WordTrace tailWord_5575011 prefixEnd_5575011 2862660297102992477523497 := by
  unfold tailWord_5575011
  simp only [CollatzResearch.WordTrace]
  refine ⟨203337356005694757920484887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135558237337129838613656591 203337356005694757920484887)
  ·
    refine ⟨305006034008542136880727331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203337356005694757920484887 305006034008542136880727331)
    ·
      refine ⟨457509051012813205321090997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305006034008542136880727331 457509051012813205321090997)
      ·
        refine ⟨42891473532451237998852281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 457509051012813205321090997 42891473532451237998852281)
        ·
          refine ⟨32168605149338428499139211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42891473532451237998852281 32168605149338428499139211)
          ·
            refine ⟨48252907724007642748708817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32168605149338428499139211 48252907724007642748708817)
            ·
              refine ⟨36189680793005732061531613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48252907724007642748708817 36189680793005732061531613)
              ·
                refine ⟨13571130297377149523074355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36189680793005732061531613 13571130297377149523074355)
                ·
                  refine ⟨20356695446065724284611533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13571130297377149523074355 20356695446065724284611533)
                  ·
                    refine ⟨7633760792274646606729325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20356695446065724284611533 7633760792274646606729325)
                    ·
                      refine ⟨2862660297102992477523497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7633760792274646606729325 2862660297102992477523497)
                      ·
                        rfl

theorem cell23_5575011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_5575011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575011 prefixEnd_5575011 := by exact prefixLift 5575011
  have htrace : WordTrace (prefixWord ++ tailWord_5575011) baseStart_5575011 baseEnd_5575011 := by
    simpa [prefixWord, tailWord_5575011, baseEnd_5575011] using wordTrace_append hprefix tailTrace_5575011
  have hstable : (prefixWord ++ tailWord_5575011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575011).length < 2 ^ (prefixWord ++ tailWord_5575011).sum := by decide
  have hdescent : baseEnd_5575011 < baseStart_5575011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575015 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_5575015 : Nat := 118140960795 + 5575015 * 2 ^ 59
def prefixEnd_5575015 : Nat := 4983230072969 + 3 ^ 40 * 5575015 * 2
def baseEnd_5575015 : Nat := 2862662351025610461873479

theorem tailTrace_5575015 : CollatzResearch.WordTrace tailWord_5575015 prefixEnd_5575015 2862662351025610461873479 := by
  unfold tailWord_5575015
  simp only [CollatzResearch.WordTrace]
  refine ⟨203337501897680266603630499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135558334598453511069086999 203337501897680266603630499)
  ·
    refine ⟨305006252846520399905445749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203337501897680266603630499 305006252846520399905445749)
    ·
      refine ⟨28594336204361287491135539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 305006252846520399905445749 28594336204361287491135539)
      ·
        refine ⟨42891504306541931236703309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28594336204361287491135539 42891504306541931236703309)
        ·
          refine ⟨16084314114953224213763741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42891504306541931236703309 16084314114953224213763741)
          ·
            refine ⟨6031617793107459080161403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16084314114953224213763741 6031617793107459080161403)
            ·
              refine ⟨9047426689661188620242105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031617793107459080161403 9047426689661188620242105)
              ·
                refine ⟨6785570017245891465181579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9047426689661188620242105 6785570017245891465181579)
                ·
                  refine ⟨10178355025868837197772369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6785570017245891465181579 10178355025868837197772369)
                  ·
                    refine ⟨7633766269401627898329277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10178355025868837197772369 7633766269401627898329277)
                    ·
                      refine ⟨2862662351025610461873479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7633766269401627898329277 2862662351025610461873479)
                      ·
                        rfl

theorem cell23_5575015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_5575015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575015 prefixEnd_5575015 := by exact prefixLift 5575015
  have htrace : WordTrace (prefixWord ++ tailWord_5575015) baseStart_5575015 baseEnd_5575015 := by
    simpa [prefixWord, tailWord_5575015, baseEnd_5575015] using wordTrace_append hprefix tailTrace_5575015
  have hstable : (prefixWord ++ tailWord_5575015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575015).length < 2 ^ (prefixWord ++ tailWord_5575015).sum := by decide
  have hdescent : baseEnd_5575015 < baseStart_5575015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575034 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_5575034 : Nat := 118140960795 + 5575034 * 2 ^ 59
def prefixEnd_5575034 : Nat := 4983230072969 + 3 ^ 40 * 5575034 * 2
def baseEnd_5575034 : Nat := 2862672107158045887535891

theorem tailTrace_5575034 : CollatzResearch.WordTrace tailWord_5575034 prefixEnd_5575034 2862672107158045887535891 := by
  unfold tailWord_5575034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50834548721152858212143039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135558796589740955232381437 50834548721152858212143039)
  ·
    refine ⟨76251823081729287318214559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50834548721152858212143039 76251823081729287318214559)
    ·
      refine ⟨114377734622593930977321839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76251823081729287318214559 114377734622593930977321839)
      ·
        refine ⟨171566601933890896465982759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114377734622593930977321839 171566601933890896465982759)
        ·
          refine ⟨257349902900836344698974139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171566601933890896465982759 257349902900836344698974139)
          ·
            refine ⟨386024854351254517048461209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257349902900836344698974139 386024854351254517048461209)
            ·
              refine ⟨289518640763440887786345907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386024854351254517048461209 289518640763440887786345907)
              ·
                refine ⟨434277961145161331679518861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289518640763440887786345907 434277961145161331679518861)
                ·
                  refine ⟨162854235429435499379819573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434277961145161331679518861 162854235429435499379819573)
                  ·
                    refine ⟨15267584571509578066858085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162854235429435499379819573 15267584571509578066858085)
                    ·
                      refine ⟨2862672107158045887535891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15267584571509578066858085 2862672107158045887535891)
                      ·
                        rfl

theorem cell23_5575034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_5575034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575034 prefixEnd_5575034 := by exact prefixLift 5575034
  have htrace : WordTrace (prefixWord ++ tailWord_5575034) baseStart_5575034 baseEnd_5575034 := by
    simpa [prefixWord, tailWord_5575034, baseEnd_5575034] using wordTrace_append hprefix tailTrace_5575034
  have hstable : (prefixWord ++ tailWord_5575034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575034).length < 2 ^ (prefixWord ++ tailWord_5575034).sum := by decide
  have hdescent : baseEnd_5575034 < baseStart_5575034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575071 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 3]
def baseStart_5575071 : Nat := 118140960795 + 5575071 * 2 ^ 59
def prefixEnd_5575071 : Nat := 4983230072969 + 3 ^ 40 * 5575071 * 2
def baseEnd_5575071 : Nat := 2862691105942262242773221

theorem tailTrace_5575071 : CollatzResearch.WordTrace tailWord_5575071 prefixEnd_5575071 2862691105942262242773221 := by
  unfold tailWord_5575071
  simp only [CollatzResearch.WordTrace]
  refine ⟨203339544385477388167669067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135559696256984925445112711 203339544385477388167669067)
  ·
    refine ⟨305009316578216082251503601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203339544385477388167669067 305009316578216082251503601)
    ·
      refine ⟨228756987433662061688627701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305009316578216082251503601 228756987433662061688627701)
      ·
        refine ⟨21445967571905818283308847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228756987433662061688627701 21445967571905818283308847)
        ·
          refine ⟨32168951357858727424963271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21445967571905818283308847 32168951357858727424963271)
          ·
            refine ⟨48253427036788091137444907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32168951357858727424963271 48253427036788091137444907)
            ·
              refine ⟨72380140555182136706167361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48253427036788091137444907 72380140555182136706167361)
              ·
                refine ⟨54285105416386602529625521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72380140555182136706167361 54285105416386602529625521)
                ·
                  refine ⟨40713829062289951897219141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54285105416386602529625521 40713829062289951897219141)
                  ·
                    refine ⟨7633842949179365980728589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40713829062289951897219141 7633842949179365980728589)
                    ·
                      refine ⟨2862691105942262242773221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7633842949179365980728589 2862691105942262242773221)
                      ·
                        rfl

theorem cell23_5575071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_5575071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575071 prefixEnd_5575071 := by exact prefixLift 5575071
  have htrace : WordTrace (prefixWord ++ tailWord_5575071) baseStart_5575071 baseEnd_5575071 := by
    simpa [prefixWord, tailWord_5575071, baseEnd_5575071] using wordTrace_append hprefix tailTrace_5575071
  have hstable : (prefixWord ++ tailWord_5575071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575071).length < 2 ^ (prefixWord ++ tailWord_5575071).sum := by decide
  have hdescent : baseEnd_5575071 < baseStart_5575071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575084 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_5575084 : Nat := 118140960795 + 5575084 * 2 ^ 59
def prefixEnd_5575084 : Nat := 4983230072969 + 3 ^ 40 * 5575084 * 2
def baseEnd_5575084 : Nat := 2862697781190770691910661

theorem tailTrace_5575084 : CollatzResearch.WordTrace tailWord_5575084 prefixEnd_5575084 2862697781190770691910661 := by
  unfold tailWord_5575084
  simp only [CollatzResearch.WordTrace]
  refine ⟨101670009267215145693946153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135560012356286860925261537 101670009267215145693946153)
  ·
    refine ⟨76252506950411359270459615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101670009267215145693946153 76252506950411359270459615)
    ·
      refine ⟨114378760425617038905689423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76252506950411359270459615 114378760425617038905689423)
      ·
        refine ⟨171568140638425558358534135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114378760425617038905689423 171568140638425558358534135)
        ·
          refine ⟨257352210957638337537801203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171568140638425558358534135 257352210957638337537801203)
          ·
            refine ⟨386028316436457506306701805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257352210957638337537801203 386028316436457506306701805)
            ·
              refine ⟨144760618663671564865013177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386028316436457506306701805 144760618663671564865013177)
              ·
                refine ⟨108570463997753673648759883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144760618663671564865013177 108570463997753673648759883)
                ·
                  refine ⟨162855695996630510473139825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108570463997753673648759883 162855695996630510473139825)
                  ·
                    refine ⟨122141771997472882854854869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 162855695996630510473139825 122141771997472882854854869)
                    ·
                      refine ⟨2862697781190770691910661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122141771997472882854854869 2862697781190770691910661)
                      ·
                        rfl

theorem cell23_5575084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_5575084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575084 prefixEnd_5575084 := by exact prefixLift 5575084
  have htrace : WordTrace (prefixWord ++ tailWord_5575084) baseStart_5575084 baseEnd_5575084 := by
    simpa [prefixWord, tailWord_5575084, baseEnd_5575084] using wordTrace_append hprefix tailTrace_5575084
  have hstable : (prefixWord ++ tailWord_5575084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575084).length < 2 ^ (prefixWord ++ tailWord_5575084).sum := by decide
  have hdescent : baseEnd_5575084 < baseStart_5575084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575102 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_5575102 : Nat := 118140960795 + 5575102 * 2 ^ 59
def prefixEnd_5575102 : Nat := 4983230072969 + 3 ^ 40 * 5575102 * 2
def baseEnd_5575102 : Nat := 2862707023842551621485579

theorem tailTrace_5575102 : CollatzResearch.WordTrace tailWord_5575102 prefixEnd_5575102 2862707023842551621485579 := by
  unfold tailWord_5575102
  simp only [CollatzResearch.WordTrace]
  refine ⟨25417584381045635057755945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135560450032243386974698373 25417584381045635057755945)
  ·
    refine ⟨19063188285784226293316959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25417584381045635057755945 19063188285784226293316959)
    ·
      refine ⟨28594782428676339439975439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19063188285784226293316959 28594782428676339439975439)
      ·
        refine ⟨42892173643014509159963159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28594782428676339439975439 42892173643014509159963159)
        ·
          refine ⟨64338260464521763739944739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42892173643014509159963159 64338260464521763739944739)
          ·
            refine ⟨96507390696782645609917109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64338260464521763739944739 96507390696782645609917109)
            ·
              refine ⟨9047567877823373025929729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96507390696782645609917109 9047567877823373025929729)
              ·
                refine ⟨6785675908367529769447297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9047567877823373025929729 6785675908367529769447297)
                ·
                  refine ⟨5089256931275647327085473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6785675908367529769447297 5089256931275647327085473)
                  ·
                    refine ⟨3816942698456735495314105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5089256931275647327085473 3816942698456735495314105)
                    ·
                      refine ⟨2862707023842551621485579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3816942698456735495314105 2862707023842551621485579)
                      ·
                        rfl

theorem cell23_5575102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_5575102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575102 prefixEnd_5575102 := by exact prefixLift 5575102
  have htrace : WordTrace (prefixWord ++ tailWord_5575102) baseStart_5575102 baseEnd_5575102 := by
    simpa [prefixWord, tailWord_5575102, baseEnd_5575102] using wordTrace_append hprefix tailTrace_5575102
  have hstable : (prefixWord ++ tailWord_5575102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575102).length < 2 ^ (prefixWord ++ tailWord_5575102).sum := by decide
  have hdescent : baseEnd_5575102 < baseStart_5575102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575178 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_5575178 : Nat := 118140960795 + 5575178 * 2 ^ 59
def prefixEnd_5575178 : Nat := 4983230072969 + 3 ^ 40 * 5575178 * 2
def baseEnd_5575178 : Nat := 2862746048372293324135229

theorem tailTrace_5575178 : CollatzResearch.WordTrace tailWord_5575178 prefixEnd_5575178 2862746048372293324135229 := by
  unfold tailWord_5575178
  simp only [CollatzResearch.WordTrace]
  refine ⟨50835861749022436360453547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135562297997393163627876125 50835861749022436360453547)
  ·
    refine ⟨76253792623533654540680321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50835861749022436360453547 76253792623533654540680321)
    ·
      refine ⟨57190344467650240905510241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76253792623533654540680321 57190344467650240905510241)
      ·
        refine ⟨42892758350737680679132681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57190344467650240905510241 42892758350737680679132681)
        ·
          refine ⟨32169568763053260509349511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42892758350737680679132681 32169568763053260509349511)
          ·
            refine ⟨48254353144579890764024267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32169568763053260509349511 48254353144579890764024267)
            ·
              refine ⟨72381529716869836146036401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48254353144579890764024267 72381529716869836146036401)
              ·
                refine ⟨54286147287652377109527301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72381529716869836146036401 54286147287652377109527301)
                ·
                  refine ⟨10178652616434820708036369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54286147287652377109527301 10178652616434820708036369)
                  ·
                    refine ⟨7633989462326115531027277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10178652616434820708036369 7633989462326115531027277)
                    ·
                      refine ⟨2862746048372293324135229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7633989462326115531027277 2862746048372293324135229)
                      ·
                        rfl

theorem cell23_5575178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_5575178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575178 prefixEnd_5575178 := by exact prefixLift 5575178
  have htrace : WordTrace (prefixWord ++ tailWord_5575178) baseStart_5575178 baseEnd_5575178 := by
    simpa [prefixWord, tailWord_5575178, baseEnd_5575178] using wordTrace_append hprefix tailTrace_5575178
  have hstable : (prefixWord ++ tailWord_5575178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575178).length < 2 ^ (prefixWord ++ tailWord_5575178).sum := by decide
  have hdescent : baseEnd_5575178 < baseStart_5575178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575225 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 3]
def baseStart_5575225 : Nat := 118140960795 + 5575225 * 2 ^ 59
def prefixEnd_5575225 : Nat := 4983230072969 + 3 ^ 40 * 5575225 * 2
def baseEnd_5575225 : Nat := 2862770181963054640247513

theorem tailTrace_5575225 : CollatzResearch.WordTrace tailWord_5575225 prefixEnd_5575225 2862770181963054640247513 := by
  unfold tailWord_5575225
  simp only [CollatzResearch.WordTrace]
  refine ⟨203345161226919472468775129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135563440817946314979183419 203345161226919472468775129)
  ·
    refine ⟨152508870920189604351581347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203345161226919472468775129 152508870920189604351581347)
    ·
      refine ⟨228763306380284406527372021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152508870920189604351581347 228763306380284406527372021)
      ·
        refine ⟨21446559973151663111941127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228763306380284406527372021 21446559973151663111941127)
        ·
          refine ⟨32169839959727494667911691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21446559973151663111941127 32169839959727494667911691)
          ·
            refine ⟨48254759939591242001867537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32169839959727494667911691 48254759939591242001867537)
            ·
              refine ⟨36191069954693431501400653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48254759939591242001867537 36191069954693431501400653)
              ·
                refine ⟨13571651233010036813025245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36191069954693431501400653 13571651233010036813025245)
                ·
                  refine ⟨5089369212378763804884467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13571651233010036813025245 5089369212378763804884467)
                  ·
                    refine ⟨7634053818568145707326701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5089369212378763804884467 7634053818568145707326701)
                    ·
                      refine ⟨2862770181963054640247513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634053818568145707326701 2862770181963054640247513)
                      ·
                        rfl

theorem cell23_5575225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_5575225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575225 prefixEnd_5575225 := by exact prefixLift 5575225
  have htrace : WordTrace (prefixWord ++ tailWord_5575225) baseStart_5575225 baseEnd_5575225 := by
    simpa [prefixWord, tailWord_5575225, baseEnd_5575225] using wordTrace_append hprefix tailTrace_5575225
  have hstable : (prefixWord ++ tailWord_5575225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575225).length < 2 ^ (prefixWord ++ tailWord_5575225).sum := by decide
  have hdescent : baseEnd_5575225 < baseStart_5575225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575228 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_5575228 : Nat := 118140960795 + 5575228 * 2 ^ 59
def prefixEnd_5575228 : Nat := 4983230072969 + 3 ^ 40 * 5575228 * 2
def baseEnd_5575228 : Nat := 954257240801672709503333

theorem tailTrace_5575228 : CollatzResearch.WordTrace tailWord_5575228 prefixEnd_5575228 954257240801672709503333 := by
  unfold tailWord_5575228
  simp only [CollatzResearch.WordTrace]
  refine ⟨101672635322954301990567169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135563513763939069320756225 101672635322954301990567169)
  ·
    refine ⟨76254476492215726492925377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101672635322954301990567169 76254476492215726492925377)
    ·
      refine ⟨57190857369161794869694033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76254476492215726492925377 57190857369161794869694033)
      ·
        refine ⟨42893143026871346152270525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57190857369161794869694033 42893143026871346152270525)
        ·
          refine ⟨16084928635076754807101447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42893143026871346152270525 16084928635076754807101447)
          ·
            refine ⟨24127392952615132210652171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16084928635076754807101447 24127392952615132210652171)
            ·
              refine ⟨36191089428922698315978257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24127392952615132210652171 36191089428922698315978257)
              ·
                refine ⟨27143317071692023736983693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36191089428922698315978257 27143317071692023736983693)
                ·
                  refine ⟨10178743901884508901368885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27143317071692023736983693 10178743901884508901368885)
                  ·
                    refine ⟨954257240801672709503333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10178743901884508901368885 954257240801672709503333)
                    ·
                      rfl

theorem cell23_5575228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_5575228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575228 prefixEnd_5575228 := by exact prefixLift 5575228
  have htrace : WordTrace (prefixWord ++ tailWord_5575228) baseStart_5575228 baseEnd_5575228 := by
    simpa [prefixWord, tailWord_5575228, baseEnd_5575228] using wordTrace_append hprefix tailTrace_5575228
  have hstable : (prefixWord ++ tailWord_5575228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575228).length < 2 ^ (prefixWord ++ tailWord_5575228).sum := by decide
  have hdescent : baseEnd_5575228 < baseStart_5575228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575245 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5575245 : Nat := 118140960795 + 5575245 * 2 ^ 59
def prefixEnd_5575245 : Nat := 4983230072969 + 3 ^ 40 * 5575245 * 2
def baseEnd_5575245 : Nat := 954260150525381520665807

theorem tailTrace_5575245 : CollatzResearch.WordTrace tailWord_5575245 prefixEnd_5575245 954260150525381520665807 := by
  unfold tailWord_5575245
  simp only [CollatzResearch.WordTrace]
  refine ⟨203345890686847015884503189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135563927124564677256335459 203345890686847015884503189)
  ·
    refine ⟨9531838625945953869586087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203345890686847015884503189 9531838625945953869586087)
    ·
      refine ⟨14297757938918930804379131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9531838625945953869586087 14297757938918930804379131)
      ·
        refine ⟨21446636908378396206568697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14297757938918930804379131 21446636908378396206568697)
        ·
          refine ⟨16084977681283797154926523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21446636908378396206568697 16084977681283797154926523)
          ·
            refine ⟨24127466521925695732389785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16084977681283797154926523 24127466521925695732389785)
            ·
              refine ⟨18095599891444271799292339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24127466521925695732389785 18095599891444271799292339)
              ·
                refine ⟨27143399837166407698938509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18095599891444271799292339 27143399837166407698938509)
                ·
                  refine ⟨10178774938937402887101941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27143399837166407698938509 10178774938937402887101941)
                  ·
                    refine ⟨954260150525381520665807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10178774938937402887101941 954260150525381520665807)
                    ·
                      rfl

theorem cell23_5575245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5575245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575245 prefixEnd_5575245 := by exact prefixLift 5575245
  have htrace : WordTrace (prefixWord ++ tailWord_5575245) baseStart_5575245 baseEnd_5575245 := by
    simpa [prefixWord, tailWord_5575245, baseEnd_5575245] using wordTrace_append hprefix tailTrace_5575245
  have hstable : (prefixWord ++ tailWord_5575245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575245).length < 2 ^ (prefixWord ++ tailWord_5575245).sum := by decide
  have hdescent : baseEnd_5575245 < baseStart_5575245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575248 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 8, 2]
def baseStart_5575248 : Nat := 118140960795 + 5575248 * 2 ^ 59
def prefixEnd_5575248 : Nat := 4983230072969 + 3 ^ 40 * 5575248 * 2
def baseEnd_5575248 : Nat := 2862781992018108050259907

theorem tailTrace_5575248 : CollatzResearch.WordTrace tailWord_5575248 prefixEnd_5575248 2862781992018108050259907 := by
  unfold tailWord_5575248
  simp only [CollatzResearch.WordTrace]
  refine ⟨101673000052918073698431199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135564000070557431597908265 101673000052918073698431199)
  ·
    refine ⟨152509500079377110547646799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101673000052918073698431199 152509500079377110547646799)
    ·
      refine ⟨228764250119065665821470199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152509500079377110547646799 228764250119065665821470199)
      ·
        refine ⟨343146375178598498732205299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228764250119065665821470199 343146375178598498732205299)
        ·
          refine ⟨514719562767897748098307949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343146375178598498732205299 514719562767897748098307949)
          ·
            refine ⟨193019836037961655536865481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514719562767897748098307949 193019836037961655536865481)
            ·
              refine ⟨144764877028471241652649111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193019836037961655536865481 144764877028471241652649111)
              ·
                refine ⟨217147315542706862478973667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144764877028471241652649111 217147315542706862478973667)
                ·
                  refine ⟨325720973314060293718460501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217147315542706862478973667 325720973314060293718460501)
                  ·
                    refine ⟨3817042656024144067013209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 325720973314060293718460501 3817042656024144067013209)
                    ·
                      refine ⟨2862781992018108050259907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817042656024144067013209 2862781992018108050259907)
                      ·
                        rfl

theorem cell23_5575248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 8, 2].length) (baseStart_5575248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575248 prefixEnd_5575248 := by exact prefixLift 5575248
  have htrace : WordTrace (prefixWord ++ tailWord_5575248) baseStart_5575248 baseEnd_5575248 := by
    simpa [prefixWord, tailWord_5575248, baseEnd_5575248] using wordTrace_append hprefix tailTrace_5575248
  have hstable : (prefixWord ++ tailWord_5575248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575248).length < 2 ^ (prefixWord ++ tailWord_5575248).sum := by decide
  have hdescent : baseEnd_5575248 < baseStart_5575248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575252 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_5575252 : Nat := 118140960795 + 5575252 * 2 ^ 59
def prefixEnd_5575252 : Nat := 4983230072969 + 3 ^ 40 * 5575252 * 2
def baseEnd_5575252 : Nat := 2862784045940726034609889

theorem tailTrace_5575252 : CollatzResearch.WordTrace tailWord_5575252 prefixEnd_5575252 2862784045940726034609889 := by
  unfold tailWord_5575252
  simp only [CollatzResearch.WordTrace]
  refine ⟨101673072998910828040004005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135564097331881104053338673 101673072998910828040004005)
  ·
    refine ⟨19063701187295780257500751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101673072998910828040004005 19063701187295780257500751)
    ·
      refine ⟨28595551780943670386251127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19063701187295780257500751 28595551780943670386251127)
      ·
        refine ⟨42893327671415505579376691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28595551780943670386251127 42893327671415505579376691)
        ·
          refine ⟨64339991507123258369065037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42893327671415505579376691 64339991507123258369065037)
          ·
            refine ⟨24127496815171221888399389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64339991507123258369065037 24127496815171221888399389)
            ·
              refine ⟨9047811305689208208149771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24127496815171221888399389 9047811305689208208149771)
              ·
                refine ⟨13571716958533812312224657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9047811305689208208149771 13571716958533812312224657)
                ·
                  refine ⟨10178787718900359234168493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13571716958533812312224657 10178787718900359234168493)
                  ·
                    refine ⟨3817045394587634712813185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10178787718900359234168493 3817045394587634712813185)
                    ·
                      refine ⟨2862784045940726034609889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817045394587634712813185 2862784045940726034609889)
                      ·
                        rfl

theorem cell23_5575252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_5575252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575252 prefixEnd_5575252 := by exact prefixLift 5575252
  have htrace : WordTrace (prefixWord ++ tailWord_5575252) baseStart_5575252 baseEnd_5575252 := by
    simpa [prefixWord, tailWord_5575252, baseEnd_5575252] using wordTrace_append hprefix tailTrace_5575252
  have hstable : (prefixWord ++ tailWord_5575252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575252).length < 2 ^ (prefixWord ++ tailWord_5575252).sum := by decide
  have hdescent : baseEnd_5575252 < baseStart_5575252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575265 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_5575265 : Nat := 118140960795 + 5575265 * 2 ^ 59
def prefixEnd_5575265 : Nat := 4983230072969 + 3 ^ 40 * 5575265 * 2
def baseEnd_5575265 : Nat := 2862790721189234483747329

theorem tailTrace_5575265 : CollatzResearch.WordTrace tailWord_5575265 prefixEnd_5575265 2862790721189234483747329 := by
  unfold tailWord_5575265
  simp only [CollatzResearch.WordTrace]
  refine ⟨203346620146774559300231249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135564413431183039533487499 203346620146774559300231249)
  ·
    refine ⟨152509965110080919475173437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203346620146774559300231249 152509965110080919475173437)
    ·
      refine ⟨57191236916280344803190039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152509965110080919475173437 57191236916280344803190039)
      ·
        refine ⟨85786855374420517204785059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57191236916280344803190039 85786855374420517204785059)
        ·
          refine ⟨128680283061630775807177589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85786855374420517204785059 128680283061630775807177589)
          ·
            refine ⟨12063776537027885231922899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128680283061630775807177589 12063776537027885231922899)
            ·
              refine ⟨18095664805541827847884349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12063776537027885231922899 18095664805541827847884349)
              ·
                refine ⟨6785874302078185442956631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18095664805541827847884349 6785874302078185442956631)
                ·
                  refine ⟨10178811453117278164434947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6785874302078185442956631 10178811453117278164434947)
                  ·
                    refine ⟨15268217179675917246652421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10178811453117278164434947 15268217179675917246652421)
                    ·
                      refine ⟨2862790721189234483747329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15268217179675917246652421 2862790721189234483747329)
                      ·
                        rfl

theorem cell23_5575265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_5575265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575265 prefixEnd_5575265 := by exact prefixLift 5575265
  have htrace : WordTrace (prefixWord ++ tailWord_5575265) baseStart_5575265 baseEnd_5575265 := by
    simpa [prefixWord, tailWord_5575265, baseEnd_5575265] using wordTrace_append hprefix tailTrace_5575265
  have hstable : (prefixWord ++ tailWord_5575265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575265).length < 2 ^ (prefixWord ++ tailWord_5575265).sum := by decide
  have hdescent : baseEnd_5575265 < baseStart_5575265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575268 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_5575268 : Nat := 118140960795 + 5575268 * 2 ^ 59
def prefixEnd_5575268 : Nat := 4983230072969 + 3 ^ 40 * 5575268 * 2
def baseEnd_5575268 : Nat := 2862792261631197972009815

theorem tailTrace_5575268 : CollatzResearch.WordTrace tailWord_5575268 prefixEnd_5575268 2862792261631197972009815 := by
  unfold tailWord_5575268
  simp only [CollatzResearch.WordTrace]
  refine ⟨101673364782881845406295229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135564486377175793875060305 101673364782881845406295229)
  ·
    refine ⟨38127511793580692027360711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101673364782881845406295229 38127511793580692027360711)
    ·
      refine ⟨57191267690371038041041067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38127511793580692027360711 57191267690371038041041067)
      ·
        refine ⟨85786901535556557061561601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57191267690371038041041067 85786901535556557061561601)
        ·
          refine ⟨64340176151667417796171201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85786901535556557061561601 64340176151667417796171201)
          ·
            refine ⟨48255132113750563347128401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64340176151667417796171201 48255132113750563347128401)
            ·
              refine ⟨36191349085312922510346301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48255132113750563347128401 36191349085312922510346301)
              ·
                refine ⟨13571755906992345941379863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36191349085312922510346301 13571755906992345941379863)
                ·
                  refine ⟨20357633860488518912069795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13571755906992345941379863 20357633860488518912069795)
                  ·
                    refine ⟨30536450790732778368104693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20357633860488518912069795 30536450790732778368104693)
                    ·
                      refine ⟨2862792261631197972009815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30536450790732778368104693 2862792261631197972009815)
                      ·
                        rfl

theorem cell23_5575268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_5575268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575268 prefixEnd_5575268 := by exact prefixLift 5575268
  have htrace : WordTrace (prefixWord ++ tailWord_5575268) baseStart_5575268 baseEnd_5575268 := by
    simpa [prefixWord, tailWord_5575268, baseEnd_5575268] using wordTrace_append hprefix tailTrace_5575268
  have hstable : (prefixWord ++ tailWord_5575268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575268).length < 2 ^ (prefixWord ++ tailWord_5575268).sum := by decide
  have hdescent : baseEnd_5575268 < baseStart_5575268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575281 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_5575281 : Nat := 118140960795 + 5575281 * 2 ^ 59
def prefixEnd_5575281 : Nat := 4983230072969 + 3 ^ 40 * 5575281 * 2
def baseEnd_5575281 : Nat := 2862798936879706421147255

theorem tailTrace_5575281 : CollatzResearch.WordTrace tailWord_5575281 prefixEnd_5575281 2862798936879706421147255 := by
  unfold tailWord_5575281
  simp only [CollatzResearch.WordTrace]
  refine ⟨203347203714716594032813697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135564802476477729355209131 203347203714716594032813697)
  ·
    refine ⟨152510402786037445524610273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203347203714716594032813697 152510402786037445524610273)
    ·
      refine ⟨114382802089528084143457705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152510402786037445524610273 114382802089528084143457705)
      ·
        refine ⟨85787101567146063107593279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114382802089528084143457705 85787101567146063107593279)
        ·
          refine ⟨128680652350719094661389919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85787101567146063107593279 128680652350719094661389919)
          ·
            refine ⟨193020978526078641992084879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128680652350719094661389919 193020978526078641992084879)
            ·
              refine ⟨289531467789117962988127319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193020978526078641992084879 289531467789117962988127319)
              ·
                refine ⟨434297201683676944482190979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289531467789117962988127319 434297201683676944482190979)
                ·
                  refine ⟨651445802525515416723286469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434297201683676944482190979 651445802525515416723286469)
                  ·
                    refine ⟨122146087973534140635616213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651445802525515416723286469 122146087973534140635616213)
                    ·
                      refine ⟨2862798936879706421147255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122146087973534140635616213 2862798936879706421147255)
                      ·
                        rfl

theorem cell23_5575281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_5575281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575281 prefixEnd_5575281 := by exact prefixLift 5575281
  have htrace : WordTrace (prefixWord ++ tailWord_5575281) baseStart_5575281 baseEnd_5575281 := by
    simpa [prefixWord, tailWord_5575281, baseEnd_5575281] using wordTrace_append hprefix tailTrace_5575281
  have hstable : (prefixWord ++ tailWord_5575281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575281).length < 2 ^ (prefixWord ++ tailWord_5575281).sum := by decide
  have hdescent : baseEnd_5575281 < baseStart_5575281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575291 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6]
def baseStart_5575291 : Nat := 118140960795 + 5575291 * 2 ^ 59
def prefixEnd_5575291 : Nat := 4983230072969 + 3 ^ 40 * 5575291 * 2
def baseEnd_5575291 : Nat := 2862804071686251382022209

theorem tailTrace_5575291 : CollatzResearch.WordTrace tailWord_5575291 prefixEnd_5575291 2862804071686251382022209 := by
  unfold tailWord_5575291
  simp only [CollatzResearch.WordTrace]
  refine ⟨203347568444680365740677727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135565045629786910493785151 203347568444680365740677727)
  ·
    refine ⟨305021352667020548611016591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203347568444680365740677727 305021352667020548611016591)
    ·
      refine ⟨457532029000530822916524887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305021352667020548611016591 457532029000530822916524887)
      ·
        refine ⟨686298043500796234374787331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457532029000530822916524887 686298043500796234374787331)
        ·
          refine ⟨1029447065251194351562180997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686298043500796234374787331 1029447065251194351562180997)
          ·
            refine ⟨193021324734598940917908937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1029447065251194351562180997 193021324734598940917908937)
            ·
              refine ⟨144765993550949205688431703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193021324734598940917908937 144765993550949205688431703)
              ·
                refine ⟨217148990326423808532647555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144765993550949205688431703 217148990326423808532647555)
                ·
                  refine ⟨325723485489635712798971333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217148990326423808532647555 325723485489635712798971333)
                  ·
                    refine ⟨61073153529306696149807125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325723485489635712798971333 61073153529306696149807125)
                    ·
                      refine ⟨2862804071686251382022209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61073153529306696149807125 2862804071686251382022209)
                      ·
                        rfl

theorem cell23_5575291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_5575291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575291 prefixEnd_5575291 := by exact prefixLift 5575291
  have htrace : WordTrace (prefixWord ++ tailWord_5575291) baseStart_5575291 baseEnd_5575291 := by
    simpa [prefixWord, tailWord_5575291, baseEnd_5575291] using wordTrace_append hprefix tailTrace_5575291
  have hstable : (prefixWord ++ tailWord_5575291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575291).length < 2 ^ (prefixWord ++ tailWord_5575291).sum := by decide
  have hdescent : baseEnd_5575291 < baseStart_5575291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575322 : List Nat := [3, 1, 1, 6, 2, 1, 9]
def baseStart_5575322 : Nat := 118140960795 + 5575322 * 2 ^ 59
def prefixEnd_5575322 : Nat := 4983230072969 + 3 ^ 40 * 5575322 * 2
def baseEnd_5575322 : Nat := 35343456661562231614007

theorem tailTrace_5575322 : CollatzResearch.WordTrace tailWord_5575322 prefixEnd_5575322 35343456661562231614007 := by
  unfold tailWord_5575322
  simp only [CollatzResearch.WordTrace]
  refine ⟨50837174776892014508764055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135565799405045372023370813 50837174776892014508764055)
  ·
    refine ⟨76255762165338021763146083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50837174776892014508764055 76255762165338021763146083)
    ·
      refine ⟨114383643248007032644719125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76255762165338021763146083 114383643248007032644719125)
      ·
        refine ⟨5361733277250329655221209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114383643248007032644719125 5361733277250329655221209)
        ·
          refine ⟨4021299957937747241415907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5361733277250329655221209 4021299957937747241415907)
          ·
            refine ⟨6031949936906620862123861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021299957937747241415907 6031949936906620862123861)
            ·
              refine ⟨35343456661562231614007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6031949936906620862123861 35343456661562231614007)
              ·
                rfl

theorem cell23_5575322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 9].length) (baseStart_5575322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575322 prefixEnd_5575322 := by exact prefixLift 5575322
  have htrace : WordTrace (prefixWord ++ tailWord_5575322) baseStart_5575322 baseEnd_5575322 := by
    simpa [prefixWord, tailWord_5575322, baseEnd_5575322] using wordTrace_append hprefix tailTrace_5575322
  have hstable : (prefixWord ++ tailWord_5575322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575322).length < 2 ^ (prefixWord ++ tailWord_5575322).sum := by decide
  have hdescent : baseEnd_5575322 < baseStart_5575322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575332 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_5575332 : Nat := 118140960795 + 5575332 * 2 ^ 59
def prefixEnd_5575332 : Nat := 4983230072969 + 3 ^ 40 * 5575332 * 2
def baseEnd_5575332 : Nat := 2862825124393085721609521

theorem tailTrace_5575332 : CollatzResearch.WordTrace tailWord_5575332 prefixEnd_5575332 2862825124393085721609521 := by
  unfold tailWord_5575332
  simp only [CollatzResearch.WordTrace]
  refine ⟨101674531918765914871460125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135566042558354553161946833 101674531918765914871460125)
  ·
    refine ⟨38127949469537218076797547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101674531918765914871460125 38127949469537218076797547)
    ·
      refine ⟨57191924204305827115196321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38127949469537218076797547 57191924204305827115196321)
      ·
        refine ⟨42893943153229370336397241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57191924204305827115196321 42893943153229370336397241)
        ·
          refine ⟨32170457364922027752297931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42893943153229370336397241 32170457364922027752297931)
          ·
            refine ⟨48255686047383041628446897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32170457364922027752297931 48255686047383041628446897)
            ·
              refine ⟨36191764535537281221335173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48255686047383041628446897 36191764535537281221335173)
              ·
                refine ⟨6785955850413240229000345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36191764535537281221335173 6785955850413240229000345)
                ·
                  refine ⟨5089466887809930171750259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6785955850413240229000345 5089466887809930171750259)
                  ·
                    refine ⟨7634200331714895257625389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5089466887809930171750259 7634200331714895257625389)
                    ·
                      refine ⟨2862825124393085721609521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634200331714895257625389 2862825124393085721609521)
                      ·
                        rfl

theorem cell23_5575332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_5575332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575332 prefixEnd_5575332 := by exact prefixLift 5575332
  have htrace : WordTrace (prefixWord ++ tailWord_5575332) baseStart_5575332 baseEnd_5575332 := by
    simpa [prefixWord, tailWord_5575332, baseEnd_5575332] using wordTrace_append hprefix tailTrace_5575332
  have hstable : (prefixWord ++ tailWord_5575332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575332).length < 2 ^ (prefixWord ++ tailWord_5575332).sum := by decide
  have hdescent : baseEnd_5575332 < baseStart_5575332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575349 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_5575349 : Nat := 118140960795 + 5575349 * 2 ^ 59
def prefixEnd_5575349 : Nat := 4983230072969 + 3 ^ 40 * 5575349 * 2
def baseEnd_5575349 : Nat := 2862833853564212155096943

theorem tailTrace_5575349 : CollatzResearch.WordTrace tailWord_5575349 prefixEnd_5575349 2862833853564212155096943 := by
  unfold tailWord_5575349
  simp only [CollatzResearch.WordTrace]
  refine ⟨203349683878470241646289101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135566455918980161097526067 203349683878470241646289101)
  ·
    refine ⟨76256131454426340617358413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203349683878470241646289101 76256131454426340617358413)
    ·
      refine ⟨28596049295409877731509405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76256131454426340617358413 28596049295409877731509405)
      ·
        refine ⟨10723518485778704149316027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28596049295409877731509405 10723518485778704149316027)
        ·
          refine ⟨16085277728668056223974041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10723518485778704149316027 16085277728668056223974041)
          ·
            refine ⟨12063958296501042167980531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16085277728668056223974041 12063958296501042167980531)
            ·
              refine ⟨18095937444751563251970797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12063958296501042167980531 18095937444751563251970797)
              ·
                refine ⟨6785976541781836219489049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18095937444751563251970797 6785976541781836219489049)
                ·
                  refine ⟨5089482406336377164616787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6785976541781836219489049 5089482406336377164616787)
                  ·
                    refine ⟨7634223609504565746925181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5089482406336377164616787 7634223609504565746925181)
                    ·
                      refine ⟨2862833853564212155096943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634223609504565746925181 2862833853564212155096943)
                      ·
                        rfl

theorem cell23_5575349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_5575349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575349 prefixEnd_5575349 := by exact prefixLift 5575349
  have htrace : WordTrace (prefixWord ++ tailWord_5575349) baseStart_5575349 baseEnd_5575349 := by
    simpa [prefixWord, tailWord_5575349, baseEnd_5575349] using wordTrace_append hprefix tailTrace_5575349
  have hstable : (prefixWord ++ tailWord_5575349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575349).length < 2 ^ (prefixWord ++ tailWord_5575349).sum := by decide
  have hdescent : baseEnd_5575349 < baseStart_5575349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575359 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 1, 3, 2]
def baseStart_5575359 : Nat := 118140960795 + 5575359 * 2 ^ 59
def prefixEnd_5575359 : Nat := 4983230072969 + 3 ^ 40 * 5575359 * 2
def baseEnd_5575359 : Nat := 2862838988370757115971897

theorem tailTrace_5575359 : CollatzResearch.WordTrace tailWord_5575359 prefixEnd_5575359 2862838988370757115971897 := by
  unfold tailWord_5575359
  simp only [CollatzResearch.WordTrace]
  refine ⟨203350048608434013354153131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135566699072289342236102087 203350048608434013354153131)
  ·
    refine ⟨305025072912651020031229697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203350048608434013354153131 305025072912651020031229697)
    ·
      refine ⟨228768804684488265023422273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305025072912651020031229697 228768804684488265023422273)
      ·
        refine ⟨171576603513366198767566705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228768804684488265023422273 171576603513366198767566705)
        ·
          refine ⟨128682452635024649075675029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171576603513366198767566705 128682452635024649075675029)
          ·
            refine ⟨6031989967266780425422267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128682452635024649075675029 6031989967266780425422267)
            ·
              refine ⟨9047984950900170638133401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031989967266780425422267 9047984950900170638133401)
              ·
                refine ⟨6785988713175127978600051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9047984950900170638133401 6785988713175127978600051)
                ·
                  refine ⟨10178983069762691967900077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6785988713175127978600051 10178983069762691967900077)
                  ·
                    refine ⟨3817118651161009487962529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10178983069762691967900077 3817118651161009487962529)
                    ·
                      refine ⟨2862838988370757115971897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817118651161009487962529 2862838988370757115971897)
                      ·
                        rfl

theorem cell23_5575359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_5575359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575359 prefixEnd_5575359 := by exact prefixLift 5575359
  have htrace : WordTrace (prefixWord ++ tailWord_5575359) baseStart_5575359 baseEnd_5575359 := by
    simpa [prefixWord, tailWord_5575359, baseEnd_5575359] using wordTrace_append hprefix tailTrace_5575359
  have hstable : (prefixWord ++ tailWord_5575359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575359).length < 2 ^ (prefixWord ++ tailWord_5575359).sum := by decide
  have hdescent : baseEnd_5575359 < baseStart_5575359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575366 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_5575366 : Nat := 118140960795 + 5575366 * 2 ^ 59
def prefixEnd_5575366 : Nat := 4983230072969 + 3 ^ 40 * 5575366 * 2
def baseEnd_5575366 : Nat := 2862842582735338588584365

theorem tailTrace_5575366 : CollatzResearch.WordTrace tailWord_5575366 prefixEnd_5575366 2862842582735338588584365 := by
  unfold tailWord_5575366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354696997481520423426811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135566869279605769033105301 6354696997481520423426811)
  ·
    refine ⟨9532045496222280635140217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6354696997481520423426811 9532045496222280635140217)
    ·
      refine ⟨7149034122166710476355163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9532045496222280635140217 7149034122166710476355163)
      ·
        refine ⟨10723551183250065714532745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7149034122166710476355163 10723551183250065714532745)
        ·
          refine ⟨8042663387437549285899559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10723551183250065714532745 8042663387437549285899559)
          ·
            refine ⟨12063995081156323928849339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8042663387437549285899559 12063995081156323928849339)
            ·
              refine ⟨18095992621734485893274009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12063995081156323928849339 18095992621734485893274009)
              ·
                refine ⟨13571994466300864419955507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18095992621734485893274009 13571994466300864419955507)
                ·
                  refine ⟨20357991699451296629933261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13571994466300864419955507 20357991699451296629933261)
                  ·
                    refine ⟨7634246887294236236224973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20357991699451296629933261 7634246887294236236224973)
                    ·
                      refine ⟨2862842582735338588584365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634246887294236236224973 2862842582735338588584365)
                      ·
                        rfl

theorem cell23_5575366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_5575366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575366 prefixEnd_5575366 := by exact prefixLift 5575366
  have htrace : WordTrace (prefixWord ++ tailWord_5575366) baseStart_5575366 baseEnd_5575366 := by
    simpa [prefixWord, tailWord_5575366, baseEnd_5575366] using wordTrace_append hprefix tailTrace_5575366
  have hstable : (prefixWord ++ tailWord_5575366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575366).length < 2 ^ (prefixWord ++ tailWord_5575366).sum := by decide
  have hdescent : baseEnd_5575366 < baseStart_5575366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575372 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5575372 : Nat := 118140960795 + 5575372 * 2 ^ 59
def prefixEnd_5575372 : Nat := 4983230072969 + 3 ^ 40 * 5575372 * 2
def baseEnd_5575372 : Nat := 2862845663619265565109337

theorem tailTrace_5575372 : CollatzResearch.WordTrace tailWord_5575372 prefixEnd_5575372 2862845663619265565109337 := by
  unfold tailWord_5575372
  simp only [CollatzResearch.WordTrace]
  refine ⟨101675261378693458287188185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135567015171591277716250913 101675261378693458287188185)
  ·
    refine ⟨76256446034020093715391139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101675261378693458287188185 76256446034020093715391139)
    ·
      refine ⟨114384669051030140573086709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76256446034020093715391139 114384669051030140573086709)
      ·
        refine ⟨10723562723534075678726879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114384669051030140573086709 10723562723534075678726879)
        ·
          refine ⟨16085344085301113518090319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10723562723534075678726879 16085344085301113518090319)
          ·
            refine ⟨24128016127951670277135479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16085344085301113518090319 24128016127951670277135479)
            ·
              refine ⟨36192024191927505415703219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24128016127951670277135479 36192024191927505415703219)
              ·
                refine ⟨54288036287891258123554829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36192024191927505415703219 54288036287891258123554829)
                ·
                  refine ⟨20358013607959221796333061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54288036287891258123554829 20358013607959221796333061)
                  ·
                    refine ⟨3817127551492354086812449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20358013607959221796333061 3817127551492354086812449)
                    ·
                      refine ⟨2862845663619265565109337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817127551492354086812449 2862845663619265565109337)
                      ·
                        rfl

theorem cell23_5575372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5575372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575372 prefixEnd_5575372 := by exact prefixLift 5575372
  have htrace : WordTrace (prefixWord ++ tailWord_5575372) baseStart_5575372 baseEnd_5575372 := by
    simpa [prefixWord, tailWord_5575372, baseEnd_5575372] using wordTrace_append hprefix tailTrace_5575372
  have hstable : (prefixWord ++ tailWord_5575372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575372).length < 2 ^ (prefixWord ++ tailWord_5575372).sum := by decide
  have hdescent : baseEnd_5575372 < baseStart_5575372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575408 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 1, 7]
def baseStart_5575408 : Nat := 118140960795 + 5575408 * 2 ^ 59
def prefixEnd_5575408 : Nat := 4983230072969 + 3 ^ 40 * 5575408 * 2
def baseEnd_5575408 : Nat := 954288049640942474753057

theorem tailTrace_5575408 : CollatzResearch.WordTrace tailWord_5575408 prefixEnd_5575408 954288049640942474753057 := by
  unfold tailWord_5575408
  simp only [CollatzResearch.WordTrace]
  refine ⟨101675917892628247361343439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135567890523504329815124585 101675917892628247361343439)
  ·
    refine ⟨152513876838942371042015159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101675917892628247361343439 152513876838942371042015159)
    ·
      refine ⟨228770815258413556563022739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152513876838942371042015159 228770815258413556563022739)
      ·
        refine ⟨343156222887620334844534109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228770815258413556563022739 343156222887620334844534109)
        ·
          refine ⟨128683583582857625566700291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343156222887620334844534109 128683583582857625566700291)
          ·
            refine ⟨193025375374286438350050437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128683583582857625566700291 193025375374286438350050437)
            ·
              refine ⟨36192257882678707190634457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193025375374286438350050437 36192257882678707190634457)
              ·
                refine ⟨27144193412009030392975843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36192257882678707190634457 27144193412009030392975843)
                ·
                  refine ⟨40716290118013545589463765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27144193412009030392975843 40716290118013545589463765)
                  ·
                    refine ⟨954288049640942474753057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40716290118013545589463765 954288049640942474753057)
                    ·
                      rfl

theorem cell23_5575408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_5575408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575408 prefixEnd_5575408 := by exact prefixLift 5575408
  have htrace : WordTrace (prefixWord ++ tailWord_5575408) baseStart_5575408 baseEnd_5575408 := by
    simpa [prefixWord, tailWord_5575408, baseEnd_5575408] using wordTrace_append hprefix tailTrace_5575408
  have hstable : (prefixWord ++ tailWord_5575408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575408).length < 2 ^ (prefixWord ++ tailWord_5575408).sum := by decide
  have hdescent : baseEnd_5575408 < baseStart_5575408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575415 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 4, 5, 2]
def baseStart_5575415 : Nat := 118140960795 + 5575415 * 2 ^ 59
def prefixEnd_5575415 : Nat := 4983230072969 + 3 ^ 40 * 5575415 * 2
def baseEnd_5575415 : Nat := 2862867743287408896871639

theorem tailTrace_5575415 : CollatzResearch.WordTrace tailWord_5575415 prefixEnd_5575415 2862867743287408896871639 := by
  unfold tailWord_5575415
  simp only [CollatzResearch.WordTrace]
  refine ⟨203352091096231134918191699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135568060730820756612127799 203352091096231134918191699)
  ·
    refine ⟨305028136644346702377287549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203352091096231134918191699 305028136644346702377287549)
    ·
      refine ⟨114385551241630013391482831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305028136644346702377287549 114385551241630013391482831)
      ·
        refine ⟨171578326862445020087224247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114385551241630013391482831 171578326862445020087224247)
        ·
          refine ⟨257367490293667530130836371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171578326862445020087224247 257367490293667530130836371)
          ·
            refine ⟨386051235440501295196254557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257367490293667530130836371 386051235440501295196254557)
            ·
              refine ⟨144769213290187985698595459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386051235440501295196254557 144769213290187985698595459)
              ·
                refine ⟨217153819935281978547893189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144769213290187985698595459 217153819935281978547893189)
                ·
                  refine ⟨40716341237865370977729973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217153819935281978547893189 40716341237865370977729973)
                  ·
                    refine ⟨3817156991049878529162185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40716341237865370977729973 3817156991049878529162185)
                    ·
                      refine ⟨2862867743287408896871639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817156991049878529162185 2862867743287408896871639)
                      ·
                        rfl

theorem cell23_5575415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_5575415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575415 prefixEnd_5575415 := by exact prefixLift 5575415
  have htrace : WordTrace (prefixWord ++ tailWord_5575415) baseStart_5575415 baseEnd_5575415 := by
    simpa [prefixWord, tailWord_5575415, baseEnd_5575415] using wordTrace_append hprefix tailTrace_5575415
  have hstable : (prefixWord ++ tailWord_5575415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575415).length < 2 ^ (prefixWord ++ tailWord_5575415).sum := by decide
  have hdescent : baseEnd_5575415 < baseStart_5575415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575418 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_5575418 : Nat := 118140960795 + 5575418 * 2 ^ 59
def prefixEnd_5575418 : Nat := 4983230072969 + 3 ^ 40 * 5575418 * 2
def baseEnd_5575418 : Nat := 2862869283729372385134125

theorem tailTrace_5575418 : CollatzResearch.WordTrace tailWord_5575418 prefixEnd_5575418 2862869283729372385134125 := by
  unfold tailWord_5575418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50838050128805066607637727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135568133676813510953700605 50838050128805066607637727)
  ·
    refine ⟨76257075193207599911456591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50838050128805066607637727 76257075193207599911456591)
    ·
      refine ⟨114385612789811399867184887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76257075193207599911456591 114385612789811399867184887)
      ·
        refine ⟨171578419184717099800777331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114385612789811399867184887 171578419184717099800777331)
        ·
          refine ⟨257367628777075649701165997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171578419184717099800777331 257367628777075649701165997)
          ·
            refine ⟨96512860791403368637937249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257367628777075649701165997 96512860791403368637937249)
            ·
              refine ⟨72384645593552526478452937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96512860791403368637937249 72384645593552526478452937)
              ·
                refine ⟨54288484195164394858839703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72384645593552526478452937 54288484195164394858839703)
                ·
                  refine ⟨81432726292746592288259555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54288484195164394858839703 81432726292746592288259555)
                  ·
                    refine ⟨122149089439119888432389333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81432726292746592288259555 122149089439119888432389333)
                    ·
                      refine ⟨2862869283729372385134125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122149089439119888432389333 2862869283729372385134125)
                      ·
                        rfl

theorem cell23_5575418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_5575418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575418 prefixEnd_5575418 := by exact prefixLift 5575418
  have htrace : WordTrace (prefixWord ++ tailWord_5575418) baseStart_5575418 baseEnd_5575418 := by
    simpa [prefixWord, tailWord_5575418, baseEnd_5575418] using wordTrace_append hprefix tailTrace_5575418
  have hstable : (prefixWord ++ tailWord_5575418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575418).length < 2 ^ (prefixWord ++ tailWord_5575418).sum := by decide
  have hdescent : baseEnd_5575418 < baseStart_5575418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575445 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_5575445 : Nat := 118140960795 + 5575445 * 2 ^ 59
def prefixEnd_5575445 : Nat := 4983230072969 + 3 ^ 40 * 5575445 * 2
def baseEnd_5575445 : Nat := 2862883147707043779496501

theorem tailTrace_5575445 : CollatzResearch.WordTrace tailWord_5575445 prefixEnd_5575445 2862883147707043779496501 := by
  unfold tailWord_5575445
  simp only [CollatzResearch.WordTrace]
  refine ⟨203353185286122450041783789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135568790190748300027855859 203353185286122450041783789)
  ·
    refine ⟨76257444482295918765668921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203353185286122450041783789 76257444482295918765668921)
    ·
      refine ⟨57193083361721939074251691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76257444482295918765668921 57193083361721939074251691)
      ·
        refine ⟨85789625042582908611377537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57193083361721939074251691 85789625042582908611377537)
        ·
          refine ⟨64342218781937181458533153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85789625042582908611377537 64342218781937181458533153)
          ·
            refine ⟨48256664086452886093899865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64342218781937181458533153 48256664086452886093899865)
            ·
              refine ⟨36192498064839664570424899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48256664086452886093899865 36192498064839664570424899)
              ·
                refine ⟨54288747097259496855637349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36192498064839664570424899 54288747097259496855637349)
                ·
                  refine ⟨10179140080736155660432003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54288747097259496855637349 10179140080736155660432003)
                  ·
                    refine ⟨15268710121104233490648005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10179140080736155660432003 15268710121104233490648005)
                    ·
                      refine ⟨2862883147707043779496501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15268710121104233490648005 2862883147707043779496501)
                      ·
                        rfl

theorem cell23_5575445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_5575445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575445 prefixEnd_5575445 := by exact prefixLift 5575445
  have htrace : WordTrace (prefixWord ++ tailWord_5575445) baseStart_5575445 baseEnd_5575445 := by
    simpa [prefixWord, tailWord_5575445, baseEnd_5575445] using wordTrace_append hprefix tailTrace_5575445
  have hstable : (prefixWord ++ tailWord_5575445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575445).length < 2 ^ (prefixWord ++ tailWord_5575445).sum := by decide
  have hdescent : baseEnd_5575445 < baseStart_5575445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575465 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 3]
def baseStart_5575465 : Nat := 118140960795 + 5575465 * 2 ^ 59
def prefixEnd_5575465 : Nat := 4983230072969 + 3 ^ 40 * 5575465 * 2
def baseEnd_5575465 : Nat := 2862893417320133701246409

theorem tailTrace_5575465 : CollatzResearch.WordTrace tailWord_5575465 prefixEnd_5575465 2862893417320133701246409 := by
  unfold tailWord_5575465
  simp only [CollatzResearch.WordTrace]
  refine ⟨203353914746049993457511849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135569276497366662305007899 203353914746049993457511849)
  ·
    refine ⟨152515436059537495093133887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203353914746049993457511849 152515436059537495093133887)
    ·
      refine ⟨228773154089306242639700831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152515436059537495093133887 228773154089306242639700831)
      ·
        refine ⟨343159731133959363959551247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228773154089306242639700831 343159731133959363959551247)
        ·
          refine ⟨514739596700939045939326871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343159731133959363959551247 514739596700939045939326871)
          ·
            refine ⟨772109395051408568908990307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514739596700939045939326871 772109395051408568908990307)
            ·
              refine ⟨1158164092577112853363485461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772109395051408568908990307 1158164092577112853363485461)
              ·
                refine ⟨54288941839552165001413381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1158164092577112853363485461 54288941839552165001413381)
                ·
                  refine ⟨10179176594916030937765009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54288941839552165001413381 10179176594916030937765009)
                  ·
                    refine ⟨7634382446187023203323757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10179176594916030937765009 7634382446187023203323757)
                    ·
                      refine ⟨2862893417320133701246409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634382446187023203323757 2862893417320133701246409)
                      ·
                        rfl

theorem cell23_5575465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_5575465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575465 prefixEnd_5575465 := by exact prefixLift 5575465
  have htrace : WordTrace (prefixWord ++ tailWord_5575465) baseStart_5575465 baseEnd_5575465 := by
    simpa [prefixWord, tailWord_5575465, baseEnd_5575465] using wordTrace_append hprefix tailTrace_5575465
  have hstable : (prefixWord ++ tailWord_5575465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575465).length < 2 ^ (prefixWord ++ tailWord_5575465).sum := by decide
  have hdescent : baseEnd_5575465 < baseStart_5575465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575506 : List Nat := [3, 2, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_5575506 : Nat := 118140960795 + 5575506 * 2 ^ 59
def prefixEnd_5575506 : Nat := 4983230072969 + 3 ^ 40 * 5575506 * 2
def baseEnd_5575506 : Nat := 954304823342322680277907

theorem tailTrace_5575506 : CollatzResearch.WordTrace tailWord_5575506 prefixEnd_5575506 954304823342322680277907 := by
  unfold tailWord_5575506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50838852534725364364938593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135570273425934304973169581 50838852534725364364938593)
  ·
    refine ⟨38129139401044023273703945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50838852534725364364938593 38129139401044023273703945)
    ·
      refine ⟨28596854550783017455277959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38129139401044023273703945 28596854550783017455277959)
      ·
        refine ⟨42895281826174526182916939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28596854550783017455277959 42895281826174526182916939)
        ·
          refine ⟨64342922739261789274375409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42895281826174526182916939 64342922739261789274375409)
          ·
            refine ⟨48257192054446341955781557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64342922739261789274375409 48257192054446341955781557)
            ·
              refine ⟨4524111755104344558354521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48257192054446341955781557 4524111755104344558354521)
              ·
                refine ⟨3393083816328258418765891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4524111755104344558354521 3393083816328258418765891)
                ·
                  refine ⟨5089625724492387628148837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393083816328258418765891 5089625724492387628148837)
                  ·
                    refine ⟨954304823342322680277907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5089625724492387628148837 954304823342322680277907)
                    ·
                      rfl

theorem cell23_5575506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_5575506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575506 prefixEnd_5575506 := by exact prefixLift 5575506
  have htrace : WordTrace (prefixWord ++ tailWord_5575506) baseStart_5575506 baseEnd_5575506 := by
    simpa [prefixWord, tailWord_5575506, baseEnd_5575506] using wordTrace_append hprefix tailTrace_5575506
  have hstable : (prefixWord ++ tailWord_5575506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575506).length < 2 ^ (prefixWord ++ tailWord_5575506).sum := by decide
  have hdescent : baseEnd_5575506 < baseStart_5575506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575545 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 3, 6]
def baseStart_5575545 : Nat := 118140960795 + 5575545 * 2 ^ 59
def prefixEnd_5575545 : Nat := 4983230072969 + 3 ^ 40 * 5575545 * 2
def baseEnd_5575545 : Nat := 954311498590831129415347

theorem tailTrace_5575545 : CollatzResearch.WordTrace tailWord_5575545 prefixEnd_5575545 954311498590831129415347 := by
  unfold tailWord_5575545
  simp only [CollatzResearch.WordTrace]
  refine ⟨203356832585760167120424089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135571221723840111413616059 203356832585760167120424089)
  ·
    refine ⟨152517624439320125340318067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203356832585760167120424089 152517624439320125340318067)
    ·
      refine ⟨228776436658980188010477101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152517624439320125340318067 228776436658980188010477101)
      ·
        refine ⟨85791163747117570503928913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228776436658980188010477101 85791163747117570503928913)
        ·
          refine ⟨64343372810338177877946685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85791163747117570503928913 64343372810338177877946685)
          ·
            refine ⟨24128764803876816704230007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64343372810338177877946685 24128764803876816704230007)
            ·
              refine ⟨36193147205815225056345011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24128764803876816704230007 36193147205815225056345011)
              ·
                refine ⟨54289720808722837584517517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36193147205815225056345011 54289720808722837584517517)
                ·
                  refine ⟨20358645303271064094194069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54289720808722837584517517 20358645303271064094194069)
                  ·
                    refine ⟨954311498590831129415347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20358645303271064094194069 954311498590831129415347)
                    ·
                      rfl

theorem cell23_5575545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_5575545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575545 prefixEnd_5575545 := by exact prefixLift 5575545
  have htrace : WordTrace (prefixWord ++ tailWord_5575545) baseStart_5575545 baseEnd_5575545 := by
    simpa [prefixWord, tailWord_5575545, baseEnd_5575545] using wordTrace_append hprefix tailTrace_5575545
  have hstable : (prefixWord ++ tailWord_5575545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575545).length < 2 ^ (prefixWord ++ tailWord_5575545).sum := by decide
  have hdescent : baseEnd_5575545 < baseStart_5575545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575569 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 3, 2, 2]
def baseStart_5575569 : Nat := 118140960795 + 5575569 * 2 ^ 59
def prefixEnd_5575569 : Nat := 4983230072969 + 3 ^ 40 * 5575569 * 2
def baseEnd_5575569 : Nat := 2862946819308201294345931

theorem tailTrace_5575569 : CollatzResearch.WordTrace tailWord_5575569 prefixEnd_5575569 2862946819308201294345931 := by
  unfold tailWord_5575569
  simp only [CollatzResearch.WordTrace]
  refine ⟨203357707937673219219297761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135571805291782146146198507 203357707937673219219297761)
  ·
    refine ⟨152518280953254914414473321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203357707937673219219297761 152518280953254914414473321)
    ·
      refine ⟨114388710714941185810854991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152518280953254914414473321 114388710714941185810854991)
      ·
        refine ⟨171583066072411778716282487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114388710714941185810854991 171583066072411778716282487)
        ·
          refine ⟨257374599108617668074423731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171583066072411778716282487 257374599108617668074423731)
          ·
            refine ⟨386061898662926502111635597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257374599108617668074423731 386061898662926502111635597)
            ·
              refine ⟨144773211998597438291863349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386061898662926502111635597 144773211998597438291863349)
              ·
                refine ⟨13572488624868509839862189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144773211998597438291863349 13572488624868509839862189)
                ·
                  refine ⟨5089683234325691189948321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13572488624868509839862189 5089683234325691189948321)
                  ·
                    refine ⟨3817262425744268392461241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5089683234325691189948321 3817262425744268392461241)
                    ·
                      refine ⟨2862946819308201294345931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817262425744268392461241 2862946819308201294345931)
                      ·
                        rfl

theorem cell23_5575569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_5575569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575569 prefixEnd_5575569 := by exact prefixLift 5575569
  have htrace : WordTrace (prefixWord ++ tailWord_5575569) baseStart_5575569 baseEnd_5575569 := by
    simpa [prefixWord, tailWord_5575569, baseEnd_5575569] using wordTrace_append hprefix tailTrace_5575569
  have hstable : (prefixWord ++ tailWord_5575569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575569).length < 2 ^ (prefixWord ++ tailWord_5575569).sum := by decide
  have hdescent : baseEnd_5575569 < baseStart_5575569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575572 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5575572 : Nat := 118140960795 + 5575572 * 2 ^ 59
def prefixEnd_5575572 : Nat := 4983230072969 + 3 ^ 40 * 5575572 * 2
def baseEnd_5575572 : Nat := 2862948359750164782608417

theorem tailTrace_5575572 : CollatzResearch.WordTrace tailWord_5575572 prefixEnd_5575572 2862948359750164782608417 := by
  unfold tailWord_5575572
  simp only [CollatzResearch.WordTrace]
  refine ⟨101678908678331175365828485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135571878237774900487771313 101678908678331175365828485)
  ·
    refine ⟨19064795377187095381092841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101678908678331175365828485 19064795377187095381092841)
    ·
      refine ⟨14298596532890321535819631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19064795377187095381092841 14298596532890321535819631)
      ·
        refine ⟨21447894799335482303729447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14298596532890321535819631 21447894799335482303729447)
        ·
          refine ⟨32171842199003223455594171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21447894799335482303729447 32171842199003223455594171)
          ·
            refine ⟨48257763298504835183391257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32171842199003223455594171 48257763298504835183391257)
            ·
              refine ⟨36193322473878626387543443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48257763298504835183391257 36193322473878626387543443)
              ·
                refine ⟨54289983710817939581315165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36193322473878626387543443 54289983710817939581315165)
                ·
                  refine ⟨20358743891556727342993187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54289983710817939581315165 20358743891556727342993187)
                  ·
                    refine ⟨30538115837335091014489781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20358743891556727342993187 30538115837335091014489781)
                    ·
                      refine ⟨2862948359750164782608417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30538115837335091014489781 2862948359750164782608417)
                      ·
                        rfl

theorem cell23_5575572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5575572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575572 prefixEnd_5575572 := by exact prefixLift 5575572
  have htrace : WordTrace (prefixWord ++ tailWord_5575572) baseStart_5575572 baseEnd_5575572 := by
    simpa [prefixWord, tailWord_5575572, baseEnd_5575572] using wordTrace_append hprefix tailTrace_5575572
  have hstable : (prefixWord ++ tailWord_5575572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575572).length < 2 ^ (prefixWord ++ tailWord_5575572).sum := by decide
  have hdescent : baseEnd_5575572 < baseStart_5575572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575586 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_5575586 : Nat := 118140960795 + 5575586 * 2 ^ 59
def prefixEnd_5575586 : Nat := 4983230072969 + 3 ^ 40 * 5575586 * 2
def baseEnd_5575586 : Nat := 2862955548479327727833353

theorem tailTrace_5575586 : CollatzResearch.WordTrace tailWord_5575586 prefixEnd_5575586 2862955548479327727833353 := by
  unfold tailWord_5575586
  simp only [CollatzResearch.WordTrace]
  refine ⟨50839581994652907780666653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135572218652407754081777741 50839581994652907780666653)
  ·
    refine ⟨19064843247994840417749995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50839581994652907780666653 19064843247994840417749995)
    ·
      refine ⟨28597264871992260626624993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19064843247994840417749995 28597264871992260626624993)
      ·
        refine ⟨21447948653994195469968745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28597264871992260626624993 21447948653994195469968745)
        ·
          refine ⟨16085961490495646602476559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21447948653994195469968745 16085961490495646602476559)
          ·
            refine ⟨24128942235743469903714839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16085961490495646602476559 24128942235743469903714839)
            ·
              refine ⟨36193413353615204855572259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24128942235743469903714839 36193413353615204855572259)
              ·
                refine ⟨54290120030422807283358389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36193413353615204855572259 54290120030422807283358389)
                ·
                  refine ⟨5089698752852138182814849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54290120030422807283358389 5089698752852138182814849)
                  ·
                    refine ⟨3817274064639103637111137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5089698752852138182814849 3817274064639103637111137)
                    ·
                      refine ⟨2862955548479327727833353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817274064639103637111137 2862955548479327727833353)
                      ·
                        rfl

theorem cell23_5575586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_5575586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575586 prefixEnd_5575586 := by exact prefixLift 5575586
  have htrace : WordTrace (prefixWord ++ tailWord_5575586) baseStart_5575586 baseEnd_5575586 := by
    simpa [prefixWord, tailWord_5575586, baseEnd_5575586] using wordTrace_append hprefix tailTrace_5575586
  have hstable : (prefixWord ++ tailWord_5575586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575586).length < 2 ^ (prefixWord ++ tailWord_5575586).sum := by decide
  have hdescent : baseEnd_5575586 < baseStart_5575586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575613 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_5575613 : Nat := 118140960795 + 5575613 * 2 ^ 59
def prefixEnd_5575613 : Nat := 4983230072969 + 3 ^ 40 * 5575613 * 2
def baseEnd_5575613 : Nat := 954323137485666374065243

theorem tailTrace_5575613 : CollatzResearch.WordTrace tailWord_5575613 prefixEnd_5575613 954323137485666374065243 := by
  unfold tailWord_5575613
  simp only [CollatzResearch.WordTrace]
  refine ⟨203359312749513814733899493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135572875166342543155932995 203359312749513814733899493)
  ·
    refine ⟨38129871140533840262606155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203359312749513814733899493 38129871140533840262606155)
    ·
      refine ⟨57194806710800760393909233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38129871140533840262606155 57194806710800760393909233)
      ·
        refine ⟨42896105033100570295431925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57194806710800760393909233 42896105033100570295431925)
        ·
          refine ⟨4021509846853178465196743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42896105033100570295431925 4021509846853178465196743)
          ·
            refine ⟨6032264770279767697795115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021509846853178465196743 6032264770279767697795115)
            ·
              refine ⟨9048397155419651546692673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032264770279767697795115 9048397155419651546692673)
              ·
                refine ⟨6786297866564738660019505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9048397155419651546692673 6786297866564738660019505)
                ·
                  refine ⟨5089723399923553995014629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6786297866564738660019505 5089723399923553995014629)
                  ·
                    refine ⟨954323137485666374065243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5089723399923553995014629 954323137485666374065243)
                    ·
                      rfl

theorem cell23_5575613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_5575613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575613 prefixEnd_5575613 := by exact prefixLift 5575613
  have htrace : WordTrace (prefixWord ++ tailWord_5575613) baseStart_5575613 baseEnd_5575613 := by
    simpa [prefixWord, tailWord_5575613, baseEnd_5575613] using wordTrace_append hprefix tailTrace_5575613
  have hstable : (prefixWord ++ tailWord_5575613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575613).length < 2 ^ (prefixWord ++ tailWord_5575613).sum := by decide
  have hdescent : baseEnd_5575613 < baseStart_5575613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575615 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_5575615 : Nat := 118140960795 + 5575615 * 2 ^ 59
def prefixEnd_5575615 : Nat := 4983230072969 + 3 ^ 40 * 5575615 * 2
def baseEnd_5575615 : Nat := 2862970439418308114370719

theorem tailTrace_5575615 : CollatzResearch.WordTrace tailWord_5575615 prefixEnd_5575615 2862970439418308114370719 := by
  unfold tailWord_5575615
  simp only [CollatzResearch.WordTrace]
  refine ⟨203359385695506569075472299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135572923797004379383648199 203359385695506569075472299)
  ·
    refine ⟨305039078543259853613208449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203359385695506569075472299 305039078543259853613208449)
    ·
      refine ⟨228779308907444890209906337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305039078543259853613208449 228779308907444890209906337)
      ·
        refine ⟨171584481680583667657429753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228779308907444890209906337 171584481680583667657429753)
        ·
          refine ⟨128688361260437750743072315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171584481680583667657429753 128688361260437750743072315)
          ·
            refine ⟨193032541890656626114608473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128688361260437750743072315 193032541890656626114608473)
            ·
              refine ⟨144774406417992469585956355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193032541890656626114608473 144774406417992469585956355)
              ·
                refine ⟨217161609626988704378934533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144774406417992469585956355 217161609626988704378934533)
                ·
                  refine ⟨40717801805060382071050225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217161609626988704378934533 40717801805060382071050225)
                  ·
                    refine ⟨30538351353795286553287669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40717801805060382071050225 30538351353795286553287669)
                    ·
                      refine ⟨2862970439418308114370719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30538351353795286553287669 2862970439418308114370719)
                      ·
                        rfl

theorem cell23_5575615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_5575615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575615 prefixEnd_5575615 := by exact prefixLift 5575615
  have htrace : WordTrace (prefixWord ++ tailWord_5575615) baseStart_5575615 baseEnd_5575615 := by
    simpa [prefixWord, tailWord_5575615, baseEnd_5575615] using wordTrace_append hprefix tailTrace_5575615
  have hstable : (prefixWord ++ tailWord_5575615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575615).length < 2 ^ (prefixWord ++ tailWord_5575615).sum := by decide
  have hdescent : baseEnd_5575615 < baseStart_5575615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
