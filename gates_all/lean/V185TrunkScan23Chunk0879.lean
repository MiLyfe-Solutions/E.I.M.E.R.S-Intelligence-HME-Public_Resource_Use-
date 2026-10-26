import V185TrunkScan23Chunk0878

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5201591 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 2, 2, 2]
def baseStart_5201591 : Nat := 118140960795 + 5201591 * 2 ^ 59
def prefixEnd_5201591 : Nat := 4983230072969 + 3 ^ 40 * 5201591 * 2
def baseEnd_5201591 : Nat := 2670916351101063484990825

theorem tailTrace_5201591 : CollatzResearch.WordTrace tailWord_5201591 prefixEnd_5201591 2670916351101063484990825 := by
  unfold tailWord_5201591
  simp only [CollatzResearch.WordTrace]
  refine ⟨189717609698531642861876627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126478406465687761907917751 189717609698531642861876627)
  ·
    refine ⟨284576414547797464292814941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189717609698531642861876627 284576414547797464292814941)
    ·
      refine ⟨106716155455424049109805603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284576414547797464292814941 106716155455424049109805603)
      ·
        refine ⟨160074233183136073664708405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106716155455424049109805603 160074233183136073664708405)
        ·
          refine ⟨15006959360919006906066413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160074233183136073664708405 15006959360919006906066413)
          ·
            refine ⟨5627609760344627589774905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15006959360919006906066413 5627609760344627589774905)
            ·
              refine ⟨4220707320258470692331179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627609760344627589774905 4220707320258470692331179)
              ·
                refine ⟨6331060980387706038496769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220707320258470692331179 6331060980387706038496769)
                ·
                  refine ⟨4748295735290779528872577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6331060980387706038496769 4748295735290779528872577)
                  ·
                    refine ⟨3561221801468084646654433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4748295735290779528872577 3561221801468084646654433)
                    ·
                      refine ⟨2670916351101063484990825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561221801468084646654433 2670916351101063484990825)
                      ·
                        rfl

theorem cell23_5201591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_5201591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201591 prefixEnd_5201591 := by exact prefixLift 5201591
  have htrace : WordTrace (prefixWord ++ tailWord_5201591) baseStart_5201591 baseEnd_5201591 := by
    simpa [prefixWord, tailWord_5201591, baseEnd_5201591] using wordTrace_append hprefix tailTrace_5201591
  have hstable : (prefixWord ++ tailWord_5201591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201591).length < 2 ^ (prefixWord ++ tailWord_5201591).sum := by decide
  have hdescent : baseEnd_5201591 < baseStart_5201591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201620 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5201620 : Nat := 118140960795 + 5201620 * 2 ^ 59
def prefixEnd_5201620 : Nat := 4983230072969 + 3 ^ 40 * 5201620 * 2
def baseEnd_5201620 : Nat := 2670931242040043871528191

theorem tailTrace_5201620 : CollatzResearch.WordTrace tailWord_5201620 prefixEnd_5201620 2670931242040043871528191 := by
  unfold tailWord_5201620
  simp only [CollatzResearch.WordTrace]
  refine ⟨94859333707713290407341157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126479111610284387209788209 94859333707713290407341157)
  ·
    refine ⟨17786125070196241951376467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94859333707713290407341157 17786125070196241951376467)
    ·
      refine ⟨26679187605294362927064701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17786125070196241951376467 26679187605294362927064701)
      ·
        refine ⟨10004695351985386097649263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26679187605294362927064701 10004695351985386097649263)
        ·
          refine ⟨15007043027978079146473895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004695351985386097649263 15007043027978079146473895)
          ·
            refine ⟨22510564541967118719710843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15007043027978079146473895 22510564541967118719710843)
            ·
              refine ⟨33765846812950678079566265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22510564541967118719710843 33765846812950678079566265)
              ·
                refine ⟨25324385109713008559674699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33765846812950678079566265 25324385109713008559674699)
                ·
                  refine ⟨37986577664569512839512049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25324385109713008559674699 37986577664569512839512049)
                  ·
                    refine ⟨28489933248427134629634037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37986577664569512839512049 28489933248427134629634037)
                    ·
                      refine ⟨2670931242040043871528191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28489933248427134629634037 2670931242040043871528191)
                      ·
                        rfl

theorem cell23_5201620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5201620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201620 prefixEnd_5201620 := by exact prefixLift 5201620
  have htrace : WordTrace (prefixWord ++ tailWord_5201620) baseStart_5201620 baseEnd_5201620 := by
    simpa [prefixWord, tailWord_5201620, baseEnd_5201620] using wordTrace_append hprefix tailTrace_5201620
  have hstable : (prefixWord ++ tailWord_5201620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201620).length < 2 ^ (prefixWord ++ tailWord_5201620).sum := by decide
  have hdescent : baseEnd_5201620 < baseStart_5201620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201650 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5201650 : Nat := 118140960795 + 5201650 * 2 ^ 59
def prefixEnd_5201650 : Nat := 4983230072969 + 3 ^ 40 * 5201650 * 2
def baseEnd_5201650 : Nat := 2670946646459678754153053

theorem tailTrace_5201650 : CollatzResearch.WordTrace tailWord_5201650 prefixEnd_5201650 2670946646459678754153053 := by
  unfold tailWord_5201650
  simp only [CollatzResearch.WordTrace]
  refine ⟨47429940401329473984568601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126479841070211930625516269 47429940401329473984568601)
  ·
    refine ⟨35572455300997105488426451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47429940401329473984568601 35572455300997105488426451)
    ·
      refine ⟨53358682951495658232639677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35572455300997105488426451 53358682951495658232639677)
      ·
        refine ⟨20009506106810871837239879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53358682951495658232639677 20009506106810871837239879)
        ·
          refine ⟨30014259160216307755859819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20009506106810871837239879 30014259160216307755859819)
          ·
            refine ⟨45021388740324461633789729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30014259160216307755859819 45021388740324461633789729)
            ·
              refine ⟨33766041555243346225342297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45021388740324461633789729 33766041555243346225342297)
              ·
                refine ⟨25324531166432509669006723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33766041555243346225342297 25324531166432509669006723)
                ·
                  refine ⟨37986796749648764503510085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25324531166432509669006723 37986796749648764503510085)
                  ·
                    refine ⟨7122524390559143344408141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37986796749648764503510085 7122524390559143344408141)
                    ·
                      refine ⟨2670946646459678754153053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122524390559143344408141 2670946646459678754153053)
                      ·
                        rfl

theorem cell23_5201650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5201650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201650 prefixEnd_5201650 := by exact prefixLift 5201650
  have htrace : WordTrace (prefixWord ++ tailWord_5201650) baseStart_5201650 baseEnd_5201650 := by
    simpa [prefixWord, tailWord_5201650, baseEnd_5201650] using wordTrace_append hprefix tailTrace_5201650
  have hstable : (prefixWord ++ tailWord_5201650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201650).length < 2 ^ (prefixWord ++ tailWord_5201650).sum := by decide
  have hdescent : baseEnd_5201650 < baseStart_5201650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201674 : List Nat := [3, 1, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_5201674 : Nat := 118140960795 + 5201674 * 2 ^ 59
def prefixEnd_5201674 : Nat := 4983230072969 + 3 ^ 40 * 5201674 * 2
def baseEnd_5201674 : Nat := 890319656665128886750981

theorem tailTrace_5201674 : CollatzResearch.WordTrace tailWord_5201674 prefixEnd_5201674 890319656665128886750981 := by
  unfold tailWord_5201674
  simp only [CollatzResearch.WordTrace]
  refine ⟨47430159239307737009287019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126480424638153965358098717 47430159239307737009287019)
  ·
    refine ⟨71145238858961605513930529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47430159239307737009287019 71145238858961605513930529)
    ·
      refine ⟨53358929144221204135447897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71145238858961605513930529 53358929144221204135447897)
      ·
        refine ⟨40019196858165903101585923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53358929144221204135447897 40019196858165903101585923)
        ·
          refine ⟨60028795287248854652378885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40019196858165903101585923 60028795287248854652378885)
          ·
            refine ⟨11255399116359160247321041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60028795287248854652378885 11255399116359160247321041)
            ·
              refine ⟨8441549337269370185490781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11255399116359160247321041 8441549337269370185490781)
              ·
                refine ⟨3165581001476013819559043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8441549337269370185490781 3165581001476013819559043)
                ·
                  refine ⟨4748371502214020729338565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165581001476013819559043 4748371502214020729338565)
                  ·
                    refine ⟨890319656665128886750981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4748371502214020729338565 890319656665128886750981)
                    ·
                      rfl

theorem cell23_5201674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_5201674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201674 prefixEnd_5201674 := by exact prefixLift 5201674
  have htrace : WordTrace (prefixWord ++ tailWord_5201674) baseStart_5201674 baseEnd_5201674 := by
    simpa [prefixWord, tailWord_5201674, baseEnd_5201674] using wordTrace_append hprefix tailTrace_5201674
  have hstable : (prefixWord ++ tailWord_5201674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201674).length < 2 ^ (prefixWord ++ tailWord_5201674).sum := by decide
  have hdescent : baseEnd_5201674 < baseStart_5201674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201683 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 5, 5]
def baseStart_5201683 : Nat := 118140960795 + 5201683 * 2 ^ 59
def prefixEnd_5201683 : Nat := 4983230072969 + 3 ^ 40 * 5201683 * 2
def baseEnd_5201683 : Nat := 890321197107092375013467

theorem tailTrace_5201683 : CollatzResearch.WordTrace tailWord_5201683 prefixEnd_5201683 890321197107092375013467 := by
  unfold tailWord_5201683
  simp only [CollatzResearch.WordTrace]
  refine ⟨189720965214198342574225703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126480643476132228382817135 189720965214198342574225703)
  ·
    refine ⟨284581447821297513861338555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189720965214198342574225703 284581447821297513861338555)
    ·
      refine ⟨426872171731946270792007833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284581447821297513861338555 426872171731946270792007833)
      ·
        refine ⟨320154128798959703094005875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426872171731946270792007833 320154128798959703094005875)
        ·
          refine ⟨480231193198439554641008813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320154128798959703094005875 480231193198439554641008813)
          ·
            refine ⟨180086697449414832990378305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 480231193198439554641008813 180086697449414832990378305)
            ·
              refine ⟨135065023087061124742783729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180086697449414832990378305 135065023087061124742783729)
              ·
                refine ⟨101298767315295843557087797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135065023087061124742783729 101298767315295843557087797)
                ·
                  refine ⟨9496759435808985333476981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101298767315295843557087797 9496759435808985333476981)
                  ·
                    refine ⟨890321197107092375013467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9496759435808985333476981 890321197107092375013467)
                    ·
                      rfl

theorem cell23_5201683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 5].length) (baseStart_5201683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201683 prefixEnd_5201683 := by exact prefixLift 5201683
  have htrace : WordTrace (prefixWord ++ tailWord_5201683) baseStart_5201683 baseEnd_5201683 := by
    simpa [prefixWord, tailWord_5201683, baseEnd_5201683] using wordTrace_append hprefix tailTrace_5201683
  have hstable : (prefixWord ++ tailWord_5201683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201683).length < 2 ^ (prefixWord ++ tailWord_5201683).sum := by decide
  have hdescent : baseEnd_5201683 < baseStart_5201683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201687 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 6]
def baseStart_5201687 : Nat := 118140960795 + 5201687 * 2 ^ 59
def prefixEnd_5201687 : Nat := 4983230072969 + 3 ^ 40 * 5201687 * 2
def baseEnd_5201687 : Nat := 296773960582655012154487

theorem tailTrace_5201687 : CollatzResearch.WordTrace tailWord_5201687 prefixEnd_5201687 296773960582655012154487 := by
  unfold tailWord_5201687
  simp only [CollatzResearch.WordTrace]
  refine ⟨189721111106183851257371315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126480740737455900838247543 189721111106183851257371315)
  ·
    refine ⟨284581666659275776886056973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189721111106183851257371315 284581666659275776886056973)
    ·
      refine ⟨106718124997228416332271365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284581666659275776886056973 106718124997228416332271365)
      ·
        refine ⟨20009648436980328062300881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106718124997228416332271365 20009648436980328062300881)
        ·
          refine ⟨15007236327735246046725661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20009648436980328062300881 15007236327735246046725661)
          ·
            refine ⟨5627713622900717267522123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15007236327735246046725661 5627713622900717267522123)
            ·
              refine ⟨8441570434351075901283185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5627713622900717267522123 8441570434351075901283185)
              ·
                refine ⟨6331177825763306925962389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8441570434351075901283185 6331177825763306925962389)
                ·
                  refine ⟨296773960582655012154487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6331177825763306925962389 296773960582655012154487)
                  ·
                    rfl

theorem cell23_5201687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 6].length) (baseStart_5201687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201687 prefixEnd_5201687 := by exact prefixLift 5201687
  have htrace : WordTrace (prefixWord ++ tailWord_5201687) baseStart_5201687 baseEnd_5201687 := by
    simpa [prefixWord, tailWord_5201687, baseEnd_5201687] using wordTrace_append hprefix tailTrace_5201687
  have hstable : (prefixWord ++ tailWord_5201687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201687).length < 2 ^ (prefixWord ++ tailWord_5201687).sum := by decide
  have hdescent : baseEnd_5201687 < baseStart_5201687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201697 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_5201697 : Nat := 118140960795 + 5201697 * 2 ^ 59
def prefixEnd_5201697 : Nat := 4983230072969 + 3 ^ 40 * 5201697 * 2
def baseEnd_5201697 : Nat := 2670970780050440070265337

theorem tailTrace_5201697 : CollatzResearch.WordTrace tailWord_5201697 prefixEnd_5201697 2670970780050440070265337 := by
  unfold tailWord_5201697
  simp only [CollatzResearch.WordTrace]
  refine ⟨189721475836147622965235345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126480983890765081976823563 189721475836147622965235345)
  ·
    refine ⟨142291106877110717223926509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189721475836147622965235345 142291106877110717223926509)
    ·
      refine ⟨53359165078916518958972441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142291106877110717223926509 53359165078916518958972441)
      ·
        refine ⟨40019373809187389219229331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53359165078916518958972441 40019373809187389219229331)
        ·
          refine ⟨60029060713781083828843997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40019373809187389219229331 60029060713781083828843997)
          ·
            refine ⟨22510897767667906435816499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60029060713781083828843997 22510897767667906435816499)
            ·
              refine ⟨33766346651501859653724749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22510897767667906435816499 33766346651501859653724749)
              ·
                refine ⟨12662379994313197370146781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33766346651501859653724749 12662379994313197370146781)
                ·
                  refine ⟨4748392497867449013805043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12662379994313197370146781 4748392497867449013805043)
                  ·
                    refine ⟨7122588746801173520707565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4748392497867449013805043 7122588746801173520707565)
                    ·
                      refine ⟨2670970780050440070265337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122588746801173520707565 2670970780050440070265337)
                      ·
                        rfl

theorem cell23_5201697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_5201697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201697 prefixEnd_5201697 := by exact prefixLift 5201697
  have htrace : WordTrace (prefixWord ++ tailWord_5201697) baseStart_5201697 baseEnd_5201697 := by
    simpa [prefixWord, tailWord_5201697, baseEnd_5201697] using wordTrace_append hprefix tailTrace_5201697
  have hstable : (prefixWord ++ tailWord_5201697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201697).length < 2 ^ (prefixWord ++ tailWord_5201697).sum := by decide
  have hdescent : baseEnd_5201697 < baseStart_5201697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201731 : List Nat := [1, 1, 1, 3, 1, 7, 1, 3, 1, 1, 3]
def baseStart_5201731 : Nat := 118140960795 + 5201731 * 2 ^ 59
def prefixEnd_5201731 : Nat := 4983230072969 + 3 ^ 40 * 5201731 * 2
def baseEnd_5201731 : Nat := 2670988238392692937240181

theorem tailTrace_5201731 : CollatzResearch.WordTrace tailWord_5201731 prefixEnd_5201731 2670988238392692937240181 := by
  unfold tailWord_5201731
  simp only [CollatzResearch.WordTrace]
  refine ⟨189722715918024446771973047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126481810612016297847982031 189722715918024446771973047)
  ·
    refine ⟨284584073877036670157959571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189722715918024446771973047 284584073877036670157959571)
    ·
      refine ⟨426876110815555005236939357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284584073877036670157959571 426876110815555005236939357)
      ·
        refine ⟨160078541555833126963852259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426876110815555005236939357 160078541555833126963852259)
        ·
          refine ⟨240117812333749690445778389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160078541555833126963852259 240117812333749690445778389)
          ·
            refine ⟨5627761226572258369822931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 240117812333749690445778389 5627761226572258369822931)
            ·
              refine ⟨8441641839858387554734397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5627761226572258369822931 8441641839858387554734397)
              ·
                refine ⟨3165615689946895333025399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8441641839858387554734397 3165615689946895333025399)
                ·
                  refine ⟨4748423534920342999538099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165615689946895333025399 4748423534920342999538099)
                  ·
                    refine ⟨7122635302380514499307149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4748423534920342999538099 7122635302380514499307149)
                    ·
                      refine ⟨2670988238392692937240181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122635302380514499307149 2670988238392692937240181)
                      ·
                        rfl

theorem cell23_5201731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_5201731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201731 prefixEnd_5201731 := by exact prefixLift 5201731
  have htrace : WordTrace (prefixWord ++ tailWord_5201731) baseStart_5201731 baseEnd_5201731 := by
    simpa [prefixWord, tailWord_5201731, baseEnd_5201731] using wordTrace_append hprefix tailTrace_5201731
  have hstable : (prefixWord ++ tailWord_5201731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201731).length < 2 ^ (prefixWord ++ tailWord_5201731).sum := by decide
  have hdescent : baseEnd_5201731 < baseStart_5201731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201741 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5201741 : Nat := 118140960795 + 5201741 * 2 ^ 59
def prefixEnd_5201741 : Nat := 4983230072969 + 3 ^ 40 * 5201741 * 2
def baseEnd_5201741 : Nat := 2670993373199237898115135

theorem tailTrace_5201741 : CollatzResearch.WordTrace tailWord_5201741 prefixEnd_5201741 2670993373199237898115135 := by
  unfold tailWord_5201741
  simp only [CollatzResearch.WordTrace]
  refine ⟨189723080647988218479837077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126482053765325478986558051 189723080647988218479837077)
  ·
    refine ⟨8893269405374447741242363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 189723080647988218479837077 8893269405374447741242363)
    ·
      refine ⟨13339904108061671611863545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8893269405374447741242363 13339904108061671611863545)
      ·
        refine ⟨10004928081046253708897659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13339904108061671611863545 10004928081046253708897659)
        ·
          refine ⟨15007392121569380563346489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004928081046253708897659 15007392121569380563346489)
          ·
            refine ⟨11255544091177035422509867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15007392121569380563346489 11255544091177035422509867)
            ·
              refine ⟨16883316136765553133764801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11255544091177035422509867 16883316136765553133764801)
              ·
                refine ⟨12662487102574164850323601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16883316136765553133764801 12662487102574164850323601)
                ·
                  refine ⟨9496865326930623637742701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12662487102574164850323601 9496865326930623637742701)
                  ·
                    refine ⟨3561324497598983864153513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9496865326930623637742701 3561324497598983864153513)
                    ·
                      refine ⟨2670993373199237898115135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561324497598983864153513 2670993373199237898115135)
                      ·
                        rfl

theorem cell23_5201741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5201741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201741 prefixEnd_5201741 := by exact prefixLift 5201741
  have htrace : WordTrace (prefixWord ++ tailWord_5201741) baseStart_5201741 baseEnd_5201741 := by
    simpa [prefixWord, tailWord_5201741, baseEnd_5201741] using wordTrace_append hprefix tailTrace_5201741
  have hstable : (prefixWord ++ tailWord_5201741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201741).length < 2 ^ (prefixWord ++ tailWord_5201741).sum := by decide
  have hdescent : baseEnd_5201741 < baseStart_5201741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201748 : List Nat := [2, 4, 1, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_5201748 : Nat := 118140960795 + 5201748 * 2 ^ 59
def prefixEnd_5201748 : Nat := 4983230072969 + 3 ^ 40 * 5201748 * 2
def baseEnd_5201748 : Nat := 2670996967563819370727603

theorem tailTrace_5201748 : CollatzResearch.WordTrace tailWord_5201748 prefixEnd_5201748 2670996967563819370727603 := by
  unfold tailWord_5201748
  simp only [CollatzResearch.WordTrace]
  refine ⟨94861667979481429337670949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126482223972641905783561265 94861667979481429337670949)
  ·
    refine ⟨17786562746152768000813303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94861667979481429337670949 17786562746152768000813303)
    ·
      refine ⟨26679844119229152001219955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17786562746152768000813303 26679844119229152001219955)
      ·
        refine ⟨40019766178843728001829933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26679844119229152001219955 40019766178843728001829933)
        ·
          refine ⟨15007412317066398000686225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40019766178843728001829933 15007412317066398000686225)
          ·
            refine ⟨11255559237799798500514669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15007412317066398000686225 11255559237799798500514669)
            ·
              refine ⟨4220834714174924437693001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11255559237799798500514669 4220834714174924437693001)
              ·
                refine ⟨3165626035631193328269751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220834714174924437693001 3165626035631193328269751)
                ·
                  refine ⟨4748439053446789992404627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165626035631193328269751 4748439053446789992404627)
                  ·
                    refine ⟨7122658580170184988606941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4748439053446789992404627 7122658580170184988606941)
                    ·
                      refine ⟨2670996967563819370727603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122658580170184988606941 2670996967563819370727603)
                      ·
                        rfl

theorem cell23_5201748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_5201748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201748 prefixEnd_5201748 := by exact prefixLift 5201748
  have htrace : WordTrace (prefixWord ++ tailWord_5201748) baseStart_5201748 baseEnd_5201748 := by
    simpa [prefixWord, tailWord_5201748, baseEnd_5201748] using wordTrace_append hprefix tailTrace_5201748
  have hstable : (prefixWord ++ tailWord_5201748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201748).length < 2 ^ (prefixWord ++ tailWord_5201748).sum := by decide
  have hdescent : baseEnd_5201748 < baseStart_5201748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201760 : List Nat := [2, 1, 1, 3, 3, 3, 2, 8]
def baseStart_5201760 : Nat := 118140960795 + 5201760 * 2 ^ 59
def prefixEnd_5201760 : Nat := 4983230072969 + 3 ^ 40 * 5201760 * 2
def baseEnd_5201760 : Nat := 98926041827099011991761

theorem tailTrace_5201760 : CollatzResearch.WordTrace tailWord_5201760 prefixEnd_5201760 98926041827099011991761 := by
  unfold tailWord_5201760
  simp only [CollatzResearch.WordTrace]
  refine ⟨94861886817459692362389367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126482515756612923149852489 94861886817459692362389367)
  ·
    refine ⟨142292830226189538543584051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94861886817459692362389367 142292830226189538543584051)
    ·
      refine ⟨213439245339284307815376077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142292830226189538543584051 213439245339284307815376077)
      ·
        refine ⟨80039717002231615430766029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213439245339284307815376077 80039717002231615430766029)
        ·
          refine ⟨30014893875836855786537261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80039717002231615430766029 30014893875836855786537261)
          ·
            refine ⟨11255585203438820919951473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30014893875836855786537261 11255585203438820919951473)
            ·
              refine ⟨8441688902579115689963605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11255585203438820919951473 8441688902579115689963605)
              ·
                refine ⟨98926041827099011991761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8441688902579115689963605 98926041827099011991761)
                ·
                  rfl

theorem cell23_5201760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 8].length) (baseStart_5201760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201760 prefixEnd_5201760 := by exact prefixLift 5201760
  have htrace : WordTrace (prefixWord ++ tailWord_5201760) baseStart_5201760 baseEnd_5201760 := by
    simpa [prefixWord, tailWord_5201760, baseEnd_5201760] using wordTrace_append hprefix tailTrace_5201760
  have hstable : (prefixWord ++ tailWord_5201760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201760).length < 2 ^ (prefixWord ++ tailWord_5201760).sum := by decide
  have hdescent : baseEnd_5201760 < baseStart_5201760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201764 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_5201764 : Nat := 118140960795 + 5201764 * 2 ^ 59
def prefixEnd_5201764 : Nat := 4983230072969 + 3 ^ 40 * 5201764 * 2
def baseEnd_5201764 : Nat := 890335061084763769375843

theorem tailTrace_5201764 : CollatzResearch.WordTrace tailWord_5201764 prefixEnd_5201764 890335061084763769375843 := by
  unfold tailWord_5201764
  simp only [CollatzResearch.WordTrace]
  refine ⟨94861959763452446703962173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126482613017936595605282897 94861959763452446703962173)
  ·
    refine ⟨35573234911294667513985815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94861959763452446703962173 35573234911294667513985815)
    ·
      refine ⟨53359852366942001270978723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35573234911294667513985815 53359852366942001270978723)
      ·
        refine ⟨80039778550413001906468085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53359852366942001270978723 80039778550413001906468085)
        ·
          refine ⟨7503729239101218928731383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80039778550413001906468085 7503729239101218928731383)
          ·
            refine ⟨11255593858651828393097075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7503729239101218928731383 11255593858651828393097075)
            ·
              refine ⟨16883390787977742589645613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11255593858651828393097075 16883390787977742589645613)
              ·
                refine ⟨6331271545491653471117105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16883390787977742589645613 6331271545491653471117105)
                ·
                  refine ⟨4748453659118740103337829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6331271545491653471117105 4748453659118740103337829)
                  ·
                    refine ⟨890335061084763769375843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4748453659118740103337829 890335061084763769375843)
                    ·
                      rfl

theorem cell23_5201764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_5201764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201764 prefixEnd_5201764 := by exact prefixLift 5201764
  have htrace : WordTrace (prefixWord ++ tailWord_5201764) baseStart_5201764 baseEnd_5201764 := by
    simpa [prefixWord, tailWord_5201764, baseEnd_5201764] using wordTrace_append hprefix tailTrace_5201764
  have hstable : (prefixWord ++ tailWord_5201764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201764).length < 2 ^ (prefixWord ++ tailWord_5201764).sum := by decide
  have hdescent : baseEnd_5201764 < baseStart_5201764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201774 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_5201774 : Nat := 118140960795 + 5201774 * 2 ^ 59
def prefixEnd_5201774 : Nat := 4983230072969 + 3 ^ 40 * 5201774 * 2
def baseEnd_5201774 : Nat := 2671010318060836269002483

theorem tailTrace_5201774 : CollatzResearch.WordTrace tailWord_5201774 prefixEnd_5201774 2671010318060836269002483 := by
  unfold tailWord_5201774
  simp only [CollatzResearch.WordTrace]
  refine ⟨23715535532108583139473547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126482856171245776743858917 23715535532108583139473547)
  ·
    refine ⟨35573303298162874709210321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23715535532108583139473547 35573303298162874709210321)
    ·
      refine ⟨26679977473622156031907741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35573303298162874709210321 26679977473622156031907741)
      ·
        refine ⟨10004991552608308511965403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26679977473622156031907741 10004991552608308511965403)
        ·
          refine ⟨15007487328912462767948105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004991552608308511965403 15007487328912462767948105)
          ·
            refine ⟨11255615496684347075961079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15007487328912462767948105 11255615496684347075961079)
            ·
              refine ⟨16883423245026520613941619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11255615496684347075961079 16883423245026520613941619)
              ·
                refine ⟨25325134867539780920912429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16883423245026520613941619 25325134867539780920912429)
                ·
                  refine ⟨9496925575327417845342161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25325134867539780920912429 9496925575327417845342161)
                  ·
                    refine ⟨7122694181495563384006621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9496925575327417845342161 7122694181495563384006621)
                    ·
                      refine ⟨2671010318060836269002483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122694181495563384006621 2671010318060836269002483)
                      ·
                        rfl

theorem cell23_5201774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_5201774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201774 prefixEnd_5201774 := by exact prefixLift 5201774
  have htrace : WordTrace (prefixWord ++ tailWord_5201774) baseStart_5201774 baseEnd_5201774 := by
    simpa [prefixWord, tailWord_5201774, baseEnd_5201774] using wordTrace_append hprefix tailTrace_5201774
  have hstable : (prefixWord ++ tailWord_5201774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201774).length < 2 ^ (prefixWord ++ tailWord_5201774).sum := by decide
  have hdescent : baseEnd_5201774 < baseStart_5201774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201867 : List Nat := [1, 1, 1, 1, 3, 4, 1, 6, 5]
def baseStart_5201867 : Nat := 118140960795 + 5201867 * 2 ^ 59
def prefixEnd_5201867 : Nat := 4983230072969 + 3 ^ 40 * 5201867 * 2
def baseEnd_5201867 : Nat := 296784230195744933904395

theorem tailTrace_5201867 : CollatzResearch.WordTrace tailWord_5201867 prefixEnd_5201867 296784230195744933904395 := by
  unfold tailWord_5201867
  simp only [CollatzResearch.WordTrace]
  refine ⟨189727676245531741998923855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126485117497021161332615903 189727676245531741998923855)
  ·
    refine ⟨284591514368297612998385783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189727676245531741998923855 284591514368297612998385783)
    ·
      refine ⟨426887271552446419497578675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284591514368297612998385783 426887271552446419497578675)
      ·
        refine ⟨640330907328669629246368013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426887271552446419497578675 640330907328669629246368013)
        ·
          refine ⟨240124090248251110967388005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640330907328669629246368013 240124090248251110967388005)
          ·
            refine ⟨45023266921547083306385251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240124090248251110967388005 45023266921547083306385251)
            ·
              refine ⟨67534900382320624959577877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45023266921547083306385251 67534900382320624959577877)
              ·
                refine ⟨3165698455421279294980213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67534900382320624959577877 3165698455421279294980213)
                ·
                  refine ⟨296784230195744933904395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3165698455421279294980213 296784230195744933904395)
                  ·
                    rfl

theorem cell23_5201867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 5].length) (baseStart_5201867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201867 prefixEnd_5201867 := by exact prefixLift 5201867
  have htrace : WordTrace (prefixWord ++ tailWord_5201867) baseStart_5201867 baseEnd_5201867 := by
    simpa [prefixWord, tailWord_5201867, baseEnd_5201867] using wordTrace_append hprefix tailTrace_5201867
  have hstable : (prefixWord ++ tailWord_5201867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201867).length < 2 ^ (prefixWord ++ tailWord_5201867).sum := by decide
  have hdescent : baseEnd_5201867 < baseStart_5201867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201880 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 3, 7]
def baseStart_5201880 : Nat := 118140960795 + 5201880 * 2 ^ 59
def prefixEnd_5201880 : Nat := 4983230072969 + 3 ^ 40 * 5201880 * 2
def baseEnd_5201880 : Nat := 890354915670070951425665

theorem tailTrace_5201880 : CollatzResearch.WordTrace tailWord_5201880 prefixEnd_5201880 890354915670070951425665 := by
  unfold tailWord_5201880
  simp only [CollatzResearch.WordTrace]
  refine ⟨94864075197242322609573547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126485433596323096812764729 94864075197242322609573547)
  ·
    refine ⟨142296112795863483914360321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94864075197242322609573547 142296112795863483914360321)
    ·
      refine ⟨106722084596897612935770241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142296112795863483914360321 106722084596897612935770241)
      ·
        refine ⟨80041563447673209701827681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106722084596897612935770241 80041563447673209701827681)
        ·
          refine ⟨60031172585754907276370761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80041563447673209701827681 60031172585754907276370761)
          ·
            refine ⟨45023379439316180457278071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60031172585754907276370761 45023379439316180457278071)
            ·
              refine ⟨67535069158974270685917107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45023379439316180457278071 67535069158974270685917107)
              ·
                refine ⟨101302603738461406028875661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67535069158974270685917107 101302603738461406028875661)
                ·
                  refine ⟨37988476401923027260828373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101302603738461406028875661 37988476401923027260828373)
                  ·
                    refine ⟨890354915670070951425665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37988476401923027260828373 890354915670070951425665)
                    ·
                      rfl

theorem cell23_5201880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_5201880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201880 prefixEnd_5201880 := by exact prefixLift 5201880
  have htrace : WordTrace (prefixWord ++ tailWord_5201880) baseStart_5201880 baseEnd_5201880 := by
    simpa [prefixWord, tailWord_5201880, baseEnd_5201880] using wordTrace_append hprefix tailTrace_5201880
  have hstable : (prefixWord ++ tailWord_5201880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201880).length < 2 ^ (prefixWord ++ tailWord_5201880).sum := by decide
  have hdescent : baseEnd_5201880 < baseStart_5201880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201917 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_5201917 : Nat := 118140960795 + 5201917 * 2 ^ 59
def prefixEnd_5201917 : Nat := 4983230072969 + 3 ^ 40 * 5201917 * 2
def baseEnd_5201917 : Nat := 2671083745794429209514325

theorem tailTrace_5201917 : CollatzResearch.WordTrace tailWord_5201917 prefixEnd_5201917 2671083745794429209514325 := by
  unfold tailWord_5201917
  simp only [CollatzResearch.WordTrace]
  refine ⟨189729499895350600538244005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126486333263567067025496003 189729499895350600538244005)
  ·
    refine ⟨35574281230378237600920751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189729499895350600538244005 35574281230378237600920751)
    ·
      refine ⟨53361421845567356401381127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35574281230378237600920751 53361421845567356401381127)
      ·
        refine ⟨80042132768351034602071691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53361421845567356401381127 80042132768351034602071691)
        ·
          refine ⟨120063199152526551903107537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80042132768351034602071691 120063199152526551903107537)
          ·
            refine ⟨90047399364394913927330653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120063199152526551903107537 90047399364394913927330653)
            ·
              refine ⟨33767774761648092722748995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90047399364394913927330653 33767774761648092722748995)
              ·
                refine ⟨50651662142472139084123493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33767774761648092722748995 50651662142472139084123493)
                ·
                  refine ⟨9497186651713526078273155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50651662142472139084123493 9497186651713526078273155)
                  ·
                    refine ⟨14245779977570289117409733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9497186651713526078273155 14245779977570289117409733)
                    ·
                      refine ⟨2671083745794429209514325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14245779977570289117409733 2671083745794429209514325)
                      ·
                        rfl

theorem cell23_5201917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_5201917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201917 prefixEnd_5201917 := by exact prefixLift 5201917
  have htrace : WordTrace (prefixWord ++ tailWord_5201917) baseStart_5201917 baseEnd_5201917 := by
    simpa [prefixWord, tailWord_5201917, baseEnd_5201917] using wordTrace_append hprefix tailTrace_5201917
  have hstable : (prefixWord ++ tailWord_5201917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201917).length < 2 ^ (prefixWord ++ tailWord_5201917).sum := by decide
  have hdescent : baseEnd_5201917 < baseStart_5201917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201918 : List Nat := [4, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_5201918 : Nat := 118140960795 + 5201918 * 2 ^ 59
def prefixEnd_5201918 : Nat := 4983230072969 + 3 ^ 40 * 5201918 * 2
def baseEnd_5201918 : Nat := 296787139919453745066869

theorem tailTrace_5201918 : CollatzResearch.WordTrace tailWord_5201918 prefixEnd_5201918 296787139919453745066869 := by
  unfold tailWord_5201918
  simp only [CollatzResearch.WordTrace]
  refine ⟨23716192046043372213628801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126486357578897985139353605 23716192046043372213628801)
  ·
    refine ⟨17787144034532529160221601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23716192046043372213628801 17787144034532529160221601)
    ·
      refine ⟨13340358025899396870166201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17787144034532529160221601 13340358025899396870166201)
      ·
        refine ⟨10005268519424547652624651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13340358025899396870166201 10005268519424547652624651)
        ·
          refine ⟨15007902779136821478936977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10005268519424547652624651 15007902779136821478936977)
          ·
            refine ⟨11255927084352616109202733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15007902779136821478936977 11255927084352616109202733)
            ·
              refine ⟨4220972656632231040951025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11255927084352616109202733 4220972656632231040951025)
              ·
                refine ⟨3165729492474173280713269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220972656632231040951025 3165729492474173280713269)
                ·
                  refine ⟨296787139919453745066869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3165729492474173280713269 296787139919453745066869)
                  ·
                    rfl

theorem cell23_5201918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_5201918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201918 prefixEnd_5201918 := by exact prefixLift 5201918
  have htrace : WordTrace (prefixWord ++ tailWord_5201918) baseStart_5201918 baseEnd_5201918 := by
    simpa [prefixWord, tailWord_5201918, baseEnd_5201918] using wordTrace_append hprefix tailTrace_5201918
  have hstable : (prefixWord ++ tailWord_5201918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201918).length < 2 ^ (prefixWord ++ tailWord_5201918).sum := by decide
  have hdescent : baseEnd_5201918 < baseStart_5201918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201920 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_5201920 : Nat := 118140960795 + 5201920 * 2 ^ 59
def prefixEnd_5201920 : Nat := 4983230072969 + 3 ^ 40 * 5201920 * 2
def baseEnd_5201920 : Nat := 2671085286236392697776811

theorem tailTrace_5201920 : CollatzResearch.WordTrace tailWord_5201920 prefixEnd_5201920 2671085286236392697776811 := by
  unfold tailWord_5201920
  simp only [CollatzResearch.WordTrace]
  refine ⟨94864804657169866025301607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126486406209559821367068809 94864804657169866025301607)
  ·
    refine ⟨142297206985754799037952411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94864804657169866025301607 142297206985754799037952411)
    ·
      refine ⟨213445810478632198556928617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142297206985754799037952411 213445810478632198556928617)
      ·
        refine ⟨160084357858974148917696463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213445810478632198556928617 160084357858974148917696463)
        ·
          refine ⟨240126536788461223376544695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160084357858974148917696463 240126536788461223376544695)
          ·
            refine ⟨360189805182691835064817043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240126536788461223376544695 360189805182691835064817043)
            ·
              refine ⟨540284707774037752597225565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360189805182691835064817043 540284707774037752597225565)
              ·
                refine ⟨202606765415264157223959587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540284707774037752597225565 202606765415264157223959587)
                ·
                  refine ⟨303910148122896235835939381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202606765415264157223959587 303910148122896235835939381)
                  ·
                    refine ⟨28491576386521522109619317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 303910148122896235835939381 28491576386521522109619317)
                    ·
                      refine ⟨2671085286236392697776811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28491576386521522109619317 2671085286236392697776811)
                      ·
                        rfl

theorem cell23_5201920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_5201920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201920 prefixEnd_5201920 := by exact prefixLift 5201920
  have htrace : WordTrace (prefixWord ++ tailWord_5201920) baseStart_5201920 baseEnd_5201920 := by
    simpa [prefixWord, tailWord_5201920, baseEnd_5201920] using wordTrace_append hprefix tailTrace_5201920
  have hstable : (prefixWord ++ tailWord_5201920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201920).length < 2 ^ (prefixWord ++ tailWord_5201920).sum := by decide
  have hdescent : baseEnd_5201920 < baseStart_5201920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201934 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_5201934 : Nat := 118140960795 + 5201934 * 2 ^ 59
def prefixEnd_5201934 : Nat := 4983230072969 + 3 ^ 40 * 5201934 * 2
def baseEnd_5201934 : Nat := 2671092474965555643001747

theorem tailTrace_5201934 : CollatzResearch.WordTrace tailWord_5201934 prefixEnd_5201934 2671092474965555643001747 := by
  unfold tailWord_5201934
  simp only [CollatzResearch.WordTrace]
  refine ⟨23716264992036126555201607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126486746624192674961075237 23716264992036126555201607)
  ·
    refine ⟨35574397488054189832802411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23716264992036126555201607 35574397488054189832802411)
    ·
      refine ⟨53361596232081284749203617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35574397488054189832802411 53361596232081284749203617)
      ·
        refine ⟨40021197174060963561902713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53361596232081284749203617 40021197174060963561902713)
        ·
          refine ⟨30015897880545722671427035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40021197174060963561902713 30015897880545722671427035)
          ·
            refine ⟨45023846820818584007140553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30015897880545722671427035 45023846820818584007140553)
            ·
              refine ⟨33767885115613938005355415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45023846820818584007140553 33767885115613938005355415)
              ·
                refine ⟨50651827673420907008033123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33767885115613938005355415 50651827673420907008033123)
                ·
                  refine ⟨75977741510131360512049685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50651827673420907008033123 75977741510131360512049685)
                  ·
                    refine ⟨3561456633287407524002329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75977741510131360512049685 3561456633287407524002329)
                    ·
                      refine ⟨2671092474965555643001747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561456633287407524002329 2671092474965555643001747)
                      ·
                        rfl

theorem cell23_5201934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_5201934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201934 prefixEnd_5201934 := by exact prefixLift 5201934
  have htrace : WordTrace (prefixWord ++ tailWord_5201934) baseStart_5201934 baseEnd_5201934 := by
    simpa [prefixWord, tailWord_5201934, baseEnd_5201934] using wordTrace_append hprefix tailTrace_5201934
  have hstable : (prefixWord ++ tailWord_5201934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201934).length < 2 ^ (prefixWord ++ tailWord_5201934).sum := by decide
  have hdescent : baseEnd_5201934 < baseStart_5201934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201994 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_5201994 : Nat := 118140960795 + 5201994 * 2 ^ 59
def prefixEnd_5201994 : Nat := 4983230072969 + 3 ^ 40 * 5201994 * 2
def baseEnd_5201994 : Nat := 2671123283804825408251471

theorem tailTrace_5201994 : CollatzResearch.WordTrace tailWord_5201994 prefixEnd_5201994 2671123283804825408251471 := by
  unfold tailWord_5201994
  simp only [CollatzResearch.WordTrace]
  refine ⟨47433077079017910672199259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126488205544047761792531357 47433077079017910672199259)
  ·
    refine ⟨71149615618526866008298889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47433077079017910672199259 71149615618526866008298889)
    ·
      refine ⟨53362211713895149506224167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71149615618526866008298889 53362211713895149506224167)
      ·
        refine ⟨80043317570842724259336251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53362211713895149506224167 80043317570842724259336251)
        ·
          refine ⟨120064976356264086389004377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80043317570842724259336251 120064976356264086389004377)
          ·
            refine ⟨90048732267198064791753283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120064976356264086389004377 90048732267198064791753283)
            ·
              refine ⟨135073098400797097187629925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90048732267198064791753283 135073098400797097187629925)
              ·
                refine ⟨25326205950149455722680611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135073098400797097187629925 25326205950149455722680611)
                ·
                  refine ⟨37989308925224183584020917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25326205950149455722680611 37989308925224183584020917)
                  ·
                    refine ⟨3561497711739767211001961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37989308925224183584020917 3561497711739767211001961)
                    ·
                      refine ⟨2671123283804825408251471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561497711739767211001961 2671123283804825408251471)
                      ·
                        rfl

theorem cell23_5201994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_5201994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201994 prefixEnd_5201994 := by exact prefixLift 5201994
  have htrace : WordTrace (prefixWord ++ tailWord_5201994) baseStart_5201994 baseEnd_5201994 := by
    simpa [prefixWord, tailWord_5201994, baseEnd_5201994] using wordTrace_append hprefix tailTrace_5201994
  have hstable : (prefixWord ++ tailWord_5201994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201994).length < 2 ^ (prefixWord ++ tailWord_5201994).sum := by decide
  have hdescent : baseEnd_5201994 < baseStart_5201994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202004 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_5202004 : Nat := 118140960795 + 5202004 * 2 ^ 59
def prefixEnd_5202004 : Nat := 4983230072969 + 3 ^ 40 * 5202004 * 2
def baseEnd_5202004 : Nat := 890376139537123456375475

theorem tailTrace_5202004 : CollatzResearch.WordTrace tailWord_5202004 prefixEnd_5202004 890376139537123456375475 := by
  unfold tailWord_5202004
  simp only [CollatzResearch.WordTrace]
  refine ⟨94866336523017707198330533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126488448697356942931107377 94866336523017707198330533)
  ·
    refine ⟨17787438098065820099686975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94866336523017707198330533 17787438098065820099686975)
    ·
      refine ⟨26681157147098730149530463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17787438098065820099686975 26681157147098730149530463)
      ·
        refine ⟨40021735720648095224295695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26681157147098730149530463 40021735720648095224295695)
        ·
          refine ⟨60032603580972142836443543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40021735720648095224295695 60032603580972142836443543)
          ·
            refine ⟨90048905371458214254665315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60032603580972142836443543 90048905371458214254665315)
            ·
              refine ⟨135073358057187321381997973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90048905371458214254665315 135073358057187321381997973)
              ·
                refine ⟨6331563658930655689781155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135073358057187321381997973 6331563658930655689781155)
                ·
                  refine ⟨9497345488395983534671733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6331563658930655689781155 9497345488395983534671733)
                  ·
                    refine ⟨890376139537123456375475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9497345488395983534671733 890376139537123456375475)
                    ·
                      rfl

theorem cell23_5202004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_5202004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202004 prefixEnd_5202004 := by exact prefixLift 5202004
  have htrace : WordTrace (prefixWord ++ tailWord_5202004) baseStart_5202004 baseEnd_5202004 := by
    simpa [prefixWord, tailWord_5202004, baseEnd_5202004] using wordTrace_append hprefix tailTrace_5202004
  have hstable : (prefixWord ++ tailWord_5202004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202004).length < 2 ^ (prefixWord ++ tailWord_5202004).sum := by decide
  have hdescent : baseEnd_5202004 < baseStart_5202004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202021 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_5202021 : Nat := 118140960795 + 5202021 * 2 ^ 59
def prefixEnd_5202021 : Nat := 4983230072969 + 3 ^ 40 * 5202021 * 2
def baseEnd_5202021 : Nat := 890379049260832267537949

theorem tailTrace_5202021 : CollatzResearch.WordTrace tailWord_5202021 prefixEnd_5202021 890379049260832267537949 := by
  unfold tailWord_5202021
  simp only [CollatzResearch.WordTrace]
  refine ⟨189733293086973826300029917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126488862057982550866686611 189733293086973826300029917)
  ·
    refine ⟨71149984907615184862511219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189733293086973826300029917 71149984907615184862511219)
    ·
      refine ⟨106724977361422777293766829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71149984907615184862511219 106724977361422777293766829)
      ·
        refine ⟨40021866510533541485162561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106724977361422777293766829 40021866510533541485162561)
        ·
          refine ⟨30016399882900156113871921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40021866510533541485162561 30016399882900156113871921)
          ·
            refine ⟨22512299912175117085403941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30016399882900156113871921 22512299912175117085403941)
            ·
              refine ⟨4221056233532834453513239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22512299912175117085403941 4221056233532834453513239)
              ·
                refine ⟨6331584350299251680269859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4221056233532834453513239 6331584350299251680269859)
                ·
                  refine ⟨9497376525448877520404789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6331584350299251680269859 9497376525448877520404789)
                  ·
                    refine ⟨890379049260832267537949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9497376525448877520404789 890379049260832267537949)
                    ·
                      rfl

theorem cell23_5202021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_5202021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202021 prefixEnd_5202021 := by exact prefixLift 5202021
  have htrace : WordTrace (prefixWord ++ tailWord_5202021) baseStart_5202021 baseEnd_5202021 := by
    simpa [prefixWord, tailWord_5202021, baseEnd_5202021] using wordTrace_append hprefix tailTrace_5202021
  have hstable : (prefixWord ++ tailWord_5202021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202021).length < 2 ^ (prefixWord ++ tailWord_5202021).sum := by decide
  have hdescent : baseEnd_5202021 < baseStart_5202021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202044 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_5202044 : Nat := 118140960795 + 5202044 * 2 ^ 59
def prefixEnd_5202044 : Nat := 4983230072969 + 3 ^ 40 * 5202044 * 2
def baseEnd_5202044 : Nat := 2671148957837550212626241

theorem tailTrace_5202044 : CollatzResearch.WordTrace tailWord_5202044 prefixEnd_5202044 2671148957837550212626241 := by
  unfold tailWord_5202044
  simp only [CollatzResearch.WordTrace]
  refine ⟨94867065982945250614058593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126489421310593667485411457 94867065982945250614058593)
  ·
    refine ⟨71150299487208937960543945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94867065982945250614058593 71150299487208937960543945)
    ·
      refine ⟨53362724615406703470407959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71150299487208937960543945 53362724615406703470407959)
      ·
        refine ⟨80044086923110055205611939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53362724615406703470407959 80044086923110055205611939)
        ·
          refine ⟨120066130384665082808417909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80044086923110055205611939 120066130384665082808417909)
          ·
            refine ⟨11256199723562351513289179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120066130384665082808417909 11256199723562351513289179)
            ·
              refine ⟨16884299585343527269933769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11256199723562351513289179 16884299585343527269933769)
              ·
                refine ⟨12663224689007645452450327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16884299585343527269933769 12663224689007645452450327)
                ·
                  refine ⟨18994837033511468178675491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12663224689007645452450327 18994837033511468178675491)
                  ·
                    refine ⟨28492255550267202268013237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18994837033511468178675491 28492255550267202268013237)
                    ·
                      refine ⟨2671148957837550212626241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28492255550267202268013237 2671148957837550212626241)
                      ·
                        rfl

theorem cell23_5202044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_5202044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202044 prefixEnd_5202044 := by exact prefixLift 5202044
  have htrace : WordTrace (prefixWord ++ tailWord_5202044) baseStart_5202044 baseEnd_5202044 := by
    simpa [prefixWord, tailWord_5202044, baseEnd_5202044] using wordTrace_append hprefix tailTrace_5202044
  have hstable : (prefixWord ++ tailWord_5202044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202044).length < 2 ^ (prefixWord ++ tailWord_5202044).sum := by decide
  have hdescent : baseEnd_5202044 < baseStart_5202044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202058 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_5202058 : Nat := 118140960795 + 5202058 * 2 ^ 59
def prefixEnd_5202058 : Nat := 4983230072969 + 3 ^ 40 * 5202058 * 2
def baseEnd_5202058 : Nat := 2671156146566713157851177

theorem tailTrace_5202058 : CollatzResearch.WordTrace tailWord_5202058 prefixEnd_5202058 2671156146566713157851177 := by
  unfold tailWord_5202058
  simp only [CollatzResearch.WordTrace]
  refine ⟨47433660646959945404781707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126489761725226521079417885 47433660646959945404781707)
  ·
    refine ⟨71150490970439918107172561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47433660646959945404781707 71150490970439918107172561)
    ·
      refine ⟨53362868227829938580379421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71150490970439918107172561 53362868227829938580379421)
      ·
        refine ⟨20011075585436226967642283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53362868227829938580379421 20011075585436226967642283)
        ·
          refine ⟨30016613378154340451463425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20011075585436226967642283 30016613378154340451463425)
          ·
            refine ⟨22512460033615755338597569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30016613378154340451463425 22512460033615755338597569)
            ·
              refine ⟨16884345025211816503948177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22512460033615755338597569 16884345025211816503948177)
              ·
                refine ⟨12663258768908862377961133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16884345025211816503948177 12663258768908862377961133)
                ·
                  refine ⟨4748722038340823391735425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12663258768908862377961133 4748722038340823391735425)
                  ·
                    refine ⟨3561541528755617543801569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4748722038340823391735425 3561541528755617543801569)
                    ·
                      refine ⟨2671156146566713157851177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561541528755617543801569 2671156146566713157851177)
                      ·
                        rfl

theorem cell23_5202058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_5202058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202058 prefixEnd_5202058 := by exact prefixLift 5202058
  have htrace : WordTrace (prefixWord ++ tailWord_5202058) baseStart_5202058 baseEnd_5202058 := by
    simpa [prefixWord, tailWord_5202058, baseEnd_5202058] using wordTrace_append hprefix tailTrace_5202058
  have hstable : (prefixWord ++ tailWord_5202058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202058).length < 2 ^ (prefixWord ++ tailWord_5202058).sum := by decide
  have hdescent : baseEnd_5202058 < baseStart_5202058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202078 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_5202078 : Nat := 118140960795 + 5202078 * 2 ^ 59
def prefixEnd_5202078 : Nat := 4983230072969 + 3 ^ 40 * 5202078 * 2
def baseEnd_5202078 : Nat := 2671166416179803079601085

theorem tailTrace_5202078 : CollatzResearch.WordTrace tailWord_5202078 prefixEnd_5202078 2671166416179803079601085 := by
  unfold tailWord_5202078
  simp only [CollatzResearch.WordTrace]
  refine ⟨23716921505970915629356861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126490248031844883356569925 23716921505970915629356861)
  ·
    refine ⟨8893845564739093361008823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23716921505970915629356861 8893845564739093361008823)
    ·
      refine ⟨13340768347108640041513235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8893845564739093361008823 13340768347108640041513235)
      ·
        refine ⟨20011152520662960062269853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13340768347108640041513235 20011152520662960062269853)
        ·
          refine ⟨7504182195248610023351195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20011152520662960062269853 7504182195248610023351195)
          ·
            refine ⟨11256273292872915035026793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7504182195248610023351195 11256273292872915035026793)
            ·
              refine ⟨8442204969654686276270095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11256273292872915035026793 8442204969654686276270095)
              ·
                refine ⟨12663307454482029414405143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8442204969654686276270095 12663307454482029414405143)
                ·
                  refine ⟨18994961181723044121607715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12663307454482029414405143 18994961181723044121607715)
                  ·
                    refine ⟨28492441772584566182411573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18994961181723044121607715 28492441772584566182411573)
                    ·
                      refine ⟨2671166416179803079601085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28492441772584566182411573 2671166416179803079601085)
                      ·
                        rfl

theorem cell23_5202078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_5202078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202078 prefixEnd_5202078 := by exact prefixLift 5202078
  have htrace : WordTrace (prefixWord ++ tailWord_5202078) baseStart_5202078 baseEnd_5202078 := by
    simpa [prefixWord, tailWord_5202078, baseEnd_5202078] using wordTrace_append hprefix tailTrace_5202078
  have hstable : (prefixWord ++ tailWord_5202078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202078).length < 2 ^ (prefixWord ++ tailWord_5202078).sum := by decide
  have hdescent : baseEnd_5202078 < baseStart_5202078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202107 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 1, 8]
def baseStart_5202107 : Nat := 118140960795 + 5202107 * 2 ^ 59
def prefixEnd_5202107 : Nat := 4983230072969 + 3 ^ 40 * 5202107 * 2
def baseEnd_5202107 : Nat := 890393769039594488712817

theorem tailTrace_5202107 : CollatzResearch.WordTrace tailWord_5202107 prefixEnd_5202107 890393769039594488712817 := by
  unfold tailWord_5202107
  simp only [CollatzResearch.WordTrace]
  refine ⟨189736429764662262987660575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126490953176441508658440383 189736429764662262987660575)
  ·
    refine ⟨284604644646993394481490863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189736429764662262987660575 284604644646993394481490863)
    ·
      refine ⟨426906966970490091722236295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284604644646993394481490863 426906966970490091722236295)
      ·
        refine ⟨640360450455735137583354443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426906966970490091722236295 640360450455735137583354443)
        ·
          refine ⟨960540675683602706375031665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640360450455735137583354443 960540675683602706375031665)
          ·
            refine ⟨720405506762702029781273749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960540675683602706375031665 720405506762702029781273749)
            ·
              refine ⟨33769008129501657645997207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 720405506762702029781273749 33769008129501657645997207)
              ·
                refine ⟨50653512194252486468995811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33769008129501657645997207 50653512194252486468995811)
                ·
                  refine ⟨75980268291378729703493717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50653512194252486468995811 75980268291378729703493717)
                  ·
                    refine ⟨890393769039594488712817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75980268291378729703493717 890393769039594488712817)
                    ·
                      rfl

theorem cell23_5202107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_5202107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202107 prefixEnd_5202107 := by exact prefixLift 5202107
  have htrace : WordTrace (prefixWord ++ tailWord_5202107) baseStart_5202107 baseEnd_5202107 := by
    simpa [prefixWord, tailWord_5202107, baseEnd_5202107] using wordTrace_append hprefix tailTrace_5202107
  have hstable : (prefixWord ++ tailWord_5202107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202107).length < 2 ^ (prefixWord ++ tailWord_5202107).sum := by decide
  have hdescent : baseEnd_5202107 < baseStart_5202107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202144 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_5202144 : Nat := 118140960795 + 5202144 * 2 ^ 59
def prefixEnd_5202144 : Nat := 4983230072969 + 3 ^ 40 * 5202144 * 2
def baseEnd_5202144 : Nat := 2671200305902999821375781

theorem tailTrace_5202144 : CollatzResearch.WordTrace tailWord_5202144 prefixEnd_5202144 2671200305902999821375781 := by
  unfold tailWord_5202144
  simp only [CollatzResearch.WordTrace]
  refine ⟨94868889632764109153378743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126491852843685478871171657 94868889632764109153378743)
  ·
    refine ⟨142303334449146163730068115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94868889632764109153378743 142303334449146163730068115)
    ·
      refine ⟨213455001673719245595102173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142303334449146163730068115 213455001673719245595102173)
      ·
        refine ⟨80045625627644717098163315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213455001673719245595102173 80045625627644717098163315)
        ·
          refine ⟨120068438441467075647244973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80045625627644717098163315 120068438441467075647244973)
          ·
            refine ⟨45025664415550153367716865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120068438441467075647244973 45025664415550153367716865)
            ·
              refine ⟨33769248311662615025787649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45025664415550153367716865 33769248311662615025787649)
              ·
                refine ⟨25326936233746961269340737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33769248311662615025787649 25326936233746961269340737)
                ·
                  refine ⟨18995202175310220952005553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25326936233746961269340737 18995202175310220952005553)
                  ·
                    refine ⟨14246401631482665714004165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18995202175310220952005553 14246401631482665714004165)
                    ·
                      refine ⟨2671200305902999821375781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14246401631482665714004165 2671200305902999821375781)
                      ·
                        rfl

theorem cell23_5202144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_5202144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202144 prefixEnd_5202144 := by exact prefixLift 5202144
  have htrace : WordTrace (prefixWord ++ tailWord_5202144) baseStart_5202144 baseEnd_5202144 := by
    simpa [prefixWord, tailWord_5202144, baseEnd_5202144] using wordTrace_append hprefix tailTrace_5202144
  have hstable : (prefixWord ++ tailWord_5202144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202144).length < 2 ^ (prefixWord ++ tailWord_5202144).sum := by decide
  have hdescent : baseEnd_5202144 < baseStart_5202144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202151 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5202151 : Nat := 118140960795 + 5202151 * 2 ^ 59
def prefixEnd_5202151 : Nat := 4983230072969 + 3 ^ 40 * 5202151 * 2
def baseEnd_5202151 : Nat := 2671203900267581293988249

theorem tailTrace_5202151 : CollatzResearch.WordTrace tailWord_5202151 prefixEnd_5202151 2671203900267581293988249 := by
  unfold tailWord_5202151
  simp only [CollatzResearch.WordTrace]
  refine ⟨189738034576502858502262307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126492023051001905668174871 189738034576502858502262307)
  ·
    refine ⟨284607051864754287753393461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189738034576502858502262307 284607051864754287753393461)
    ·
      refine ⟨26681911112320714476880637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 284607051864754287753393461 26681911112320714476880637)
      ·
        refine ⟨10005716667120267928830239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26681911112320714476880637 10005716667120267928830239)
        ·
          refine ⟨15008575000680401893245359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10005716667120267928830239 15008575000680401893245359)
          ·
            refine ⟨22512862501020602839868039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15008575000680401893245359 22512862501020602839868039)
            ·
              refine ⟨33769293751530904259802059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22512862501020602839868039 33769293751530904259802059)
              ·
                refine ⟨50653940627296356389703089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33769293751530904259802059 50653940627296356389703089)
                ·
                  refine ⟨37990455470472267292277317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50653940627296356389703089 37990455470472267292277317)
                  ·
                    refine ⟨7123210400713550117301997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37990455470472267292277317 7123210400713550117301997)
                    ·
                      refine ⟨2671203900267581293988249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7123210400713550117301997 2671203900267581293988249)
                      ·
                        rfl

theorem cell23_5202151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5202151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202151 prefixEnd_5202151 := by exact prefixLift 5202151
  have htrace : WordTrace (prefixWord ++ tailWord_5202151) baseStart_5202151 baseEnd_5202151 := by
    simpa [prefixWord, tailWord_5202151, baseEnd_5202151] using wordTrace_append hprefix tailTrace_5202151
  have hstable : (prefixWord ++ tailWord_5202151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202151).length < 2 ^ (prefixWord ++ tailWord_5202151).sum := by decide
  have hdescent : baseEnd_5202151 < baseStart_5202151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202154 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 7]
def baseStart_5202154 : Nat := 118140960795 + 5202154 * 2 ^ 59
def prefixEnd_5202154 : Nat := 4983230072969 + 3 ^ 40 * 5202154 * 2
def baseEnd_5202154 : Nat := 296800604523282753583415

theorem tailTrace_5202154 : CollatzResearch.WordTrace tailWord_5202154 prefixEnd_5202154 296800604523282753583415 := by
  unfold tailWord_5202154
  simp only [CollatzResearch.WordTrace]
  refine ⟨47434535998872997503655379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126492095996994660009747677 47434535998872997503655379)
  ·
    refine ⟨71151803998309496255483069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47434535998872997503655379 71151803998309496255483069)
    ·
      refine ⟨26681926499366061095806151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71151803998309496255483069 26681926499366061095806151)
      ·
        refine ⟨40022889749049091643709227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26681926499366061095806151 40022889749049091643709227)
        ·
          refine ⟨60034334623573637465563841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40022889749049091643709227 60034334623573637465563841)
          ·
            refine ⟨45025750967680228099172881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60034334623573637465563841 45025750967680228099172881)
            ·
              refine ⟨33769313225760171074379661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45025750967680228099172881 33769313225760171074379661)
              ·
                refine ⟨12663492459660064152892373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33769313225760171074379661 12663492459660064152892373)
                ·
                  refine ⟨296800604523282753583415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12663492459660064152892373 296800604523282753583415)
                  ·
                    rfl

theorem cell23_5202154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_5202154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202154 prefixEnd_5202154 := by exact prefixLift 5202154
  have htrace : WordTrace (prefixWord ++ tailWord_5202154) baseStart_5202154 baseEnd_5202154 := by
    simpa [prefixWord, tailWord_5202154, baseEnd_5202154] using wordTrace_append hprefix tailTrace_5202154
  have hstable : (prefixWord ++ tailWord_5202154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202154).length < 2 ^ (prefixWord ++ tailWord_5202154).sum := by decide
  have hdescent : baseEnd_5202154 < baseStart_5202154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202264 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_5202264 : Nat := 118140960795 + 5202264 * 2 ^ 59
def prefixEnd_5202264 : Nat := 4983230072969 + 3 ^ 40 * 5202264 * 2
def baseEnd_5202264 : Nat := 2671261923581539351875229

theorem tailTrace_5202264 : CollatzResearch.WordTrace tailWord_5202264 prefixEnd_5202264 2671261923581539351875229 := by
  unfold tailWord_5202264
  simp only [CollatzResearch.WordTrace]
  refine ⟨94871078012546739400562923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126494770683395652534083897 94871078012546739400562923)
  ·
    refine ⟨142306617018820109100844385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94871078012546739400562923 142306617018820109100844385)
    ·
      refine ⟨106729962764115081825633289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142306617018820109100844385 106729962764115081825633289)
      ·
        refine ⟨80047472073086311369224967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106729962764115081825633289 80047472073086311369224967)
        ·
          refine ⟨120071208109629467053837451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80047472073086311369224967 120071208109629467053837451)
          ·
            refine ⟨180106812164444200580756177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120071208109629467053837451 180106812164444200580756177)
            ·
              refine ⟨135080109123333150435567133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180106812164444200580756177 135080109123333150435567133)
              ·
                refine ⟨50655040921249931413337675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135080109123333150435567133 50655040921249931413337675)
                ·
                  refine ⟨75982561381874897120006513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50655040921249931413337675 75982561381874897120006513)
                  ·
                    refine ⟨56986921036406172840004885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75982561381874897120006513 56986921036406172840004885)
                    ·
                      refine ⟨2671261923581539351875229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56986921036406172840004885 2671261923581539351875229)
                      ·
                        rfl

theorem cell23_5202264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_5202264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202264 prefixEnd_5202264 := by exact prefixLift 5202264
  have htrace : WordTrace (prefixWord ++ tailWord_5202264) baseStart_5202264 baseEnd_5202264 := by
    simpa [prefixWord, tailWord_5202264, baseEnd_5202264] using wordTrace_append hprefix tailTrace_5202264
  have hstable : (prefixWord ++ tailWord_5202264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202264).length < 2 ^ (prefixWord ++ tailWord_5202264).sum := by decide
  have hdescent : baseEnd_5202264 < baseStart_5202264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202328 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5202328 : Nat := 118140960795 + 5202328 * 2 ^ 59
def prefixEnd_5202328 : Nat := 4983230072969 + 3 ^ 40 * 5202328 * 2
def baseEnd_5202328 : Nat := 2671294786343427101474935

theorem tailTrace_5202328 : CollatzResearch.WordTrace tailWord_5202328 prefixEnd_5202328 2671294786343427101474935 := by
  unfold tailWord_5202328
  simp only [CollatzResearch.WordTrace]
  refine ⟨94872245148430808865727819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126496326864574411820970425 94872245148430808865727819)
  ·
    refine ⟨142308367722646213298591729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94872245148430808865727819 142308367722646213298591729)
    ·
      refine ⟨106731275791984659973943797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142308367722646213298591729 106731275791984659973943797)
      ·
        refine ⟨10006057105498561872557231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106731275791984659973943797 10006057105498561872557231)
        ·
          refine ⟨15009085658247842808835847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10006057105498561872557231 15009085658247842808835847)
          ·
            refine ⟨22513628487371764213253771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15009085658247842808835847 22513628487371764213253771)
            ·
              refine ⟨33770442731057646319880657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22513628487371764213253771 33770442731057646319880657)
              ·
                refine ⟨25327832048293234739910493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33770442731057646319880657 25327832048293234739910493)
                ·
                  refine ⟨9497937018109963027466435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25327832048293234739910493 9497937018109963027466435)
                  ·
                    refine ⟨14246905527164944541199653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9497937018109963027466435 14246905527164944541199653)
                    ·
                      refine ⟨2671294786343427101474935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14246905527164944541199653 2671294786343427101474935)
                      ·
                        rfl

theorem cell23_5202328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5202328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202328 prefixEnd_5202328 := by exact prefixLift 5202328
  have htrace : WordTrace (prefixWord ++ tailWord_5202328) baseStart_5202328 baseEnd_5202328 := by
    simpa [prefixWord, tailWord_5202328, baseEnd_5202328] using wordTrace_append hprefix tailTrace_5202328
  have hstable : (prefixWord ++ tailWord_5202328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202328).length < 2 ^ (prefixWord ++ tailWord_5202328).sum := by decide
  have hdescent : baseEnd_5202328 < baseStart_5202328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202338 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_5202338 : Nat := 118140960795 + 5202338 * 2 ^ 59
def prefixEnd_5202338 : Nat := 4983230072969 + 3 ^ 40 * 5202338 * 2
def baseEnd_5202338 : Nat := 890433307049990687449963

theorem tailTrace_5202338 : CollatzResearch.WordTrace tailWord_5202338 prefixEnd_5202338 890433307049990687449963 := by
  unfold tailWord_5202338
  simp only [CollatzResearch.WordTrace]
  refine ⟨47436213756706347359829917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126496570017883592959546445 47436213756706347359829917)
  ·
    refine ⟨17788580158764880259936219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47436213756706347359829917 17788580158764880259936219)
    ·
      refine ⟨26682870238147320389904329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17788580158764880259936219 26682870238147320389904329)
      ·
        refine ⟨20012152678610490292428247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26682870238147320389904329 20012152678610490292428247)
        ·
          refine ⟨30018229017915735438642371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20012152678610490292428247 30018229017915735438642371)
          ·
            refine ⟨45027343526873603157963557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30018229017915735438642371 45027343526873603157963557)
            ·
              refine ⟨8442626911288800592118167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45027343526873603157963557 8442626911288800592118167)
              ·
                refine ⟨12663940366933200888177251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8442626911288800592118167 12663940366933200888177251)
                ·
                  refine ⟨18995910550399801332265877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12663940366933200888177251 18995910550399801332265877)
                  ·
                    refine ⟨890433307049990687449963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18995910550399801332265877 890433307049990687449963)
                    ·
                      rfl

theorem cell23_5202338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_5202338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202338 prefixEnd_5202338 := by exact prefixLift 5202338
  have htrace : WordTrace (prefixWord ++ tailWord_5202338) baseStart_5202338 baseEnd_5202338 := by
    simpa [prefixWord, tailWord_5202338, baseEnd_5202338] using wordTrace_append hprefix tailTrace_5202338
  have hstable : (prefixWord ++ tailWord_5202338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202338).length < 2 ^ (prefixWord ++ tailWord_5202338).sum := by decide
  have hdescent : baseEnd_5202338 < baseStart_5202338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202348 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_5202348 : Nat := 118140960795 + 5202348 * 2 ^ 59
def prefixEnd_5202348 : Nat := 4983230072969 + 3 ^ 40 * 5202348 * 2
def baseEnd_5202348 : Nat := 2671305055956517023224843

theorem tailTrace_5202348 : CollatzResearch.WordTrace tailWord_5202348 prefixEnd_5202348 2671305055956517023224843 := by
  unfold tailWord_5202348
  simp only [CollatzResearch.WordTrace]
  refine ⟨94872609878394580573591849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126496813171192774098122465 94872609878394580573591849)
  ·
    refine ⟨71154457408795935430193887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94872609878394580573591849 71154457408795935430193887)
    ·
      refine ⟨106731686113193903145290831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71154457408795935430193887 106731686113193903145290831)
      ·
        refine ⟨160097529169790854717936247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106731686113193903145290831 160097529169790854717936247)
        ·
          refine ⟨240146293754686282076904371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160097529169790854717936247 240146293754686282076904371)
          ·
            refine ⟨360219440632029423115356557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240146293754686282076904371 360219440632029423115356557)
            ·
              refine ⟨135082290237011033668258709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360219440632029423115356557 135082290237011033668258709)
              ·
                refine ⟨6331982354859892203199627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135082290237011033668258709 6331982354859892203199627)
                ·
                  refine ⟨9497973532289838304799441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6331982354859892203199627 9497973532289838304799441)
                  ·
                    refine ⟨7123480149217378728599581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9497973532289838304799441 7123480149217378728599581)
                    ·
                      refine ⟨2671305055956517023224843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7123480149217378728599581 2671305055956517023224843)
                      ·
                        rfl

theorem cell23_5202348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_5202348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202348 prefixEnd_5202348 := by exact prefixLift 5202348
  have htrace : WordTrace (prefixWord ++ tailWord_5202348) baseStart_5202348 baseEnd_5202348 := by
    simpa [prefixWord, tailWord_5202348, baseEnd_5202348] using wordTrace_append hprefix tailTrace_5202348
  have hstable : (prefixWord ++ tailWord_5202348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202348).length < 2 ^ (prefixWord ++ tailWord_5202348).sum := by decide
  have hdescent : baseEnd_5202348 < baseStart_5202348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202349 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5202349 : Nat := 118140960795 + 5202349 * 2 ^ 59
def prefixEnd_5202349 : Nat := 4983230072969 + 3 ^ 40 * 5202349 * 2
def baseEnd_5202349 : Nat := 2671305569437171519312339

theorem tailTrace_5202349 : CollatzResearch.WordTrace tailWord_5202349 prefixEnd_5202349 2671305569437171519312339 := by
  unfold tailWord_5202349
  simp only [CollatzResearch.WordTrace]
  refine ⟨189745256229785538317970101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126496837486523692211980067 189745256229785538317970101)
  ·
    refine ⟨17788617771542394217309697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189745256229785538317970101 17788617771542394217309697)
    ·
      refine ⟨13341463328656795662982273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17788617771542394217309697 13341463328656795662982273)
      ·
        refine ⟨10006097496492596747236705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13341463328656795662982273 10006097496492596747236705)
        ·
          refine ⟨7504573122369447560427529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10006097496492596747236705 7504573122369447560427529)
          ·
            refine ⟨5628429841777085670320647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7504573122369447560427529 5628429841777085670320647)
            ·
              refine ⟨8442644762665628505480971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5628429841777085670320647 8442644762665628505480971)
              ·
                refine ⟨12663967143998442758221457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8442644762665628505480971 12663967143998442758221457)
                ·
                  refine ⟨9497975357998832068666093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12663967143998442758221457 9497975357998832068666093)
                  ·
                    refine ⟨3561740759249562025749785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9497975357998832068666093 3561740759249562025749785)
                    ·
                      refine ⟨2671305569437171519312339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561740759249562025749785 2671305569437171519312339)
                      ·
                        rfl

theorem cell23_5202349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5202349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202349 prefixEnd_5202349 := by exact prefixLift 5202349
  have htrace : WordTrace (prefixWord ++ tailWord_5202349) baseStart_5202349 baseEnd_5202349 := by
    simpa [prefixWord, tailWord_5202349, baseEnd_5202349] using wordTrace_append hprefix tailTrace_5202349
  have hstable : (prefixWord ++ tailWord_5202349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202349).length < 2 ^ (prefixWord ++ tailWord_5202349).sum := by decide
  have hdescent : baseEnd_5202349 < baseStart_5202349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202365 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_5202365 : Nat := 118140960795 + 5202365 * 2 ^ 59
def prefixEnd_5202365 : Nat := 4983230072969 + 3 ^ 40 * 5202365 * 2
def baseEnd_5202365 : Nat := 2671313785127643456712265

theorem tailTrace_5202365 : CollatzResearch.WordTrace tailWord_5202365 prefixEnd_5202365 2671313785127643456712265 := by
  unfold tailWord_5202365
  simp only [CollatzResearch.WordTrace]
  refine ⟨189745839797727573050552549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126497226531818382033701699 189745839797727573050552549)
  ·
    refine ⟨35577344962073919946978603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189745839797727573050552549 35577344962073919946978603)
    ·
      refine ⟨53366017443110879920467905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35577344962073919946978603 53366017443110879920467905)
      ·
        refine ⟨40024513082333159940350929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53366017443110879920467905 40024513082333159940350929)
        ·
          refine ⟨30018384811749869955263197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40024513082333159940350929 30018384811749869955263197)
          ·
            refine ⟨11256894304406201233223699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30018384811749869955263197 11256894304406201233223699)
            ·
              refine ⟨16885341456609301849835549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11256894304406201233223699 16885341456609301849835549)
              ·
                refine ⟨6332003046228488193688331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16885341456609301849835549 6332003046228488193688331)
                ·
                  refine ⟨9498004569342732290532497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6332003046228488193688331 9498004569342732290532497)
                  ·
                    refine ⟨7123503427007049217899373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9498004569342732290532497 7123503427007049217899373)
                    ·
                      refine ⟨2671313785127643456712265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7123503427007049217899373 2671313785127643456712265)
                      ·
                        rfl

theorem cell23_5202365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_5202365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202365 prefixEnd_5202365 := by exact prefixLift 5202365
  have htrace : WordTrace (prefixWord ++ tailWord_5202365) baseStart_5202365 baseEnd_5202365 := by
    simpa [prefixWord, tailWord_5202365, baseEnd_5202365] using wordTrace_append hprefix tailTrace_5202365
  have hstable : (prefixWord ++ tailWord_5202365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202365).length < 2 ^ (prefixWord ++ tailWord_5202365).sum := by decide
  have hdescent : baseEnd_5202365 < baseStart_5202365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202422 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_5202422 : Nat := 118140960795 + 5202422 * 2 ^ 59
def prefixEnd_5202422 : Nat := 4983230072969 + 3 ^ 40 * 5202422 * 2
def baseEnd_5202422 : Nat := 2671343053524949733699503

theorem tailTrace_5202422 : CollatzResearch.WordTrace tailWord_5202422 prefixEnd_5202422 2671343053524949733699503 := by
  unfold tailWord_5202422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11859244922407566986586095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126498612505680714523585013 11859244922407566986586095)
  ·
    refine ⟨17788867383611350479879143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11859244922407566986586095 17788867383611350479879143)
    ·
      refine ⟨26683301075417025719818715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17788867383611350479879143 26683301075417025719818715)
      ·
        refine ⟨40024951613125538579728073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26683301075417025719818715 40024951613125538579728073)
        ·
          refine ⟨30018713709844153934796055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40024951613125538579728073 30018713709844153934796055)
          ·
            refine ⟨45028070564766230902194083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30018713709844153934796055 45028070564766230902194083)
            ·
              refine ⟨67542105847149346353291125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45028070564766230902194083 67542105847149346353291125)
              ·
                refine ⟨6332072423170251220621043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67542105847149346353291125 6332072423170251220621043)
                ·
                  refine ⟨9498108634755376830931565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6332072423170251220621043 9498108634755376830931565)
                  ·
                    refine ⟨3561790738033266311599337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9498108634755376830931565 3561790738033266311599337)
                    ·
                      refine ⟨2671343053524949733699503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561790738033266311599337 2671343053524949733699503)
                      ·
                        rfl

theorem cell23_5202422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_5202422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202422 prefixEnd_5202422 := by exact prefixLift 5202422
  have htrace : WordTrace (prefixWord ++ tailWord_5202422) baseStart_5202422 baseEnd_5202422 := by
    simpa [prefixWord, tailWord_5202422, baseEnd_5202422] using wordTrace_append hprefix tailTrace_5202422
  have hstable : (prefixWord ++ tailWord_5202422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202422).length < 2 ^ (prefixWord ++ tailWord_5202422).sum := by decide
  have hdescent : baseEnd_5202422 < baseStart_5202422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202435 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 4, 2, 2]
def baseStart_5202435 : Nat := 118140960795 + 5202435 * 2 ^ 59
def prefixEnd_5202435 : Nat := 4983230072969 + 3 ^ 40 * 5202435 * 2
def baseEnd_5202435 : Nat := 2671349728773458182836943

theorem tailTrace_5202435 : CollatzResearch.WordTrace tailWord_5202435 prefixEnd_5202435 2671349728773458182836943 := by
  unfold tailWord_5202435
  simp only [CollatzResearch.WordTrace]
  refine ⟨189748392907473975005600759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126498928604982650003733839 189748392907473975005600759)
  ·
    refine ⟨284622589361210962508401139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189748392907473975005600759 284622589361210962508401139)
    ·
      refine ⟨426933884041816443762601709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284622589361210962508401139 426933884041816443762601709)
      ·
        refine ⟨160100206515681166410975641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426933884041816443762601709 160100206515681166410975641)
        ·
          refine ⟨120075154886760874808231731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160100206515681166410975641 120075154886760874808231731)
          ·
            refine ⟨180112732330141312212347597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120075154886760874808231731 180112732330141312212347597)
            ·
              refine ⟨67542274623802992079630349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180112732330141312212347597 67542274623802992079630349)
              ·
                refine ⟨25328352983926122029861381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67542274623802992079630349 25328352983926122029861381)
                ·
                  refine ⟨4749066184486147880599009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25328352983926122029861381 4749066184486147880599009)
                  ·
                    refine ⟨3561799638364610910449257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4749066184486147880599009 3561799638364610910449257)
                    ·
                      refine ⟨2671349728773458182836943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561799638364610910449257 2671349728773458182836943)
                      ·
                        rfl

theorem cell23_5202435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_5202435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202435 prefixEnd_5202435 := by exact prefixLift 5202435
  have htrace : WordTrace (prefixWord ++ tailWord_5202435) baseStart_5202435 baseEnd_5202435 := by
    simpa [prefixWord, tailWord_5202435, baseEnd_5202435] using wordTrace_append hprefix tailTrace_5202435
  have hstable : (prefixWord ++ tailWord_5202435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202435).length < 2 ^ (prefixWord ++ tailWord_5202435).sum := by decide
  have hdescent : baseEnd_5202435 < baseStart_5202435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202441 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 7]
def baseStart_5202441 : Nat := 118140960795 + 5202441 * 2 ^ 59
def prefixEnd_5202441 : Nat := 4983230072969 + 3 ^ 40 * 5202441 * 2
def baseEnd_5202441 : Nat := 296816978850820573262435

theorem tailTrace_5202441 : CollatzResearch.WordTrace tailWord_5202441 prefixEnd_5202441 296816978850820573262435 := by
  unfold tailWord_5202441
  simp only [CollatzResearch.WordTrace]
  refine ⟨189748611745452238030319177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126499074496968158686879451 189748611745452238030319177)
  ·
    refine ⟨142311458809089178522739383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189748611745452238030319177 142311458809089178522739383)
    ·
      refine ⟨213467188213633767784109075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142311458809089178522739383 213467188213633767784109075)
      ·
        refine ⟨320200782320450651676163613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213467188213633767784109075 320200782320450651676163613)
        ·
          refine ⟨120075293370168994378561355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320200782320450651676163613 120075293370168994378561355)
          ·
            refine ⟨180112940055253491567842033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120075293370168994378561355 180112940055253491567842033)
            ·
              refine ⟨135084705041440118675881525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180112940055253491567842033 135084705041440118675881525)
              ·
                refine ⟨12664191097635011125863893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135084705041440118675881525 12664191097635011125863893)
                ·
                  refine ⟨296816978850820573262435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12664191097635011125863893 296816978850820573262435)
                  ·
                    rfl

theorem cell23_5202441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_5202441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202441 prefixEnd_5202441 := by exact prefixLift 5202441
  have htrace : WordTrace (prefixWord ++ tailWord_5202441) baseStart_5202441 baseEnd_5202441 := by
    simpa [prefixWord, tailWord_5202441, baseEnd_5202441] using wordTrace_append hprefix tailTrace_5202441
  have hstable : (prefixWord ++ tailWord_5202441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202441).length < 2 ^ (prefixWord ++ tailWord_5202441).sum := by decide
  have hdescent : baseEnd_5202441 < baseStart_5202441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202486 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_5202486 : Nat := 118140960795 + 5202486 * 2 ^ 59
def prefixEnd_5202486 : Nat := 4983230072969 + 3 ^ 40 * 5202486 * 2
def baseEnd_5202486 : Nat := 2671375916286837483299209

theorem tailTrace_5202486 : CollatzResearch.WordTrace tailWord_5202486 prefixEnd_5202486 2671375916286837483299209 := by
  unfold tailWord_5202486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11859390814393075669731707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126500168686859473810471541 11859390814393075669731707)
  ·
    refine ⟨17789086221589613504597561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11859390814393075669731707 17789086221589613504597561)
    ·
      refine ⟨13341814666192210128448171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17789086221589613504597561 13341814666192210128448171)
      ·
        refine ⟨20012721999288315192672257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13341814666192210128448171 20012721999288315192672257)
        ·
          refine ⟨15009541499466236394504193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20012721999288315192672257 15009541499466236394504193)
          ·
            refine ⟨11257156124599677295878145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15009541499466236394504193 11257156124599677295878145)
            ·
              refine ⟨8442867093449757971908609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11257156124599677295878145 8442867093449757971908609)
              ·
                refine ⟨6332150320087318478931457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8442867093449757971908609 6332150320087318478931457)
                ·
                  refine ⟨4749112740065488859198593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6332150320087318478931457 4749112740065488859198593)
                  ·
                    refine ⟨3561834555049116644398945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4749112740065488859198593 3561834555049116644398945)
                    ·
                      refine ⟨2671375916286837483299209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561834555049116644398945 2671375916286837483299209)
                      ·
                        rfl

theorem cell23_5202486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_5202486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202486 prefixEnd_5202486 := by exact prefixLift 5202486
  have htrace : WordTrace (prefixWord ++ tailWord_5202486) baseStart_5202486 baseEnd_5202486 := by
    simpa [prefixWord, tailWord_5202486, baseEnd_5202486] using wordTrace_append hprefix tailTrace_5202486
  have hstable : (prefixWord ++ tailWord_5202486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202486).length < 2 ^ (prefixWord ++ tailWord_5202486).sum := by decide
  have hdescent : baseEnd_5202486 < baseStart_5202486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202488 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 2, 5]
def baseStart_5202488 : Nat := 118140960795 + 5202488 * 2 ^ 59
def prefixEnd_5202488 : Nat := 4983230072969 + 3 ^ 40 * 5202488 * 2
def baseEnd_5202488 : Nat := 890458981082715491824733

theorem tailTrace_5202488 : CollatzResearch.WordTrace tailWord_5202488 prefixEnd_5202488 890458981082715491824733 := by
  unfold tailWord_5202488
  simp only [CollatzResearch.WordTrace]
  refine ⟨94875162988140982528640059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126500217317521310038186745 94875162988140982528640059)
  ·
    refine ⟨142312744482211473792960089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94875162988140982528640059 142312744482211473792960089)
    ·
      refine ⟨106734558361658605344720067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142312744482211473792960089 106734558361658605344720067)
      ·
        refine ⟨160101837542487908017080101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106734558361658605344720067 160101837542487908017080101)
        ·
          refine ⟨30019094539216482753202519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160101837542487908017080101 30019094539216482753202519)
          ·
            refine ⟨45028641808824724129803779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30019094539216482753202519 45028641808824724129803779)
            ·
              refine ⟨67542962713237086194705669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45028641808824724129803779 67542962713237086194705669)
              ·
                refine ⟨12664305508731953661507313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67542962713237086194705669 12664305508731953661507313)
                ·
                  refine ⟨9498229131548965246130485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12664305508731953661507313 9498229131548965246130485)
                  ·
                    refine ⟨890458981082715491824733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9498229131548965246130485 890458981082715491824733)
                    ·
                      rfl

theorem cell23_5202488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_5202488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202488 prefixEnd_5202488 := by exact prefixLift 5202488
  have htrace : WordTrace (prefixWord ++ tailWord_5202488) baseStart_5202488 baseEnd_5202488 := by
    simpa [prefixWord, tailWord_5202488, baseEnd_5202488] using wordTrace_append hprefix tailTrace_5202488
  have hstable : (prefixWord ++ tailWord_5202488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202488).length < 2 ^ (prefixWord ++ tailWord_5202488).sum := by decide
  have hdescent : baseEnd_5202488 < baseStart_5202488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202492 : List Nat := [2, 2, 2, 2, 3, 1, 4, 2, 5]
def baseStart_5202492 : Nat := 118140960795 + 5202492 * 2 ^ 59
def prefixEnd_5202492 : Nat := 4983230072969 + 3 ^ 40 * 5202492 * 2
def baseEnd_5202492 : Nat := 296819888574529384424909

theorem tailTrace_5202492 : CollatzResearch.WordTrace tailWord_5202492 prefixEnd_5202492 296819888574529384424909 := by
  unfold tailWord_5202492
  simp only [CollatzResearch.WordTrace]
  refine ⟨94875235934133736870212865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126500314578844982493617153 94875235934133736870212865)
  ·
    refine ⟨71156426950600302652659649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94875235934133736870212865 71156426950600302652659649)
    ·
      refine ⟨53367320212950226989494737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71156426950600302652659649 53367320212950226989494737)
      ·
        refine ⟨40025490159712670242121053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53367320212950226989494737 40025490159712670242121053)
        ·
          refine ⟨15009558809892251340795395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40025490159712670242121053 15009558809892251340795395)
          ·
            refine ⟨22514338214838377011193093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15009558809892251340795395 22514338214838377011193093)
            ·
              refine ⟨4221438415282195689598705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22514338214838377011193093 4221438415282195689598705)
              ·
                refine ⟨3166078811461646767199029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4221438415282195689598705 3166078811461646767199029)
                ·
                  refine ⟨296819888574529384424909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3166078811461646767199029 296819888574529384424909)
                  ·
                    rfl

theorem cell23_5202492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_5202492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202492 prefixEnd_5202492 := by exact prefixLift 5202492
  have htrace : WordTrace (prefixWord ++ tailWord_5202492) baseStart_5202492 baseEnd_5202492 := by
    simpa [prefixWord, tailWord_5202492, baseEnd_5202492] using wordTrace_append hprefix tailTrace_5202492
  have hstable : (prefixWord ++ tailWord_5202492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202492).length < 2 ^ (prefixWord ++ tailWord_5202492).sum := by decide
  have hdescent : baseEnd_5202492 < baseStart_5202492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202502 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5202502 : Nat := 118140960795 + 5202502 * 2 ^ 59
def prefixEnd_5202502 : Nat := 4983230072969 + 3 ^ 40 * 5202502 * 2
def baseEnd_5202502 : Nat := 2671384131977309420699135

theorem tailTrace_5202502 : CollatzResearch.WordTrace tailWord_5202502 prefixEnd_5202502 2671384131977309420699135 := by
  unfold tailWord_5202502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929713643694726420259055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126500557732154163632193173 5929713643694726420259055)
  ·
    refine ⟨8894570465542089630388583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5929713643694726420259055 8894570465542089630388583)
    ·
      refine ⟨13341855698313134445582875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8894570465542089630388583 13341855698313134445582875)
      ·
        refine ⟨20012783547469701668374313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13341855698313134445582875 20012783547469701668374313)
        ·
          refine ⟨15009587660602276251280735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20012783547469701668374313 15009587660602276251280735)
          ·
            refine ⟨22514381490903414376921103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15009587660602276251280735 22514381490903414376921103)
            ·
              refine ⟨33771572236355121565381655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22514381490903414376921103 33771572236355121565381655)
              ·
                refine ⟨50657358354532682348072483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33771572236355121565381655 50657358354532682348072483)
                ·
                  refine ⟨75986037531799023522108725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50657358354532682348072483 75986037531799023522108725)
                  ·
                    refine ⟨7123691018606158455197693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75986037531799023522108725 7123691018606158455197693)
                    ·
                      refine ⟨2671384131977309420699135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7123691018606158455197693 2671384131977309420699135)
                      ·
                        rfl

theorem cell23_5202502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5202502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202502 prefixEnd_5202502 := by exact prefixLift 5202502
  have htrace : WordTrace (prefixWord ++ tailWord_5202502) baseStart_5202502 baseEnd_5202502 := by
    simpa [prefixWord, tailWord_5202502, baseEnd_5202502] using wordTrace_append hprefix tailTrace_5202502
  have hstable : (prefixWord ++ tailWord_5202502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202502).length < 2 ^ (prefixWord ++ tailWord_5202502).sum := by decide
  have hdescent : baseEnd_5202502 < baseStart_5202502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202508 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5202508 : Nat := 118140960795 + 5202508 * 2 ^ 59
def prefixEnd_5202508 : Nat := 4983230072969 + 3 ^ 40 * 5202508 * 2
def baseEnd_5202508 : Nat := 2671387212861236397224107

theorem tailTrace_5202508 : CollatzResearch.WordTrace tailWord_5202508 prefixEnd_5202508 2671387212861236397224107 := by
  unfold tailWord_5202508
  simp only [CollatzResearch.WordTrace]
  refine ⟨94875527718104754236504089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126500703624139672315338785 94875527718104754236504089)
  ·
    refine ⟨71156645788578565677378067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94875527718104754236504089 71156645788578565677378067)
    ·
      refine ⟨106734968682867848516067101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71156645788578565677378067 106734968682867848516067101)
      ·
        refine ⟨40025613256075443193525163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106734968682867848516067101 40025613256075443193525163)
        ·
          refine ⟨60038419884113164790287745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40025613256075443193525163 60038419884113164790287745)
          ·
            refine ⟨45028814913084873592715809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60038419884113164790287745 45028814913084873592715809)
            ·
              refine ⟨33771611184813655194536857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45028814913084873592715809 33771611184813655194536857)
              ·
                refine ⟨25328708388610241395902643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33771611184813655194536857 25328708388610241395902643)
                ·
                  refine ⟨37993062582915362093853965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25328708388610241395902643 37993062582915362093853965)
                  ·
                    refine ⟨14247398468593260785195237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37993062582915362093853965 14247398468593260785195237)
                    ·
                      refine ⟨2671387212861236397224107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14247398468593260785195237 2671387212861236397224107)
                      ·
                        rfl

theorem cell23_5202508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5202508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202508 prefixEnd_5202508 := by exact prefixLift 5202508
  have htrace : WordTrace (prefixWord ++ tailWord_5202508) baseStart_5202508 baseEnd_5202508 := by
    simpa [prefixWord, tailWord_5202508, baseEnd_5202508] using wordTrace_append hprefix tailTrace_5202508
  have hstable : (prefixWord ++ tailWord_5202508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202508).length < 2 ^ (prefixWord ++ tailWord_5202508).sum := by decide
  have hdescent : baseEnd_5202508 < baseStart_5202508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202538 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5202538 : Nat := 118140960795 + 5202538 * 2 ^ 59
def prefixEnd_5202538 : Nat := 4983230072969 + 3 ^ 40 * 5202538 * 2
def baseEnd_5202538 : Nat := 2671402617280871279848969

theorem tailTrace_5202538 : CollatzResearch.WordTrace tailWord_5202538 prefixEnd_5202538 2671402617280871279848969 := by
  unfold tailWord_5202538
  simp only [CollatzResearch.WordTrace]
  refine ⟨47438037406525205899150067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126501433084067215731066845 47438037406525205899150067)
  ·
    refine ⟨71157056109787808848725101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47438037406525205899150067 71157056109787808848725101)
    ·
      refine ⟨26683896041170428318271913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71157056109787808848725101 26683896041170428318271913)
      ·
        refine ⟨20012922030877821238703935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26683896041170428318271913 20012922030877821238703935)
        ·
          refine ⟨30019383046316731858055903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20012922030877821238703935 30019383046316731858055903)
          ·
            refine ⟨45029074569475097787083855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30019383046316731858055903 45029074569475097787083855)
            ·
              refine ⟨67543611854212646680625783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45029074569475097787083855 67543611854212646680625783)
              ·
                refine ⟨101315417781318970020938675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67543611854212646680625783 101315417781318970020938675)
                ·
                  refine ⟨151973126671978455031408013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101315417781318970020938675 151973126671978455031408013)
                  ·
                    refine ⟨56989922501991920636778005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151973126671978455031408013 56989922501991920636778005)
                    ·
                      refine ⟨2671402617280871279848969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56989922501991920636778005 2671402617280871279848969)
                      ·
                        rfl

theorem cell23_5202538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5202538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202538 prefixEnd_5202538 := by exact prefixLift 5202538
  have htrace : WordTrace (prefixWord ++ tailWord_5202538) baseStart_5202538 baseEnd_5202538 := by
    simpa [prefixWord, tailWord_5202538, baseEnd_5202538] using wordTrace_append hprefix tailTrace_5202538
  have hstable : (prefixWord ++ tailWord_5202538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202538).length < 2 ^ (prefixWord ++ tailWord_5202538).sum := by decide
  have hdescent : baseEnd_5202538 < baseStart_5202538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202542 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_5202542 : Nat := 118140960795 + 5202542 * 2 ^ 59
def prefixEnd_5202542 : Nat := 4983230072969 + 3 ^ 40 * 5202542 * 2
def baseEnd_5202542 : Nat := 2671404671203489264198951

theorem tailTrace_5202542 : CollatzResearch.WordTrace tailWord_5202542 prefixEnd_5202542 2671404671203489264198951 := by
  unfold tailWord_5202542
  simp only [CollatzResearch.WordTrace]
  refine ⟨23719036939760791534968235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126501530345390888186497253 23719036939760791534968235)
  ·
    refine ⟨35578555409641187302452353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23719036939760791534968235 35578555409641187302452353)
    ·
      refine ⟨26683916557230890476839265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35578555409641187302452353 26683916557230890476839265)
      ·
        refine ⟨20012937417923167857629449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26683916557230890476839265 20012937417923167857629449)
        ·
          refine ⟨15009703063442375893222087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20012937417923167857629449 15009703063442375893222087)
          ·
            refine ⟨22514554595163563839833131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15009703063442375893222087 22514554595163563839833131)
            ·
              refine ⟨33771831892745345759749697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22514554595163563839833131 33771831892745345759749697)
              ·
                refine ⟨25328873919559009319812273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33771831892745345759749697 25328873919559009319812273)
                ·
                  refine ⟨18996655439669256989859205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25328873919559009319812273 18996655439669256989859205)
                  ·
                    refine ⟨3561872894937985685598601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18996655439669256989859205 3561872894937985685598601)
                    ·
                      refine ⟨2671404671203489264198951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561872894937985685598601 2671404671203489264198951)
                      ·
                        rfl

theorem cell23_5202542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_5202542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202542 prefixEnd_5202542 := by exact prefixLift 5202542
  have htrace : WordTrace (prefixWord ++ tailWord_5202542) baseStart_5202542 baseEnd_5202542 := by
    simpa [prefixWord, tailWord_5202542, baseEnd_5202542] using wordTrace_append hprefix tailTrace_5202542
  have hstable : (prefixWord ++ tailWord_5202542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202542).length < 2 ^ (prefixWord ++ tailWord_5202542).sum := by decide
  have hdescent : baseEnd_5202542 < baseStart_5202542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202585 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 1, 5, 2]
def baseStart_5202585 : Nat := 118140960795 + 5202585 * 2 ^ 59
def prefixEnd_5202585 : Nat := 4983230072969 + 3 ^ 40 * 5202585 * 2
def baseEnd_5202585 : Nat := 2671426750871632595961253

theorem tailTrace_5202585 : CollatzResearch.WordTrace tailWord_5202585 prefixEnd_5202585 2671426750871632595961253 := by
  unfold tailWord_5202585
  simp only [CollatzResearch.WordTrace]
  refine ⟨189753863856930550623561209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126502575904620367082374139 189753863856930550623561209)
  ·
    refine ⟨142315397892697912967670907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189753863856930550623561209 142315397892697912967670907)
    ·
      refine ⟨213473096839046869451506361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142315397892697912967670907 213473096839046869451506361)
      ·
        refine ⟨160104822629285152088629771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213473096839046869451506361 160104822629285152088629771)
        ·
          refine ⟨240157233943927728132944657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160104822629285152088629771 240157233943927728132944657)
          ·
            refine ⟨180117925457945796099708493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240157233943927728132944657 180117925457945796099708493)
            ·
              refine ⟨67544222046729673537390685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180117925457945796099708493 67544222046729673537390685)
              ·
                refine ⟨25329083267523627576521507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67544222046729673537390685 25329083267523627576521507)
                ·
                  refine ⟨37993624901285441364782261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25329083267523627576521507 37993624901285441364782261)
                  ·
                    refine ⟨3561902334495510127948337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37993624901285441364782261 3561902334495510127948337)
                    ·
                      refine ⟨2671426750871632595961253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561902334495510127948337 2671426750871632595961253)
                      ·
                        rfl

theorem cell23_5202585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_5202585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202585 prefixEnd_5202585 := by exact prefixLift 5202585
  have htrace : WordTrace (prefixWord ++ tailWord_5202585) baseStart_5202585 baseEnd_5202585 := by
    simpa [prefixWord, tailWord_5202585, baseEnd_5202585] using wordTrace_append hprefix tailTrace_5202585
  have hstable : (prefixWord ++ tailWord_5202585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202585).length < 2 ^ (prefixWord ++ tailWord_5202585).sum := by decide
  have hdescent : baseEnd_5202585 < baseStart_5202585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202632 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_5202632 : Nat := 118140960795 + 5202632 * 2 ^ 59
def prefixEnd_5202632 : Nat := 4983230072969 + 3 ^ 40 * 5202632 * 2
def baseEnd_5202632 : Nat := 2671450884462393912073537

theorem tailTrace_5202632 : CollatzResearch.WordTrace tailWord_5202632 prefixEnd_5202632 2671450884462393912073537 := by
  unfold tailWord_5202632
  simp only [CollatzResearch.WordTrace]
  refine ⟨94877789043880138825261075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126503718725173518433681433 94877789043880138825261075)
  ·
    refine ⟨142316683565820208237891613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94877789043880138825261075 142316683565820208237891613)
    ·
      refine ⟨53368756337182578089209355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142316683565820208237891613 53368756337182578089209355)
      ·
        refine ⟨80053134505773867133814033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53368756337182578089209355 80053134505773867133814033)
        ·
          refine ⟨60039850879330400350360525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80053134505773867133814033 60039850879330400350360525)
          ·
            refine ⟨22514944079748900131385197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60039850879330400350360525 22514944079748900131385197)
            ·
              refine ⟨8443104029905837549269449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22514944079748900131385197 8443104029905837549269449)
              ·
                refine ⟨6332328022429378161952087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8443104029905837549269449 6332328022429378161952087)
                ·
                  refine ⟨9498492033644067242928131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6332328022429378161952087 9498492033644067242928131)
                  ·
                    refine ⟨14247738050466100864392197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9498492033644067242928131 14247738050466100864392197)
                    ·
                      refine ⟨2671450884462393912073537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14247738050466100864392197 2671450884462393912073537)
                      ·
                        rfl

theorem cell23_5202632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_5202632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202632 prefixEnd_5202632 := by exact prefixLift 5202632
  have htrace : WordTrace (prefixWord ++ tailWord_5202632) baseStart_5202632 baseEnd_5202632 := by
    simpa [prefixWord, tailWord_5202632, baseEnd_5202632] using wordTrace_append hprefix tailTrace_5202632
  have hstable : (prefixWord ++ tailWord_5202632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202632).length < 2 ^ (prefixWord ++ tailWord_5202632).sum := by decide
  have hdescent : baseEnd_5202632 < baseStart_5202632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202642 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_5202642 : Nat := 118140960795 + 5202642 * 2 ^ 59
def prefixEnd_5202642 : Nat := 4983230072969 + 3 ^ 40 * 5202642 * 2
def baseEnd_5202642 : Nat := 890485339756312957649497

theorem tailTrace_5202642 : CollatzResearch.WordTrace tailWord_5202642 prefixEnd_5202642 890485339756312957649497 := by
  unfold tailWord_5202642
  simp only [CollatzResearch.WordTrace]
  refine ⟨47438985704431012339596545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126503961878482699572257453 47438985704431012339596545)
  ·
    refine ⟨35579239278323259254697409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47438985704431012339596545 35579239278323259254697409)
    ·
      refine ⟨26684429458742444441023057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35579239278323259254697409 26684429458742444441023057)
      ·
        refine ⟨20013322094056833330767293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26684429458742444441023057 20013322094056833330767293)
        ·
          refine ⟨7504995785271312499037735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20013322094056833330767293 7504995785271312499037735)
          ·
            refine ⟨11257493677906968748556603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7504995785271312499037735 11257493677906968748556603)
            ·
              refine ⟨16886240516860453122834905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11257493677906968748556603 16886240516860453122834905)
              ·
                refine ⟨12664680387645339842126179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16886240516860453122834905 12664680387645339842126179)
                ·
                  refine ⟨18997020581468009763189269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12664680387645339842126179 18997020581468009763189269)
                  ·
                    refine ⟨890485339756312957649497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18997020581468009763189269 890485339756312957649497)
                    ·
                      rfl

theorem cell23_5202642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_5202642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202642 prefixEnd_5202642 := by exact prefixLift 5202642
  have htrace : WordTrace (prefixWord ++ tailWord_5202642) baseStart_5202642 baseEnd_5202642 := by
    simpa [prefixWord, tailWord_5202642, baseEnd_5202642] using wordTrace_append hprefix tailTrace_5202642
  have hstable : (prefixWord ++ tailWord_5202642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202642).length < 2 ^ (prefixWord ++ tailWord_5202642).sum := by decide
  have hdescent : baseEnd_5202642 < baseStart_5202642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202659 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 2, 4]
def baseStart_5202659 : Nat := 118140960795 + 5202659 * 2 ^ 59
def prefixEnd_5202659 : Nat := 4983230072969 + 3 ^ 40 * 5202659 * 2
def baseEnd_5202659 : Nat := 890488249480021768811971

theorem tailTrace_5202659 : CollatzResearch.WordTrace tailWord_5202659 prefixEnd_5202659 890488249480021768811971 := by
  unfold tailWord_5202659
  simp only [CollatzResearch.WordTrace]
  refine ⟨189756562858662461261755031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126504375239108307507836687 189756562858662461261755031)
  ·
    refine ⟨284634844287993691892632547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189756562858662461261755031 284634844287993691892632547)
    ·
      refine ⟨426952266431990537838948821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284634844287993691892632547 426952266431990537838948821)
      ·
        refine ⟨10006693744499778230600363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 426952266431990537838948821 10006693744499778230600363)
        ·
          refine ⟨15010040616749667345900545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10006693744499778230600363 15010040616749667345900545)
          ·
            refine ⟨11257530462562250509425409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15010040616749667345900545 11257530462562250509425409)
            ·
              refine ⟨8443147846921687882069057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11257530462562250509425409 8443147846921687882069057)
              ·
                refine ⟨6332360885191265911551793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8443147846921687882069057 6332360885191265911551793)
                ·
                  refine ⟨4749270663893449433663845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6332360885191265911551793 4749270663893449433663845)
                  ·
                    refine ⟨890488249480021768811971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4749270663893449433663845 890488249480021768811971)
                    ·
                      rfl

theorem cell23_5202659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 4].length) (baseStart_5202659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202659 prefixEnd_5202659 := by exact prefixLift 5202659
  have htrace : WordTrace (prefixWord ++ tailWord_5202659) baseStart_5202659 baseEnd_5202659 := by
    simpa [prefixWord, tailWord_5202659, baseEnd_5202659] using wordTrace_append hprefix tailTrace_5202659
  have hstable : (prefixWord ++ tailWord_5202659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202659).length < 2 ^ (prefixWord ++ tailWord_5202659).sum := by decide
  have hdescent : baseEnd_5202659 < baseStart_5202659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202676 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5202676 : Nat := 118140960795 + 5202676 * 2 ^ 59
def prefixEnd_5202676 : Nat := 4983230072969 + 3 ^ 40 * 5202676 * 2
def baseEnd_5202676 : Nat := 890491159203730579974445

theorem tailTrace_5202676 : CollatzResearch.WordTrace tailWord_5202676 prefixEnd_5202676 890491159203730579974445 := by
  unfold tailWord_5202676
  simp only [CollatzResearch.WordTrace]
  refine ⟨94878591449800436582561941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126504788599733915443415921 94878591449800436582561941)
  ·
    refine ⟨4447433974209395464807591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94878591449800436582561941 4447433974209395464807591)
    ·
      refine ⟨6671150961314093197211387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4447433974209395464807591 6671150961314093197211387)
      ·
        refine ⟨10006726441971139795817081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6671150961314093197211387 10006726441971139795817081)
        ·
          refine ⟨7505044831478354846862811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10006726441971139795817081 7505044831478354846862811)
          ·
            refine ⟨11257567247217532270294217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7505044831478354846862811 11257567247217532270294217)
            ·
              refine ⟨8443175435413149202720663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11257567247217532270294217 8443175435413149202720663)
              ·
                refine ⟨12664763153119723804080995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8443175435413149202720663 12664763153119723804080995)
                ·
                  refine ⟨18997144729679585706121493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12664763153119723804080995 18997144729679585706121493)
                  ·
                    refine ⟨890491159203730579974445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18997144729679585706121493 890491159203730579974445)
                    ·
                      rfl

theorem cell23_5202676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5202676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202676 prefixEnd_5202676 := by exact prefixLift 5202676
  have htrace : WordTrace (prefixWord ++ tailWord_5202676) baseStart_5202676 baseEnd_5202676 := by
    simpa [prefixWord, tailWord_5202676, baseEnd_5202676] using wordTrace_append hprefix tailTrace_5202676
  have hstable : (prefixWord ++ tailWord_5202676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202676).length < 2 ^ (prefixWord ++ tailWord_5202676).sum := by decide
  have hdescent : baseEnd_5202676 < baseStart_5202676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202688 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_5202688 : Nat := 118140960795 + 5202688 * 2 ^ 59
def prefixEnd_5202688 : Nat := 4983230072969 + 3 ^ 40 * 5202688 * 2
def baseEnd_5202688 : Nat := 2671479639379045692973279

theorem tailTrace_5202688 : CollatzResearch.WordTrace tailWord_5202688 prefixEnd_5202688 2671479639379045692973279 := by
  unfold tailWord_5202688
  simp only [CollatzResearch.WordTrace]
  refine ⟨94878810287778699607280359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126505080383704932809707145 94878810287778699607280359)
  ·
    refine ⟨142318215431668049410920539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94878810287778699607280359 142318215431668049410920539)
    ·
      refine ⟨213477323147502074116380809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142318215431668049410920539 213477323147502074116380809)
      ·
        refine ⟨160107992360626555587285607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213477323147502074116380809 160107992360626555587285607)
        ·
          refine ⟨240161988540939833380928411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160107992360626555587285607 240161988540939833380928411)
          ·
            refine ⟨360242982811409750071392617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240161988540939833380928411 360242982811409750071392617)
            ·
              refine ⟨270182237108557312553544463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360242982811409750071392617 270182237108557312553544463)
              ·
                refine ⟨405273355662835968830316695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270182237108557312553544463 405273355662835968830316695)
                ·
                  refine ⟨607910033494253953245475043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405273355662835968830316695 607910033494253953245475043)
                  ·
                    refine ⟨911865050241380929868212565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 607910033494253953245475043 911865050241380929868212565)
                    ·
                      refine ⟨2671479639379045692973279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 911865050241380929868212565 2671479639379045692973279)
                      ·
                        rfl

theorem cell23_5202688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_5202688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202688 prefixEnd_5202688 := by exact prefixLift 5202688
  have htrace : WordTrace (prefixWord ++ tailWord_5202688) baseStart_5202688 baseEnd_5202688 := by
    simpa [prefixWord, tailWord_5202688, baseEnd_5202688] using wordTrace_append hprefix tailTrace_5202688
  have hstable : (prefixWord ++ tailWord_5202688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202688).length < 2 ^ (prefixWord ++ tailWord_5202688).sum := by decide
  have hdescent : baseEnd_5202688 < baseStart_5202688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202709 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_5202709 : Nat := 118140960795 + 5202709 * 2 ^ 59
def prefixEnd_5202709 : Nat := 4983230072969 + 3 ^ 40 * 5202709 * 2
def baseEnd_5202709 : Nat := 2671490422472790110810683

theorem tailTrace_5202709 : CollatzResearch.WordTrace tailWord_5202709 prefixEnd_5202709 2671490422472790110810683 := by
  unfold tailWord_5202709
  simp only [CollatzResearch.WordTrace]
  refine ⟨189758386508481319801075181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126505591005654213200716787 189758386508481319801075181)
  ·
    refine ⟨71159394940680494925403193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189758386508481319801075181 71159394940680494925403193)
    ·
      refine ⟨53369546205510371194052395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71159394940680494925403193 53369546205510371194052395)
      ·
        refine ⟨80054319308265556791078593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53369546205510371194052395 80054319308265556791078593)
        ·
          refine ⟨60040739481199167593308945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80054319308265556791078593 60040739481199167593308945)
          ·
            refine ⟨45030554610899375694981709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60040739481199167593308945 45030554610899375694981709)
            ·
              refine ⟨16886457979087265885618141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45030554610899375694981709 16886457979087265885618141)
              ·
                refine ⟨6332421742157724707106803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16886457979087265885618141 6332421742157724707106803)
                ·
                  refine ⟨9498632613236587060660205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6332421742157724707106803 9498632613236587060660205)
                  ·
                    refine ⟨3561987229963720147747577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9498632613236587060660205 3561987229963720147747577)
                    ·
                      refine ⟨2671490422472790110810683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561987229963720147747577 2671490422472790110810683)
                      ·
                        rfl

theorem cell23_5202709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_5202709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202709 prefixEnd_5202709 := by exact prefixLift 5202709
  have htrace : WordTrace (prefixWord ++ tailWord_5202709) baseStart_5202709 baseEnd_5202709 := by
    simpa [prefixWord, tailWord_5202709, baseEnd_5202709] using wordTrace_append hprefix tailTrace_5202709
  have hstable : (prefixWord ++ tailWord_5202709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202709).length < 2 ^ (prefixWord ++ tailWord_5202709).sum := by decide
  have hdescent : baseEnd_5202709 < baseStart_5202709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202716 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_5202716 : Nat := 118140960795 + 5202716 * 2 ^ 59
def prefixEnd_5202716 : Nat := 4983230072969 + 3 ^ 40 * 5202716 * 2
def baseEnd_5202716 : Nat := 2671494016837371583423151

theorem tailTrace_5202716 : CollatzResearch.WordTrace tailWord_5202716 prefixEnd_5202716 2671494016837371583423151 := by
  unfold tailWord_5202716
  simp only [CollatzResearch.WordTrace]
  refine ⟨94879320909727979998290001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126505761212970639997720001 94879320909727979998290001)
  ·
    refine ⟨71159490682295984998717501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94879320909727979998290001 71159490682295984998717501)
    ·
      refine ⟨26684809005860994374519063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71159490682295984998717501 26684809005860994374519063)
      ·
        refine ⟨40027213508791491561778595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26684809005860994374519063 40027213508791491561778595)
        ·
          refine ⟨60040820263187237342667893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40027213508791491561778595 60040820263187237342667893)
          ·
            refine ⟨5628826899673803500875115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60040820263187237342667893 5628826899673803500875115)
            ·
              refine ⟨8443240349510705251312673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5628826899673803500875115 8443240349510705251312673)
              ·
                refine ⟨6332430262133028938484505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8443240349510705251312673 6332430262133028938484505)
                ·
                  refine ⟨4749322696599771703863379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6332430262133028938484505 4749322696599771703863379)
                  ·
                    refine ⟨7123984044899657555795069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4749322696599771703863379 7123984044899657555795069)
                    ·
                      refine ⟨2671494016837371583423151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7123984044899657555795069 2671494016837371583423151)
                      ·
                        rfl

theorem cell23_5202716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_5202716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202716 prefixEnd_5202716 := by exact prefixLift 5202716
  have htrace : WordTrace (prefixWord ++ tailWord_5202716) baseStart_5202716 baseEnd_5202716 := by
    simpa [prefixWord, tailWord_5202716, baseEnd_5202716] using wordTrace_append hprefix tailTrace_5202716
  have hstable : (prefixWord ++ tailWord_5202716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202716).length < 2 ^ (prefixWord ++ tailWord_5202716).sum := by decide
  have hdescent : baseEnd_5202716 < baseStart_5202716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202733 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5202733 : Nat := 118140960795 + 5202733 * 2 ^ 59
def prefixEnd_5202733 : Nat := 4983230072969 + 3 ^ 40 * 5202733 * 2
def baseEnd_5202733 : Nat := 2671502746008498016910573

theorem tailTrace_5202733 : CollatzResearch.WordTrace tailWord_5202733 prefixEnd_5202733 2671502746008498016910573 := by
  unfold tailWord_5202733
  simp only [CollatzResearch.WordTrace]
  refine ⟨189759261860394371899948853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126506174573596247933299235 189759261860394371899948853)
  ·
    refine ⟨17789930799411972365620205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189759261860394371899948853 17789930799411972365620205)
    ·
      refine ⟨6671224049779489637107577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17789930799411972365620205 6671224049779489637107577)
      ·
        refine ⟨5003418037334617227830683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6671224049779489637107577 5003418037334617227830683)
        ·
          refine ⟨7505127056001925841746025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5003418037334617227830683 7505127056001925841746025)
          ·
            refine ⟨5628845292001444381309519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7505127056001925841746025 5628845292001444381309519)
            ·
              refine ⟨8443267938002166571964279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5628845292001444381309519 8443267938002166571964279)
              ·
                refine ⟨12664901907003249857946419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8443267938002166571964279 12664901907003249857946419)
                ·
                  refine ⟨18997352860504874786919629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12664901907003249857946419 18997352860504874786919629)
                  ·
                    refine ⟨7124007322689328045094861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18997352860504874786919629 7124007322689328045094861)
                    ·
                      refine ⟨2671502746008498016910573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7124007322689328045094861 2671502746008498016910573)
                      ·
                        rfl

theorem cell23_5202733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5202733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202733 prefixEnd_5202733 := by exact prefixLift 5202733
  have htrace : WordTrace (prefixWord ++ tailWord_5202733) baseStart_5202733 baseEnd_5202733 := by
    simpa [prefixWord, tailWord_5202733, baseEnd_5202733] using wordTrace_append hprefix tailTrace_5202733
  have hstable : (prefixWord ++ tailWord_5202733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202733).length < 2 ^ (prefixWord ++ tailWord_5202733).sum := by decide
  have hdescent : baseEnd_5202733 < baseStart_5202733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202739 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 1, 4, 2]
def baseStart_5202739 : Nat := 118140960795 + 5202739 * 2 ^ 59
def prefixEnd_5202739 : Nat := 4983230072969 + 3 ^ 40 * 5202739 * 2
def baseEnd_5202739 : Nat := 2671505826892424993435545

theorem tailTrace_5202739 : CollatzResearch.WordTrace tailWord_5202739 prefixEnd_5202739 2671505826892424993435545 := by
  unfold tailWord_5202739
  simp only [CollatzResearch.WordTrace]
  refine ⟨189759480698372634924667271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126506320465581756616444847 189759480698372634924667271)
  ·
    refine ⟨284639221047558952387000907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189759480698372634924667271 284639221047558952387000907)
    ·
      refine ⟨426958831571338428580501361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284639221047558952387000907 426958831571338428580501361)
      ·
        refine ⟨320219123678503821435376021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426958831571338428580501361 320219123678503821435376021)
        ·
          refine ⟨15010271422429866629783251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 320219123678503821435376021 15010271422429866629783251)
          ·
            refine ⟨22515407133644799944674877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15010271422429866629783251 22515407133644799944674877)
            ·
              refine ⟨8443277675116799979253079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22515407133644799944674877 8443277675116799979253079)
              ·
                refine ⟨12664916512675199968879619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8443277675116799979253079 12664916512675199968879619)
                ·
                  refine ⟨18997374769012799953319429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12664916512675199968879619 18997374769012799953319429)
                  ·
                    refine ⟨3562007769189899991247393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18997374769012799953319429 3562007769189899991247393)
                    ·
                      refine ⟨2671505826892424993435545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562007769189899991247393 2671505826892424993435545)
                      ·
                        rfl

theorem cell23_5202739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4, 2].length) (baseStart_5202739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202739 prefixEnd_5202739 := by exact prefixLift 5202739
  have htrace : WordTrace (prefixWord ++ tailWord_5202739) baseStart_5202739 baseEnd_5202739 := by
    simpa [prefixWord, tailWord_5202739, baseEnd_5202739] using wordTrace_append hprefix tailTrace_5202739
  have hstable : (prefixWord ++ tailWord_5202739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202739).length < 2 ^ (prefixWord ++ tailWord_5202739).sum := by decide
  have hdescent : baseEnd_5202739 < baseStart_5202739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202762 : List Nat := [3, 1, 2, 1, 1, 1, 2, 7, 5]
def baseStart_5202762 : Nat := 118140960795 + 5202762 * 2 ^ 59
def prefixEnd_5202762 : Nat := 4983230072969 + 3 ^ 40 * 5202762 * 2
def baseEnd_5202762 : Nat := 296835292994164267049771

theorem tailTrace_5202762 : CollatzResearch.WordTrace tailWord_5202762 prefixEnd_5202762 296835292994164267049771 := by
  unfold tailWord_5202762
  simp only [CollatzResearch.WordTrace]
  refine ⟨47440079894322327463188635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126506879718192873235169693 47440079894322327463188635)
  ·
    refine ⟨71160119841483491194782953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47440079894322327463188635 71160119841483491194782953)
    ·
      refine ⟨53370089881112618396087215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71160119841483491194782953 53370089881112618396087215)
      ·
        refine ⟨80055134821668927594130823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53370089881112618396087215 80055134821668927594130823)
        ·
          refine ⟨120082702232503391391196235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80055134821668927594130823 120082702232503391391196235)
          ·
            refine ⟨180124053348755087086794353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120082702232503391391196235 180124053348755087086794353)
            ·
              refine ⟨135093040011566315315095765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180124053348755087086794353 135093040011566315315095765)
              ·
                refine ⟨3166243125271085515197557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135093040011566315315095765 3166243125271085515197557)
                ·
                  refine ⟨296835292994164267049771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3166243125271085515197557 296835292994164267049771)
                  ·
                    rfl

theorem cell23_5202762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_5202762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202762 prefixEnd_5202762 := by exact prefixLift 5202762
  have htrace : WordTrace (prefixWord ++ tailWord_5202762) baseStart_5202762 baseEnd_5202762 := by
    simpa [prefixWord, tailWord_5202762, baseEnd_5202762] using wordTrace_append hprefix tailTrace_5202762
  have hstable : (prefixWord ++ tailWord_5202762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202762).length < 2 ^ (prefixWord ++ tailWord_5202762).sum := by decide
  have hdescent : baseEnd_5202762 < baseStart_5202762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202795 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4]
def baseStart_5202795 : Nat := 118140960795 + 5202795 * 2 ^ 59
def prefixEnd_5202795 : Nat := 4983230072969 + 3 ^ 40 * 5202795 * 2
def baseEnd_5202795 : Nat := 2671534581809076774335287

theorem tailTrace_5202795 : CollatzResearch.WordTrace tailWord_5202795 prefixEnd_5202795 2671534581809076774335287 := by
  unfold tailWord_5202795
  simp only [CollatzResearch.WordTrace]
  refine ⟨189761523186169756488705839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126507682124113170992470559 189761523186169756488705839)
  ·
    refine ⟨284642284779254634733058759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189761523186169756488705839 284642284779254634733058759)
    ·
      refine ⟨426963427168881952099588139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284642284779254634733058759 426963427168881952099588139)
      ·
        refine ⟨640445140753322928149382209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426963427168881952099588139 640445140753322928149382209)
        ·
          refine ⟨480333855564992196112036657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640445140753322928149382209 480333855564992196112036657)
          ·
            refine ⟨360250391673744147084027493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480333855564992196112036657 360250391673744147084027493)
            ·
              refine ⟨67546948438827027578255155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360250391673744147084027493 67546948438827027578255155)
              ·
                refine ⟨101320422658240541367382733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67546948438827027578255155 101320422658240541367382733)
                ·
                  refine ⟨37995158496840203012768525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101320422658240541367382733 37995158496840203012768525)
                  ·
                    refine ⟨14248184436315076129788197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37995158496840203012768525 14248184436315076129788197)
                    ·
                      refine ⟨2671534581809076774335287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14248184436315076129788197 2671534581809076774335287)
                      ·
                        rfl

theorem cell23_5202795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_5202795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202795 prefixEnd_5202795 := by exact prefixLift 5202795
  have htrace : WordTrace (prefixWord ++ tailWord_5202795) baseStart_5202795 baseEnd_5202795 := by
    simpa [prefixWord, tailWord_5202795, baseEnd_5202795] using wordTrace_append hprefix tailTrace_5202795
  have hstable : (prefixWord ++ tailWord_5202795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202795).length < 2 ^ (prefixWord ++ tailWord_5202795).sum := by decide
  have hdescent : baseEnd_5202795 < baseStart_5202795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202852 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 6]
def baseStart_5202852 : Nat := 118140960795 + 5202852 * 2 ^ 59
def prefixEnd_5202852 : Nat := 4983230072969 + 3 ^ 40 * 5202852 * 2
def baseEnd_5202852 : Nat := 296840427800709227924725

theorem tailTrace_5202852 : CollatzResearch.WordTrace tailWord_5202852 prefixEnd_5202852 296840427800709227924725 := by
  unfold tailWord_5202852
  simp only [CollatzResearch.WordTrace]
  refine ⟨94881801073481627611765405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126509068097975503482353873 94881801073481627611765405)
  ·
    refine ⟨35580675402555610354412027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94881801073481627611765405 35580675402555610354412027)
    ·
      refine ⟨53371013103833415531618041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35580675402555610354412027 53371013103833415531618041)
      ·
        refine ⟨40028259827875061648713531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53371013103833415531618041 40028259827875061648713531)
        ·
          refine ⟨60042389741812592473070297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40028259827875061648713531 60042389741812592473070297)
          ·
            refine ⟨45031792306359444354802723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60042389741812592473070297 45031792306359444354802723)
            ·
              refine ⟨67547688459539166532204085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45031792306359444354802723 67547688459539166532204085)
              ·
                refine ⟨6332595793081796862394133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67547688459539166532204085 6332595793081796862394133)
                ·
                  refine ⟨296840427800709227924725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6332595793081796862394133 296840427800709227924725)
                  ·
                    rfl

theorem cell23_5202852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_5202852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202852 prefixEnd_5202852 := by exact prefixLift 5202852
  have htrace : WordTrace (prefixWord ++ tailWord_5202852) baseStart_5202852 baseEnd_5202852 := by
    simpa [prefixWord, tailWord_5202852, baseEnd_5202852] using wordTrace_append hprefix tailTrace_5202852
  have hstable : (prefixWord ++ tailWord_5202852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202852).length < 2 ^ (prefixWord ++ tailWord_5202852).sum := by decide
  have hdescent : baseEnd_5202852 < baseStart_5202852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202875 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7]
def baseStart_5202875 : Nat := 118140960795 + 5202875 * 2 ^ 59
def prefixEnd_5202875 : Nat := 4983230072969 + 3 ^ 40 * 5202875 * 2
def baseEnd_5202875 : Nat := 2671575660261436461334919

theorem tailTrace_5202875 : CollatzResearch.WordTrace tailWord_5202875 prefixEnd_5202875 2671575660261436461334919 := by
  unfold tailWord_5202875
  simp only [CollatzResearch.WordTrace]
  refine ⟨189764441025879930151618079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126509627350586620101078719 189764441025879930151618079)
  ·
    refine ⟨284646661538819895227427119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189764441025879930151618079 284646661538819895227427119)
    ·
      refine ⟨426969992308229842841140679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284646661538819895227427119 426969992308229842841140679)
      ·
        refine ⟨640454988462344764261711019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426969992308229842841140679 640454988462344764261711019)
        ·
          refine ⟨960682482693517146392566529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640454988462344764261711019 960682482693517146392566529)
          ·
            refine ⟨720511862020137859794424897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960682482693517146392566529 720511862020137859794424897)
            ·
              refine ⟨540383896515103394845818673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720511862020137859794424897 540383896515103394845818673)
              ·
                refine ⟨405287922386327546134364005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540383896515103394845818673 405287922386327546134364005)
                ·
                  refine ⟨75991485447436414900193251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405287922386327546134364005 75991485447436414900193251)
                  ·
                    refine ⟨113987228171154622350289877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75991485447436414900193251 113987228171154622350289877)
                    ·
                      refine ⟨2671575660261436461334919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113987228171154622350289877 2671575660261436461334919)
                      ·
                        rfl

theorem cell23_5202875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_5202875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202875 prefixEnd_5202875 := by exact prefixLift 5202875
  have htrace : WordTrace (prefixWord ++ tailWord_5202875) baseStart_5202875 baseEnd_5202875 := by
    simpa [prefixWord, tailWord_5202875, baseEnd_5202875] using wordTrace_append hprefix tailTrace_5202875
  have hstable : (prefixWord ++ tailWord_5202875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202875).length < 2 ^ (prefixWord ++ tailWord_5202875).sum := by decide
  have hdescent : baseEnd_5202875 < baseStart_5202875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202929 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 4, 4]
def baseStart_5202929 : Nat := 118140960795 + 5202929 * 2 ^ 59
def prefixEnd_5202929 : Nat := 4983230072969 + 3 ^ 40 * 5202929 * 2
def baseEnd_5202929 : Nat := 890534462738926416686557

theorem tailTrace_5202929 : CollatzResearch.WordTrace tailWord_5202929 prefixEnd_5202929 890534462738926416686557 := by
  unfold tailWord_5202929
  simp only [CollatzResearch.WordTrace]
  refine ⟨189766410567684297374083841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126510940378456198249389227 189766410567684297374083841)
  ·
    refine ⟨142324807925763223030562881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189766410567684297374083841 142324807925763223030562881)
    ·
      refine ⟨106743605944322417272922161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142324807925763223030562881 106743605944322417272922161)
      ·
        refine ⟨80057704458241812954691621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106743605944322417272922161 80057704458241812954691621)
        ·
          refine ⟨15010819585920339929004679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80057704458241812954691621 15010819585920339929004679)
          ·
            refine ⟨22516229378880509893507019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15010819585920339929004679 22516229378880509893507019)
            ·
              refine ⟨33774344068320764840260529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22516229378880509893507019 33774344068320764840260529)
              ·
                refine ⟨25330758051240573630195397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33774344068320764840260529 25330758051240573630195397)
                ·
                  refine ⟨4749517134607607555661637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25330758051240573630195397 4749517134607607555661637)
                  ·
                    refine ⟨890534462738926416686557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4749517134607607555661637 890534462738926416686557)
                    ·
                      rfl

theorem cell23_5202929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_5202929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202929 prefixEnd_5202929 := by exact prefixLift 5202929
  have htrace : WordTrace (prefixWord ++ tailWord_5202929) baseStart_5202929 baseEnd_5202929 := by
    simpa [prefixWord, tailWord_5202929, baseEnd_5202929] using wordTrace_append hprefix tailTrace_5202929
  have hstable : (prefixWord ++ tailWord_5202929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202929).length < 2 ^ (prefixWord ++ tailWord_5202929).sum := by decide
  have hdescent : baseEnd_5202929 < baseStart_5202929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5202953 : List Nat := [1, 2, 1, 1, 3, 1, 1, 8, 1, 2, 2]
def baseStart_5202953 : Nat := 118140960795 + 5202953 * 2 ^ 59
def prefixEnd_5202953 : Nat := 4983230072969 + 3 ^ 40 * 5202953 * 2
def baseEnd_5202953 : Nat := 2671615711752487156159561

theorem tailTrace_5202953 : CollatzResearch.WordTrace tailWord_5202953 prefixEnd_5202953 2671615711752487156159561 := by
  unfold tailWord_5202953
  simp only [CollatzResearch.WordTrace]
  refine ⟨189767285919597349472957513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126511523946398232981971675 189767285919597349472957513)
  ·
    refine ⟨142325464439698012104718135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189767285919597349472957513 142325464439698012104718135)
    ·
      refine ⟨213488196659547018157077203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142325464439698012104718135 213488196659547018157077203)
      ·
        refine ⟨320232294989320527235615805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213488196659547018157077203 320232294989320527235615805)
        ·
          refine ⟨120087110620995197713355927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320232294989320527235615805 120087110620995197713355927)
          ·
            refine ⟨180130665931492796570033891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120087110620995197713355927 180130665931492796570033891)
            ·
              refine ⟨270195998897239194855050837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180130665931492796570033891 270195998897239194855050837)
              ·
                refine ⟨3166359362077021814707627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 270195998897239194855050837 3166359362077021814707627)
                ·
                  refine ⟨4749539043115532722061441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166359362077021814707627 4749539043115532722061441)
                  ·
                    refine ⟨3562154282336649541546081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4749539043115532722061441 3562154282336649541546081)
                    ·
                      refine ⟨2671615711752487156159561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562154282336649541546081 2671615711752487156159561)
                      ·
                        rfl

theorem cell23_5202953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 2, 2].length) (baseStart_5202953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5202953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5202953 prefixEnd_5202953 := by exact prefixLift 5202953
  have htrace : WordTrace (prefixWord ++ tailWord_5202953) baseStart_5202953 baseEnd_5202953 := by
    simpa [prefixWord, tailWord_5202953, baseEnd_5202953] using wordTrace_append hprefix tailTrace_5202953
  have hstable : (prefixWord ++ tailWord_5202953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5202953).length < 2 ^ (prefixWord ++ tailWord_5202953).sum := by decide
  have hdescent : baseEnd_5202953 < baseStart_5202953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5202953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203029 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_5203029 : Nat := 118140960795 + 5203029 * 2 ^ 59
def prefixEnd_5203029 : Nat := 4983230072969 + 3 ^ 40 * 5203029 * 2
def baseEnd_5203029 : Nat := 2671654736282228858809211

theorem tailTrace_5203029 : CollatzResearch.WordTrace tailWord_5203029 prefixEnd_5203029 2671654736282228858809211 := by
  unfold tailWord_5203029
  simp only [CollatzResearch.WordTrace]
  refine ⟨189770057867322014452724141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126513371911548009635149427 189770057867322014452724141)
  ·
    refine ⟨71163771700245755419771553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189770057867322014452724141 71163771700245755419771553)
    ·
      refine ⟨53372828775184316564828665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71163771700245755419771553 53372828775184316564828665)
      ·
        refine ⟨40029621581388237423621499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53372828775184316564828665 40029621581388237423621499)
        ·
          refine ⟨60044432372082356135432249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40029621581388237423621499 60044432372082356135432249)
          ·
            refine ⟨45033324279061767101574187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60044432372082356135432249 45033324279061767101574187)
            ·
              refine ⟨67549986418592650652361281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45033324279061767101574187 67549986418592650652361281)
              ·
                refine ⟨50662489813944487989270961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67549986418592650652361281 50662489813944487989270961)
                ·
                  refine ⟨37996867360458365991953221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50662489813944487989270961 37996867360458365991953221)
                  ·
                    refine ⟨7124412630085943623491229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37996867360458365991953221 7124412630085943623491229)
                    ·
                      refine ⟨2671654736282228858809211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7124412630085943623491229 2671654736282228858809211)
                      ·
                        rfl

theorem cell23_5203029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_5203029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203029 prefixEnd_5203029 := by exact prefixLift 5203029
  have htrace : WordTrace (prefixWord ++ tailWord_5203029) baseStart_5203029 baseEnd_5203029 := by
    simpa [prefixWord, tailWord_5203029, baseEnd_5203029] using wordTrace_append hprefix tailTrace_5203029
  have hstable : (prefixWord ++ tailWord_5203029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203029).length < 2 ^ (prefixWord ++ tailWord_5203029).sum := by decide
  have hdescent : baseEnd_5203029 < baseStart_5203029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203076 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_5203076 : Nat := 118140960795 + 5203076 * 2 ^ 59
def prefixEnd_5203076 : Nat := 4983230072969 + 3 ^ 40 * 5203076 * 2
def baseEnd_5203076 : Nat := 2671678869872990174921495

theorem tailTrace_5203076 : CollatzResearch.WordTrace tailWord_5203076 prefixEnd_5203076 2671678869872990174921495 := by
  unfold tailWord_5203076
  simp only [CollatzResearch.WordTrace]
  refine ⟨94885886049075870739842541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126514514732101160986456721 94885886049075870739842541)
  ·
    refine ⟨35582207268403451527440953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94885886049075870739842541 35582207268403451527440953)
    ·
      refine ⟨26686655451302588645580715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35582207268403451527440953 26686655451302588645580715)
      ·
        refine ⟨40029983176953882968371073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26686655451302588645580715 40029983176953882968371073)
        ·
          refine ⟨30022487382715412226278305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40029983176953882968371073 30022487382715412226278305)
          ·
            refine ⟨22516865537036559169708729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30022487382715412226278305 22516865537036559169708729)
            ·
              refine ⟨16887649152777419377281547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22516865537036559169708729 16887649152777419377281547)
              ·
                refine ⟨25331473729166129065922321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16887649152777419377281547 25331473729166129065922321)
                ·
                  refine ⟨18998605296874596799441741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25331473729166129065922321 18998605296874596799441741)
                  ·
                    refine ⟨7124476986327973799790653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18998605296874596799441741 7124476986327973799790653)
                    ·
                      refine ⟨2671678869872990174921495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7124476986327973799790653 2671678869872990174921495)
                      ·
                        rfl

theorem cell23_5203076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_5203076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203076 prefixEnd_5203076 := by exact prefixLift 5203076
  have htrace : WordTrace (prefixWord ++ tailWord_5203076) baseStart_5203076 baseEnd_5203076 := by
    simpa [prefixWord, tailWord_5203076, baseEnd_5203076] using wordTrace_append hprefix tailTrace_5203076
  have hstable : (prefixWord ++ tailWord_5203076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203076).length < 2 ^ (prefixWord ++ tailWord_5203076).sum := by decide
  have hdescent : baseEnd_5203076 < baseStart_5203076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203077 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 2, 2, 2]
def baseStart_5203077 : Nat := 118140960795 + 5203077 * 2 ^ 59
def prefixEnd_5203077 : Nat := 4983230072969 + 3 ^ 40 * 5203077 * 2
def baseEnd_5203077 : Nat := 2671679383353644671008991

theorem tailTrace_5203077 : CollatzResearch.WordTrace tailWord_5203077 prefixEnd_5203077 2671679383353644671008991 := by
  unfold tailWord_5203077
  simp only [CollatzResearch.WordTrace]
  refine ⟨189771808571148118650471485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126514539047432079100314323 189771808571148118650471485)
  ·
    refine ⟨71164428214180544493926807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189771808571148118650471485 71164428214180544493926807)
    ·
      refine ⟨106746642321270816740890211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71164428214180544493926807 106746642321270816740890211)
      ·
        refine ⟨160119963481906225111335317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106746642321270816740890211 160119963481906225111335317)
        ·
          refine ⟨7505623288214354302093843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160119963481906225111335317 7505623288214354302093843)
          ·
            refine ⟨11258434932321531453140765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7505623288214354302093843 11258434932321531453140765)
            ·
              refine ⟨4221913099620574294927787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11258434932321531453140765 4221913099620574294927787)
              ·
                refine ⟨6332869649430861442391681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4221913099620574294927787 6332869649430861442391681)
                ·
                  refine ⟨4749652237073146081793761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6332869649430861442391681 4749652237073146081793761)
                  ·
                    refine ⟨3562239177804859561345321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4749652237073146081793761 3562239177804859561345321)
                    ·
                      refine ⟨2671679383353644671008991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562239177804859561345321 2671679383353644671008991)
                      ·
                        rfl

theorem cell23_5203077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_5203077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203077 prefixEnd_5203077 := by exact prefixLift 5203077
  have htrace : WordTrace (prefixWord ++ tailWord_5203077) baseStart_5203077 baseEnd_5203077 := by
    simpa [prefixWord, tailWord_5203077, baseEnd_5203077] using wordTrace_append hprefix tailTrace_5203077
  have hstable : (prefixWord ++ tailWord_5203077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203077).length < 2 ^ (prefixWord ++ tailWord_5203077).sum := by decide
  have hdescent : baseEnd_5203077 < baseStart_5203077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203116 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 2, 4, 2]
def baseStart_5203116 : Nat := 118140960795 + 5203116 * 2 ^ 59
def prefixEnd_5203116 : Nat := 4983230072969 + 3 ^ 40 * 5203116 * 2
def baseEnd_5203116 : Nat := 2671699409099170018421311

theorem tailTrace_5203116 : CollatzResearch.WordTrace tailWord_5203116 prefixEnd_5203116 2671699409099170018421311 := by
  unfold tailWord_5203116
  simp only [CollatzResearch.WordTrace]
  refine ⟨94886615509003414155570601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126515487345337885540760801 94886615509003414155570601)
  ·
    refine ⟨71164961631752560616677951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94886615509003414155570601 71164961631752560616677951)
    ·
      refine ⟨106747442447628840925016927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71164961631752560616677951 106747442447628840925016927)
      ·
        refine ⟨160121163671443261387525391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106747442447628840925016927 160121163671443261387525391)
        ·
          refine ⟨240181745507164892081288087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160121163671443261387525391 240181745507164892081288087)
          ·
            refine ⟨360272618260747338121932131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240181745507164892081288087 360272618260747338121932131)
            ·
              refine ⟨540408927391121007182898197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360272618260747338121932131 540408927391121007182898197)
              ·
                refine ⟨25331668471458797211698353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 540408927391121007182898197 25331668471458797211698353)
                ·
                  refine ⟨18998751353594097908773765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25331668471458797211698353 18998751353594097908773765)
                  ·
                    refine ⟨3562265878798893357895081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18998751353594097908773765 3562265878798893357895081)
                    ·
                      refine ⟨2671699409099170018421311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562265878798893357895081 2671699409099170018421311)
                      ·
                        rfl

theorem cell23_5203116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_5203116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203116 prefixEnd_5203116 := by exact prefixLift 5203116
  have htrace : WordTrace (prefixWord ++ tailWord_5203116) baseStart_5203116 baseEnd_5203116 := by
    simpa [prefixWord, tailWord_5203116, baseEnd_5203116] using wordTrace_append hprefix tailTrace_5203116
  have hstable : (prefixWord ++ tailWord_5203116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203116).length < 2 ^ (prefixWord ++ tailWord_5203116).sum := by decide
  have hdescent : baseEnd_5203116 < baseStart_5203116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203173 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 6]
def baseStart_5203173 : Nat := 118140960795 + 5203173 * 2 ^ 59
def prefixEnd_5203173 : Nat := 4983230072969 + 3 ^ 40 * 5203173 * 2
def baseEnd_5203173 : Nat := 296858741944052921712061

theorem tailTrace_5203173 : CollatzResearch.WordTrace tailWord_5203173 prefixEnd_5203173 296858741944052921712061 := by
  unfold tailWord_5203173
  simp only [CollatzResearch.WordTrace]
  refine ⟨189775309978800327045966173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126516873319200218030644115 189775309978800327045966173)
  ·
    refine ⟨71165741242050122642237315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189775309978800327045966173 71165741242050122642237315)
    ·
      refine ⟨106748611863075183963355973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71165741242050122642237315 106748611863075183963355973)
      ·
        refine ⟨20015364724326596993129245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106748611863075183963355973 20015364724326596993129245)
        ·
          refine ⟨7505761771622473872423467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20015364724326596993129245 7505761771622473872423467)
          ·
            refine ⟨11258642657433710808635201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7505761771622473872423467 11258642657433710808635201)
            ·
              refine ⟨8443981993075283106476401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11258642657433710808635201 8443981993075283106476401)
              ·
                refine ⟨6332986494806462329857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8443981993075283106476401 6332986494806462329857301)
                ·
                  refine ⟨296858741944052921712061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6332986494806462329857301 296858741944052921712061)
                  ·
                    rfl

theorem cell23_5203173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_5203173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203173 prefixEnd_5203173 := by exact prefixLift 5203173
  have htrace : WordTrace (prefixWord ++ tailWord_5203173) baseStart_5203173 baseEnd_5203173 := by
    simpa [prefixWord, tailWord_5203173, baseEnd_5203173] using wordTrace_append hprefix tailTrace_5203173
  have hstable : (prefixWord ++ tailWord_5203173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203173).length < 2 ^ (prefixWord ++ tailWord_5203173).sum := by decide
  have hdescent : baseEnd_5203173 < baseStart_5203173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203219 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6]
def baseStart_5203219 : Nat := 118140960795 + 5203219 * 2 ^ 59
def prefixEnd_5203219 : Nat := 4983230072969 + 3 ^ 40 * 5203219 * 2
def baseEnd_5203219 : Nat := 2671752297606583115433337

theorem tailTrace_5203219 : CollatzResearch.WordTrace tailWord_5203219 prefixEnd_5203219 2671752297606583115433337 := by
  unfold tailWord_5203219
  simp only [CollatzResearch.WordTrace]
  refine ⟨189776987736633676902140711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126517991824422451268093807 189776987736633676902140711)
  ·
    refine ⟨284665481604950515353211067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189776987736633676902140711 284665481604950515353211067)
    ·
      refine ⟨426998222407425773029816601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284665481604950515353211067 426998222407425773029816601)
      ·
        refine ⟨320248666805569329772362451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426998222407425773029816601 320248666805569329772362451)
        ·
          refine ⟨480373000208353994658543677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320248666805569329772362451 480373000208353994658543677)
          ·
            refine ⟨180139875078132747996953879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 480373000208353994658543677 180139875078132747996953879)
            ·
              refine ⟨270209812617199121995430819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180139875078132747996953879 270209812617199121995430819)
              ·
                refine ⟨405314718925798682993146229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270209812617199121995430819 405314718925798682993146229)
                ·
                  refine ⟨37998254899293626530607459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405314718925798682993146229 37998254899293626530607459)
                  ·
                    refine ⟨56997382348940439795911189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37998254899293626530607459 56997382348940439795911189)
                    ·
                      refine ⟨2671752297606583115433337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56997382348940439795911189 2671752297606583115433337)
                      ·
                        rfl

theorem cell23_5203219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_5203219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203219 prefixEnd_5203219 := by exact prefixLift 5203219
  have htrace : WordTrace (prefixWord ++ tailWord_5203219) baseStart_5203219 baseEnd_5203219 := by
    simpa [prefixWord, tailWord_5203219, baseEnd_5203219] using wordTrace_append hprefix tailTrace_5203219
  have hstable : (prefixWord ++ tailWord_5203219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203219).length < 2 ^ (prefixWord ++ tailWord_5203219).sum := by decide
  have hdescent : baseEnd_5203219 < baseStart_5203219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203223 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_5203223 : Nat := 118140960795 + 5203223 * 2 ^ 59
def prefixEnd_5203223 : Nat := 4983230072969 + 3 ^ 40 * 5203223 * 2
def baseEnd_5203223 : Nat := 2671754351529201099783319

theorem tailTrace_5203223 : CollatzResearch.WordTrace tailWord_5203223 prefixEnd_5203223 2671754351529201099783319 := by
  unfold tailWord_5203223
  simp only [CollatzResearch.WordTrace]
  refine ⟨189777133628619185585286323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126518089085746123723524215 189777133628619185585286323)
  ·
    refine ⟨284665700442928778377929485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189777133628619185585286323 284665700442928778377929485)
    ·
      refine ⟨106749637666098291891723557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284665700442928778377929485 106749637666098291891723557)
      ·
        refine ⟨20015557062393429729698167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106749637666098291891723557 20015557062393429729698167)
        ·
          refine ⟨30023335593590144594547251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20015557062393429729698167 30023335593590144594547251)
          ·
            refine ⟨45035003390385216891820877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30023335593590144594547251 45035003390385216891820877)
            ·
              refine ⟨16888126271394456334432829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45035003390385216891820877 16888126271394456334432829)
              ·
                refine ⟨6333047351772921125412311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16888126271394456334432829 6333047351772921125412311)
                ·
                  refine ⟨9499571027659381688118467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333047351772921125412311 9499571027659381688118467)
                  ·
                    refine ⟨14249356541489072532177701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9499571027659381688118467 14249356541489072532177701)
                    ·
                      refine ⟨2671754351529201099783319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14249356541489072532177701 2671754351529201099783319)
                      ·
                        rfl

theorem cell23_5203223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_5203223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203223 prefixEnd_5203223 := by exact prefixLift 5203223
  have htrace : WordTrace (prefixWord ++ tailWord_5203223) baseStart_5203223 baseEnd_5203223 := by
    simpa [prefixWord, tailWord_5203223, baseEnd_5203223] using wordTrace_append hprefix tailTrace_5203223
  have hstable : (prefixWord ++ tailWord_5203223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203223).length < 2 ^ (prefixWord ++ tailWord_5203223).sum := by decide
  have hdescent : baseEnd_5203223 < baseStart_5203223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203236 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_5203236 : Nat := 118140960795 + 5203236 * 2 ^ 59
def prefixEnd_5203236 : Nat := 4983230072969 + 3 ^ 40 * 5203236 * 2
def baseEnd_5203236 : Nat := 2671761026777709548920759

theorem tailTrace_5203236 : CollatzResearch.WordTrace tailWord_5203236 prefixEnd_5203236 2671761026777709548920759 := by
  unfold tailWord_5203236
  simp only [CollatzResearch.WordTrace]
  refine ⟨94888803888786044402754781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126518405185048059203673041 94888803888786044402754781)
  ·
    refine ⟨35583301458294766651033043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94888803888786044402754781 35583301458294766651033043)
    ·
      refine ⟨53374952187442149976549565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35583301458294766651033043 53374952187442149976549565)
      ·
        refine ⟨20015607070290806241206087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53374952187442149976549565 20015607070290806241206087)
        ·
          refine ⟨30023410605436209361809131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20015607070290806241206087 30023410605436209361809131)
          ·
            refine ⟨45035115908154314042713697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30023410605436209361809131 45035115908154314042713697)
            ·
              refine ⟨33776336931115735532035273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45035115908154314042713697 33776336931115735532035273)
              ·
                refine ⟨25332252698336801649026455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33776336931115735532035273 25332252698336801649026455)
                ·
                  refine ⟨37998379047505202473539683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25332252698336801649026455 37998379047505202473539683)
                  ·
                    refine ⟨56997568571257803710309525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37998379047505202473539683 56997568571257803710309525)
                    ·
                      refine ⟨2671761026777709548920759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56997568571257803710309525 2671761026777709548920759)
                      ·
                        rfl

theorem cell23_5203236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_5203236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203236 prefixEnd_5203236 := by exact prefixLift 5203236
  have htrace : WordTrace (prefixWord ++ tailWord_5203236) baseStart_5203236 baseEnd_5203236 := by
    simpa [prefixWord, tailWord_5203236, baseEnd_5203236] using wordTrace_append hprefix tailTrace_5203236
  have hstable : (prefixWord ++ tailWord_5203236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203236).length < 2 ^ (prefixWord ++ tailWord_5203236).sum := by decide
  have hdescent : baseEnd_5203236 < baseStart_5203236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203253 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_5203253 : Nat := 118140960795 + 5203253 * 2 ^ 59
def prefixEnd_5203253 : Nat := 4983230072969 + 3 ^ 40 * 5203253 * 2
def baseEnd_5203253 : Nat := 2671769755948835982408181

theorem tailTrace_5203253 : CollatzResearch.WordTrace tailWord_5203253 prefixEnd_5203253 2671769755948835982408181 := by
  unfold tailWord_5203253
  simp only [CollatzResearch.WordTrace]
  refine ⟨189778227818510500708878413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126518818545673667139252275 189778227818510500708878413)
  ·
    refine ⟨71166835431941437765829405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189778227818510500708878413 71166835431941437765829405)
    ·
      refine ⟨26687563286978039162186027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71166835431941437765829405 26687563286978039162186027)
      ·
        refine ⟨40031344930467058743279041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26687563286978039162186027 40031344930467058743279041)
        ·
          refine ⟨30023508697850294057459281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40031344930467058743279041 30023508697850294057459281)
          ·
            refine ⟨22517631523387720543094461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30023508697850294057459281 22517631523387720543094461)
            ·
              refine ⟨8444111821270395203660423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22517631523387720543094461 8444111821270395203660423)
              ·
                refine ⟨12666167731905592805490635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8444111821270395203660423 12666167731905592805490635)
                ·
                  refine ⟨18999251597858389208235953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12666167731905592805490635 18999251597858389208235953)
                  ·
                    refine ⟨14249438698393791906176965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18999251597858389208235953 14249438698393791906176965)
                    ·
                      refine ⟨2671769755948835982408181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14249438698393791906176965 2671769755948835982408181)
                      ·
                        rfl

theorem cell23_5203253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_5203253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203253 prefixEnd_5203253 := by exact prefixLift 5203253
  have htrace : WordTrace (prefixWord ++ tailWord_5203253) baseStart_5203253 baseEnd_5203253 := by
    simpa [prefixWord, tailWord_5203253, baseEnd_5203253] using wordTrace_append hprefix tailTrace_5203253
  have hstable : (prefixWord ++ tailWord_5203253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203253).length < 2 ^ (prefixWord ++ tailWord_5203253).sum := by decide
  have hdescent : baseEnd_5203253 < baseStart_5203253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203259 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 9]
def baseStart_5203259 : Nat := 118140960795 + 5203259 * 2 ^ 59
def prefixEnd_5203259 : Nat := 4983230072969 + 3 ^ 40 * 5203259 * 2
def baseEnd_5203259 : Nat := 890590945610920986311051

theorem tailTrace_5203259 : CollatzResearch.WordTrace tailWord_5203259 prefixEnd_5203259 890590945610920986311051 := by
  unfold tailWord_5203259
  simp only [CollatzResearch.WordTrace]
  refine ⟨189778446656488763733596831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126518964437659175822397887 189778446656488763733596831)
  ·
    refine ⟨284667669984733145600395247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189778446656488763733596831 284667669984733145600395247)
    ·
      refine ⟨427001504977099718400592871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284667669984733145600395247 427001504977099718400592871)
      ·
        refine ⟨640502257465649577600889307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427001504977099718400592871 640502257465649577600889307)
        ·
          refine ⟨960753386198474366401333961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640502257465649577600889307 960753386198474366401333961)
          ·
            refine ⟨720565039648855774801000471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960753386198474366401333961 720565039648855774801000471)
            ·
              refine ⟨1080847559473283662201500707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720565039648855774801000471 1080847559473283662201500707)
              ·
                refine ⟨1621271339209925493302251061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080847559473283662201500707 1621271339209925493302251061)
                ·
                  refine ⟨151994188050930514997086037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1621271339209925493302251061 151994188050930514997086037)
                  ·
                    refine ⟨890590945610920986311051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151994188050930514997086037 890590945610920986311051)
                    ·
                      rfl

theorem cell23_5203259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_5203259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203259 prefixEnd_5203259 := by exact prefixLift 5203259
  have htrace : WordTrace (prefixWord ++ tailWord_5203259) baseStart_5203259 baseEnd_5203259 := by
    simpa [prefixWord, tailWord_5203259, baseEnd_5203259] using wordTrace_append hprefix tailTrace_5203259
  have hstable : (prefixWord ++ tailWord_5203259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203259).length < 2 ^ (prefixWord ++ tailWord_5203259).sum := by decide
  have hdescent : baseEnd_5203259 < baseStart_5203259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203260 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_5203260 : Nat := 118140960795 + 5203260 * 2 ^ 59
def prefixEnd_5203260 : Nat := 4983230072969 + 3 ^ 40 * 5203260 * 2
def baseEnd_5203260 : Nat := 2671773350313417455020649

theorem tailTrace_5203260 : CollatzResearch.WordTrace tailWord_5203260 prefixEnd_5203260 2671773350313417455020649 := by
  unfold tailWord_5203260
  simp only [CollatzResearch.WordTrace]
  refine ⟨94889241564742570452191617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126518988752990093936255489 94889241564742570452191617)
  ·
    refine ⟨71166931173556927839143713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94889241564742570452191617 71166931173556927839143713)
    ·
      refine ⟨53375198380167695879357785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71166931173556927839143713 53375198380167695879357785)
      ·
        refine ⟨40031398785125771909518339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53375198380167695879357785 40031398785125771909518339)
        ·
          refine ⟨60047098177688657864277509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40031398785125771909518339 60047098177688657864277509)
          ·
            refine ⟨11258830908316623349552033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60047098177688657864277509 11258830908316623349552033)
            ·
              refine ⟨8444123181237467512164025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11258830908316623349552033 8444123181237467512164025)
              ·
                refine ⟨6333092385928100634123019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8444123181237467512164025 6333092385928100634123019)
                ·
                  refine ⟨9499638578892150951184529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333092385928100634123019 9499638578892150951184529)
                  ·
                    refine ⟨7124728934169113213388397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9499638578892150951184529 7124728934169113213388397)
                    ·
                      refine ⟨2671773350313417455020649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7124728934169113213388397 2671773350313417455020649)
                      ·
                        rfl

theorem cell23_5203260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_5203260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203260 prefixEnd_5203260 := by exact prefixLift 5203260
  have htrace : WordTrace (prefixWord ++ tailWord_5203260) baseStart_5203260 baseEnd_5203260 := by
    simpa [prefixWord, tailWord_5203260, baseEnd_5203260] using wordTrace_append hprefix tailTrace_5203260
  have hstable : (prefixWord ++ tailWord_5203260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203260).length < 2 ^ (prefixWord ++ tailWord_5203260).sum := by decide
  have hdescent : baseEnd_5203260 < baseStart_5203260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203263 : List Nat := [1, 1, 2, 2, 4, 4, 2, 7]
def baseStart_5203263 : Nat := 118140960795 + 5203263 * 2 ^ 59
def prefixEnd_5203263 : Nat := 4983230072969 + 3 ^ 40 * 5203263 * 2
def baseEnd_5203263 : Nat := 98954625583532627529005

theorem tailTrace_5203263 : CollatzResearch.WordTrace tailWord_5203263 prefixEnd_5203263 98954625583532627529005 := by
  unfold tailWord_5203263
  simp only [CollatzResearch.WordTrace]
  refine ⟨189778592548474272416742443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126519061698982848277828295 189778592548474272416742443)
  ·
    refine ⟨284667888822711408625113665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189778592548474272416742443 284667888822711408625113665)
    ·
      refine ⟨213500916617033556468835249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284667888822711408625113665 213500916617033556468835249)
      ·
        refine ⟨160125687462775167351626437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213500916617033556468835249 160125687462775167351626437)
        ·
          refine ⟨30023566399270343878429957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160125687462775167351626437 30023566399270343878429957)
          ·
            refine ⟨5629418699863189477205617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30023566399270343878429957 5629418699863189477205617)
            ·
              refine ⟨4222064024897392107904213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5629418699863189477205617 4222064024897392107904213)
              ·
                refine ⟨98954625583532627529005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4222064024897392107904213 98954625583532627529005)
                ·
                  rfl

theorem cell23_5203263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 7].length) (baseStart_5203263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203263 prefixEnd_5203263 := by exact prefixLift 5203263
  have htrace : WordTrace (prefixWord ++ tailWord_5203263) baseStart_5203263 baseEnd_5203263 := by
    simpa [prefixWord, tailWord_5203263, baseEnd_5203263] using wordTrace_append hprefix tailTrace_5203263
  have hstable : (prefixWord ++ tailWord_5203263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203263).length < 2 ^ (prefixWord ++ tailWord_5203263).sum := by decide
  have hdescent : baseEnd_5203263 < baseStart_5203263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203273 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 3]
def baseStart_5203273 : Nat := 118140960795 + 5203273 * 2 ^ 59
def prefixEnd_5203273 : Nat := 4983230072969 + 3 ^ 40 * 5203273 * 2
def baseEnd_5203273 : Nat := 2671780025561925904158089

theorem tailTrace_5203273 : CollatzResearch.WordTrace tailWord_5203273 prefixEnd_5203273 2671780025561925904158089 := by
  unfold tailWord_5203273
  simp only [CollatzResearch.WordTrace]
  refine ⟨189778957278438044124606473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126519304852292029416404315 189778957278438044124606473)
  ·
    refine ⟨142334217958828533093454855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189778957278438044124606473 142334217958828533093454855)
    ·
      refine ⟨213501326938242799640182283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142334217958828533093454855 213501326938242799640182283)
      ·
        refine ⟨320251990407364199460273425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213501326938242799640182283 320251990407364199460273425)
        ·
          refine ⟨240188992805523149595205069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320251990407364199460273425 240188992805523149595205069)
          ·
            refine ⟨90070872302071181098201901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240188992805523149595205069 90070872302071181098201901)
            ·
              refine ⟨33776577113276692911825713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90070872302071181098201901 33776577113276692911825713)
              ·
                refine ⟨25332432834957519683869285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33776577113276692911825713 25332432834957519683869285)
                ·
                  refine ⟨4749831156554534940725491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25332432834957519683869285 4749831156554534940725491)
                  ·
                    refine ⟨7124746734831802411088237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4749831156554534940725491 7124746734831802411088237)
                    ·
                      refine ⟨2671780025561925904158089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7124746734831802411088237 2671780025561925904158089)
                      ·
                        rfl

theorem cell23_5203273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 3].length) (baseStart_5203273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203273 prefixEnd_5203273 := by exact prefixLift 5203273
  have htrace : WordTrace (prefixWord ++ tailWord_5203273) baseStart_5203273 baseEnd_5203273 := by
    simpa [prefixWord, tailWord_5203273, baseEnd_5203273] using wordTrace_append hprefix tailTrace_5203273
  have hstable : (prefixWord ++ tailWord_5203273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203273).length < 2 ^ (prefixWord ++ tailWord_5203273).sum := by decide
  have hdescent : baseEnd_5203273 < baseStart_5203273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203277 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5203277 : Nat := 118140960795 + 5203277 * 2 ^ 59
def prefixEnd_5203277 : Nat := 4983230072969 + 3 ^ 40 * 5203277 * 2
def baseEnd_5203277 : Nat := 2671782079484543888508071

theorem tailTrace_5203277 : CollatzResearch.WordTrace tailWord_5203277 prefixEnd_5203277 2671782079484543888508071 := by
  unfold tailWord_5203277
  simp only [CollatzResearch.WordTrace]
  refine ⟨189779103170423552807752085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126519402113615701871834723 189779103170423552807752085)
  ·
    refine ⟨8895895461113604037863379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 189779103170423552807752085 8895895461113604037863379)
    ·
      refine ⟨13343843191670406056795069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895895461113604037863379 13343843191670406056795069)
      ·
        refine ⟨5003941196876402271298151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13343843191670406056795069 5003941196876402271298151)
        ·
          refine ⟨7505911795314603406947227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5003941196876402271298151 7505911795314603406947227)
          ·
            refine ⟨11258867692971905110420841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7505911795314603406947227 11258867692971905110420841)
            ·
              refine ⟨8444150769728928832815631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11258867692971905110420841 8444150769728928832815631)
              ·
                refine ⟨12666226154593393249223447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8444150769728928832815631 12666226154593393249223447)
                ·
                  refine ⟨18999339231890089873835171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12666226154593393249223447 18999339231890089873835171)
                  ·
                    refine ⟨28499008847835134810752757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18999339231890089873835171 28499008847835134810752757)
                    ·
                      refine ⟨2671782079484543888508071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28499008847835134810752757 2671782079484543888508071)
                      ·
                        rfl

theorem cell23_5203277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5203277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203277 prefixEnd_5203277 := by exact prefixLift 5203277
  have htrace : WordTrace (prefixWord ++ tailWord_5203277) baseStart_5203277 baseEnd_5203277 := by
    simpa [prefixWord, tailWord_5203277, baseEnd_5203277] using wordTrace_append hprefix tailTrace_5203277
  have hstable : (prefixWord ++ tailWord_5203277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203277).length < 2 ^ (prefixWord ++ tailWord_5203277).sum := by decide
  have hdescent : baseEnd_5203277 < baseStart_5203277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203317 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_5203317 : Nat := 118140960795 + 5203317 * 2 ^ 59
def prefixEnd_5203317 : Nat := 4983230072969 + 3 ^ 40 * 5203317 * 2
def baseEnd_5203317 : Nat := 2671802618710723732007887

theorem tailTrace_5203317 : CollatzResearch.WordTrace tailWord_5203317 prefixEnd_5203317 2671802618710723732007887 := by
  unfold tailWord_5203317
  simp only [CollatzResearch.WordTrace]
  refine ⟨189780562090278639639208205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126520374726852426426138803 189780562090278639639208205)
  ·
    refine ⟨71167710783854489864703077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189780562090278639639208205 71167710783854489864703077)
    ·
      refine ⟨13343945771972716849631827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71167710783854489864703077 13343945771972716849631827)
      ·
        refine ⟨20015918657959075274447741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13343945771972716849631827 20015918657959075274447741)
        ·
          refine ⟨7505969496734653227917903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20015918657959075274447741 7505969496734653227917903)
          ·
            refine ⟨11258954245101979841876855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7505969496734653227917903 11258954245101979841876855)
            ·
              refine ⟨16888431367652969762815283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11258954245101979841876855 16888431367652969762815283)
              ·
                refine ⟨25332647051479454644222925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16888431367652969762815283 25332647051479454644222925)
                ·
                  refine ⟨9499742644304795491583597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25332647051479454644222925 9499742644304795491583597)
                  ·
                    refine ⟨3562403491614298309343849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9499742644304795491583597 3562403491614298309343849)
                    ·
                      refine ⟨2671802618710723732007887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562403491614298309343849 2671802618710723732007887)
                      ·
                        rfl

theorem cell23_5203317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_5203317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203317 prefixEnd_5203317 := by exact prefixLift 5203317
  have htrace : WordTrace (prefixWord ++ tailWord_5203317) baseStart_5203317 baseEnd_5203317 := by
    simpa [prefixWord, tailWord_5203317, baseEnd_5203317] using wordTrace_append hprefix tailTrace_5203317
  have hstable : (prefixWord ++ tailWord_5203317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203317).length < 2 ^ (prefixWord ++ tailWord_5203317).sum := by decide
  have hdescent : baseEnd_5203317 < baseStart_5203317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203363 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 3]
def baseStart_5203363 : Nat := 118140960795 + 5203363 * 2 ^ 59
def prefixEnd_5203363 : Nat := 4983230072969 + 3 ^ 40 * 5203363 * 2
def baseEnd_5203363 : Nat := 2671826238820830552032675

theorem tailTrace_5203363 : CollatzResearch.WordTrace tailWord_5203363 prefixEnd_5203363 2671826238820830552032675 := by
  unfold tailWord_5203363
  simp only [CollatzResearch.WordTrace]
  refine ⟨189782239848111989495382743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126521493232074659663588495 189782239848111989495382743)
  ·
    refine ⟨284673359772167984243074115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189782239848111989495382743 284673359772167984243074115)
    ·
      refine ⟨427010039658251976364611173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284673359772167984243074115 427010039658251976364611173)
      ·
        refine ⟨80064382435922245568364595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 427010039658251976364611173 80064382435922245568364595)
        ·
          refine ⟨120096573653883368352546893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80064382435922245568364595 120096573653883368352546893)
          ·
            refine ⟨45036215120206263132205085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120096573653883368352546893 45036215120206263132205085)
            ·
              refine ⟨16888580670077348674576907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45036215120206263132205085 16888580670077348674576907)
              ·
                refine ⟨25332871005116023011865361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16888580670077348674576907 25332871005116023011865361)
                ·
                  refine ⟨18999653253837017258899021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25332871005116023011865361 18999653253837017258899021)
                  ·
                    refine ⟨7124869970188881472087133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18999653253837017258899021 7124869970188881472087133)
                    ·
                      refine ⟨2671826238820830552032675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7124869970188881472087133 2671826238820830552032675)
                      ·
                        rfl

theorem cell23_5203363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_5203363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203363 prefixEnd_5203363 := by exact prefixLift 5203363
  have htrace : WordTrace (prefixWord ++ tailWord_5203363) baseStart_5203363 baseEnd_5203363 := by
    simpa [prefixWord, tailWord_5203363, baseEnd_5203363] using wordTrace_append hprefix tailTrace_5203363
  have hstable : (prefixWord ++ tailWord_5203363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203363).length < 2 ^ (prefixWord ++ tailWord_5203363).sum := by decide
  have hdescent : baseEnd_5203363 < baseStart_5203363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203376 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_5203376 : Nat := 118140960795 + 5203376 * 2 ^ 59
def prefixEnd_5203376 : Nat := 4983230072969 + 3 ^ 40 * 5203376 * 2
def baseEnd_5203376 : Nat := 2671832914069339001170115

theorem tailTrace_5203376 : CollatzResearch.WordTrace tailWord_5203376 prefixEnd_5203376 2671832914069339001170115 := by
  unfold tailWord_5203376
  simp only [CollatzResearch.WordTrace]
  refine ⟨94891356998532446357802991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126521809331376595143737321 94891356998532446357802991)
  ·
    refine ⟨142337035497798669536704487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94891356998532446357802991 142337035497798669536704487)
    ·
      refine ⟨213505553246698004305056731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142337035497798669536704487 213505553246698004305056731)
      ·
        refine ⟨320258329870047006457585097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213505553246698004305056731 320258329870047006457585097)
        ·
          refine ⟨240193747402535254843188823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320258329870047006457585097 240193747402535254843188823)
          ·
            refine ⟨360290621103802882264783235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240193747402535254843188823 360290621103802882264783235)
            ·
              refine ⟨540435931655704323397174853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360290621103802882264783235 540435931655704323397174853)
              ·
                refine ⟨101331737185444560636970285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540435931655704323397174853 101331737185444560636970285)
                ·
                  refine ⟨37999401444541710238863857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101331737185444560636970285 37999401444541710238863857)
                  ·
                    refine ⟨28499551083406282679147893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37999401444541710238863857 28499551083406282679147893)
                    ·
                      refine ⟨2671832914069339001170115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28499551083406282679147893 2671832914069339001170115)
                      ·
                        rfl

theorem cell23_5203376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_5203376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203376 prefixEnd_5203376 := by exact prefixLift 5203376
  have htrace : WordTrace (prefixWord ++ tailWord_5203376) baseStart_5203376 baseEnd_5203376 := by
    simpa [prefixWord, tailWord_5203376, baseEnd_5203376] using wordTrace_append hprefix tailTrace_5203376
  have hstable : (prefixWord ++ tailWord_5203376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203376).length < 2 ^ (prefixWord ++ tailWord_5203376).sum := by decide
  have hdescent : baseEnd_5203376 < baseStart_5203376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203403 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 4]
def baseStart_5203403 : Nat := 118140960795 + 5203403 * 2 ^ 59
def prefixEnd_5203403 : Nat := 4983230072969 + 3 ^ 40 * 5203403 * 2
def baseEnd_5203403 : Nat := 2671846778047010395532491

theorem tailTrace_5203403 : CollatzResearch.WordTrace tailWord_5203403 prefixEnd_5203403 2671846778047010395532491 := by
  unfold tailWord_5203403
  simp only [CollatzResearch.WordTrace]
  refine ⟨189783698767967076326838863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126522465845311384217892575 189783698767967076326838863)
  ·
    refine ⟨284675548151950614490258295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189783698767967076326838863 284675548151950614490258295)
    ·
      refine ⟨427013322227925921735387443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284675548151950614490258295 427013322227925921735387443)
      ·
        refine ⟨640519983341888882603081165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427013322227925921735387443 640519983341888882603081165)
        ·
          refine ⟨240194993753208330976155437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640519983341888882603081165 240194993753208330976155437)
          ·
            refine ⟨90073122657453124116058289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240194993753208330976155437 90073122657453124116058289)
            ·
              refine ⟨67554841993089843087043717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90073122657453124116058289 67554841993089843087043717)
              ·
                refine ⟨12666532873704345578820697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67554841993089843087043717 12666532873704345578820697)
                ·
                  refine ⟨9499899655278259184115523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12666532873704345578820697 9499899655278259184115523)
                  ·
                    refine ⟨14249849482917388776173285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9499899655278259184115523 14249849482917388776173285)
                    ·
                      refine ⟨2671846778047010395532491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14249849482917388776173285 2671846778047010395532491)
                      ·
                        rfl

theorem cell23_5203403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 4].length) (baseStart_5203403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203403 prefixEnd_5203403 := by exact prefixLift 5203403
  have htrace : WordTrace (prefixWord ++ tailWord_5203403) baseStart_5203403 baseEnd_5203403 := by
    simpa [prefixWord, tailWord_5203403, baseEnd_5203403] using wordTrace_append hprefix tailTrace_5203403
  have hstable : (prefixWord ++ tailWord_5203403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203403).length < 2 ^ (prefixWord ++ tailWord_5203403).sum := by decide
  have hdescent : baseEnd_5203403 < baseStart_5203403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203423 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 3]
def baseStart_5203423 : Nat := 118140960795 + 5203423 * 2 ^ 59
def prefixEnd_5203423 : Nat := 4983230072969 + 3 ^ 40 * 5203423 * 2
def baseEnd_5203423 : Nat := 2671857047660100317282399

theorem tailTrace_5203423 : CollatzResearch.WordTrace tailWord_5203423 prefixEnd_5203423 2671857047660100317282399 := by
  unfold tailWord_5203423
  simp only [CollatzResearch.WordTrace]
  refine ⟨189784428227894619742566923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126522952151929746495044615 189784428227894619742566923)
  ·
    refine ⟨284676642341841929613850385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189784428227894619742566923 284676642341841929613850385)
    ·
      refine ⟨213507481756381447210387789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284676642341841929613850385 213507481756381447210387789)
      ·
        refine ⟨80065305658643042703895421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213507481756381447210387789 80065305658643042703895421)
        ·
          refine ⟨30024489621991141013960783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80065305658643042703895421 30024489621991141013960783)
          ·
            refine ⟨45036734432986711520941175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30024489621991141013960783 45036734432986711520941175)
            ·
              refine ⟨67555101649480067281411763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45036734432986711520941175 67555101649480067281411763)
              ·
                refine ⟨101332652474220100922117645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67555101649480067281411763 101332652474220100922117645)
                ·
                  refine ⟨37999744677832537845794117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101332652474220100922117645 37999744677832537845794117)
                  ·
                    refine ⟨7124952127093600846086397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37999744677832537845794117 7124952127093600846086397)
                    ·
                      refine ⟨2671857047660100317282399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7124952127093600846086397 2671857047660100317282399)
                      ·
                        rfl

theorem cell23_5203423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_5203423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203423 prefixEnd_5203423 := by exact prefixLift 5203423
  have htrace : WordTrace (prefixWord ++ tailWord_5203423) baseStart_5203423 baseEnd_5203423 := by
    simpa [prefixWord, tailWord_5203423, baseEnd_5203423] using wordTrace_append hprefix tailTrace_5203423
  have hstable : (prefixWord ++ tailWord_5203423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203423).length < 2 ^ (prefixWord ++ tailWord_5203423).sum := by decide
  have hdescent : baseEnd_5203423 < baseStart_5203423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203454 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5203454 : Nat := 118140960795 + 5203454 * 2 ^ 59
def prefixEnd_5203454 : Nat := 4983230072969 + 3 ^ 40 * 5203454 * 2
def baseEnd_5203454 : Nat := 2671872965560389695994757

theorem tailTrace_5203454 : CollatzResearch.WordTrace tailWord_5203454 prefixEnd_5203454 2671872965560389695994757 := by
  unfold tailWord_5203454
  simp only [CollatzResearch.WordTrace]
  refine ⟨23723194861347789004618177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126523705927188208024630277 23723194861347789004618177)
  ·
    refine ⟨17792396146010841753463633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23723194861347789004618177 17792396146010841753463633)
    ·
      refine ⟨13344297109508131315097725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17792396146010841753463633 13344297109508131315097725)
      ·
        refine ⟨5004111416065549243161647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13344297109508131315097725 5004111416065549243161647)
        ·
          refine ⟨7506167124098323864742471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5004111416065549243161647 7506167124098323864742471)
          ·
            refine ⟨11259250686147485797113707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7506167124098323864742471 11259250686147485797113707)
            ·
              refine ⟨16888876029221228695670561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11259250686147485797113707 16888876029221228695670561)
              ·
                refine ⟨12666657021915921521752921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16888876029221228695670561 12666657021915921521752921)
                ·
                  refine ⟨9499992766436941141314691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12666657021915921521752921 9499992766436941141314691)
                  ·
                    refine ⟨14249989149655411711972037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9499992766436941141314691 14249989149655411711972037)
                    ·
                      refine ⟨2671872965560389695994757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14249989149655411711972037 2671872965560389695994757)
                      ·
                        rfl

theorem cell23_5203454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5203454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203454 prefixEnd_5203454 := by exact prefixLift 5203454
  have htrace : WordTrace (prefixWord ++ tailWord_5203454) baseStart_5203454 baseEnd_5203454 := by
    simpa [prefixWord, tailWord_5203454, baseEnd_5203454] using wordTrace_append hprefix tailTrace_5203454
  have hstable : (prefixWord ++ tailWord_5203454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203454).length < 2 ^ (prefixWord ++ tailWord_5203454).sum := by decide
  have hdescent : baseEnd_5203454 < baseStart_5203454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203457 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_5203457 : Nat := 118140960795 + 5203457 * 2 ^ 59
def prefixEnd_5203457 : Nat := 4983230072969 + 3 ^ 40 * 5203457 * 2
def baseEnd_5203457 : Nat := 2671874506002353184257243

theorem tailTrace_5203457 : CollatzResearch.WordTrace tailWord_5203457 prefixEnd_5203457 2671874506002353184257243 := by
  unfold tailWord_5203457
  simp only [CollatzResearch.WordTrace]
  refine ⟨189785668309771443549304625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126523778873180962366203083 189785668309771443549304625)
  ·
    refine ⟨142339251232328582661978469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189785668309771443549304625 142339251232328582661978469)
    ·
      refine ⟨26688609606061609249120963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142339251232328582661978469 26688609606061609249120963)
      ·
        refine ⟨40032914409092413873681445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26688609606061609249120963 40032914409092413873681445)
        ·
          refine ⟨7506171451704827601315271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40032914409092413873681445 7506171451704827601315271)
          ·
            refine ⟨11259257177557241401972907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7506171451704827601315271 11259257177557241401972907)
            ·
              refine ⟨16888885766335862102959361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11259257177557241401972907 16888885766335862102959361)
              ·
                refine ⟨12666664324751896577219521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16888885766335862102959361 12666664324751896577219521)
                ·
                  refine ⟨9499998243563922432914641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12666664324751896577219521 9499998243563922432914641)
                  ·
                    refine ⟨7124998682672941824685981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9499998243563922432914641 7124998682672941824685981)
                    ·
                      refine ⟨2671874506002353184257243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7124998682672941824685981 2671874506002353184257243)
                      ·
                        rfl

theorem cell23_5203457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_5203457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203457 prefixEnd_5203457 := by exact prefixLift 5203457
  have htrace : WordTrace (prefixWord ++ tailWord_5203457) baseStart_5203457 baseEnd_5203457 := by
    simpa [prefixWord, tailWord_5203457, baseEnd_5203457] using wordTrace_append hprefix tailTrace_5203457
  have hstable : (prefixWord ++ tailWord_5203457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203457).length < 2 ^ (prefixWord ++ tailWord_5203457).sum := by decide
  have hdescent : baseEnd_5203457 < baseStart_5203457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203473 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 3, 5]
def baseStart_5203473 : Nat := 118140960795 + 5203473 * 2 ^ 59
def prefixEnd_5203473 : Nat := 4983230072969 + 3 ^ 40 * 5203473 * 2
def baseEnd_5203473 : Nat := 890627573897608373885723

theorem tailTrace_5203473 : CollatzResearch.WordTrace tailWord_5203473 prefixEnd_5203473 890627573897608373885723 := by
  unfold tailWord_5203473
  simp only [CollatzResearch.WordTrace]
  refine ⟨189786251877713478281887073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126524167918475652187924715 189786251877713478281887073)
  ·
    refine ⟨142339688908285108711415305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189786251877713478281887073 142339688908285108711415305)
    ·
      refine ⟨106754766681213831533561479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142339688908285108711415305 106754766681213831533561479)
      ·
        refine ⟨160132150021820747300342219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106754766681213831533561479 160132150021820747300342219)
        ·
          refine ⟨240198225032731120950513329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160132150021820747300342219 240198225032731120950513329)
          ·
            refine ⟨180148668774548340712884997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240198225032731120950513329 180148668774548340712884997)
            ·
              refine ⟨33777875395227813883665937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180148668774548340712884997 33777875395227813883665937)
              ·
                refine ⟨25333406546420860412749453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33777875395227813883665937 25333406546420860412749453)
                ·
                  refine ⟨9500027454907822654781045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25333406546420860412749453 9500027454907822654781045)
                  ·
                    refine ⟨890627573897608373885723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9500027454907822654781045 890627573897608373885723)
                    ·
                      rfl

theorem cell23_5203473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_5203473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203473 prefixEnd_5203473 := by exact prefixLift 5203473
  have htrace : WordTrace (prefixWord ++ tailWord_5203473) baseStart_5203473 baseEnd_5203473 := by
    simpa [prefixWord, tailWord_5203473, baseEnd_5203473] using wordTrace_append hprefix tailTrace_5203473
  have hstable : (prefixWord ++ tailWord_5203473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203473).length < 2 ^ (prefixWord ++ tailWord_5203473).sum := by decide
  have hdescent : baseEnd_5203473 < baseStart_5203473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203477 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 6]
def baseStart_5203477 : Nat := 118140960795 + 5203477 * 2 ^ 59
def prefixEnd_5203477 : Nat := 4983230072969 + 3 ^ 40 * 5203477 * 2
def baseEnd_5203477 : Nat := 296876086179493678445239

theorem tailTrace_5203477 : CollatzResearch.WordTrace tailWord_5203477 prefixEnd_5203477 296876086179493678445239 := by
  unfold tailWord_5203477
  simp only [CollatzResearch.WordTrace]
  refine ⟨189786397769698986965032685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126524265179799324643355123 189786397769698986965032685)
  ·
    refine ⟨71169899163637120111887257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189786397769698986965032685 71169899163637120111887257)
    ·
      refine ⟨53377424372727840083915443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71169899163637120111887257 53377424372727840083915443)
      ·
        refine ⟨80066136559091760125873165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53377424372727840083915443 80066136559091760125873165)
        ·
          refine ⟨30024801209659410047202437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80066136559091760125873165 30024801209659410047202437)
          ·
            refine ⟨5629650226811139383850457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30024801209659410047202437 5629650226811139383850457)
            ·
              refine ⟨4222237670108354537887843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5629650226811139383850457 4222237670108354537887843)
              ·
                refine ⟨6333356505162531806831765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222237670108354537887843 6333356505162531806831765)
                ·
                  refine ⟨296876086179493678445239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6333356505162531806831765 296876086179493678445239)
                  ·
                    rfl

theorem cell23_5203477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_5203477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203477 prefixEnd_5203477 := by exact prefixLift 5203477
  have htrace : WordTrace (prefixWord ++ tailWord_5203477) baseStart_5203477 baseEnd_5203477 := by
    simpa [prefixWord, tailWord_5203477, baseEnd_5203477] using wordTrace_append hprefix tailTrace_5203477
  have hstable : (prefixWord ++ tailWord_5203477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203477).length < 2 ^ (prefixWord ++ tailWord_5203477).sum := by decide
  have hdescent : baseEnd_5203477 < baseStart_5203477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203507 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 1, 5]
def baseStart_5203507 : Nat := 118140960795 + 5203507 * 2 ^ 59
def prefixEnd_5203507 : Nat := 4983230072969 + 3 ^ 40 * 5203507 * 2
def baseEnd_5203507 : Nat := 890633393345025996210671

theorem tailTrace_5203507 : CollatzResearch.WordTrace tailWord_5203507 prefixEnd_5203507 890633393345025996210671 := by
  unfold tailWord_5203507
  simp only [CollatzResearch.WordTrace]
  refine ⟨189787491959590302088624775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126524994639726868059083183 189787491959590302088624775)
  ·
    refine ⟨284681237939385453132937163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189787491959590302088624775 284681237939385453132937163)
    ·
      refine ⟨427021856909078179699405745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284681237939385453132937163 427021856909078179699405745)
      ·
        refine ⟨320266392681808634774554309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427021856909078179699405745 320266392681808634774554309)
        ·
          refine ⟨60049948627839119020228933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 320266392681808634774554309 60049948627839119020228933)
          ·
            refine ⟨11259365367719834816292925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60049948627839119020228933 11259365367719834816292925)
            ·
              refine ⟨4222262012894938056109847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11259365367719834816292925 4222262012894938056109847)
              ·
                refine ⟨6333393019342407084164771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222262012894938056109847 6333393019342407084164771)
                ·
                  refine ⟨9500089529013610626247157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333393019342407084164771 9500089529013610626247157)
                  ·
                    refine ⟨890633393345025996210671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9500089529013610626247157 890633393345025996210671)
                    ·
                      rfl

theorem cell23_5203507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 5].length) (baseStart_5203507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203507 prefixEnd_5203507 := by exact prefixLift 5203507
  have htrace : WordTrace (prefixWord ++ tailWord_5203507) baseStart_5203507 baseEnd_5203507 := by
    simpa [prefixWord, tailWord_5203507, baseEnd_5203507] using wordTrace_append hprefix tailTrace_5203507
  have hstable : (prefixWord ++ tailWord_5203507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203507).length < 2 ^ (prefixWord ++ tailWord_5203507).sum := by decide
  have hdescent : baseEnd_5203507 < baseStart_5203507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203530 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_5203530 : Nat := 118140960795 + 5203530 * 2 ^ 59
def prefixEnd_5203530 : Nat := 4983230072969 + 3 ^ 40 * 5203530 * 2
def baseEnd_5203530 : Nat := 2671911990090131398644407

theorem tailTrace_5203530 : CollatzResearch.WordTrace tailWord_5203530 prefixEnd_5203530 2671911990090131398644407 := by
  unfold tailWord_5203530
  simp only [CollatzResearch.WordTrace]
  refine ⟨47447082709626744254178011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126525553892337984677808029 47447082709626744254178011)
  ·
    refine ⟨71170624064440116381267017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47447082709626744254178011 71170624064440116381267017)
    ·
      refine ⟨53377968048330087285950263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71170624064440116381267017 53377968048330087285950263)
      ·
        refine ⟨80066952072495130928925395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53377968048330087285950263 80066952072495130928925395)
        ·
          refine ⟨120100428108742696393388093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80066952072495130928925395 120100428108742696393388093)
          ·
            refine ⟨45037660540778511147520535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120100428108742696393388093 45037660540778511147520535)
            ·
              refine ⟨67556490811167766721280803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45037660540778511147520535 67556490811167766721280803)
              ·
                refine ⟨101334736216751650081921205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67556490811167766721280803 101334736216751650081921205)
                ·
                  refine ⟨9500131520320467195180113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101334736216751650081921205 9500131520320467195180113)
                  ·
                    refine ⟨7125098640240350396385085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9500131520320467195180113 7125098640240350396385085)
                    ·
                      refine ⟨2671911990090131398644407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7125098640240350396385085 2671911990090131398644407)
                      ·
                        rfl

theorem cell23_5203530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_5203530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203530 prefixEnd_5203530 := by exact prefixLift 5203530
  have htrace : WordTrace (prefixWord ++ tailWord_5203530) baseStart_5203530 baseEnd_5203530 := by
    simpa [prefixWord, tailWord_5203530, baseEnd_5203530] using wordTrace_append hprefix tailTrace_5203530
  have hstable : (prefixWord ++ tailWord_5203530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203530).length < 2 ^ (prefixWord ++ tailWord_5203530).sum := by decide
  have hdescent : baseEnd_5203530 < baseStart_5203530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203577 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 3]
def baseStart_5203577 : Nat := 118140960795 + 5203577 * 2 ^ 59
def prefixEnd_5203577 : Nat := 4983230072969 + 3 ^ 40 * 5203577 * 2
def baseEnd_5203577 : Nat := 2671936123680892714756691

theorem tailTrace_5203577 : CollatzResearch.WordTrace tailWord_5203577 prefixEnd_5203577 2671936123680892714756691 := by
  unfold tailWord_5203577
  simp only [CollatzResearch.WordTrace]
  refine ⟨189790045069336704043672985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126526696712891136029115323 189790045069336704043672985)
  ·
    refine ⟨142342533802002528032754739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189790045069336704043672985 142342533802002528032754739)
    ·
      refine ⟨213513800703003792049132109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142342533802002528032754739 213513800703003792049132109)
      ·
        refine ⟨80067675263626422018424541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213513800703003792049132109 80067675263626422018424541)
        ·
          refine ⟨30025378223859908256909203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80067675263626422018424541 30025378223859908256909203)
          ·
            refine ⟨45038067335789862385363805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30025378223859908256909203 45038067335789862385363805)
            ·
              refine ⟨16889275250921198394511427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45038067335789862385363805 16889275250921198394511427)
              ·
                refine ⟨25333912876381797591767141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16889275250921198394511427 25333912876381797591767141)
                ·
                  refine ⟨4750108664321587048456339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25333912876381797591767141 4750108664321587048456339)
                  ·
                    refine ⟨7125162996482380572684509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4750108664321587048456339 7125162996482380572684509)
                    ·
                      refine ⟨2671936123680892714756691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7125162996482380572684509 2671936123680892714756691)
                      ·
                        rfl

theorem cell23_5203577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_5203577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203577 prefixEnd_5203577 := by exact prefixLift 5203577
  have htrace : WordTrace (prefixWord ++ tailWord_5203577) baseStart_5203577 baseEnd_5203577 := by
    simpa [prefixWord, tailWord_5203577, baseEnd_5203577] using wordTrace_append hprefix tailTrace_5203577
  have hstable : (prefixWord ++ tailWord_5203577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203577).length < 2 ^ (prefixWord ++ tailWord_5203577).sum := by decide
  have hdescent : baseEnd_5203577 < baseStart_5203577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203594 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_5203594 : Nat := 118140960795 + 5203594 * 2 ^ 59
def prefixEnd_5203594 : Nat := 4983230072969 + 3 ^ 40 * 5203594 * 2
def baseEnd_5203594 : Nat := 2671944852852019148244113

theorem tailTrace_5203594 : CollatzResearch.WordTrace tailWord_5203594 prefixEnd_5203594 2671944852852019148244113 := by
  unfold tailWord_5203594
  simp only [CollatzResearch.WordTrace]
  refine ⟨47447666277568778986760459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126527110073516743964694557 47447666277568778986760459)
  ·
    refine ⟨71171499416353168480140689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47447666277568778986760459 71171499416353168480140689)
    ·
      refine ⟨53378624562264876360105517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71171499416353168480140689 53378624562264876360105517)
      ·
        refine ⟨20016984210849328635039569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53378624562264876360105517 20016984210849328635039569)
        ·
          refine ⟨15012738158136996476279677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20016984210849328635039569 15012738158136996476279677)
          ·
            refine ⟨5629776809301373678604879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15012738158136996476279677 5629776809301373678604879)
            ·
              refine ⟨8444665213952060517907319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5629776809301373678604879 8444665213952060517907319)
              ·
                refine ⟨12666997820928090776860979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8444665213952060517907319 12666997820928090776860979)
                ·
                  refine ⟨19000496731392136165291469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12666997820928090776860979 19000496731392136165291469)
                  ·
                    refine ⟨7125186274272051061984301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19000496731392136165291469 7125186274272051061984301)
                    ·
                      refine ⟨2671944852852019148244113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7125186274272051061984301 2671944852852019148244113)
                      ·
                        rfl

theorem cell23_5203594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_5203594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203594 prefixEnd_5203594 := by exact prefixLift 5203594
  have htrace : WordTrace (prefixWord ++ tailWord_5203594) baseStart_5203594 baseEnd_5203594 := by
    simpa [prefixWord, tailWord_5203594, baseEnd_5203594] using wordTrace_append hprefix tailTrace_5203594
  have hstable : (prefixWord ++ tailWord_5203594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203594).length < 2 ^ (prefixWord ++ tailWord_5203594).sum := by decide
  have hdescent : baseEnd_5203594 < baseStart_5203594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203620 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_5203620 : Nat := 118140960795 + 5203620 * 2 ^ 59
def prefixEnd_5203620 : Nat := 4983230072969 + 3 ^ 40 * 5203620 * 2
def baseEnd_5203620 : Nat := 2671958203349036046518993

theorem tailTrace_5203620 : CollatzResearch.WordTrace tailWord_5203620 prefixEnd_5203620 2671958203349036046518993 := by
  unfold tailWord_5203620
  simp only [CollatzResearch.WordTrace]
  refine ⟨94895806704090461193744157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126527742272120614924992209 94895806704090461193744157)
  ·
    refine ⟨35585927514033922947654059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94895806704090461193744157 35585927514033922947654059)
    ·
      refine ⟨53378891271050884421481089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35585927514033922947654059 53378891271050884421481089)
      ·
        refine ⟨40034168453288163316110817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53378891271050884421481089 40034168453288163316110817)
        ·
          refine ⟨30025626339966122487083113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40034168453288163316110817 30025626339966122487083113)
          ·
            refine ⟨22519219754974591865312335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30025626339966122487083113 22519219754974591865312335)
            ·
              refine ⟨33778829632461887797968503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22519219754974591865312335 33778829632461887797968503)
              ·
                refine ⟨50668244448692831696952755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33778829632461887797968503 50668244448692831696952755)
                ·
                  refine ⟨76002366673039247545429133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50668244448692831696952755 76002366673039247545429133)
                  ·
                    refine ⟨28500887502389717829535925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76002366673039247545429133 28500887502389717829535925)
                    ·
                      refine ⟨2671958203349036046518993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28500887502389717829535925 2671958203349036046518993)
                      ·
                        rfl

theorem cell23_5203620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_5203620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203620 prefixEnd_5203620 := by exact prefixLift 5203620
  have htrace : WordTrace (prefixWord ++ tailWord_5203620) baseStart_5203620 baseEnd_5203620 := by
    simpa [prefixWord, tailWord_5203620, baseEnd_5203620] using wordTrace_append hprefix tailTrace_5203620
  have hstable : (prefixWord ++ tailWord_5203620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203620).length < 2 ^ (prefixWord ++ tailWord_5203620).sum := by decide
  have hdescent : baseEnd_5203620 < baseStart_5203620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203634 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_5203634 : Nat := 118140960795 + 5203634 * 2 ^ 59
def prefixEnd_5203634 : Nat := 4983230072969 + 3 ^ 40 * 5203634 * 2
def baseEnd_5203634 : Nat := 2671965392078198991743929

theorem tailTrace_5203634 : CollatzResearch.WordTrace tailWord_5203634 prefixEnd_5203634 2671965392078198991743929 := by
  unfold tailWord_5203634
  simp only [CollatzResearch.WordTrace]
  refine ⟨47448031007532550694624489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126528082686753468518998637 47448031007532550694624489)
  ·
    refine ⟨35586023255649413020968367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47448031007532550694624489 35586023255649413020968367)
    ·
      refine ⟨53379034883474119531452551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35586023255649413020968367 53379034883474119531452551)
      ·
        refine ⟨80068552325211179297178827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53379034883474119531452551 80068552325211179297178827)
        ·
          refine ⟨120102828487816768945768241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80068552325211179297178827 120102828487816768945768241)
          ·
            refine ⟨90077121365862576709326181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120102828487816768945768241 90077121365862576709326181)
            ·
              refine ⟨16889460256099233132998659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90077121365862576709326181 16889460256099233132998659)
              ·
                refine ⟨25334190384148849699497989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16889460256099233132998659 25334190384148849699497989)
                ·
                  refine ⟨4750160697027909318655873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25334190384148849699497989 4750160697027909318655873)
                  ·
                    refine ⟨3562620522770931988991905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4750160697027909318655873 3562620522770931988991905)
                    ·
                      refine ⟨2671965392078198991743929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562620522770931988991905 2671965392078198991743929)
                      ·
                        rfl

theorem cell23_5203634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_5203634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203634 prefixEnd_5203634 := by exact prefixLift 5203634
  have htrace : WordTrace (prefixWord ++ tailWord_5203634) baseStart_5203634 baseEnd_5203634 := by
    simpa [prefixWord, tailWord_5203634, baseEnd_5203634] using wordTrace_append hprefix tailTrace_5203634
  have hstable : (prefixWord ++ tailWord_5203634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203634).length < 2 ^ (prefixWord ++ tailWord_5203634).sum := by decide
  have hdescent : baseEnd_5203634 < baseStart_5203634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203680 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_5203680 : Nat := 118140960795 + 5203680 * 2 ^ 59
def prefixEnd_5203680 : Nat := 4983230072969 + 3 ^ 40 * 5203680 * 2
def baseEnd_5203680 : Nat := 2671989012188305811768717

theorem tailTrace_5203680 : CollatzResearch.WordTrace tailWord_5203680 prefixEnd_5203680 2671989012188305811768717 := by
  unfold tailWord_5203680
  simp only [CollatzResearch.WordTrace]
  refine ⟨94896900893981776317336247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126529201191975701756448329 94896900893981776317336247)
  ·
    refine ⟨142345351340972664476004371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94896900893981776317336247 142345351340972664476004371)
    ·
      refine ⟨213518027011458996714006557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142345351340972664476004371 213518027011458996714006557)
      ·
        refine ⟨80069260129297123767752459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213518027011458996714006557 80069260129297123767752459)
        ·
          refine ⟨120103890193945685651628689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80069260129297123767752459 120103890193945685651628689)
          ·
            refine ⟨90077917645459264238721517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120103890193945685651628689 90077917645459264238721517)
            ·
              refine ⟨33779219117047224089520569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90077917645459264238721517 33779219117047224089520569)
              ·
                refine ⟨25334414337785418067140427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33779219117047224089520569 25334414337785418067140427)
                ·
                  refine ⟨38001621506678127100710641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25334414337785418067140427 38001621506678127100710641)
                  ·
                    refine ⟨28501216130008595325532981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38001621506678127100710641 28501216130008595325532981)
                    ·
                      refine ⟨2671989012188305811768717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28501216130008595325532981 2671989012188305811768717)
                      ·
                        rfl

theorem cell23_5203680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_5203680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203680 prefixEnd_5203680 := by exact prefixLift 5203680
  have htrace : WordTrace (prefixWord ++ tailWord_5203680) baseStart_5203680 baseEnd_5203680 := by
    simpa [prefixWord, tailWord_5203680, baseEnd_5203680] using wordTrace_append hprefix tailTrace_5203680
  have hstable : (prefixWord ++ tailWord_5203680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203680).length < 2 ^ (prefixWord ++ tailWord_5203680).sum := by decide
  have hdescent : baseEnd_5203680 < baseStart_5203680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203727 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 3]
def baseStart_5203727 : Nat := 118140960795 + 5203727 * 2 ^ 59
def prefixEnd_5203727 : Nat := 4983230072969 + 3 ^ 40 * 5203727 * 2
def baseEnd_5203727 : Nat := 2672013145779067127881001

theorem tailTrace_5203727 : CollatzResearch.WordTrace tailWord_5203727 prefixEnd_5203727 2672013145779067127881001 := by
  unfold tailWord_5203727
  simp only [CollatzResearch.WordTrace]
  refine ⟨189795516018793279661633435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126530344012528853107755623 189795516018793279661633435)
  ·
    refine ⟨284693274028189919492450153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189795516018793279661633435 284693274028189919492450153)
    ·
      refine ⟨213519955521142439619337615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284693274028189919492450153 213519955521142439619337615)
      ·
        refine ⟨320279933281713659429006423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213519955521142439619337615 320279933281713659429006423)
        ·
          refine ⟨480419899922570489143509635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320279933281713659429006423 480419899922570489143509635)
          ·
            refine ⟨720629849883855733715264453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480419899922570489143509635 720629849883855733715264453)
            ·
              refine ⟨135118096853222950071612085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 720629849883855733715264453 135118096853222950071612085)
              ·
                refine ⟨12667321579989651569213633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135118096853222950071612085 12667321579989651569213633)
                ·
                  refine ⟨9500491184992238676910225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12667321579989651569213633 9500491184992238676910225)
                  ·
                    refine ⟨7125368388744179007682669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9500491184992238676910225 7125368388744179007682669)
                    ·
                      refine ⟨2672013145779067127881001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7125368388744179007682669 2672013145779067127881001)
                      ·
                        rfl

theorem cell23_5203727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_5203727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203727 prefixEnd_5203727 := by exact prefixLift 5203727
  have htrace : WordTrace (prefixWord ++ tailWord_5203727) baseStart_5203727 baseEnd_5203727 := by
    simpa [prefixWord, tailWord_5203727, baseEnd_5203727] using wordTrace_append hprefix tailTrace_5203727
  have hstable : (prefixWord ++ tailWord_5203727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203727).length < 2 ^ (prefixWord ++ tailWord_5203727).sum := by decide
  have hdescent : baseEnd_5203727 < baseStart_5203727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203747 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 6]
def baseStart_5203747 : Nat := 118140960795 + 5203747 * 2 ^ 59
def prefixEnd_5203747 : Nat := 4983230072969 + 3 ^ 40 * 5203747 * 2
def baseEnd_5203747 : Nat := 296891490599128561070101

theorem tailTrace_5203747 : CollatzResearch.WordTrace tailWord_5203747 prefixEnd_5203747 296891490599128561070101 := by
  unfold tailWord_5203747
  simp only [CollatzResearch.WordTrace]
  refine ⟨189796245478720823077361495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126530830319147215384907663 189796245478720823077361495)
  ·
    refine ⟨284694368218081234616042243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189796245478720823077361495 284694368218081234616042243)
    ·
      refine ⟨427041552327121851924063365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284694368218081234616042243 427041552327121851924063365)
      ·
        refine ⟨80070291061335347235761881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 427041552327121851924063365 80070291061335347235761881)
        ·
          refine ⟨60052718296001510426821411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80070291061335347235761881 60052718296001510426821411)
          ·
            refine ⟨90079077444002265640232117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60052718296001510426821411 90079077444002265640232117)
            ·
              refine ⟨8444913510375212403771761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90079077444002265640232117 8444913510375212403771761)
              ·
                refine ⟨6333685132781409302828821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8444913510375212403771761 6333685132781409302828821)
                ·
                  refine ⟨296891490599128561070101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6333685132781409302828821 296891490599128561070101)
                  ·
                    rfl

theorem cell23_5203747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 6].length) (baseStart_5203747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203747 prefixEnd_5203747 := by exact prefixLift 5203747
  have htrace : WordTrace (prefixWord ++ tailWord_5203747) baseStart_5203747 baseEnd_5203747 := by
    simpa [prefixWord, tailWord_5203747, baseEnd_5203747] using wordTrace_append hprefix tailTrace_5203747
  have hstable : (prefixWord ++ tailWord_5203747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203747).length < 2 ^ (prefixWord ++ tailWord_5203747).sum := by decide
  have hdescent : baseEnd_5203747 < baseStart_5203747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203784 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_5203784 : Nat := 118140960795 + 5203784 * 2 ^ 59
def prefixEnd_5203784 : Nat := 4983230072969 + 3 ^ 40 * 5203784 * 2
def baseEnd_5203784 : Nat := 2672042414176373404868239

theorem tailTrace_5203784 : CollatzResearch.WordTrace tailWord_5203784 prefixEnd_5203784 2672042414176373404868239 := by
  unfold tailWord_5203784
  simp only [CollatzResearch.WordTrace]
  refine ⟨94898797489793389198229203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126531729986391185597638937 94898797489793389198229203)
  ·
    refine ⟨142348196234690083797343805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94898797489793389198229203 142348196234690083797343805)
    ·
      refine ⟨53380573588008781424003927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142348196234690083797343805 53380573588008781424003927)
      ·
        refine ⟨80070860382013172136005891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53380573588008781424003927 80070860382013172136005891)
        ·
          refine ⟨120106290573019758204008837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80070860382013172136005891 120106290573019758204008837)
          ·
            refine ⟨22519929482441204663251657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120106290573019758204008837 22519929482441204663251657)
            ·
              refine ⟨16889947111830903497438743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22519929482441204663251657 16889947111830903497438743)
              ·
                refine ⟨25334920667746355246158115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16889947111830903497438743 25334920667746355246158115)
                ·
                  refine ⟨38002381001619532869237173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25334920667746355246158115 38002381001619532869237173)
                  ·
                    refine ⟨3562723218901831206490985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38002381001619532869237173 3562723218901831206490985)
                    ·
                      refine ⟨2672042414176373404868239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562723218901831206490985 2672042414176373404868239)
                      ·
                        rfl

theorem cell23_5203784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_5203784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203784 prefixEnd_5203784 := by exact prefixLift 5203784
  have htrace : WordTrace (prefixWord ++ tailWord_5203784) baseStart_5203784 baseEnd_5203784 := by
    simpa [prefixWord, tailWord_5203784, baseEnd_5203784] using wordTrace_append hprefix tailTrace_5203784
  have hstable : (prefixWord ++ tailWord_5203784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203784).length < 2 ^ (prefixWord ++ tailWord_5203784).sum := by decide
  have hdescent : baseEnd_5203784 < baseStart_5203784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203794 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_5203794 : Nat := 118140960795 + 5203794 * 2 ^ 59
def prefixEnd_5203794 : Nat := 4983230072969 + 3 ^ 40 * 5203794 * 2
def baseEnd_5203794 : Nat := 890682516327639455247731

theorem tailTrace_5203794 : CollatzResearch.WordTrace tailWord_5203794 prefixEnd_5203794 890682516327639455247731 := by
  unfold tailWord_5203794
  simp only [CollatzResearch.WordTrace]
  refine ⟨47449489927387637526080609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126531973139700366736214957 47449489927387637526080609)
  ·
    refine ⟨35587117445540728144560457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47449489927387637526080609 35587117445540728144560457)
    ·
      refine ⟨26690338084155546108420343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35587117445540728144560457 26690338084155546108420343)
      ·
        refine ⟨40035507126233319162630515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26690338084155546108420343 40035507126233319162630515)
        ·
          refine ⟨60053260689349978743945773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40035507126233319162630515 60053260689349978743945773)
          ·
            refine ⟨22519972758506242028979665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60053260689349978743945773 22519972758506242028979665)
            ·
              refine ⟨16889979568879681521734749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22519972758506242028979665 16889979568879681521734749)
              ·
                refine ⟨6333742338329880570650531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16889979568879681521734749 6333742338329880570650531)
                ·
                  refine ⟨9500613507494820855975797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333742338329880570650531 9500613507494820855975797)
                  ·
                    refine ⟨890682516327639455247731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9500613507494820855975797 890682516327639455247731)
                    ·
                      rfl

theorem cell23_5203794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_5203794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203794 prefixEnd_5203794 := by exact prefixLift 5203794
  have htrace : WordTrace (prefixWord ++ tailWord_5203794) baseStart_5203794 baseEnd_5203794 := by
    simpa [prefixWord, tailWord_5203794, baseEnd_5203794] using wordTrace_append hprefix tailTrace_5203794
  have hstable : (prefixWord ++ tailWord_5203794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203794).length < 2 ^ (prefixWord ++ tailWord_5203794).sum := by decide
  have hdescent : baseEnd_5203794 < baseStart_5203794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203827 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4]
def baseStart_5203827 : Nat := 118140960795 + 5203827 * 2 ^ 59
def prefixEnd_5203827 : Nat := 4983230072969 + 3 ^ 40 * 5203827 * 2
def baseEnd_5203827 : Nat := 2672064493844516736630541

theorem tailTrace_5203827 : CollatzResearch.WordTrace tailWord_5203827 prefixEnd_5203827 2672064493844516736630541 := by
  unfold tailWord_5203827
  simp only [CollatzResearch.WordTrace]
  refine ⟨189799163318430996740273735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126532775545620664493515823 189799163318430996740273735)
  ·
    refine ⟨284698744977646495110410603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189799163318430996740273735 284698744977646495110410603)
    ·
      refine ⟨427048117466469742665615905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284698744977646495110410603 427048117466469742665615905)
      ·
        refine ⟨320286088099852306999211929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427048117466469742665615905 320286088099852306999211929)
        ·
          refine ⟨240214566074889230249408947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320286088099852306999211929 240214566074889230249408947)
          ·
            refine ⟨360321849112333845374113421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240214566074889230249408947 360321849112333845374113421)
            ·
              refine ⟨135120693417125192015292533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360321849112333845374113421 135120693417125192015292533)
              ·
                refine ⟨12667565007855486751433675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135120693417125192015292533 12667565007855486751433675)
                ·
                  refine ⟨19001347511783230127150513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12667565007855486751433675 19001347511783230127150513)
                  ·
                    refine ⟨14251010633837422595362885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19001347511783230127150513 14251010633837422595362885)
                    ·
                      refine ⟨2672064493844516736630541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14251010633837422595362885 2672064493844516736630541)
                      ·
                        rfl

theorem cell23_5203827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_5203827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203827 prefixEnd_5203827 := by exact prefixLift 5203827
  have htrace : WordTrace (prefixWord ++ tailWord_5203827) baseStart_5203827 baseEnd_5203827 := by
    simpa [prefixWord, tailWord_5203827, baseEnd_5203827] using wordTrace_append hprefix tailTrace_5203827
  have hstable : (prefixWord ++ tailWord_5203827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203827).length < 2 ^ (prefixWord ++ tailWord_5203827).sum := by decide
  have hdescent : baseEnd_5203827 < baseStart_5203827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203841 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 1, 6]
def baseStart_5203841 : Nat := 118140960795 + 5203841 * 2 ^ 59
def prefixEnd_5203841 : Nat := 4983230072969 + 3 ^ 40 * 5203841 * 2
def baseEnd_5203841 : Nat := 890690560857893227285159

theorem tailTrace_5203841 : CollatzResearch.WordTrace tailWord_5203841 prefixEnd_5203841 890690560857893227285159 := by
  unfold tailWord_5203841
  simp only [CollatzResearch.WordTrace]
  refine ⟨189799673940380277131283377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126533115960253518087522251 189799673940380277131283377)
  ·
    refine ⟨142349755455285207848462533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189799673940380277131283377 142349755455285207848462533)
    ·
      refine ⟨26690579147865976471586725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142349755455285207848462533 26690579147865976471586725)
      ·
        refine ⟨5004483590224870588422511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26690579147865976471586725 5004483590224870588422511)
        ·
          refine ⟨7506725385337305882633767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5004483590224870588422511 7506725385337305882633767)
          ·
            refine ⟨11260088078005958823950651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7506725385337305882633767 11260088078005958823950651)
            ·
              refine ⟨16890132117008938235925977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11260088078005958823950651 16890132117008938235925977)
              ·
                refine ⟨12667599087756703676944483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16890132117008938235925977 12667599087756703676944483)
                ·
                  refine ⟨19001398631635055515416725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12667599087756703676944483 19001398631635055515416725)
                  ·
                    refine ⟨890690560857893227285159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19001398631635055515416725 890690560857893227285159)
                    ·
                      rfl

theorem cell23_5203841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_5203841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203841 prefixEnd_5203841 := by exact prefixLift 5203841
  have htrace : WordTrace (prefixWord ++ tailWord_5203841) baseStart_5203841 baseEnd_5203841 := by
    simpa [prefixWord, tailWord_5203841, baseEnd_5203841] using wordTrace_append hprefix tailTrace_5203841
  have hstable : (prefixWord ++ tailWord_5203841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203841).length < 2 ^ (prefixWord ++ tailWord_5203841).sum := by decide
  have hdescent : baseEnd_5203841 < baseStart_5203841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203848 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_5203848 : Nat := 118140960795 + 5203848 * 2 ^ 59
def prefixEnd_5203848 : Nat := 4983230072969 + 3 ^ 40 * 5203848 * 2
def baseEnd_5203848 : Nat := 2672075276938261154467945

theorem tailTrace_5203848 : CollatzResearch.WordTrace tailWord_5203848 prefixEnd_5203848 2672075276938261154467945 := by
  unfold tailWord_5203848
  simp only [CollatzResearch.WordTrace]
  refine ⟨94899964625677458663394099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126533286167569944884525465 94899964625677458663394099)
  ·
    refine ⟨142349946938516187995091149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94899964625677458663394099 142349946938516187995091149)
    ·
      refine ⟨53381230101943570498159181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142349946938516187995091149 53381230101943570498159181)
      ·
        refine ⟨20017961288228838936809693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53381230101943570498159181 20017961288228838936809693)
        ·
          refine ⟨7506735483085814601303635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20017961288228838936809693 7506735483085814601303635)
          ·
            refine ⟨11260103224628721901955453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7506735483085814601303635 11260103224628721901955453)
            ·
              refine ⟨4222538709235770713233295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11260103224628721901955453 4222538709235770713233295)
              ·
                refine ⟨6333808063853656069849943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222538709235770713233295 6333808063853656069849943)
                ·
                  refine ⟨9500712095780484104774915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333808063853656069849943 9500712095780484104774915)
                  ·
                    refine ⟨14251068143670726157162373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9500712095780484104774915 14251068143670726157162373)
                    ·
                      refine ⟨2672075276938261154467945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14251068143670726157162373 2672075276938261154467945)
                      ·
                        rfl

theorem cell23_5203848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_5203848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203848 prefixEnd_5203848 := by exact prefixLift 5203848
  have htrace : WordTrace (prefixWord ++ tailWord_5203848) baseStart_5203848 baseEnd_5203848 := by
    simpa [prefixWord, tailWord_5203848, baseEnd_5203848] using wordTrace_append hprefix tailTrace_5203848
  have hstable : (prefixWord ++ tailWord_5203848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203848).length < 2 ^ (prefixWord ++ tailWord_5203848).sum := by decide
  have hdescent : baseEnd_5203848 < baseStart_5203848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203854 : List Nat := [4, 1, 1, 5, 1, 11]
def baseStart_5203854 : Nat := 118140960795 + 5203854 * 2 ^ 59
def prefixEnd_5203854 : Nat := 4983230072969 + 3 ^ 40 * 5203854 * 2
def baseEnd_5203854 : Nat := 10996207233836165148119

theorem tailTrace_5203854 : CollatzResearch.WordTrace tailWord_5203854 prefixEnd_5203854 10996207233836165148119 := by
  unfold tailWord_5203854
  simp only [CollatzResearch.WordTrace]
  refine ⟨23725018511166647543938327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126533432059555453567671077 23725018511166647543938327)
  ·
    refine ⟨35587527766749971315907491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23725018511166647543938327 35587527766749971315907491)
    ·
      refine ⟨53381291650124956973861237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35587527766749971315907491 53381291650124956973861237)
      ·
        refine ⟨5004496092199214716299491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53381291650124956973861237 5004496092199214716299491)
        ·
          refine ⟨7506744138298822074449237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5004496092199214716299491 7506744138298822074449237)
          ·
            refine ⟨10996207233836165148119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7506744138298822074449237 10996207233836165148119)
            ·
              rfl

theorem cell23_5203854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 11].length) (baseStart_5203854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203854 prefixEnd_5203854 := by exact prefixLift 5203854
  have htrace : WordTrace (prefixWord ++ tailWord_5203854) baseStart_5203854 baseEnd_5203854 := by
    simpa [prefixWord, tailWord_5203854, baseEnd_5203854] using wordTrace_append hprefix tailTrace_5203854
  have hstable : (prefixWord ++ tailWord_5203854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203854).length < 2 ^ (prefixWord ++ tailWord_5203854).sum := by decide
  have hdescent : baseEnd_5203854 < baseStart_5203854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203858 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_5203858 : Nat := 118140960795 + 5203858 * 2 ^ 59
def prefixEnd_5203858 : Nat := 4983230072969 + 3 ^ 40 * 5203858 * 2
def baseEnd_5203858 : Nat := 890693470581602038447633

theorem tailTrace_5203858 : CollatzResearch.WordTrace tailWord_5203858 prefixEnd_5203858 890693470581602038447633 := by
  unfold tailWord_5203858
  simp only [CollatzResearch.WordTrace]
  refine ⟨47450073495329672258663057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126533529320879126023101485 47450073495329672258663057)
  ·
    refine ⟨35587555121497254193997293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47450073495329672258663057 35587555121497254193997293)
    ·
      refine ⟨13345333170561470322748985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35587555121497254193997293 13345333170561470322748985)
      ·
        refine ⟨10008999877921102742061739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13345333170561470322748985 10008999877921102742061739)
        ·
          refine ⟨15013499816881654113092609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10008999877921102742061739 15013499816881654113092609)
          ·
            refine ⟨11260124862661240584819457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15013499816881654113092609 11260124862661240584819457)
            ·
              refine ⟨8445093646995930438614593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11260124862661240584819457 8445093646995930438614593)
              ·
                refine ⟨6333820235246947828960945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8445093646995930438614593 6333820235246947828960945)
                ·
                  refine ⟨4750365176435210871720709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6333820235246947828960945 4750365176435210871720709)
                  ·
                    refine ⟨890693470581602038447633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4750365176435210871720709 890693470581602038447633)
                    ·
                      rfl

theorem cell23_5203858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_5203858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203858 prefixEnd_5203858 := by exact prefixLift 5203858
  have htrace : WordTrace (prefixWord ++ tailWord_5203858) baseStart_5203858 baseEnd_5203858 := by
    simpa [prefixWord, tailWord_5203858, baseEnd_5203858] using wordTrace_append hprefix tailTrace_5203858
  have hstable : (prefixWord ++ tailWord_5203858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203858).length < 2 ^ (prefixWord ++ tailWord_5203858).sum := by decide
  have hdescent : baseEnd_5203858 < baseStart_5203858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203865 : List Nat := [1, 2, 1, 2, 1, 3, 6, 2, 1, 2, 2]
def baseStart_5203865 : Nat := 118140960795 + 5203865 * 2 ^ 59
def prefixEnd_5203865 : Nat := 4983230072969 + 3 ^ 40 * 5203865 * 2
def baseEnd_5203865 : Nat := 2672084006109387587955367

theorem tailTrace_5203865 : CollatzResearch.WordTrace tailWord_5203865 prefixEnd_5203865 2672084006109387587955367 := by
  unfold tailWord_5203865
  simp only [CollatzResearch.WordTrace]
  refine ⟨189800549292293329230157049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126533699528195552820104699 189800549292293329230157049)
  ·
    refine ⟨142350411969219996922617787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189800549292293329230157049 142350411969219996922617787)
    ·
      refine ⟨213525617953829995383926681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142350411969219996922617787 213525617953829995383926681)
      ·
        refine ⟨160144213465372496537945011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213525617953829995383926681 160144213465372496537945011)
        ·
          refine ⟨240216320198058744806917517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160144213465372496537945011 240216320198058744806917517)
          ·
            refine ⟨90081120074272029302594069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240216320198058744806917517 90081120074272029302594069)
            ·
              refine ⟨4222552503481501373559097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90081120074272029302594069 4222552503481501373559097)
              ·
                refine ⟨3166914377611126030169323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4222552503481501373559097 3166914377611126030169323)
                ·
                  refine ⟨4750371566416689045253985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166914377611126030169323 4750371566416689045253985)
                  ·
                    refine ⟨3562778674812516783940489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4750371566416689045253985 3562778674812516783940489)
                    ·
                      refine ⟨2672084006109387587955367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562778674812516783940489 2672084006109387587955367)
                      ·
                        rfl

theorem cell23_5203865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_5203865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203865 prefixEnd_5203865 := by exact prefixLift 5203865
  have htrace : WordTrace (prefixWord ++ tailWord_5203865) baseStart_5203865 baseEnd_5203865 := by
    simpa [prefixWord, tailWord_5203865, baseEnd_5203865] using wordTrace_append hprefix tailTrace_5203865
  have hstable : (prefixWord ++ tailWord_5203865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203865).length < 2 ^ (prefixWord ++ tailWord_5203865).sum := by decide
  have hdescent : baseEnd_5203865 < baseStart_5203865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203871 : List Nat := [1, 1, 2, 5, 4, 1, 1, 8]
def baseStart_5203871 : Nat := 118140960795 + 5203871 * 2 ^ 59
def prefixEnd_5203871 : Nat := 4983230072969 + 3 ^ 40 * 5203871 * 2
def baseEnd_5203871 : Nat := 98966188407159798684457

theorem tailTrace_5203871 : CollatzResearch.WordTrace tailWord_5203871 prefixEnd_5203871 98966188407159798684457 := by
  unfold tailWord_5203871
  simp only [CollatzResearch.WordTrace]
  refine ⟨189800768130271592254875467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126533845420181061503250311 189800768130271592254875467)
  ·
    refine ⟨284701152195407388382313201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189800768130271592254875467 284701152195407388382313201)
    ·
      refine ⟨213525864146555541286734901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284701152195407388382313201 213525864146555541286734901)
      ·
        refine ⟨20018049763739581995631397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213525864146555541286734901 20018049763739581995631397)
        ·
          refine ⟨3753384330701171624180887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20018049763739581995631397 3753384330701171624180887)
          ·
            refine ⟨5630076496051757436271331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753384330701171624180887 5630076496051757436271331)
            ·
              refine ⟨8445114744077636154406997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5630076496051757436271331 8445114744077636154406997)
              ·
                refine ⟨98966188407159798684457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8445114744077636154406997 98966188407159798684457)
                ·
                  rfl

theorem cell23_5203871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 8].length) (baseStart_5203871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203871 prefixEnd_5203871 := by exact prefixLift 5203871
  have htrace : WordTrace (prefixWord ++ tailWord_5203871) baseStart_5203871 baseEnd_5203871 := by
    simpa [prefixWord, tailWord_5203871, baseEnd_5203871] using wordTrace_append hprefix tailTrace_5203871
  have hstable : (prefixWord ++ tailWord_5203871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203871).length < 2 ^ (prefixWord ++ tailWord_5203871).sum := by decide
  have hdescent : baseEnd_5203871 < baseStart_5203871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203887 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_5203887 : Nat := 118140960795 + 5203887 * 2 ^ 59
def prefixEnd_5203887 : Nat := 4983230072969 + 3 ^ 40 * 5203887 * 2
def baseEnd_5203887 : Nat := 2672095302683786501880265

theorem tailTrace_5203887 : CollatzResearch.WordTrace tailWord_5203887 prefixEnd_5203887 2672095302683786501880265 := by
  unfold tailWord_5203887
  simp only [CollatzResearch.WordTrace]
  refine ⟨189801351698213626987457915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126534234465475751324971943 189801351698213626987457915)
  ·
    refine ⟨284702027547320440481186873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189801351698213626987457915 284702027547320440481186873)
    ·
      refine ⟨213526520660490330360890155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284702027547320440481186873 213526520660490330360890155)
      ·
        refine ⟨320289780990735495541335233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213526520660490330360890155 320289780990735495541335233)
        ·
          refine ⟨240217335743051621656001425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320289780990735495541335233 240217335743051621656001425)
          ·
            refine ⟨180163001807288716242001069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240217335743051621656001425 180163001807288716242001069)
            ·
              refine ⟨67561125677733268590750401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180163001807288716242001069 67561125677733268590750401)
              ·
                refine ⟨50670844258299951443062801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67561125677733268590750401 50670844258299951443062801)
                ·
                  refine ⟨38003133193724963582297101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50670844258299951443062801 38003133193724963582297101)
                  ·
                    refine ⟨14251174947646861343361413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38003133193724963582297101 14251174947646861343361413)
                    ·
                      refine ⟨2672095302683786501880265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14251174947646861343361413 2672095302683786501880265)
                      ·
                        rfl

theorem cell23_5203887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_5203887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203887 prefixEnd_5203887 := by exact prefixLift 5203887
  have htrace : WordTrace (prefixWord ++ tailWord_5203887) baseStart_5203887 baseEnd_5203887 := by
    simpa [prefixWord, tailWord_5203887, baseEnd_5203887] using wordTrace_append hprefix tailTrace_5203887
  have hstable : (prefixWord ++ tailWord_5203887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203887).length < 2 ^ (prefixWord ++ tailWord_5203887).sum := by decide
  have hdescent : baseEnd_5203887 < baseStart_5203887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203891 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 1, 3, 2]
def baseStart_5203891 : Nat := 118140960795 + 5203891 * 2 ^ 59
def prefixEnd_5203891 : Nat := 4983230072969 + 3 ^ 40 * 5203891 * 2
def baseEnd_5203891 : Nat := 2672097356606404486230247

theorem tailTrace_5203891 : CollatzResearch.WordTrace tailWord_5203891 prefixEnd_5203891 2672097356606404486230247 := by
  unfold tailWord_5203891
  simp only [CollatzResearch.WordTrace]
  refine ⟨189801497590199135670603527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126534331726799423780402351 189801497590199135670603527)
  ·
    refine ⟨284702246385298703505905291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189801497590199135670603527 284702246385298703505905291)
    ·
      refine ⟨427053369577948055258857937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284702246385298703505905291 427053369577948055258857937)
      ·
        refine ⟨320290027183461041444143453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427053369577948055258857937 320290027183461041444143453)
        ·
          refine ⟨120108760193797890541553795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320290027183461041444143453 120108760193797890541553795)
          ·
            refine ⟨180163140290696835812330693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120108760193797890541553795 180163140290696835812330693)
            ·
              refine ⟨33780588804505656714812005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180163140290696835812330693 33780588804505656714812005)
              ·
                refine ⟨6333860400844810634027251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33780588804505656714812005 6333860400844810634027251)
                ·
                  refine ⟨9500790601267215951040877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333860400844810634027251 9500790601267215951040877)
                  ·
                    refine ⟨3562796475475205981640329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9500790601267215951040877 3562796475475205981640329)
                    ·
                      refine ⟨2672097356606404486230247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562796475475205981640329 2672097356606404486230247)
                      ·
                        rfl

theorem cell23_5203891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 3, 2].length) (baseStart_5203891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203891 prefixEnd_5203891 := by exact prefixLift 5203891
  have htrace : WordTrace (prefixWord ++ tailWord_5203891) baseStart_5203891 baseEnd_5203891 := by
    simpa [prefixWord, tailWord_5203891, baseEnd_5203891] using wordTrace_append hprefix tailTrace_5203891
  have hstable : (prefixWord ++ tailWord_5203891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203891).length < 2 ^ (prefixWord ++ tailWord_5203891).sum := by decide
  have hdescent : baseEnd_5203891 < baseStart_5203891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203897 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 1, 8]
def baseStart_5203897 : Nat := 118140960795 + 5203897 * 2 ^ 59
def prefixEnd_5203897 : Nat := 4983230072969 + 3 ^ 40 * 5203897 * 2
def baseEnd_5203897 : Nat := 890700145830110487585073

theorem tailTrace_5203897 : CollatzResearch.WordTrace tailWord_5203897 prefixEnd_5203897 890700145830110487585073 := by
  unfold tailWord_5203897
  simp only [CollatzResearch.WordTrace]
  refine ⟨189801716428177398695321945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126534477618784932463547963 189801716428177398695321945)
  ·
    refine ⟨142351287321133049021491459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189801716428177398695321945 142351287321133049021491459)
    ·
      refine ⟨213526930981699573532237189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142351287321133049021491459 213526930981699573532237189)
      ·
        refine ⟨40036299559068670037294473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213526930981699573532237189 40036299559068670037294473)
        ·
          refine ⟨30027224669301502527970855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40036299559068670037294473 30027224669301502527970855)
          ·
            refine ⟨45040837003952253791956283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30027224669301502527970855 45040837003952253791956283)
            ·
              refine ⟨67561255505928380687934425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45040837003952253791956283 67561255505928380687934425)
              ·
                refine ⟨50670941629446285515950819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67561255505928380687934425 50670941629446285515950819)
                ·
                  refine ⟨76006412444169428273926229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50670941629446285515950819 76006412444169428273926229)
                  ·
                    refine ⟨890700145830110487585073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76006412444169428273926229 890700145830110487585073)
                    ·
                      rfl

theorem cell23_5203897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_5203897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203897 prefixEnd_5203897 := by exact prefixLift 5203897
  have htrace : WordTrace (prefixWord ++ tailWord_5203897) baseStart_5203897 baseEnd_5203897 := by
    simpa [prefixWord, tailWord_5203897, baseEnd_5203897] using wordTrace_append hprefix tailTrace_5203897
  have hstable : (prefixWord ++ tailWord_5203897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203897).length < 2 ^ (prefixWord ++ tailWord_5203897).sum := by decide
  have hdescent : baseEnd_5203897 < baseStart_5203897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203932 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5203932 : Nat := 118140960795 + 5203932 * 2 ^ 59
def prefixEnd_5203932 : Nat := 4983230072969 + 3 ^ 40 * 5203932 * 2
def baseEnd_5203932 : Nat := 2672118409313238825817559

theorem tailTrace_5203932 : CollatzResearch.WordTrace tailWord_5203932 prefixEnd_5203932 2672118409313238825817559 := by
  unfold tailWord_5203932
  simp only [CollatzResearch.WordTrace]
  refine ⟨94901496491525299836423025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126535328655367066448564033 94901496491525299836423025)
  ·
    refine ⟨71176122368643974877317269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94901496491525299836423025 71176122368643974877317269)
    ·
      refine ⟨3336380736030186322374247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71176122368643974877317269 3336380736030186322374247)
      ·
        refine ⟨5004571104045279483561371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336380736030186322374247 5004571104045279483561371)
        ·
          refine ⟨7506856656067919225342057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5004571104045279483561371 7506856656067919225342057)
          ·
            refine ⟨5630142492050939419006543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7506856656067919225342057 5630142492050939419006543)
            ·
              refine ⟨8445213738076409128509815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5630142492050939419006543 8445213738076409128509815)
              ·
                refine ⟨12667820607114613692764723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8445213738076409128509815 12667820607114613692764723)
                ·
                  refine ⟨19001730910671920539147085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12667820607114613692764723 19001730910671920539147085)
                  ·
                    refine ⟨7125649091501970202180157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19001730910671920539147085 7125649091501970202180157)
                    ·
                      refine ⟨2672118409313238825817559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7125649091501970202180157 2672118409313238825817559)
                      ·
                        rfl

theorem cell23_5203932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5203932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203932 prefixEnd_5203932 := by exact prefixLift 5203932
  have htrace : WordTrace (prefixWord ++ tailWord_5203932) baseStart_5203932 baseEnd_5203932 := by
    simpa [prefixWord, tailWord_5203932, baseEnd_5203932] using wordTrace_append hprefix tailTrace_5203932
  have hstable : (prefixWord ++ tailWord_5203932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203932).length < 2 ^ (prefixWord ++ tailWord_5203932).sum := by decide
  have hdescent : baseEnd_5203932 < baseStart_5203932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203961 : List Nat := [1, 2, 1, 3, 1, 4, 3, 3, 5]
def baseStart_5203961 : Nat := 118140960795 + 5203961 * 2 ^ 59
def prefixEnd_5203961 : Nat := 4983230072969 + 3 ^ 40 * 5203961 * 2
def baseEnd_5203961 : Nat := 296903700028024356928325

theorem tailTrace_5203961 : CollatzResearch.WordTrace tailWord_5203961 prefixEnd_5203961 296903700028024356928325 := by
  unfold tailWord_5203961
  simp only [CollatzResearch.WordTrace]
  refine ⟨189804050699945537625651737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126536033799963691750434491 189804050699945537625651737)
  ·
    refine ⟨142353038024959153219238803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189804050699945537625651737 142353038024959153219238803)
    ·
      refine ⟨213529557037438729828858205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142353038024959153219238803 213529557037438729828858205)
      ·
        refine ⟨80073583889039523685821827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213529557037438729828858205 80073583889039523685821827)
        ·
          refine ⟨120110375833559285528732741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80073583889039523685821827 120110375833559285528732741)
          ·
            refine ⟨22520695468792366036637389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120110375833559285528732741 22520695468792366036637389)
            ·
              refine ⟨8445260800797137263739021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22520695468792366036637389 8445260800797137263739021)
              ·
                refine ⟨3166972800298926473902133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8445260800797137263739021 3166972800298926473902133)
                ·
                  refine ⟨296903700028024356928325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3166972800298926473902133 296903700028024356928325)
                  ·
                    rfl

theorem cell23_5203961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 5].length) (baseStart_5203961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203961 prefixEnd_5203961 := by exact prefixLift 5203961
  have htrace : WordTrace (prefixWord ++ tailWord_5203961) baseStart_5203961 baseEnd_5203961 := by
    simpa [prefixWord, tailWord_5203961, baseEnd_5203961] using wordTrace_append hprefix tailTrace_5203961
  have hstable : (prefixWord ++ tailWord_5203961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203961).length < 2 ^ (prefixWord ++ tailWord_5203961).sum := by decide
  have hdescent : baseEnd_5203961 < baseStart_5203961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203967 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_5203967 : Nat := 118140960795 + 5203967 * 2 ^ 59
def prefixEnd_5203967 : Nat := 4983230072969 + 3 ^ 40 * 5203967 * 2
def baseEnd_5203967 : Nat := 2672136381136146188879897

theorem tailTrace_5203967 : CollatzResearch.WordTrace tailWord_5203967 prefixEnd_5203967 2672136381136146188879897 := by
  unfold tailWord_5203967
  simp only [CollatzResearch.WordTrace]
  refine ⟨189804269537923800650370155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126536179691949200433580103 189804269537923800650370155)
  ·
    refine ⟨284706404306885700975555233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189804269537923800650370155 284706404306885700975555233)
    ·
      refine ⟨213529803230164275731666425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284706404306885700975555233 213529803230164275731666425)
      ·
        refine ⟨160147352422623206798749819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213529803230164275731666425 160147352422623206798749819)
        ·
          refine ⟨240221028633934810198124729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160147352422623206798749819 240221028633934810198124729)
          ·
            refine ⟨180165771475451107648593547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240221028633934810198124729 180165771475451107648593547)
            ·
              refine ⟨270248657213176661472890321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180165771475451107648593547 270248657213176661472890321)
              ·
                refine ⟨202686492909882496104667741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270248657213176661472890321 202686492909882496104667741)
                ·
                  refine ⟨76007434841205936039250403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202686492909882496104667741 76007434841205936039250403)
                  ·
                    refine ⟨114011152261808904058875605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76007434841205936039250403 114011152261808904058875605)
                    ·
                      refine ⟨2672136381136146188879897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114011152261808904058875605 2672136381136146188879897)
                      ·
                        rfl

theorem cell23_5203967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_5203967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203967 prefixEnd_5203967 := by exact prefixLift 5203967
  have htrace : WordTrace (prefixWord ++ tailWord_5203967) baseStart_5203967 baseEnd_5203967 := by
    simpa [prefixWord, tailWord_5203967, baseEnd_5203967] using wordTrace_append hprefix tailTrace_5203967
  have hstable : (prefixWord ++ tailWord_5203967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203967).length < 2 ^ (prefixWord ++ tailWord_5203967).sum := by decide
  have hdescent : baseEnd_5203967 < baseStart_5203967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203977 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_5203977 : Nat := 118140960795 + 5203977 * 2 ^ 59
def prefixEnd_5203977 : Nat := 4983230072969 + 3 ^ 40 * 5203977 * 2
def baseEnd_5203977 : Nat := 2672141515942691149754851

theorem tailTrace_5203977 : CollatzResearch.WordTrace tailWord_5203977 prefixEnd_5203977 2672141515942691149754851 := by
  unfold tailWord_5203977
  simp only [CollatzResearch.WordTrace]
  refine ⟨189804634267887572358234185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126536422845258381572156123 189804634267887572358234185)
  ·
    refine ⟨142353475700915679268675639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189804634267887572358234185 142353475700915679268675639)
    ·
      refine ⟨213530213551373518903013459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142353475700915679268675639 213530213551373518903013459)
      ·
        refine ⟨320295320327060278354520189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213530213551373518903013459 320295320327060278354520189)
        ·
          refine ⟨120110745122647604382945071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320295320327060278354520189 120110745122647604382945071)
          ·
            refine ⟨180166117683971406574417607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120110745122647604382945071 180166117683971406574417607)
            ·
              refine ⟨270249176525957109861626411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180166117683971406574417607 270249176525957109861626411)
              ·
                refine ⟨405373764788935664792439617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270249176525957109861626411 405373764788935664792439617)
                ·
                  refine ⟨304030323591701748594329713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405373764788935664792439617 304030323591701748594329713)
                  ·
                    refine ⟨228022742693776311445747285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 304030323591701748594329713 228022742693776311445747285)
                    ·
                      refine ⟨2672141515942691149754851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 228022742693776311445747285 2672141515942691149754851)
                      ·
                        rfl

theorem cell23_5203977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_5203977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203977 prefixEnd_5203977 := by exact prefixLift 5203977
  have htrace : WordTrace (prefixWord ++ tailWord_5203977) baseStart_5203977 baseEnd_5203977 := by
    simpa [prefixWord, tailWord_5203977, baseEnd_5203977] using wordTrace_append hprefix tailTrace_5203977
  have hstable : (prefixWord ++ tailWord_5203977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203977).length < 2 ^ (prefixWord ++ tailWord_5203977).sum := by decide
  have hdescent : baseEnd_5203977 < baseStart_5203977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203978 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 7]
def baseStart_5203978 : Nat := 118140960795 + 5203978 * 2 ^ 59
def prefixEnd_5203978 : Nat := 4983230072969 + 3 ^ 40 * 5203978 * 2
def baseEnd_5203978 : Nat := 296904669935927293982483

theorem tailTrace_5203978 : CollatzResearch.WordTrace tailWord_5203978 prefixEnd_5203978 296904669935927293982483 := by
  unfold tailWord_5203978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47451167685220987382255147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126536447160589299686013725 47451167685220987382255147)
  ·
    refine ⟨71176751527831481073382721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47451167685220987382255147 71176751527831481073382721)
    ·
      refine ⟨53382563645873610805037041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71176751527831481073382721 53382563645873610805037041)
      ·
        refine ⟨40036922734405208103777781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53382563645873610805037041 40036922734405208103777781)
        ·
          refine ⟨3753461506350488259729167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40036922734405208103777781 3753461506350488259729167)
          ·
            refine ⟨5630192259525732389593751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753461506350488259729167 5630192259525732389593751)
            ·
              refine ⟨8445288389288598584390627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5630192259525732389593751 8445288389288598584390627)
              ·
                refine ⟨12667932583932897876585941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8445288389288598584390627 12667932583932897876585941)
                ·
                  refine ⟨296904669935927293982483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12667932583932897876585941 296904669935927293982483)
                  ·
                    rfl

theorem cell23_5203978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_5203978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203978 prefixEnd_5203978 := by exact prefixLift 5203978
  have htrace : WordTrace (prefixWord ++ tailWord_5203978) baseStart_5203978 baseEnd_5203978 := by
    simpa [prefixWord, tailWord_5203978, baseEnd_5203978] using wordTrace_append hprefix tailTrace_5203978
  have hstable : (prefixWord ++ tailWord_5203978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203978).length < 2 ^ (prefixWord ++ tailWord_5203978).sum := by decide
  have hdescent : baseEnd_5203978 < baseStart_5203978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5203989 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_5203989 : Nat := 118140960795 + 5203989 * 2 ^ 59
def prefixEnd_5203989 : Nat := 4983230072969 + 3 ^ 40 * 5203989 * 2
def baseEnd_5203989 : Nat := 2672147677710545102804797

theorem tailTrace_5203989 : CollatzResearch.WordTrace tailWord_5203989 prefixEnd_5203989 2672147677710545102804797 := by
  unfold tailWord_5203989
  simp only [CollatzResearch.WordTrace]
  refine ⟨189805071943844098407671021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126536714629229398938447347 189805071943844098407671021)
  ·
    refine ⟨71176901978941536902876633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189805071943844098407671021 71176901978941536902876633)
    ·
      refine ⟨53382676484206152677157475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71176901978941536902876633 53382676484206152677157475)
      ·
        refine ⟨80074014726309229015736213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53382676484206152677157475 80074014726309229015736213)
        ·
          refine ⟨3753469440295745110112635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80074014726309229015736213 3753469440295745110112635)
          ·
            refine ⟨5630204160443617665168953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753469440295745110112635 5630204160443617665168953)
            ·
              refine ⟨4222653120332713248876715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5630204160443617665168953 4222653120332713248876715)
              ·
                refine ⟨6333979680499069873315073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222653120332713248876715 6333979680499069873315073)
                ·
                  refine ⟨4750484760374302404986305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6333979680499069873315073 4750484760374302404986305)
                  ·
                    refine ⟨3562863570280726803739729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4750484760374302404986305 3562863570280726803739729)
                    ·
                      refine ⟨2672147677710545102804797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3562863570280726803739729 2672147677710545102804797)
                      ·
                        rfl

theorem cell23_5203989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_5203989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5203989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5203989 prefixEnd_5203989 := by exact prefixLift 5203989
  have htrace : WordTrace (prefixWord ++ tailWord_5203989) baseStart_5203989 baseEnd_5203989 := by
    simpa [prefixWord, tailWord_5203989, baseEnd_5203989] using wordTrace_append hprefix tailTrace_5203989
  have hstable : (prefixWord ++ tailWord_5203989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5203989).length < 2 ^ (prefixWord ++ tailWord_5203989).sum := by decide
  have hdescent : baseEnd_5203989 < baseStart_5203989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5203989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204031 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 3]
def baseStart_5204031 : Nat := 118140960795 + 5204031 * 2 ^ 59
def prefixEnd_5204031 : Nat := 4983230072969 + 3 ^ 40 * 5204031 * 2
def baseEnd_5204031 : Nat := 2672169243898033938479603

theorem tailTrace_5204031 : CollatzResearch.WordTrace tailWord_5204031 prefixEnd_5204031 2672169243898033938479603 := by
  unfold tailWord_5204031
  simp only [CollatzResearch.WordTrace]
  refine ⟨189806603809691939580699947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126537735873127959720466631 189806603809691939580699947)
  ·
    refine ⟨284709905714537909371049921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189806603809691939580699947 284709905714537909371049921)
    ·
      refine ⟨213532429285903432028287441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284709905714537909371049921 213532429285903432028287441)
      ·
        refine ⟨160149321964427574021215581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213532429285903432028287441 160149321964427574021215581)
        ·
          refine ⟨60055995736660340257955843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160149321964427574021215581 60055995736660340257955843)
          ·
            refine ⟨90083993604990510386933765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60055995736660340257955843 90083993604990510386933765)
            ·
              refine ⟨16890748800935720697550081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90083993604990510386933765 16890748800935720697550081)
              ·
                refine ⟨12668061600701790523162561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16890748800935720697550081 12668061600701790523162561)
                ·
                  refine ⟨9501046200526342892371921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12668061600701790523162561 9501046200526342892371921)
                  ·
                    refine ⟨7125784650394757169278941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9501046200526342892371921 7125784650394757169278941)
                    ·
                      refine ⟨2672169243898033938479603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7125784650394757169278941 2672169243898033938479603)
                      ·
                        rfl

theorem cell23_5204031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_5204031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204031 prefixEnd_5204031 := by exact prefixLift 5204031
  have htrace : WordTrace (prefixWord ++ tailWord_5204031) baseStart_5204031 baseEnd_5204031 := by
    simpa [prefixWord, tailWord_5204031, baseEnd_5204031] using wordTrace_append hprefix tailTrace_5204031
  have hstable : (prefixWord ++ tailWord_5204031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204031).length < 2 ^ (prefixWord ++ tailWord_5204031).sum := by decide
  have hdescent : baseEnd_5204031 < baseStart_5204031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204078 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_5204078 : Nat := 118140960795 + 5204078 * 2 ^ 59
def prefixEnd_5204078 : Nat := 4983230072969 + 3 ^ 40 * 5204078 * 2
def baseEnd_5204078 : Nat := 2672193377488795254591887

theorem tailTrace_5204078 : CollatzResearch.WordTrace tailWord_5204078 prefixEnd_5204078 2672193377488795254591887 := by
  unfold tailWord_5204078
  simp only [CollatzResearch.WordTrace]
  refine ⟨23726039755065208325957611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126538878693681111071773925 23726039755065208325957611)
  ·
    refine ⟨35589059632597812488936417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23726039755065208325957611 35589059632597812488936417)
    ·
      refine ⟨26691794724448359366702313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35589059632597812488936417 26691794724448359366702313)
      ·
        refine ⟨20018846043336269525026735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26691794724448359366702313 20018846043336269525026735)
        ·
          refine ⟨30028269065004404287540103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20018846043336269525026735 30028269065004404287540103)
          ·
            refine ⟨45042403597506606431310155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30028269065004404287540103 45042403597506606431310155)
            ·
              refine ⟨67563605396259909646965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45042403597506606431310155 67563605396259909646965233)
              ·
                refine ⟨50672704047194932235223925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67563605396259909646965233 50672704047194932235223925)
                ·
                  refine ⟨4750566004424524897052243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50672704047194932235223925 4750566004424524897052243)
                  ·
                    refine ⟨7125849006636787345578365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4750566004424524897052243 7125849006636787345578365)
                    ·
                      refine ⟨2672193377488795254591887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7125849006636787345578365 2672193377488795254591887)
                      ·
                        rfl

theorem cell23_5204078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_5204078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204078 prefixEnd_5204078 := by exact prefixLift 5204078
  have htrace : WordTrace (prefixWord ++ tailWord_5204078) baseStart_5204078 baseEnd_5204078 := by
    simpa [prefixWord, tailWord_5204078, baseEnd_5204078] using wordTrace_append hprefix tailTrace_5204078
  have hstable : (prefixWord ++ tailWord_5204078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204078).length < 2 ^ (prefixWord ++ tailWord_5204078).sum := by decide
  have hdescent : baseEnd_5204078 < baseStart_5204078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204081 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 1, 5]
def baseStart_5204081 : Nat := 118140960795 + 5204081 * 2 ^ 59
def prefixEnd_5204081 : Nat := 4983230072969 + 3 ^ 40 * 5204081 * 2
def baseEnd_5204081 : Nat := 890731639310252914284791

theorem tailTrace_5204081 : CollatzResearch.WordTrace tailWord_5204081 prefixEnd_5204081 890731639310252914284791 := by
  unfold tailWord_5204081
  simp only [CollatzResearch.WordTrace]
  refine ⟨189808427459510798120020097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126538951639673865413346731 189808427459510798120020097)
  ·
    refine ⟨142356320594633098590015073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189808427459510798120020097 142356320594633098590015073)
    ·
      refine ⟨106767240445974823942511305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142356320594633098590015073 106767240445974823942511305)
      ·
        refine ⟨80075430334481117956883479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106767240445974823942511305 80075430334481117956883479)
        ·
          refine ⟨120113145501721676935325219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80075430334481117956883479 120113145501721676935325219)
          ·
            refine ⟨180169718252582515402987829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120113145501721676935325219 180169718252582515402987829)
            ·
              refine ⟨16890911086179610819030109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180169718252582515402987829 16890911086179610819030109)
              ·
                refine ⟨6334091657317354057136291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16890911086179610819030109 6334091657317354057136291)
                ·
                  refine ⟨9501137485976031085704437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6334091657317354057136291 9501137485976031085704437)
                  ·
                    refine ⟨890731639310252914284791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9501137485976031085704437 890731639310252914284791)
                    ·
                      rfl

theorem cell23_5204081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_5204081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204081 prefixEnd_5204081 := by exact prefixLift 5204081
  have htrace : WordTrace (prefixWord ++ tailWord_5204081) baseStart_5204081 baseEnd_5204081 := by
    simpa [prefixWord, tailWord_5204081, baseEnd_5204081] using wordTrace_append hprefix tailTrace_5204081
  have hstable : (prefixWord ++ tailWord_5204081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204081).length < 2 ^ (prefixWord ++ tailWord_5204081).sum := by decide
  have hdescent : baseEnd_5204081 < baseStart_5204081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204121 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 3]
def baseStart_5204121 : Nat := 118140960795 + 5204121 * 2 ^ 59
def prefixEnd_5204121 : Nat := 4983230072969 + 3 ^ 40 * 5204121 * 2
def baseEnd_5204121 : Nat := 2672215457156938586354189

theorem tailTrace_5204121 : CollatzResearch.WordTrace tailWord_5204121 prefixEnd_5204121 2672215457156938586354189 := by
  unfold tailWord_5204121
  simp only [CollatzResearch.WordTrace]
  refine ⟨189809886379365884951476217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126539924252910589967650811 189809886379365884951476217)
  ·
    refine ⟨142357414784524413713607163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189809886379365884951476217 142357414784524413713607163)
    ·
      refine ⟨213536122176786620570410745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142357414784524413713607163 213536122176786620570410745)
      ·
        refine ⟨160152091632589965427808059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213536122176786620570410745 160152091632589965427808059)
        ·
          refine ⟨240228137448884948141712089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160152091632589965427808059 240228137448884948141712089)
          ·
            refine ⟨180171103086663711106284067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240228137448884948141712089 180171103086663711106284067)
            ·
              refine ⟨270256654629995566659426101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180171103086663711106284067 270256654629995566659426101)
              ·
                refine ⟨25336561371562084374321197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270256654629995566659426101 25336561371562084374321197)
                ·
                  refine ⟨9501210514335781640370449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25336561371562084374321197 9501210514335781640370449)
                  ·
                    refine ⟨7125907885751836230277837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9501210514335781640370449 7125907885751836230277837)
                    ·
                      refine ⟨2672215457156938586354189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7125907885751836230277837 2672215457156938586354189)
                      ·
                        rfl

theorem cell23_5204121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_5204121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204121 prefixEnd_5204121 := by exact prefixLift 5204121
  have htrace : WordTrace (prefixWord ++ tailWord_5204121) baseStart_5204121 baseEnd_5204121 := by
    simpa [prefixWord, tailWord_5204121, baseEnd_5204121] using wordTrace_append hprefix tailTrace_5204121
  have hstable : (prefixWord ++ tailWord_5204121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204121).length < 2 ^ (prefixWord ++ tailWord_5204121).sum := by decide
  have hdescent : baseEnd_5204121 < baseStart_5204121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204141 : List Nat := [1, 5, 2, 1, 2, 1, 11]
def baseStart_5204141 : Nat := 118140960795 + 5204141 * 2 ^ 59
def prefixEnd_5204141 : Nat := 4983230072969 + 3 ^ 40 * 5204141 * 2
def baseEnd_5204141 : Nat := 32990441071234919853137

theorem tailTrace_5204141 : CollatzResearch.WordTrace tailWord_5204141 prefixEnd_5204141 32990441071234919853137 := by
  unfold tailWord_5204141
  simp only [CollatzResearch.WordTrace]
  refine ⟨189810615839293428367204277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126540410559528952244802851 189810615839293428367204277)
  ·
    refine ⟨17794745234933758909425401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189810615839293428367204277 17794745234933758909425401)
    ·
      refine ⟨13346058926200319182069051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17794745234933758909425401 13346058926200319182069051)
      ·
        refine ⟨20019088389300478773103577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13346058926200319182069051 20019088389300478773103577)
        ·
          refine ⟨15014316291975359079827683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20019088389300478773103577 15014316291975359079827683)
          ·
            refine ⟨22521474437963038619741525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15014316291975359079827683 22521474437963038619741525)
            ·
              refine ⟨32990441071234919853137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22521474437963038619741525 32990441071234919853137)
              ·
                rfl

theorem cell23_5204141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 11].length) (baseStart_5204141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204141 prefixEnd_5204141 := by exact prefixLift 5204141
  have htrace : WordTrace (prefixWord ++ tailWord_5204141) baseStart_5204141 baseEnd_5204141 := by
    simpa [prefixWord, tailWord_5204141, baseEnd_5204141] using wordTrace_append hprefix tailTrace_5204141
  have hstable : (prefixWord ++ tailWord_5204141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204141).length < 2 ^ (prefixWord ++ tailWord_5204141).sum := by decide
  have hdescent : baseEnd_5204141 < baseStart_5204141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204144 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_5204144 : Nat := 118140960795 + 5204144 * 2 ^ 59
def prefixEnd_5204144 : Nat := 4983230072969 + 3 ^ 40 * 5204144 * 2
def baseEnd_5204144 : Nat := 2672227267211991996366583

theorem tailTrace_5204144 : CollatzResearch.WordTrace tailWord_5204144 prefixEnd_5204144 2672227267211991996366583 := by
  unfold tailWord_5204144
  simp only [CollatzResearch.WordTrace]
  refine ⟨94905362629141279939781743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126540483505521706586375657 94905362629141279939781743)
  ·
    refine ⟨142358043943711919909672615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94905362629141279939781743 142358043943711919909672615)
    ·
      refine ⟨213537065915567879864508923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142358043943711919909672615 213537065915567879864508923)
      ·
        refine ⟨320305598873351819796763385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213537065915567879864508923 320305598873351819796763385)
        ·
          refine ⟨240229199155013864847572539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320305598873351819796763385 240229199155013864847572539)
          ·
            refine ⟨360343798732520797271358809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240229199155013864847572539 360343798732520797271358809)
            ·
              refine ⟨270257849049390597953519107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360343798732520797271358809 270257849049390597953519107)
              ·
                refine ⟨405386773574085896930278661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270257849049390597953519107 405386773574085896930278661)
                ·
                  refine ⟨76010020045141105674427249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405386773574085896930278661 76010020045141105674427249)
                  ·
                    refine ⟨57007515033855829255820437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76010020045141105674427249 57007515033855829255820437)
                    ·
                      refine ⟨2672227267211991996366583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57007515033855829255820437 2672227267211991996366583)
                      ·
                        rfl

theorem cell23_5204144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_5204144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204144 prefixEnd_5204144 := by exact prefixLift 5204144
  have htrace : WordTrace (prefixWord ++ tailWord_5204144) baseStart_5204144 baseEnd_5204144 := by
    simpa [prefixWord, tailWord_5204144, baseEnd_5204144] using wordTrace_append hprefix tailTrace_5204144
  have hstable : (prefixWord ++ tailWord_5204144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204144).length < 2 ^ (prefixWord ++ tailWord_5204144).sum := by decide
  have hdescent : baseEnd_5204144 < baseStart_5204144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204158 : List Nat := [4, 2, 1, 1, 4, 1, 2, 8]
def baseStart_5204158 : Nat := 118140960795 + 5204158 * 2 ^ 59
def prefixEnd_5204158 : Nat := 4983230072969 + 3 ^ 40 * 5204158 * 2
def baseEnd_5204158 : Nat := 98971646516339071910797

theorem tailTrace_5204158 : CollatzResearch.WordTrace tailWord_5204158 prefixEnd_5204158 98971646516339071910797 := by
  unfold tailWord_5204158
  simp only [CollatzResearch.WordTrace]
  refine ⟨23726404485028980033821641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126540823920154560180382085 23726404485028980033821641)
  ·
    refine ⟨17794803363771735025366231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23726404485028980033821641 17794803363771735025366231)
    ·
      refine ⟨26692205045657602538049347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17794803363771735025366231 26692205045657602538049347)
      ·
        refine ⟨40038307568486403807074021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26692205045657602538049347 40038307568486403807074021)
        ·
          refine ⟨7507182669091200713826379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40038307568486403807074021 7507182669091200713826379)
          ·
            refine ⟨11260774003636801070739569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7507182669091200713826379 11260774003636801070739569)
            ·
              refine ⟨8445580502727600803054677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11260774003636801070739569 8445580502727600803054677)
              ·
                refine ⟨98971646516339071910797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8445580502727600803054677 98971646516339071910797)
                ·
                  rfl

theorem cell23_5204158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_5204158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204158 prefixEnd_5204158 := by exact prefixLift 5204158
  have htrace : WordTrace (prefixWord ++ tailWord_5204158) baseStart_5204158 baseEnd_5204158 := by
    simpa [prefixWord, tailWord_5204158, baseEnd_5204158] using wordTrace_append hprefix tailTrace_5204158
  have hstable : (prefixWord ++ tailWord_5204158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204158).length < 2 ^ (prefixWord ++ tailWord_5204158).sum := by decide
  have hdescent : baseEnd_5204158 < baseStart_5204158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204211 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 3]
def baseStart_5204211 : Nat := 118140960795 + 5204211 * 2 ^ 59
def prefixEnd_5204211 : Nat := 4983230072969 + 3 ^ 40 * 5204211 * 2
def baseEnd_5204211 : Nat := 2672261670415843234228775

theorem tailTrace_5204211 : CollatzResearch.WordTrace tailWord_5204211 prefixEnd_5204211 2672261670415843234228775 := by
  unfold tailWord_5204211
  simp only [CollatzResearch.WordTrace]
  refine ⟨189813168949039830322252487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126542112632693220214834991 189813168949039830322252487)
  ·
    refine ⟨284719753423559745483378731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189813168949039830322252487 284719753423559745483378731)
    ·
      refine ⟨427079630135339618225068097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284719753423559745483378731 427079630135339618225068097)
      ·
        refine ⟨320309722601504713668801073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427079630135339618225068097 320309722601504713668801073)
        ·
          refine ⟨240232291951128535251600805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320309722601504713668801073 240232291951128535251600805)
          ·
            refine ⟨45043554740836600359675151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240232291951128535251600805 45043554740836600359675151)
            ·
              refine ⟨67565332111254900539512727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45043554740836600359675151 67565332111254900539512727)
              ·
                refine ⟨101347998166882350809269091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67565332111254900539512727 101347998166882350809269091)
                ·
                  refine ⟨152021997250323526213903637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101347998166882350809269091 152021997250323526213903637)
                  ·
                    refine ⟨7126031121108915291276733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 152021997250323526213903637 7126031121108915291276733)
                    ·
                      refine ⟨2672261670415843234228775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7126031121108915291276733 2672261670415843234228775)
                      ·
                        rfl

theorem cell23_5204211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_5204211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204211 prefixEnd_5204211 := by exact prefixLift 5204211
  have htrace : WordTrace (prefixWord ++ tailWord_5204211) baseStart_5204211 baseEnd_5204211 := by
    simpa [prefixWord, tailWord_5204211, baseEnd_5204211] using wordTrace_append hprefix tailTrace_5204211
  have hstable : (prefixWord ++ tailWord_5204211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204211).length < 2 ^ (prefixWord ++ tailWord_5204211).sum := by decide
  have hdescent : baseEnd_5204211 < baseStart_5204211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204225 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_5204225 : Nat := 118140960795 + 5204225 * 2 ^ 59
def prefixEnd_5204225 : Nat := 4983230072969 + 3 ^ 40 * 5204225 * 2
def baseEnd_5204225 : Nat := 2672268859145006179453711

theorem tailTrace_5204225 : CollatzResearch.WordTrace tailWord_5204225 prefixEnd_5204225 2672268859145006179453711 := by
  unfold tailWord_5204225
  simp only [CollatzResearch.WordTrace]
  refine ⟨189813679570989110713262129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126542453047326073808841419 189813679570989110713262129)
  ·
    refine ⟨142360259678241833034946597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189813679570989110713262129 142360259678241833034946597)
    ·
      refine ⟨26692548689670343694052487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142360259678241833034946597 26692548689670343694052487)
      ·
        refine ⟨40038823034505515541078731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26692548689670343694052487 40038823034505515541078731)
        ·
          refine ⟨60058234551758273311618097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40038823034505515541078731 60058234551758273311618097)
          ·
            refine ⟨45043675913818704983713573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60058234551758273311618097 45043675913818704983713573)
            ·
              refine ⟨8445689233841007184446295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45043675913818704983713573 8445689233841007184446295)
              ·
                refine ⟨12668533850761510776669443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8445689233841007184446295 12668533850761510776669443)
                ·
                  refine ⟨19002800776142266165004165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12668533850761510776669443 19002800776142266165004165)
                  ·
                    refine ⟨3563025145526674905938281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19002800776142266165004165 3563025145526674905938281)
                    ·
                      refine ⟨2672268859145006179453711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563025145526674905938281 2672268859145006179453711)
                      ·
                        rfl

theorem cell23_5204225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_5204225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204225 prefixEnd_5204225 := by exact prefixLift 5204225
  have htrace : WordTrace (prefixWord ++ tailWord_5204225) baseStart_5204225 baseEnd_5204225 := by
    simpa [prefixWord, tailWord_5204225, baseEnd_5204225] using wordTrace_append hprefix tailTrace_5204225
  have hstable : (prefixWord ++ tailWord_5204225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204225).length < 2 ^ (prefixWord ++ tailWord_5204225).sum := by decide
  have hdescent : baseEnd_5204225 < baseStart_5204225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204268 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 7, 2]
def baseStart_5204268 : Nat := 118140960795 + 5204268 * 2 ^ 59
def prefixEnd_5204268 : Nat := 4983230072969 + 3 ^ 40 * 5204268 * 2
def baseEnd_5204268 : Nat := 2672290938813149511216013

theorem tailTrace_5204268 : CollatzResearch.WordTrace tailWord_5204268 prefixEnd_5204268 2672290938813149511216013 := by
  unfold tailWord_5204268
  simp only [CollatzResearch.WordTrace]
  refine ⟨94907623954916664528538729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126543498606555552704718305 94907623954916664528538729)
  ·
    refine ⟨71180717966187498396404047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94907623954916664528538729 71180717966187498396404047)
    ·
      refine ⟨106771076949281247594606071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71180717966187498396404047 106771076949281247594606071)
      ·
        refine ⟨160156615423921871391909107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106771076949281247594606071 160156615423921871391909107)
        ·
          refine ⟨240234923135882807087863661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160156615423921871391909107 240234923135882807087863661)
          ·
            refine ⟨90088096175956052657948873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240234923135882807087863661 90088096175956052657948873)
            ·
              refine ⟨67566072131967039493461655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90088096175956052657948873 67566072131967039493461655)
              ·
                refine ⟨101349108197950559240192483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67566072131967039493461655 101349108197950559240192483)
                ·
                  refine ⟨152023662296925838860288725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101349108197950559240192483 152023662296925838860288725)
                  ·
                    refine ⟨3563054585084199348288017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 152023662296925838860288725 3563054585084199348288017)
                    ·
                      refine ⟨2672290938813149511216013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563054585084199348288017 2672290938813149511216013)
                      ·
                        rfl

theorem cell23_5204268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_5204268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204268 prefixEnd_5204268 := by exact prefixLift 5204268
  have htrace : WordTrace (prefixWord ++ tailWord_5204268) baseStart_5204268 baseEnd_5204268 := by
    simpa [prefixWord, tailWord_5204268, baseEnd_5204268] using wordTrace_append hprefix tailTrace_5204268
  have hstable : (prefixWord ++ tailWord_5204268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204268).length < 2 ^ (prefixWord ++ tailWord_5204268).sum := by decide
  have hdescent : baseEnd_5204268 < baseStart_5204268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204271 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_5204271 : Nat := 118140960795 + 5204271 * 2 ^ 59
def prefixEnd_5204271 : Nat := 4983230072969 + 3 ^ 40 * 5204271 * 2
def baseEnd_5204271 : Nat := 2672292479255112999478499

theorem tailTrace_5204271 : CollatzResearch.WordTrace tailWord_5204271 prefixEnd_5204271 2672292479255112999478499 := by
  unfold tailWord_5204271
  simp only [CollatzResearch.WordTrace]
  refine ⟨189815357328822460569436667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126543571552548307046291111 189815357328822460569436667)
  ·
    refine ⟨284723035993233690854155001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189815357328822460569436667 284723035993233690854155001)
    ·
      refine ⟨213542276994925268140616251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284723035993233690854155001 213542276994925268140616251)
      ·
        refine ⟨320313415492387902210924377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213542276994925268140616251 320313415492387902210924377)
        ·
          refine ⟨240235061619290926658193283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320313415492387902210924377 240235061619290926658193283)
          ·
            refine ⟨360352592428936389987289925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240235061619290926658193283 360352592428936389987289925)
            ·
              refine ⟨67566111080425573122616861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360352592428936389987289925 67566111080425573122616861)
              ·
                refine ⟨25337291655159589920981323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67566111080425573122616861 25337291655159589920981323)
                ·
                  refine ⟨38005937482739384881471985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25337291655159589920981323 38005937482739384881471985)
                  ·
                    refine ⟨28504453112054538661103989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38005937482739384881471985 28504453112054538661103989)
                    ·
                      refine ⟨2672292479255112999478499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28504453112054538661103989 2672292479255112999478499)
                      ·
                        rfl

theorem cell23_5204271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_5204271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204271 prefixEnd_5204271 := by exact prefixLift 5204271
  have htrace : WordTrace (prefixWord ++ tailWord_5204271) baseStart_5204271 baseEnd_5204271 := by
    simpa [prefixWord, tailWord_5204271, baseEnd_5204271] using wordTrace_append hprefix tailTrace_5204271
  have hstable : (prefixWord ++ tailWord_5204271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204271).length < 2 ^ (prefixWord ++ tailWord_5204271).sum := by decide
  have hdescent : baseEnd_5204271 < baseStart_5204271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204276 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_5204276 : Nat := 118140960795 + 5204276 * 2 ^ 59
def prefixEnd_5204276 : Nat := 4983230072969 + 3 ^ 40 * 5204276 * 2
def baseEnd_5204276 : Nat := 2672295046658385479915977

theorem tailTrace_5204276 : CollatzResearch.WordTrace tailWord_5204276 prefixEnd_5204276 2672295046658385479915977 := by
  unfold tailWord_5204276
  simp only [CollatzResearch.WordTrace]
  refine ⟨94907769846902173211684341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126543693129202897615579121 94907769846902173211684341)
  ·
    refine ⟨8897603423147078738595407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94907769846902173211684341 8897603423147078738595407)
    ·
      refine ⟨13346405134720618107893111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8897603423147078738595407 13346405134720618107893111)
      ·
        refine ⟨20019607702080927161839667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13346405134720618107893111 20019607702080927161839667)
        ·
          refine ⟨30029411553121390742759501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20019607702080927161839667 30029411553121390742759501)
          ·
            refine ⟨11261029332420521528534813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30029411553121390742759501 11261029332420521528534813)
            ·
              refine ⟨4222885999657695573200555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11261029332420521528534813 4222885999657695573200555)
              ·
                refine ⟨6334328999486543359800833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222885999657695573200555 6334328999486543359800833)
                ·
                  refine ⟨4750746749614907519850625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6334328999486543359800833 4750746749614907519850625)
                  ·
                    refine ⟨3563060062211180639887969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4750746749614907519850625 3563060062211180639887969)
                    ·
                      refine ⟨2672295046658385479915977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563060062211180639887969 2672295046658385479915977)
                      ·
                        rfl

theorem cell23_5204276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_5204276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204276 prefixEnd_5204276 := by exact prefixLift 5204276
  have htrace : WordTrace (prefixWord ++ tailWord_5204276) baseStart_5204276 baseEnd_5204276 := by
    simpa [prefixWord, tailWord_5204276, baseEnd_5204276] using wordTrace_append hprefix tailTrace_5204276
  have hstable : (prefixWord ++ tailWord_5204276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204276).length < 2 ^ (prefixWord ++ tailWord_5204276).sum := by decide
  have hdescent : baseEnd_5204276 < baseStart_5204276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204325 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_5204325 : Nat := 118140960795 + 5204325 * 2 ^ 59
def prefixEnd_5204325 : Nat := 4983230072969 + 3 ^ 40 * 5204325 * 2
def baseEnd_5204325 : Nat := 890773402403485262734417

theorem tailTrace_5204325 : CollatzResearch.WordTrace tailWord_5204325 prefixEnd_5204325 890773402403485262734417 := by
  unfold tailWord_5204325
  simp only [CollatzResearch.WordTrace]
  refine ⟨189817326870626827791902429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126544884580417885194601619 189817326870626827791902429)
  ·
    refine ⟨71181497576485060421963411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189817326870626827791902429 71181497576485060421963411)
    ·
      refine ⟨106772246364727590632945117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71181497576485060421963411 106772246364727590632945117)
      ·
        refine ⟨40039592386772846487354419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106772246364727590632945117 40039592386772846487354419)
        ·
          refine ⟨60059388580159269731031629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40039592386772846487354419 60059388580159269731031629)
          ·
            refine ⟨22522270717559726149136861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60059388580159269731031629 22522270717559726149136861)
            ·
              refine ⟨8445851519084897305926323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22522270717559726149136861 8445851519084897305926323)
              ·
                refine ⟨12668777278627345958889485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8445851519084897305926323 12668777278627345958889485)
                ·
                  refine ⟨4750791479485254734583557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12668777278627345958889485 4750791479485254734583557)
                  ·
                    refine ⟨890773402403485262734417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4750791479485254734583557 890773402403485262734417)
                    ·
                      rfl

theorem cell23_5204325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_5204325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204325 prefixEnd_5204325 := by exact prefixLift 5204325
  have htrace : WordTrace (prefixWord ++ tailWord_5204325) baseStart_5204325 baseEnd_5204325 := by
    simpa [prefixWord, tailWord_5204325, baseEnd_5204325] using wordTrace_append hprefix tailTrace_5204325
  have hstable : (prefixWord ++ tailWord_5204325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204325).length < 2 ^ (prefixWord ++ tailWord_5204325).sum := by decide
  have hdescent : baseEnd_5204325 < baseStart_5204325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204351 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 9]
def baseStart_5204351 : Nat := 118140960795 + 5204351 * 2 ^ 59
def prefixEnd_5204351 : Nat := 4983230072969 + 3 ^ 40 * 5204351 * 2
def baseEnd_5204351 : Nat := 890777852569157562159377

theorem tailTrace_5204351 : CollatzResearch.WordTrace tailWord_5204351 prefixEnd_5204351 890777852569157562159377 := by
  unfold tailWord_5204351
  simp only [CollatzResearch.WordTrace]
  refine ⟨189818275168532634232348907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126545516779021756154899271 189818275168532634232348907)
  ·
    refine ⟨284727412752798951348523361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189818275168532634232348907 284727412752798951348523361)
    ·
      refine ⟨213545559564599213511392521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284727412752798951348523361 213545559564599213511392521)
      ·
        refine ⟨160159169673449410133544391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213545559564599213511392521 160159169673449410133544391)
        ·
          refine ⟨240238754510174115200316587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160159169673449410133544391 240238754510174115200316587)
          ·
            refine ⟨360358131765261172800474881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240238754510174115200316587 360358131765261172800474881)
            ·
              refine ⟨270268598823945879600356161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360358131765261172800474881 270268598823945879600356161)
              ·
                refine ⟨202701449117959409700267121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270268598823945879600356161 202701449117959409700267121)
                ·
                  refine ⟨152026086838469557275200341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202701449117959409700267121 152026086838469557275200341)
                  ·
                    refine ⟨890777852569157562159377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 152026086838469557275200341 890777852569157562159377)
                    ·
                      rfl

theorem cell23_5204351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_5204351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204351 prefixEnd_5204351 := by exact prefixLift 5204351
  have htrace : WordTrace (prefixWord ++ tailWord_5204351) baseStart_5204351 baseEnd_5204351 := by
    simpa [prefixWord, tailWord_5204351, baseEnd_5204351] using wordTrace_append hprefix tailTrace_5204351
  have hstable : (prefixWord ++ tailWord_5204351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204351).length < 2 ^ (prefixWord ++ tailWord_5204351).sum := by decide
  have hdescent : baseEnd_5204351 < baseStart_5204351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204372 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 6]
def baseStart_5204372 : Nat := 118140960795 + 5204372 * 2 ^ 59
def prefixEnd_5204372 : Nat := 4983230072969 + 3 ^ 40 * 5204372 * 2
def baseEnd_5204372 : Nat := 296927148977913011590615

theorem tailTrace_5204372 : CollatzResearch.WordTrace tailWord_5204372 prefixEnd_5204372 296927148977913011590615 := by
  unfold tailWord_5204372
  simp only [CollatzResearch.WordTrace]
  refine ⟨94909520550728277409431685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126546027400971036545908913 94909520550728277409431685)
  ·
    refine ⟨17795535103261552014268441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94909520550728277409431685 17795535103261552014268441)
    ·
      refine ⟨13346651327446164010701331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17795535103261552014268441 13346651327446164010701331)
      ·
        refine ⟨20019976991169246016051997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13346651327446164010701331 20019976991169246016051997)
        ·
          refine ⟨7507491371688467256019499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20019976991169246016051997 7507491371688467256019499)
          ·
            refine ⟨11261237057532700884029249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7507491371688467256019499 11261237057532700884029249)
            ·
              refine ⟨8445927793149525663021937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11261237057532700884029249 8445927793149525663021937)
              ·
                refine ⟨6334445844862144247266453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8445927793149525663021937 6334445844862144247266453)
                ·
                  refine ⟨296927148977913011590615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6334445844862144247266453 296927148977913011590615)
                  ·
                    rfl

theorem cell23_5204372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_5204372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204372 prefixEnd_5204372 := by exact prefixLift 5204372
  have htrace : WordTrace (prefixWord ++ tailWord_5204372) baseStart_5204372 baseEnd_5204372 := by
    simpa [prefixWord, tailWord_5204372, baseEnd_5204372] using wordTrace_append hprefix tailTrace_5204372
  have hstable : (prefixWord ++ tailWord_5204372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204372).length < 2 ^ (prefixWord ++ tailWord_5204372).sum := by decide
  have hdescent : baseEnd_5204372 < baseStart_5204372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204376 : List Nat := [2, 1, 2, 5, 1, 3, 2, 2, 1, 4]
def baseStart_5204376 : Nat := 118140960795 + 5204376 * 2 ^ 59
def prefixEnd_5204376 : Nat := 4983230072969 + 3 ^ 40 * 5204376 * 2
def baseEnd_5204376 : Nat := 890782131574611696221839

theorem tailTrace_5204376 : CollatzResearch.WordTrace tailWord_5204376 prefixEnd_5204376 890782131574611696221839 := by
  unfold tailWord_5204376
  simp only [CollatzResearch.WordTrace]
  refine ⟨94909593496721031751004491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126546124662294709001339321 94909593496721031751004491)
  ·
    refine ⟨142364390245081547626506737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94909593496721031751004491 142364390245081547626506737)
    ·
      refine ⟨106773292683811160719880053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142364390245081547626506737 106773292683811160719880053)
      ·
        refine ⟨10009996189107296317488755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106773292683811160719880053 10009996189107296317488755)
        ·
          refine ⟨15014994283660944476233133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009996189107296317488755 15014994283660944476233133)
          ·
            refine ⟨5630622856372854178587425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15014994283660944476233133 5630622856372854178587425)
            ·
              refine ⟨4222967142279640633940569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5630622856372854178587425 4222967142279640633940569)
              ·
                refine ⟨3167225356709730475455427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4222967142279640633940569 3167225356709730475455427)
                ·
                  refine ⟨4750838035064595713183141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3167225356709730475455427 4750838035064595713183141)
                  ·
                    refine ⟨890782131574611696221839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4750838035064595713183141 890782131574611696221839)
                    ·
                      rfl

theorem cell23_5204376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_5204376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204376 prefixEnd_5204376 := by exact prefixLift 5204376
  have htrace : WordTrace (prefixWord ++ tailWord_5204376) baseStart_5204376 baseEnd_5204376 := by
    simpa [prefixWord, tailWord_5204376, baseEnd_5204376] using wordTrace_append hprefix tailTrace_5204376
  have hstable : (prefixWord ++ tailWord_5204376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204376).length < 2 ^ (prefixWord ++ tailWord_5204376).sum := by decide
  have hdescent : baseEnd_5204376 < baseStart_5204376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204409 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 2, 3, 2]
def baseStart_5204409 : Nat := 118140960795 + 5204409 * 2 ^ 59
def prefixEnd_5204409 : Nat := 4983230072969 + 3 ^ 40 * 5204409 * 2
def baseEnd_5204409 : Nat := 2672363339585433459552865

theorem tailTrace_5204409 : CollatzResearch.WordTrace tailWord_5204409 prefixEnd_5204409 2672363339585433459552865 := by
  unfold tailWord_5204409
  simp only [CollatzResearch.WordTrace]
  refine ⟨189820390602322510137960281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126546927068215006758640187 189820390602322510137960281)
  ·
    refine ⟨142365292951741882603470211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189820390602322510137960281 142365292951741882603470211)
    ·
      refine ⟨213547939427612823905205317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142365292951741882603470211 213547939427612823905205317)
      ·
        refine ⟨40040238642677404482225997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213547939427612823905205317 40040238642677404482225997)
        ·
          refine ⟨15015089491004026680834749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40040238642677404482225997 15015089491004026680834749)
          ·
            refine ⟨5630658559126510005313031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15015089491004026680834749 5630658559126510005313031)
            ·
              refine ⟨8445987838689765007969547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5630658559126510005313031 8445987838689765007969547)
              ·
                refine ⟨12668981758034647511954321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8445987838689765007969547 12668981758034647511954321)
                ·
                  refine ⟨9501736318525985633965741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12668981758034647511954321 9501736318525985633965741)
                  ·
                    refine ⟨3563151119447244612737153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9501736318525985633965741 3563151119447244612737153)
                    ·
                      refine ⟨2672363339585433459552865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563151119447244612737153 2672363339585433459552865)
                      ·
                        rfl

theorem cell23_5204409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_5204409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204409 prefixEnd_5204409 := by exact prefixLift 5204409
  have htrace : WordTrace (prefixWord ++ tailWord_5204409) baseStart_5204409 baseEnd_5204409 := by
    simpa [prefixWord, tailWord_5204409, baseEnd_5204409] using wordTrace_append hprefix tailTrace_5204409
  have hstable : (prefixWord ++ tailWord_5204409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204409).length < 2 ^ (prefixWord ++ tailWord_5204409).sum := by decide
  have hdescent : baseEnd_5204409 < baseStart_5204409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204462 : List Nat := [4, 1, 2, 1, 2, 4, 2, 7]
def baseStart_5204462 : Nat := 118140960795 + 5204462 * 2 ^ 59
def prefixEnd_5204462 : Nat := 4983230072969 + 3 ^ 40 * 5204462 * 2
def baseEnd_5204462 : Nat := 98977427928152657488523

theorem tailTrace_5204462 : CollatzResearch.WordTrace tailWord_5204462 prefixEnd_5204462 98977427928152657488523 := by
  unfold tailWord_5204462
  simp only [CollatzResearch.WordTrace]
  refine ⟨23727790458891312523704955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126548215780753666793093093 23727790458891312523704955)
  ·
    refine ⟨35591685688336968785557433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23727790458891312523704955 35591685688336968785557433)
    ·
      refine ⟨26693764266252726589168075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35591685688336968785557433 26693764266252726589168075)
      ·
        refine ⟨40040646399379089883752113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26693764266252726589168075 40040646399379089883752113)
        ·
          refine ⟨30030484799534317412814085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40040646399379089883752113 30030484799534317412814085)
          ·
            refine ⟨5630715899912684514902641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30030484799534317412814085 5630715899912684514902641)
            ·
              refine ⟨4223036924934513386176981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5630715899912684514902641 4223036924934513386176981)
              ·
                refine ⟨98977427928152657488523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4223036924934513386176981 98977427928152657488523)
                ·
                  rfl

theorem cell23_5204462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_5204462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204462 prefixEnd_5204462 := by exact prefixLift 5204462
  have htrace : WordTrace (prefixWord ++ tailWord_5204462) baseStart_5204462 baseEnd_5204462 := by
    simpa [prefixWord, tailWord_5204462, baseEnd_5204462] using wordTrace_append hprefix tailTrace_5204462
  have hstable : (prefixWord ++ tailWord_5204462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204462).length < 2 ^ (prefixWord ++ tailWord_5204462).sum := by decide
  have hdescent : baseEnd_5204462 < baseStart_5204462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204515 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5]
def baseStart_5204515 : Nat := 118140960795 + 5204515 * 2 ^ 59
def prefixEnd_5204515 : Nat := 4983230072969 + 3 ^ 40 * 5204515 * 2
def baseEnd_5204515 : Nat := 2672417768534810044827377

theorem tailTrace_5204515 : CollatzResearch.WordTrace tailWord_5204515 prefixEnd_5204515 2672417768534810044827377 := by
  unfold tailWord_5204515
  simp only [CollatzResearch.WordTrace]
  refine ⟨189824256739938490241318999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126549504493292326827545999 189824256739938490241318999)
  ·
    refine ⟨284736385109907735361978499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189824256739938490241318999 284736385109907735361978499)
    ·
      refine ⟨427104577664861603042967749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284736385109907735361978499 427104577664861603042967749)
      ·
        refine ⟨80082108312161550570556453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 427104577664861603042967749 80082108312161550570556453)
        ·
          refine ⟨15015395308530290731979335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80082108312161550570556453 15015395308530290731979335)
          ·
            refine ⟨22523092962795436097969003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15015395308530290731979335 22523092962795436097969003)
            ·
              refine ⟨33784639444193154146953505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22523092962795436097969003 33784639444193154146953505)
              ·
                refine ⟨25338479583144865610215129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33784639444193154146953505 25338479583144865610215129)
                ·
                  refine ⟨19003859687358649207661347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25338479583144865610215129 19003859687358649207661347)
                  ·
                    refine ⟨28505789531037973811492021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19003859687358649207661347 28505789531037973811492021)
                    ·
                      refine ⟨2672417768534810044827377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28505789531037973811492021 2672417768534810044827377)
                      ·
                        rfl

theorem cell23_5204515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_5204515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204515 prefixEnd_5204515 := by exact prefixLift 5204515
  have htrace : WordTrace (prefixWord ++ tailWord_5204515) baseStart_5204515 baseEnd_5204515 := by
    simpa [prefixWord, tailWord_5204515, baseEnd_5204515] using wordTrace_append hprefix tailTrace_5204515
  have hstable : (prefixWord ++ tailWord_5204515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204515).length < 2 ^ (prefixWord ++ tailWord_5204515).sum := by decide
  have hdescent : baseEnd_5204515 < baseStart_5204515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204516 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5204516 : Nat := 118140960795 + 5204516 * 2 ^ 59
def prefixEnd_5204516 : Nat := 4983230072969 + 3 ^ 40 * 5204516 * 2
def baseEnd_5204516 : Nat := 2672418282015464540914873

theorem tailTrace_5204516 : CollatzResearch.WordTrace tailWord_5204516 prefixEnd_5204516 2672418282015464540914873 := by
  unfold tailWord_5204516
  simp only [CollatzResearch.WordTrace]
  refine ⟨94912146606467433706052701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126549528808623244941403601 94912146606467433706052701)
  ·
    refine ⟨35592054977425287639769763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94912146606467433706052701 35592054977425287639769763)
    ·
      refine ⟨53388082466137931459654645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35592054977425287639769763 53388082466137931459654645)
      ·
        refine ⟨5005132731200431074342623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53388082466137931459654645 5005132731200431074342623)
        ·
          refine ⟨7507699096800646611513935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005132731200431074342623 7507699096800646611513935)
          ·
            refine ⟨11261548645200969917270903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7507699096800646611513935 11261548645200969917270903)
            ·
              refine ⟨16892322967801454875906355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11261548645200969917270903 16892322967801454875906355)
              ·
                refine ⟨25338484451702182313859533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16892322967801454875906355 25338484451702182313859533)
                ·
                  refine ⟨9501931669388318367697325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25338484451702182313859533 9501931669388318367697325)
                  ·
                    refine ⟨3563224376020619387886497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9501931669388318367697325 3563224376020619387886497)
                    ·
                      refine ⟨2672418282015464540914873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563224376020619387886497 2672418282015464540914873)
                      ·
                        rfl

theorem cell23_5204516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5204516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204516 prefixEnd_5204516 := by exact prefixLift 5204516
  have htrace : WordTrace (prefixWord ++ tailWord_5204516) baseStart_5204516 baseEnd_5204516 := by
    simpa [prefixWord, tailWord_5204516, baseEnd_5204516] using wordTrace_append hprefix tailTrace_5204516
  have hstable : (prefixWord ++ tailWord_5204516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204516).length < 2 ^ (prefixWord ++ tailWord_5204516).sum := by decide
  have hdescent : baseEnd_5204516 < baseStart_5204516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204562 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_5204562 : Nat := 118140960795 + 5204562 * 2 ^ 59
def prefixEnd_5204562 : Nat := 4983230072969 + 3 ^ 40 * 5204562 * 2
def baseEnd_5204562 : Nat := 2672441902125571360939661

theorem tailTrace_5204562 : CollatzResearch.WordTrace tailWord_5204562 prefixEnd_5204562 2672441902125571360939661 := by
  unfold tailWord_5204562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47456492742692054317069985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126550647313845478178853293 47456492742692054317069985)
  ·
    refine ⟨35592369557019040737802489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47456492742692054317069985 35592369557019040737802489)
    ·
      refine ⟨26694277167764280553351867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35592369557019040737802489 26694277167764280553351867)
      ·
        refine ⟨40041415751646420830027801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26694277167764280553351867 40041415751646420830027801)
        ·
          refine ⟨30031061813734815622520851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40041415751646420830027801 30031061813734815622520851)
          ·
            refine ⟨45046592720602223433781277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30031061813734815622520851 45046592720602223433781277)
            ·
              refine ⟨16892472270225833787667979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45046592720602223433781277 16892472270225833787667979)
              ·
                refine ⟨25338708405338750681501969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16892472270225833787667979 25338708405338750681501969)
                ·
                  refine ⟨19004031304004063011126477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25338708405338750681501969 19004031304004063011126477)
                  ·
                    refine ⟨7126511739001523629172429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19004031304004063011126477 7126511739001523629172429)
                    ·
                      refine ⟨2672441902125571360939661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7126511739001523629172429 2672441902125571360939661)
                      ·
                        rfl

theorem cell23_5204562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_5204562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204562 prefixEnd_5204562 := by exact prefixLift 5204562
  have htrace : WordTrace (prefixWord ++ tailWord_5204562) baseStart_5204562 baseEnd_5204562 := by
    simpa [prefixWord, tailWord_5204562, baseEnd_5204562] using wordTrace_append hprefix tailTrace_5204562
  have hstable : (prefixWord ++ tailWord_5204562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204562).length < 2 ^ (prefixWord ++ tailWord_5204562).sum := by decide
  have hdescent : baseEnd_5204562 < baseStart_5204562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204565 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_5204565 : Nat := 118140960795 + 5204565 * 2 ^ 59
def prefixEnd_5204565 : Nat := 4983230072969 + 3 ^ 40 * 5204565 * 2
def baseEnd_5204565 : Nat := 890814480855844949734049

theorem tailTrace_5204565 : CollatzResearch.WordTrace tailWord_5204565 prefixEnd_5204565 890814480855844949734049 := by
  unfold tailWord_5204565
  simp only [CollatzResearch.WordTrace]
  refine ⟨189826080389757348780639149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126550720259838232520426099 189826080389757348780639149)
  ·
    refine ⟨71184780146159005792739681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189826080389757348780639149 71184780146159005792739681)
    ·
      refine ⟨53388585109619254344554761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71184780146159005792739681 53388585109619254344554761)
      ·
        refine ⟨40041438832214440758416071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53388585109619254344554761 40041438832214440758416071)
        ·
          refine ⟨60062158248321661137624107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40041438832214440758416071 60062158248321661137624107)
          ·
            refine ⟨90093237372482491706436161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60062158248321661137624107 90093237372482491706436161)
            ·
              refine ⟨67569928029361868779827121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90093237372482491706436161 67569928029361868779827121)
              ·
                refine ⟨50677446022021401584870341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67569928029361868779827121 50677446022021401584870341)
                ·
                  refine ⟨9502021129129012797163189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50677446022021401584870341 9502021129129012797163189)
                  ·
                    refine ⟨890814480855844949734049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9502021129129012797163189 890814480855844949734049)
                    ·
                      rfl

theorem cell23_5204565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_5204565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204565 prefixEnd_5204565 := by exact prefixLift 5204565
  have htrace : WordTrace (prefixWord ++ tailWord_5204565) baseStart_5204565 baseEnd_5204565 := by
    simpa [prefixWord, tailWord_5204565, baseEnd_5204565] using wordTrace_append hprefix tailTrace_5204565
  have hstable : (prefixWord ++ tailWord_5204565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204565).length < 2 ^ (prefixWord ++ tailWord_5204565).sum := by decide
  have hdescent : baseEnd_5204565 < baseStart_5204565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204615 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_5204615 : Nat := 118140960795 + 5204615 * 2 ^ 59
def prefixEnd_5204615 : Nat := 4983230072969 + 3 ^ 40 * 5204615 * 2
def baseEnd_5204615 : Nat := 2672469116600259653576917

theorem tailTrace_5204615 : CollatzResearch.WordTrace tailWord_5204615 prefixEnd_5204615 2672469116600259653576917 := by
  unfold tailWord_5204615
  simp only [CollatzResearch.WordTrace]
  refine ⟨189827904039576207319959299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126551936026384138213306199 189827904039576207319959299)
  ·
    refine ⟨284741856059364310979938949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189827904039576207319959299 284741856059364310979938949)
    ·
      refine ⟨53389098011130808308738553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284741856059364310979938949 53389098011130808308738553)
      ·
        refine ⟨40041823508348106231553915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53389098011130808308738553 40041823508348106231553915)
        ·
          refine ⟨60062735262522159347330873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40041823508348106231553915 60062735262522159347330873)
          ·
            refine ⟨45047051446891619510498155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60062735262522159347330873 45047051446891619510498155)
            ·
              refine ⟨67570577170337429265747233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45047051446891619510498155 67570577170337429265747233)
              ·
                refine ⟨50677932877753071949310425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67570577170337429265747233 50677932877753071949310425)
                ·
                  refine ⟨38008449658314803961982819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50677932877753071949310425 38008449658314803961982819)
                  ·
                    refine ⟨57012674487472205942974229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38008449658314803961982819 57012674487472205942974229)
                    ·
                      refine ⟨2672469116600259653576917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57012674487472205942974229 2672469116600259653576917)
                      ·
                        rfl

theorem cell23_5204615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_5204615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204615 prefixEnd_5204615 := by exact prefixLift 5204615
  have htrace : WordTrace (prefixWord ++ tailWord_5204615) baseStart_5204615 baseEnd_5204615 := by
    simpa [prefixWord, tailWord_5204615, baseEnd_5204615] using wordTrace_append hprefix tailTrace_5204615
  have hstable : (prefixWord ++ tailWord_5204615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204615).length < 2 ^ (prefixWord ++ tailWord_5204615).sum := by decide
  have hdescent : baseEnd_5204615 < baseStart_5204615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204622 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5204622 : Nat := 118140960795 + 5204622 * 2 ^ 59
def prefixEnd_5204622 : Nat := 4983230072969 + 3 ^ 40 * 5204622 * 2
def baseEnd_5204622 : Nat := 2672472710964841126189385

theorem tailTrace_5204622 : CollatzResearch.WordTrace tailWord_5204622 prefixEnd_5204622 2672472710964841126189385 := by
  unfold tailWord_5204622
  simp only [CollatzResearch.WordTrace]
  refine ⟨23728519918818855939433015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126552106233700565010309413 23728519918818855939433015)
  ·
    refine ⟨35592779878228283909149523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23728519918818855939433015 35592779878228283909149523)
    ·
      refine ⟨53389169817342425863724285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35592779878228283909149523 53389169817342425863724285)
      ·
        refine ⟨20020938681503409698896607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53389169817342425863724285 20020938681503409698896607)
        ·
          refine ⟨30031408022255114548344911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20020938681503409698896607 30031408022255114548344911)
          ·
            refine ⟨45047112033382671822517367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30031408022255114548344911 45047112033382671822517367)
            ·
              refine ⟨67570668050074007733776051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45047112033382671822517367 67570668050074007733776051)
              ·
                refine ⟨101356002075111011600664077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67570668050074007733776051 101356002075111011600664077)
                ·
                  refine ⟨38008500778166629350249029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101356002075111011600664077 38008500778166629350249029)
                  ·
                    refine ⟨7126593895906243003171693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38008500778166629350249029 7126593895906243003171693)
                    ·
                      refine ⟨2672472710964841126189385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7126593895906243003171693 2672472710964841126189385)
                      ·
                        rfl

theorem cell23_5204622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5204622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204622 prefixEnd_5204622 := by exact prefixLift 5204622
  have htrace : WordTrace (prefixWord ++ tailWord_5204622) baseStart_5204622 baseEnd_5204622 := by
    simpa [prefixWord, tailWord_5204622, baseEnd_5204622] using wordTrace_append hprefix tailTrace_5204622
  have hstable : (prefixWord ++ tailWord_5204622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204622).length < 2 ^ (prefixWord ++ tailWord_5204622).sum := by decide
  have hdescent : baseEnd_5204622 < baseStart_5204622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204663 : List Nat := [1, 1, 3, 1, 6, 1, 3, 2, 1, 4]
def baseStart_5204663 : Nat := 118140960795 + 5204663 * 2 ^ 59
def prefixEnd_5204663 : Nat := 4983230072969 + 3 ^ 40 * 5204663 * 2
def baseEnd_5204663 : Nat := 890831254557225155258899

theorem tailTrace_5204663 : CollatzResearch.WordTrace tailWord_5204663 prefixEnd_5204663 890831254557225155258899 := by
  unfold tailWord_5204663
  simp only [CollatzResearch.WordTrace]
  refine ⟨189829654743402311517706643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126553103162268207678471095 189829654743402311517706643)
  ·
    refine ⟨284744482115103467276559965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189829654743402311517706643 284744482115103467276559965)
    ·
      refine ⟨106779180793163800228709987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284744482115103467276559965 106779180793163800228709987)
      ·
        refine ⟨160168771189745700343064981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106779180793163800228709987 160168771189745700343064981)
        ·
          refine ⟨7507911149519329703581171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160168771189745700343064981 7507911149519329703581171)
          ·
            refine ⟨11261866724278994555371757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7507911149519329703581171 11261866724278994555371757)
            ·
              refine ⟨4223200021604622958264409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11261866724278994555371757 4223200021604622958264409)
              ·
                refine ⟨3167400016203467218698307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4223200021604622958264409 3167400016203467218698307)
                ·
                  refine ⟨4751100024305200828047461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3167400016203467218698307 4751100024305200828047461)
                  ·
                    refine ⟨890831254557225155258899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751100024305200828047461 890831254557225155258899)
                    ·
                      rfl

theorem cell23_5204663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_5204663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204663 prefixEnd_5204663 := by exact prefixLift 5204663
  have htrace : WordTrace (prefixWord ++ tailWord_5204663) baseStart_5204663 baseEnd_5204663 := by
    simpa [prefixWord, tailWord_5204663, baseEnd_5204663] using wordTrace_append hprefix tailTrace_5204663
  have hstable : (prefixWord ++ tailWord_5204663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204663).length < 2 ^ (prefixWord ++ tailWord_5204663).sum := by decide
  have hdescent : baseEnd_5204663 < baseStart_5204663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204665 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5204665 : Nat := 118140960795 + 5204665 * 2 ^ 59
def prefixEnd_5204665 : Nat := 4983230072969 + 3 ^ 40 * 5204665 * 2
def baseEnd_5204665 : Nat := 2672494790632984457951687

theorem tailTrace_5204665 : CollatzResearch.WordTrace tailWord_5204665 prefixEnd_5204665 2672494790632984457951687 := by
  unfold tailWord_5204665
  simp only [CollatzResearch.WordTrace]
  refine ⟨189829727689395065859279449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126553151792930043906186299 189829727689395065859279449)
  ·
    refine ⟨142372295767046299394459587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189829727689395065859279449 142372295767046299394459587)
    ·
      refine ⟨213558443650569449091689381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142372295767046299394459587 213558443650569449091689381)
      ·
        refine ⟨40042208184481771704691759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213558443650569449091689381 40042208184481771704691759)
        ·
          refine ⟨60063312276722657557037639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40042208184481771704691759 60063312276722657557037639)
          ·
            refine ⟨90094968415083986335556459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60063312276722657557037639 90094968415083986335556459)
            ·
              refine ⟨135142452622625979503334689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90094968415083986335556459 135142452622625979503334689)
              ·
                refine ⟨101356839466969484627501017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135142452622625979503334689 101356839466969484627501017)
                ·
                  refine ⟨76017629600227113470625763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101356839466969484627501017 76017629600227113470625763)
                  ·
                    refine ⟨114026444400340670205938645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76017629600227113470625763 114026444400340670205938645)
                    ·
                      refine ⟨2672494790632984457951687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114026444400340670205938645 2672494790632984457951687)
                      ·
                        rfl

theorem cell23_5204665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5204665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204665 prefixEnd_5204665 := by exact prefixLift 5204665
  have htrace : WordTrace (prefixWord ++ tailWord_5204665) baseStart_5204665 baseEnd_5204665 := by
    simpa [prefixWord, tailWord_5204665, baseEnd_5204665] using wordTrace_append hprefix tailTrace_5204665
  have hstable : (prefixWord ++ tailWord_5204665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204665).length < 2 ^ (prefixWord ++ tailWord_5204665).sum := by decide
  have hdescent : baseEnd_5204665 < baseStart_5204665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204676 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 6]
def baseStart_5204676 : Nat := 118140960795 + 5204676 * 2 ^ 59
def prefixEnd_5204676 : Nat := 4983230072969 + 3 ^ 40 * 5204676 * 2
def baseEnd_5204676 : Nat := 296944493213353768323793

theorem tailTrace_5204676 : CollatzResearch.WordTrace tailWord_5204676 prefixEnd_5204676 296944493213353768323793 := by
  unfold tailWord_5204676
  simp only [CollatzResearch.WordTrace]
  refine ⟨94915064446177607368964941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126553419261570143158619921 94915064446177607368964941)
  ·
    refine ⟨35593149167316602763361853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94915064446177607368964941 35593149167316602763361853)
    ·
      refine ⟨13347430937743726036260695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35593149167316602763361853 13347430937743726036260695)
      ·
        refine ⟨20021146406615589054391043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13347430937743726036260695 20021146406615589054391043)
        ·
          refine ⟨30031719609923383581586565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20021146406615589054391043 30031719609923383581586565)
          ·
            refine ⟨5630947426860634421547481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30031719609923383581586565 5630947426860634421547481)
            ·
              refine ⟨4223210570145475816160611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5630947426860634421547481 4223210570145475816160611)
              ·
                refine ⟨6334815855218213724240917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223210570145475816160611 6334815855218213724240917)
                ·
                  refine ⟨296944493213353768323793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6334815855218213724240917 296944493213353768323793)
                  ·
                    rfl

theorem cell23_5204676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_5204676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204676 prefixEnd_5204676 := by exact prefixLift 5204676
  have htrace : WordTrace (prefixWord ++ tailWord_5204676) baseStart_5204676 baseEnd_5204676 := by
    simpa [prefixWord, tailWord_5204676, baseEnd_5204676] using wordTrace_append hprefix tailTrace_5204676
  have hstable : (prefixWord ++ tailWord_5204676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204676).length < 2 ^ (prefixWord ++ tailWord_5204676).sum := by decide
  have hdescent : baseEnd_5204676 < baseStart_5204676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204696 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 2, 3, 2]
def baseStart_5204696 : Nat := 118140960795 + 5204696 * 2 ^ 59
def prefixEnd_5204696 : Nat := 4983230072969 + 3 ^ 40 * 5204696 * 2
def baseEnd_5204696 : Nat := 2672510708533273836664045

theorem tailTrace_5204696 : CollatzResearch.WordTrace tailWord_5204696 prefixEnd_5204696 2672510708533273836664045 := by
  unfold tailWord_5204696
  simp only [CollatzResearch.WordTrace]
  refine ⟨94915429176141379076828971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126553905568188505435771961 94915429176141379076828971)
  ·
    refine ⟨142373143764212068615243457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94915429176141379076828971 142373143764212068615243457)
    ·
      refine ⟨106779857823159051461432593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142373143764212068615243457 106779857823159051461432593)
      ·
        refine ⟨80084893367369288596074445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106779857823159051461432593 80084893367369288596074445)
        ·
          refine ⟨30031835012763483223527917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80084893367369288596074445 30031835012763483223527917)
          ·
            refine ⟨11261938129786306208822969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30031835012763483223527917 11261938129786306208822969)
            ·
              refine ⟨8446453597339729656617227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11261938129786306208822969 8446453597339729656617227)
              ·
                refine ⟨12669680396009594484925841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8446453597339729656617227 12669680396009594484925841)
                ·
                  refine ⟨9502260297007195863694381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12669680396009594484925841 9502260297007195863694381)
                  ·
                    refine ⟨3563347611377698448885393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9502260297007195863694381 3563347611377698448885393)
                    ·
                      refine ⟨2672510708533273836664045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563347611377698448885393 2672510708533273836664045)
                      ·
                        rfl

theorem cell23_5204696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_5204696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204696 prefixEnd_5204696 := by exact prefixLift 5204696
  have htrace : WordTrace (prefixWord ++ tailWord_5204696) baseStart_5204696 baseEnd_5204696 := by
    simpa [prefixWord, tailWord_5204696, baseEnd_5204696] using wordTrace_append hprefix tailTrace_5204696
  have hstable : (prefixWord ++ tailWord_5204696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204696).length < 2 ^ (prefixWord ++ tailWord_5204696).sum := by decide
  have hdescent : baseEnd_5204696 < baseStart_5204696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204719 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 2, 4]
def baseStart_5204719 : Nat := 118140960795 + 5204719 * 2 ^ 59
def prefixEnd_5204719 : Nat := 4983230072969 + 3 ^ 40 * 5204719 * 2
def baseEnd_5204719 : Nat := 890840839529442415558813

theorem tailTrace_5204719 : CollatzResearch.WordTrace tailWord_5204719 prefixEnd_5204719 890840839529442415558813 := by
  unfold tailWord_5204719
  simp only [CollatzResearch.WordTrace]
  refine ⟨189831697231199433081745211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126554464820799622054496807 189831697231199433081745211)
  ·
    refine ⟨284747545846799149622617817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189831697231199433081745211 284747545846799149622617817)
    ·
      refine ⟨213560659385099362216963363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284747545846799149622617817 213560659385099362216963363)
      ·
        refine ⟨320340989077649043325445045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213560659385099362216963363 320340989077649043325445045)
        ·
          refine ⟨30031967726029597811760473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 320340989077649043325445045 30031967726029597811760473)
          ·
            refine ⟨22523975794522198358820355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30031967726029597811760473 22523975794522198358820355)
            ·
              refine ⟨33785963691783297538230533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22523975794522198358820355 33785963691783297538230533)
              ·
                refine ⟨6334868192209368288418225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33785963691783297538230533 6334868192209368288418225)
                ·
                  refine ⟨4751151144157026216313669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6334868192209368288418225 4751151144157026216313669)
                  ·
                    refine ⟨890840839529442415558813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751151144157026216313669 890840839529442415558813)
                    ·
                      rfl

theorem cell23_5204719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_5204719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204719 prefixEnd_5204719 := by exact prefixLift 5204719
  have htrace : WordTrace (prefixWord ++ tailWord_5204719) baseStart_5204719 baseEnd_5204719 := by
    simpa [prefixWord, tailWord_5204719, baseEnd_5204719] using wordTrace_append hprefix tailTrace_5204719
  have hstable : (prefixWord ++ tailWord_5204719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204719).length < 2 ^ (prefixWord ++ tailWord_5204719).sum := by decide
  have hdescent : baseEnd_5204719 < baseStart_5204719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204732 : List Nat := [2, 2, 2, 1, 3, 2, 3, 8]
def baseStart_5204732 : Nat := 118140960795 + 5204732 * 2 ^ 59
def prefixEnd_5204732 : Nat := 4983230072969 + 3 ^ 40 * 5204732 * 2
def baseEnd_5204732 : Nat := 98982562734697618363477

theorem tailTrace_5204732 : CollatzResearch.WordTrace tailWord_5204732 prefixEnd_5204732 98982562734697618363477 := by
  unfold tailWord_5204732
  simp only [CollatzResearch.WordTrace]
  refine ⟨94916085690076168150984225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126554780920101557534645633 94916085690076168150984225)
  ·
    refine ⟨71187064267557126113238169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94916085690076168150984225 71187064267557126113238169)
    ·
      refine ⟨53390298200667844584928627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71187064267557126113238169 53390298200667844584928627)
      ·
        refine ⟨80085447301001766877392941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53390298200667844584928627 80085447301001766877392941)
        ·
          refine ⟨30032042737875662579022353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80085447301001766877392941 30032042737875662579022353)
          ·
            refine ⟨22524032053406746934266765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30032042737875662579022353 22524032053406746934266765)
            ·
              refine ⟨8446512020027530100350037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22524032053406746934266765 8446512020027530100350037)
              ·
                refine ⟨98982562734697618363477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8446512020027530100350037 98982562734697618363477)
                ·
                  rfl

theorem cell23_5204732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 8].length) (baseStart_5204732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204732 prefixEnd_5204732 := by exact prefixLift 5204732
  have htrace : WordTrace (prefixWord ++ tailWord_5204732) baseStart_5204732 baseEnd_5204732 := by
    simpa [prefixWord, tailWord_5204732, baseEnd_5204732] using wordTrace_append hprefix tailTrace_5204732
  have hstable : (prefixWord ++ tailWord_5204732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204732).length < 2 ^ (prefixWord ++ tailWord_5204732).sum := by decide
  have hdescent : baseEnd_5204732 < baseStart_5204732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204743 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5204743 : Nat := 118140960795 + 5204743 * 2 ^ 59
def prefixEnd_5204743 : Nat := 4983230072969 + 3 ^ 40 * 5204743 * 2
def baseEnd_5204743 : Nat := 2672534842124035152776329

theorem tailTrace_5204743 : CollatzResearch.WordTrace tailWord_5204743 prefixEnd_5204743 2672534842124035152776329 := by
  unfold tailWord_5204743
  simp only [CollatzResearch.WordTrace]
  refine ⟨189832572583112485180618883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126555048388741656787079255 189832572583112485180618883)
  ·
    refine ⟨284748858874668727770928325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189832572583112485180618883 284748858874668727770928325)
    ·
      refine ⟨53390411039000386457049061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284748858874668727770928325 53390411039000386457049061)
      ·
        refine ⟨10010702069812572460696699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53390411039000386457049061 10010702069812572460696699)
        ·
          refine ⟨15016053104718858691045049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10010702069812572460696699 15016053104718858691045049)
          ·
            refine ⟨11262039828539144018283787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15016053104718858691045049 11262039828539144018283787)
            ·
              refine ⟨16893059742808716027425681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11262039828539144018283787 16893059742808716027425681)
              ·
                refine ⟨12669794807106537020569261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16893059742808716027425681 12669794807106537020569261)
                ·
                  refine ⟨4751173052664951382713473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12669794807106537020569261 4751173052664951382713473)
                  ·
                    refine ⟨3563379789498713537035105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4751173052664951382713473 3563379789498713537035105)
                    ·
                      refine ⟨2672534842124035152776329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563379789498713537035105 2672534842124035152776329)
                      ·
                        rfl

theorem cell23_5204743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5204743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204743 prefixEnd_5204743 := by exact prefixLift 5204743
  have htrace : WordTrace (prefixWord ++ tailWord_5204743) baseStart_5204743 baseEnd_5204743 := by
    simpa [prefixWord, tailWord_5204743, baseEnd_5204743] using wordTrace_append hprefix tailTrace_5204743
  have hstable : (prefixWord ++ tailWord_5204743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204743).length < 2 ^ (prefixWord ++ tailWord_5204743).sum := by decide
  have hdescent : baseEnd_5204743 < baseStart_5204743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204776 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_5204776 : Nat := 118140960795 + 5204776 * 2 ^ 59
def prefixEnd_5204776 : Nat := 4983230072969 + 3 ^ 40 * 5204776 * 2
def baseEnd_5204776 : Nat := 2672551786985633523663677

theorem tailTrace_5204776 : CollatzResearch.WordTrace tailWord_5204776 prefixEnd_5204776 2672551786985633523663677 := by
  unfold tailWord_5204776
  simp only [CollatzResearch.WordTrace]
  refine ⟨94916888095996465908285091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126555850794661954544380121 94916888095996465908285091)
  ·
    refine ⟨142375332143994698862427637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94916888095996465908285091 142375332143994698862427637)
    ·
      refine ⟨13347687388499503018352591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142375332143994698862427637 13347687388499503018352591)
      ·
        refine ⟨20021531082749254527528887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13347687388499503018352591 20021531082749254527528887)
        ·
          refine ⟨30032296624123881791293331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20021531082749254527528887 30032296624123881791293331)
          ·
            refine ⟨45048444936185822686939997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30032296624123881791293331 45048444936185822686939997)
            ·
              refine ⟨16893166851069683507602499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45048444936185822686939997 16893166851069683507602499)
              ·
                refine ⟨25339750276604525261403749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16893166851069683507602499 25339750276604525261403749)
                ·
                  refine ⟨4751203176863348486513203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25339750276604525261403749 4751203176863348486513203)
                  ·
                    refine ⟨7126804765295022729769805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751203176863348486513203 7126804765295022729769805)
                    ·
                      refine ⟨2672551786985633523663677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7126804765295022729769805 2672551786985633523663677)
                      ·
                        rfl

theorem cell23_5204776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_5204776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204776 prefixEnd_5204776 := by exact prefixLift 5204776
  have htrace : WordTrace (prefixWord ++ tailWord_5204776) baseStart_5204776 baseEnd_5204776 := by
    simpa [prefixWord, tailWord_5204776, baseEnd_5204776] using wordTrace_append hprefix tailTrace_5204776
  have hstable : (prefixWord ++ tailWord_5204776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204776).length < 2 ^ (prefixWord ++ tailWord_5204776).sum := by decide
  have hdescent : baseEnd_5204776 < baseStart_5204776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204790 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5204790 : Nat := 118140960795 + 5204790 * 2 ^ 59
def prefixEnd_5204790 : Nat := 4983230072969 + 3 ^ 40 * 5204790 * 2
def baseEnd_5204790 : Nat := 2672558975714796468888613

theorem tailTrace_5204790 : CollatzResearch.WordTrace tailWord_5204790 prefixEnd_5204790 2672558975714796468888613 := by
  unfold tailWord_5204790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11864642925871388262973739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126556191209294808138386549 11864642925871388262973739)
  ·
    refine ⟨17796964388807082394460609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11864642925871388262973739 17796964388807082394460609)
    ·
      refine ⟨13347723291605311795845457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17796964388807082394460609 13347723291605311795845457)
      ·
        refine ⟨10010792468703983846884093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13347723291605311795845457 10010792468703983846884093)
        ·
          refine ⟨3754047175763993942581535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10010792468703983846884093 3754047175763993942581535)
          ·
            refine ⟨5631070763645990913872303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754047175763993942581535 5631070763645990913872303)
            ·
              refine ⟨8446606145468986370808455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631070763645990913872303 8446606145468986370808455)
              ·
                refine ⟨12669909218203479556212683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8446606145468986370808455 12669909218203479556212683)
                ·
                  refine ⟨19004863827305219334319025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12669909218203479556212683 19004863827305219334319025)
                  ·
                    refine ⟨14253647870478914500739269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19004863827305219334319025 14253647870478914500739269)
                    ·
                      refine ⟨2672558975714796468888613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14253647870478914500739269 2672558975714796468888613)
                      ·
                        rfl

theorem cell23_5204790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5204790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204790 prefixEnd_5204790 := by exact prefixLift 5204790
  have htrace : WordTrace (prefixWord ++ tailWord_5204790) baseStart_5204790 baseEnd_5204790 := by
    simpa [prefixWord, tailWord_5204790, baseEnd_5204790] using wordTrace_append hprefix tailTrace_5204790
  have hstable : (prefixWord ++ tailWord_5204790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204790).length < 2 ^ (prefixWord ++ tailWord_5204790).sum := by decide
  have hdescent : baseEnd_5204790 < baseStart_5204790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204792 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 2, 6]
def baseStart_5204792 : Nat := 118140960795 + 5204792 * 2 ^ 59
def prefixEnd_5204792 : Nat := 4983230072969 + 3 ^ 40 * 5204792 * 2
def baseEnd_5204792 : Nat := 890853334225368487021201

theorem tailTrace_5204792 : CollatzResearch.WordTrace tailWord_5204792 prefixEnd_5204792 890853334225368487021201 := by
  unfold tailWord_5204792
  simp only [CollatzResearch.WordTrace]
  refine ⟨94917179879967483274576315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126556239839956644366101753 94917179879967483274576315)
  ·
    refine ⟨142375769819951224911864473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94917179879967483274576315 142375769819951224911864473)
    ·
      refine ⟨106781827364963418683898355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142375769819951224911864473 106781827364963418683898355)
      ·
        refine ⟨160172741047445128025847533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106781827364963418683898355 160172741047445128025847533)
        ·
          refine ⟨60064777892791923009692825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160172741047445128025847533 60064777892791923009692825)
          ·
            refine ⟨45048583419593942257269619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60064777892791923009692825 45048583419593942257269619)
            ·
              refine ⟨67572875129390913385904429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45048583419593942257269619 67572875129390913385904429)
              ·
                refine ⟨25339828173521592519714161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67572875129390913385904429 25339828173521592519714161)
                ·
                  refine ⟨19004871130141194389785621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25339828173521592519714161 19004871130141194389785621)
                  ·
                    refine ⟨890853334225368487021201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19004871130141194389785621 890853334225368487021201)
                    ·
                      rfl

theorem cell23_5204792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_5204792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204792 prefixEnd_5204792 := by exact prefixLift 5204792
  have htrace : WordTrace (prefixWord ++ tailWord_5204792) baseStart_5204792 baseEnd_5204792 := by
    simpa [prefixWord, tailWord_5204792, baseEnd_5204792] using wordTrace_append hprefix tailTrace_5204792
  have hstable : (prefixWord ++ tailWord_5204792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204792).length < 2 ^ (prefixWord ++ tailWord_5204792).sum := by decide
  have hdescent : baseEnd_5204792 < baseStart_5204792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204816 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 4, 2, 2]
def baseStart_5204816 : Nat := 118140960795 + 5204816 * 2 ^ 59
def prefixEnd_5204816 : Nat := 4983230072969 + 3 ^ 40 * 5204816 * 2
def baseEnd_5204816 : Nat := 2672572326211813367163493

theorem tailTrace_5204816 : CollatzResearch.WordTrace tailWord_5204816 prefixEnd_5204816 2672572326211813367163493 := by
  unfold tailWord_5204816
  simp only [CollatzResearch.WordTrace]
  refine ⟨94917617555924009324013151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126556823407898679098684201 94917617555924009324013151)
  ·
    refine ⟨142376426333886013986019727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94917617555924009324013151 142376426333886013986019727)
    ·
      refine ⟨213564639500829020979029591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142376426333886013986019727 213564639500829020979029591)
      ·
        refine ⟨320346959251243531468544387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213564639500829020979029591 320346959251243531468544387)
        ·
          refine ⟨480520438876865297202816581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320346959251243531468544387 480520438876865297202816581)
          ·
            refine ⟨90097582289412243225528109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 480520438876865297202816581 90097582289412243225528109)
            ·
              refine ⟨33786593358529591209573041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90097582289412243225528109 33786593358529591209573041)
              ·
                refine ⟨25339945018897193407179781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33786593358529591209573041 25339945018897193407179781)
                ·
                  refine ⟨4751239691043223763846209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25339945018897193407179781 4751239691043223763846209)
                  ·
                    refine ⟨3563429768282417822884657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4751239691043223763846209 3563429768282417822884657)
                    ·
                      refine ⟨2672572326211813367163493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563429768282417822884657 2672572326211813367163493)
                      ·
                        rfl

theorem cell23_5204816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 2, 2].length) (baseStart_5204816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204816 prefixEnd_5204816 := by exact prefixLift 5204816
  have htrace : WordTrace (prefixWord ++ tailWord_5204816) baseStart_5204816 baseEnd_5204816 := by
    simpa [prefixWord, tailWord_5204816, baseEnd_5204816] using wordTrace_append hprefix tailTrace_5204816
  have hstable : (prefixWord ++ tailWord_5204816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204816).length < 2 ^ (prefixWord ++ tailWord_5204816).sum := by decide
  have hdescent : baseEnd_5204816 < baseStart_5204816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204832 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_5204832 : Nat := 118140960795 + 5204832 * 2 ^ 59
def prefixEnd_5204832 : Nat := 4983230072969 + 3 ^ 40 * 5204832 * 2
def baseEnd_5204832 : Nat := 2672580541902285304563419

theorem tailTrace_5204832 : CollatzResearch.WordTrace tailWord_5204832 prefixEnd_5204832 2672580541902285304563419 := by
  unfold tailWord_5204832
  simp only [CollatzResearch.WordTrace]
  refine ⟨94917909339895026690304375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126557212453193368920405833 94917909339895026690304375)
  ·
    refine ⟨142376864009842540035456563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94917909339895026690304375 142376864009842540035456563)
    ·
      refine ⟨213565296014763810053184845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142376864009842540035456563 213565296014763810053184845)
      ·
        refine ⟨80086986005536428769944317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213565296014763810053184845 80086986005536428769944317)
        ·
          refine ⟨30032619752076160788729119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80086986005536428769944317 30032619752076160788729119)
          ·
            refine ⟨45048929628114241183093679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30032619752076160788729119 45048929628114241183093679)
            ·
              refine ⟨67573394442171361774640519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45048929628114241183093679 67573394442171361774640519)
              ·
                refine ⟨101360091663257042661960779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67573394442171361774640519 101360091663257042661960779)
                ·
                  refine ⟨152040137494885563992941169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101360091663257042661960779 152040137494885563992941169)
                  ·
                    refine ⟨114030103121164172994705877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152040137494885563992941169 114030103121164172994705877)
                    ·
                      refine ⟨2672580541902285304563419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114030103121164172994705877 2672580541902285304563419)
                      ·
                        rfl

theorem cell23_5204832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_5204832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204832 prefixEnd_5204832 := by exact prefixLift 5204832
  have htrace : WordTrace (prefixWord ++ tailWord_5204832) baseStart_5204832 baseEnd_5204832 := by
    simpa [prefixWord, tailWord_5204832, baseEnd_5204832] using wordTrace_append hprefix tailTrace_5204832
  have hstable : (prefixWord ++ tailWord_5204832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204832).length < 2 ^ (prefixWord ++ tailWord_5204832).sum := by decide
  have hdescent : baseEnd_5204832 < baseStart_5204832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204839 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 7]
def baseStart_5204839 : Nat := 118140960795 + 5204839 * 2 ^ 59
def prefixEnd_5204839 : Nat := 4983230072969 + 3 ^ 40 * 5204839 * 2
def baseEnd_5204839 : Nat := 296953792918540753019543

theorem tailTrace_5204839 : CollatzResearch.WordTrace tailWord_5204839 prefixEnd_5204839 296953792918540753019543 := by
  unfold tailWord_5204839
  simp only [CollatzResearch.WordTrace]
  refine ⟨189836073990764693576113571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126557382660509795717409047 189836073990764693576113571)
  ·
    refine ⟨284754110986147040364170357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189836073990764693576113571 284754110986147040364170357)
    ·
      refine ⟨26695697904951285034140971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 284754110986147040364170357 26695697904951285034140971)
      ·
        refine ⟨40043546857426927551211457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26695697904951285034140971 40043546857426927551211457)
        ·
          refine ⟨30032660143070195663408593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40043546857426927551211457 30032660143070195663408593)
          ·
            refine ⟨22524495107302646747556445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30032660143070195663408593 22524495107302646747556445)
            ·
              refine ⟨8446685665238492530333667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22524495107302646747556445 8446685665238492530333667)
              ·
                refine ⟨12670028497857738795500501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8446685665238492530333667 12670028497857738795500501)
                ·
                  refine ⟨296953792918540753019543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12670028497857738795500501 296953792918540753019543)
                  ·
                    rfl

theorem cell23_5204839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 7].length) (baseStart_5204839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204839 prefixEnd_5204839 := by exact prefixLift 5204839
  have htrace : WordTrace (prefixWord ++ tailWord_5204839) baseStart_5204839 baseEnd_5204839 := by
    simpa [prefixWord, tailWord_5204839, baseEnd_5204839] using wordTrace_append hprefix tailTrace_5204839
  have hstable : (prefixWord ++ tailWord_5204839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204839).length < 2 ^ (prefixWord ++ tailWord_5204839).sum := by decide
  have hdescent : baseEnd_5204839 < baseStart_5204839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204850 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_5204850 : Nat := 118140960795 + 5204850 * 2 ^ 59
def prefixEnd_5204850 : Nat := 4983230072969 + 3 ^ 40 * 5204850 * 2
def baseEnd_5204850 : Nat := 2672589784554066234138337

theorem tailTrace_5204850 : CollatzResearch.WordTrace tailWord_5204850 prefixEnd_5204850 2672589784554066234138337 := by
  unfold tailWord_5204850
  simp only [CollatzResearch.WordTrace]
  refine ⟨47459118798431210613691001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126557650129149894969842669 47459118798431210613691001)
  ·
    refine ⟨35594339098823407960268251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47459118798431210613691001 35594339098823407960268251)
    ·
      refine ⟨53391508648235111940402377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35594339098823407960268251 53391508648235111940402377)
      ·
        refine ⟨40043631486176333955301783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53391508648235111940402377 40043631486176333955301783)
        ·
          refine ⟨60065447229264500932952675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40043631486176333955301783 60065447229264500932952675)
          ·
            refine ⟨90098170843896751399429013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60065447229264500932952675 90098170843896751399429013)
            ·
              refine ⟨4223351758307660221848235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90098170843896751399429013 4223351758307660221848235)
              ·
                refine ⟨6335027637461490332772353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223351758307660221848235 6335027637461490332772353)
                ·
                  refine ⟨4751270728096117749579265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335027637461490332772353 4751270728096117749579265)
                  ·
                    refine ⟨3563453046072088312184449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4751270728096117749579265 3563453046072088312184449)
                    ·
                      refine ⟨2672589784554066234138337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563453046072088312184449 2672589784554066234138337)
                      ·
                        rfl

theorem cell23_5204850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_5204850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204850 prefixEnd_5204850 := by exact prefixLift 5204850
  have htrace : WordTrace (prefixWord ++ tailWord_5204850) baseStart_5204850 baseEnd_5204850 := by
    simpa [prefixWord, tailWord_5204850, baseEnd_5204850] using wordTrace_append hprefix tailTrace_5204850
  have hstable : (prefixWord ++ tailWord_5204850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204850).length < 2 ^ (prefixWord ++ tailWord_5204850).sum := by decide
  have hdescent : baseEnd_5204850 < baseStart_5204850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204869 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_5204869 : Nat := 118140960795 + 5204869 * 2 ^ 59
def prefixEnd_5204869 : Nat := 4983230072969 + 3 ^ 40 * 5204869 * 2
def baseEnd_5204869 : Nat := 890866513562167219933583

theorem tailTrace_5204869 : CollatzResearch.WordTrace tailWord_5204869 prefixEnd_5204869 890866513562167219933583 := by
  unfold tailWord_5204869
  simp only [CollatzResearch.WordTrace]
  refine ⟨189837168180656008699705661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126558112120437339133137107 189837168180656008699705661)
  ·
    refine ⟨71188938067746003262389623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189837168180656008699705661 71188938067746003262389623)
    ·
      refine ⟨106783407101619004893584435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71188938067746003262389623 106783407101619004893584435)
      ·
        refine ⟨160175110652428507340376653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106783407101619004893584435 160175110652428507340376653)
        ·
          refine ⟨60065666494660690252641245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160175110652428507340376653 60065666494660690252641245)
          ·
            refine ⟨22524624935497758844740467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60065666494660690252641245 22524624935497758844740467)
            ·
              refine ⟨33786937403246638267110701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22524624935497758844740467 33786937403246638267110701)
              ·
                refine ⟨12670101526217489350166513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33786937403246638267110701 12670101526217489350166513)
                ·
                  refine ⟨9502576144663117012624885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12670101526217489350166513 9502576144663117012624885)
                  ·
                    refine ⟨890866513562167219933583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9502576144663117012624885 890866513562167219933583)
                    ·
                      rfl

theorem cell23_5204869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_5204869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204869 prefixEnd_5204869 := by exact prefixLift 5204869
  have htrace : WordTrace (prefixWord ++ tailWord_5204869) baseStart_5204869 baseEnd_5204869 := by
    simpa [prefixWord, tailWord_5204869, baseEnd_5204869] using wordTrace_append hprefix tailTrace_5204869
  have hstable : (prefixWord ++ tailWord_5204869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204869).length < 2 ^ (prefixWord ++ tailWord_5204869).sum := by decide
  have hdescent : baseEnd_5204869 < baseStart_5204869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204890 : List Nat := [3, 1, 1, 4, 3, 2, 2, 2, 5]
def baseStart_5204890 : Nat := 118140960795 + 5204890 * 2 ^ 59
def prefixEnd_5204890 : Nat := 4983230072969 + 3 ^ 40 * 5204890 * 2
def baseEnd_5204890 : Nat := 296956702642249564182017

theorem tailTrace_5204890 : CollatzResearch.WordTrace tailWord_5204890 prefixEnd_5204890 296956702642249564182017 := by
  unfold tailWord_5204890
  simp only [CollatzResearch.WordTrace]
  refine ⟨47459483528394982321555031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126558622742386619524146749 47459483528394982321555031)
  ·
    refine ⟨71189225292592473482332547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47459483528394982321555031 71189225292592473482332547)
    ·
      refine ⟨106783837938888710223498821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71189225292592473482332547 106783837938888710223498821)
      ·
        refine ⟨20021969613541633166906029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106783837938888710223498821 20021969613541633166906029)
        ·
          refine ⟨7508238605078112437589761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20021969613541633166906029 7508238605078112437589761)
          ·
            refine ⟨5631178953808584328192321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7508238605078112437589761 5631178953808584328192321)
            ·
              refine ⟨4223384215356438246144241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5631178953808584328192321 4223384215356438246144241)
              ·
                refine ⟨3167538161517328684608181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4223384215356438246144241 3167538161517328684608181)
                ·
                  refine ⟨296956702642249564182017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3167538161517328684608181 296956702642249564182017)
                  ·
                    rfl

theorem cell23_5204890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_5204890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204890 prefixEnd_5204890 := by exact prefixLift 5204890
  have htrace : WordTrace (prefixWord ++ tailWord_5204890) baseStart_5204890 baseEnd_5204890 := by
    simpa [prefixWord, tailWord_5204890, baseEnd_5204890] using wordTrace_append hprefix tailTrace_5204890
  have hstable : (prefixWord ++ tailWord_5204890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204890).length < 2 ^ (prefixWord ++ tailWord_5204890).sum := by decide
  have hdescent : baseEnd_5204890 < baseStart_5204890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204926 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_5204926 : Nat := 118140960795 + 5204926 * 2 ^ 59
def prefixEnd_5204926 : Nat := 4983230072969 + 3 ^ 40 * 5204926 * 2
def baseEnd_5204926 : Nat := 2672628809083807936787987

theorem tailTrace_5204926 : CollatzResearch.WordTrace tailWord_5204926 prefixEnd_5204926 2672628809083807936787987 := by
  unfold tailWord_5204926
  simp only [CollatzResearch.WordTrace]
  refine ⟨23729905892681188429316329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126559498094299671623020421 23729905892681188429316329)
  ·
    refine ⟨17797429419510891321987247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23729905892681188429316329 17797429419510891321987247)
    ·
      refine ⟨26696144129266336982980871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17797429419510891321987247 26696144129266336982980871)
      ·
        refine ⟨40044216193899505474471307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26696144129266336982980871 40044216193899505474471307)
        ·
          refine ⟨60066324290849258211706961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40044216193899505474471307 60066324290849258211706961)
          ·
            refine ⟨45049743218136943658780221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60066324290849258211706961 45049743218136943658780221)
            ·
              refine ⟨16893653706801353872042583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45049743218136943658780221 16893653706801353872042583)
              ·
                refine ⟨25340480560202030808063875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16893653706801353872042583 25340480560202030808063875)
                ·
                  refine ⟨38010720840303046212095813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25340480560202030808063875 38010720840303046212095813)
                  ·
                    refine ⟨7127010157556821164767965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38010720840303046212095813 7127010157556821164767965)
                    ·
                      refine ⟨2672628809083807936787987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7127010157556821164767965 2672628809083807936787987)
                      ·
                        rfl

theorem cell23_5204926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_5204926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204926 prefixEnd_5204926 := by exact prefixLift 5204926
  have htrace : WordTrace (prefixWord ++ tailWord_5204926) baseStart_5204926 baseEnd_5204926 := by
    simpa [prefixWord, tailWord_5204926, baseEnd_5204926] using wordTrace_append hprefix tailTrace_5204926
  have hstable : (prefixWord ++ tailWord_5204926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204926).length < 2 ^ (prefixWord ++ tailWord_5204926).sum := by decide
  have hdescent : baseEnd_5204926 < baseStart_5204926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204946 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 8]
def baseStart_5204946 : Nat := 118140960795 + 5204946 * 2 ^ 59
def prefixEnd_5204946 : Nat := 4983230072969 + 3 ^ 40 * 5204946 * 2
def baseEnd_5204946 : Nat := 296959897632988650948655

theorem tailTrace_5204946 : CollatzResearch.WordTrace tailWord_5204946 prefixEnd_5204946 296959897632988650948655 := by
  unfold tailWord_5204946
  simp only [CollatzResearch.WordTrace]
  refine ⟨47459994150344262712564673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126559984400918033900172461 47459994150344262712564673)
  ·
    refine ⟨35594995612758197034423505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47459994150344262712564673 35594995612758197034423505)
    ·
      refine ⟨26696246709568647775817629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35594995612758197034423505 26696246709568647775817629)
      ·
        refine ⟨10011092516088242915931611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26696246709568647775817629 10011092516088242915931611)
        ·
          refine ⟨15016638774132364373897417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10011092516088242915931611 15016638774132364373897417)
          ·
            refine ⟨11262479080599273280423063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15016638774132364373897417 11262479080599273280423063)
            ·
              refine ⟨16893718620898909920634595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11262479080599273280423063 16893718620898909920634595)
              ·
                refine ⟨25340577931348364880951893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16893718620898909920634595 25340577931348364880951893)
                ·
                  refine ⟨296959897632988650948655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25340577931348364880951893 296959897632988650948655)
                  ·
                    rfl

theorem cell23_5204946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_5204946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204946 prefixEnd_5204946 := by exact prefixLift 5204946
  have htrace : WordTrace (prefixWord ++ tailWord_5204946) baseStart_5204946 baseEnd_5204946 := by
    simpa [prefixWord, tailWord_5204946, baseEnd_5204946] using wordTrace_append hprefix tailTrace_5204946
  have hstable : (prefixWord ++ tailWord_5204946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204946).length < 2 ^ (prefixWord ++ tailWord_5204946).sum := by decide
  have hdescent : baseEnd_5204946 < baseStart_5204946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204950 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5204950 : Nat := 118140960795 + 5204950 * 2 ^ 59
def prefixEnd_5204950 : Nat := 4983230072969 + 3 ^ 40 * 5204950 * 2
def baseEnd_5204950 : Nat := 890880377539838614295959

theorem tailTrace_5204950 : CollatzResearch.WordTrace tailWord_5204950 prefixEnd_5204950 890880377539838614295959 := by
  unfold tailWord_5204950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11865007655835159970837769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126560081662241706355602869 11865007655835159970837769)
  ·
    refine ⟨8898755741876369978128327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11865007655835159970837769 8898755741876369978128327)
    ·
      refine ⟨13348133612814554967192491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8898755741876369978128327 13348133612814554967192491)
      ·
        refine ⟨20022200419221832450788737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13348133612814554967192491 20022200419221832450788737)
        ·
          refine ⟨15016650314416374338091553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20022200419221832450788737 15016650314416374338091553)
          ·
            refine ⟨11262487735812280753568665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15016650314416374338091553 11262487735812280753568665)
            ·
              refine ⟨8446865801859210565176499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11262487735812280753568665 8446865801859210565176499)
              ·
                refine ⟨12670298702788815847764749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8446865801859210565176499 12670298702788815847764749)
                ·
                  refine ⟨4751362013545805942911781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12670298702788815847764749 4751362013545805942911781)
                  ·
                    refine ⟨890880377539838614295959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751362013545805942911781 890880377539838614295959)
                    ·
                      rfl

theorem cell23_5204950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5204950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204950 prefixEnd_5204950 := by exact prefixLift 5204950
  have htrace : WordTrace (prefixWord ++ tailWord_5204950) baseStart_5204950 baseEnd_5204950 := by
    simpa [prefixWord, tailWord_5204950, baseEnd_5204950] using wordTrace_append hprefix tailTrace_5204950
  have hstable : (prefixWord ++ tailWord_5204950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204950).length < 2 ^ (prefixWord ++ tailWord_5204950).sum := by decide
  have hdescent : baseEnd_5204950 < baseStart_5204950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5204989 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_5204989 : Nat := 118140960795 + 5204989 * 2 ^ 59
def prefixEnd_5204989 : Nat := 4983230072969 + 3 ^ 40 * 5204989 * 2
def baseEnd_5204989 : Nat := 890887052788347063433399

theorem tailTrace_5204989 : CollatzResearch.WordTrace tailWord_5204989 prefixEnd_5204989 890887052788347063433399 := by
  unfold tailWord_5204989
  simp only [CollatzResearch.WordTrace]
  refine ⟨189841544940221269194074021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126561029960147512796049347 189841544940221269194074021)
  ·
    refine ⟨35595289676291487973888879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189841544940221269194074021 35595289676291487973888879)
    ·
      refine ⟨53392934514437231960833319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35595289676291487973888879 53392934514437231960833319)
      ·
        refine ⟨80089401771655847941249979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53392934514437231960833319 80089401771655847941249979)
        ·
          refine ⟨120134102657483771911874969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80089401771655847941249979 120134102657483771911874969)
          ·
            refine ⟨90100576993112828933906227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120134102657483771911874969 90100576993112828933906227)
            ·
              refine ⟨135150865489669243400859341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90100576993112828933906227 135150865489669243400859341)
              ·
                refine ⟨50681574558625966275322253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135150865489669243400859341 50681574558625966275322253)
                ·
                  refine ⟨19005590459484737353245845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50681574558625966275322253 19005590459484737353245845)
                  ·
                    refine ⟨890887052788347063433399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19005590459484737353245845 890887052788347063433399)
                    ·
                      rfl

theorem cell23_5204989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_5204989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5204989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5204989 prefixEnd_5204989 := by exact prefixLift 5204989
  have htrace : WordTrace (prefixWord ++ tailWord_5204989) baseStart_5204989 baseEnd_5204989 := by
    simpa [prefixWord, tailWord_5204989, baseEnd_5204989] using wordTrace_append hprefix tailTrace_5204989
  have hstable : (prefixWord ++ tailWord_5204989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5204989).length < 2 ^ (prefixWord ++ tailWord_5204989).sum := by decide
  have hdescent : baseEnd_5204989 < baseStart_5204989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5204989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205016 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5205016 : Nat := 118140960795 + 5205016 * 2 ^ 59
def prefixEnd_5205016 : Nat := 4983230072969 + 3 ^ 40 * 5205016 * 2
def baseEnd_5205016 : Nat := 2672675022342712584662573

theorem tailTrace_5205016 : CollatzResearch.WordTrace tailWord_5205016 prefixEnd_5205016 2672675022342712584662573 := by
  unfold tailWord_5205016
  simp only [CollatzResearch.WordTrace]
  refine ⟨94921264855561726402653451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126561686474082301870204601 94921264855561726402653451)
  ·
    refine ⟨142381897283342589603980177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94921264855561726402653451 142381897283342589603980177)
    ·
      refine ⟨106786422962506942202985133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142381897283342589603980177 106786422962506942202985133)
      ·
        refine ⟨40044908610940103326119425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106786422962506942202985133 40044908610940103326119425)
        ·
          refine ⟨30033681458205077494589569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40044908610940103326119425 30033681458205077494589569)
          ·
            refine ⟨22525261093653808120942177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30033681458205077494589569 22525261093653808120942177)
            ·
              refine ⟨16893945820240356090706633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22525261093653808120942177 16893945820240356090706633)
              ·
                refine ⟨12670459365180267068029975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16893945820240356090706633 12670459365180267068029975)
                ·
                  refine ⟨19005689047770400602044963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12670459365180267068029975 19005689047770400602044963)
                  ·
                    refine ⟨28508533571655600903067445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19005689047770400602044963 28508533571655600903067445)
                    ·
                      refine ⟨2672675022342712584662573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28508533571655600903067445 2672675022342712584662573)
                      ·
                        rfl

theorem cell23_5205016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5205016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205016 prefixEnd_5205016 := by exact prefixLift 5205016
  have htrace : WordTrace (prefixWord ++ tailWord_5205016) baseStart_5205016 baseEnd_5205016 := by
    simpa [prefixWord, tailWord_5205016, baseEnd_5205016] using wordTrace_append hprefix tailTrace_5205016
  have hstable : (prefixWord ++ tailWord_5205016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205016).length < 2 ^ (prefixWord ++ tailWord_5205016).sum := by decide
  have hdescent : baseEnd_5205016 < baseStart_5205016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205023 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 2, 4]
def baseStart_5205023 : Nat := 118140960795 + 5205023 * 2 ^ 59
def prefixEnd_5205023 : Nat := 4983230072969 + 3 ^ 40 * 5205023 * 2
def baseEnd_5205023 : Nat := 890892872235764685758347

theorem tailTrace_5205023 : CollatzResearch.WordTrace tailWord_5205023 prefixEnd_5205023 890892872235764685758347 := by
  unfold tailWord_5205023
  simp only [CollatzResearch.WordTrace]
  refine ⟨189842785022098093000811723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126561856681398728667207815 189842785022098093000811723)
  ·
    refine ⟨284764177533147139501217585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189842785022098093000811723 284764177533147139501217585)
    ·
      refine ⟨213573133149860354625913189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284764177533147139501217585 213573133149860354625913189)
      ·
        refine ⟨40044962465598816492358723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213573133149860354625913189 40044962465598816492358723)
        ·
          refine ⟨60067443698398224738538085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40044962465598816492358723 60067443698398224738538085)
          ·
            refine ⟨11262645693449667138475891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60067443698398224738538085 11262645693449667138475891)
            ·
              refine ⟨16893968540174500707713837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11262645693449667138475891 16893968540174500707713837)
              ·
                refine ⟨6335238202565437765392689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16893968540174500707713837 6335238202565437765392689)
                ·
                  refine ⟨4751428651924078324044517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335238202565437765392689 4751428651924078324044517)
                  ·
                    refine ⟨890892872235764685758347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751428651924078324044517 890892872235764685758347)
                    ·
                      rfl

theorem cell23_5205023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_5205023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205023 prefixEnd_5205023 := by exact prefixLift 5205023
  have htrace : WordTrace (prefixWord ++ tailWord_5205023) baseStart_5205023 baseEnd_5205023 := by
    simpa [prefixWord, tailWord_5205023, baseEnd_5205023] using wordTrace_append hprefix tailTrace_5205023
  have hstable : (prefixWord ++ tailWord_5205023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205023).length < 2 ^ (prefixWord ++ tailWord_5205023).sum := by decide
  have hdescent : baseEnd_5205023 < baseStart_5205023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205026 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_5205026 : Nat := 118140960795 + 5205026 * 2 ^ 59
def prefixEnd_5205026 : Nat := 4983230072969 + 3 ^ 40 * 5205026 * 2
def baseEnd_5205026 : Nat := 2672680157149257545537527

theorem tailTrace_5205026 : CollatzResearch.WordTrace tailWord_5205026 prefixEnd_5205026 2672680157149257545537527 := by
  unfold tailWord_5205026
  simp only [CollatzResearch.WordTrace]
  refine ⟨47460723610271806128292733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126561929627391483008780621 47460723610271806128292733)
  ·
    refine ⟨17797771353851927298109775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47460723610271806128292733 17797771353851927298109775)
    ·
      refine ⟨26696657030777890947164663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17797771353851927298109775 26696657030777890947164663)
      ·
        refine ⟨40044985546166836420746995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26696657030777890947164663 40044985546166836420746995)
        ·
          refine ⟨60067478319250254631120493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40044985546166836420746995 60067478319250254631120493)
          ·
            refine ⟨22525304369718845486670185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60067478319250254631120493 22525304369718845486670185)
            ·
              refine ⟨16893978277289134115002639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22525304369718845486670185 16893978277289134115002639)
              ·
                refine ⟨25340967415933701172503959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16893978277289134115002639 25340967415933701172503959)
                ·
                  refine ⟨38011451123900551758755939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25340967415933701172503959 38011451123900551758755939)
                  ·
                    refine ⟨57017176685850827638133909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38011451123900551758755939 57017176685850827638133909)
                    ·
                      refine ⟨2672680157149257545537527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57017176685850827638133909 2672680157149257545537527)
                      ·
                        rfl

theorem cell23_5205026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_5205026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205026 prefixEnd_5205026 := by exact prefixLift 5205026
  have htrace : WordTrace (prefixWord ++ tailWord_5205026) baseStart_5205026 baseEnd_5205026 := by
    simpa [prefixWord, tailWord_5205026, baseEnd_5205026] using wordTrace_append hprefix tailTrace_5205026
  have hstable : (prefixWord ++ tailWord_5205026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205026).length < 2 ^ (prefixWord ++ tailWord_5205026).sum := by decide
  have hdescent : baseEnd_5205026 < baseStart_5205026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205073 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 3, 3, 2]
def baseStart_5205073 : Nat := 118140960795 + 5205073 * 2 ^ 59
def prefixEnd_5205073 : Nat := 4983230072969 + 3 ^ 40 * 5205073 * 2
def baseEnd_5205073 : Nat := 2672704290740018861649811

theorem tailTrace_5205073 : CollatzResearch.WordTrace tailWord_5205073 prefixEnd_5205073 2672704290740018861649811 := by
  unfold tailWord_5205073
  simp only [CollatzResearch.WordTrace]
  refine ⟨189844608671916951540131873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126563072447944634360087915 189844608671916951540131873)
  ·
    refine ⟨142383456503937713655098905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189844608671916951540131873 142383456503937713655098905)
    ·
      refine ⟨106787592377953285241324179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142383456503937713655098905 106787592377953285241324179)
      ·
        refine ⟨160181388566929927861986269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106787592377953285241324179 160181388566929927861986269)
        ·
          refine ⟨60068020712598722948244851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160181388566929927861986269 60068020712598722948244851)
          ·
            refine ⟨90102031068898084422367277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60068020712598722948244851 90102031068898084422367277)
            ·
              refine ⟨33788261650836781658387729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90102031068898084422367277 33788261650836781658387729)
              ·
                refine ⟨25341196238127586243790797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33788261650836781658387729 25341196238127586243790797)
                ·
                  refine ⟨9502948589297844841421549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25341196238127586243790797 9502948589297844841421549)
                  ·
                    refine ⟨3563605720986691815533081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9502948589297844841421549 3563605720986691815533081)
                    ·
                      refine ⟨2672704290740018861649811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563605720986691815533081 2672704290740018861649811)
                      ·
                        rfl

theorem cell23_5205073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_5205073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205073 prefixEnd_5205073 := by exact prefixLift 5205073
  have htrace : WordTrace (prefixWord ++ tailWord_5205073) baseStart_5205073 baseEnd_5205073 := by
    simpa [prefixWord, tailWord_5205073, baseEnd_5205073] using wordTrace_append hprefix tailTrace_5205073
  have hstable : (prefixWord ++ tailWord_5205073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205073).length < 2 ^ (prefixWord ++ tailWord_5205073).sum := by decide
  have hdescent : baseEnd_5205073 < baseStart_5205073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205103 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 1, 4, 2]
def baseStart_5205103 : Nat := 118140960795 + 5205103 * 2 ^ 59
def prefixEnd_5205103 : Nat := 4983230072969 + 3 ^ 40 * 5205103 * 2
def baseEnd_5205103 : Nat := 2672719695159653744274673

theorem tailTrace_5205103 : CollatzResearch.WordTrace tailWord_5205103 prefixEnd_5205103 2672719695159653744274673 := by
  unfold tailWord_5205103
  simp only [CollatzResearch.WordTrace]
  refine ⟨189845702861808266663723963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126563801907872177775815975 189845702861808266663723963)
  ·
    refine ⟨284768554292712399995585945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189845702861808266663723963 284768554292712399995585945)
    ·
      refine ⟨213576415719534299996689459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284768554292712399995585945 213576415719534299996689459)
      ·
        refine ⟨320364623579301449995034189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213576415719534299996689459 320364623579301449995034189)
        ·
          refine ⟨120136733842238043748137821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320364623579301449995034189 120136733842238043748137821)
          ·
            refine ⟨45051275190839266405551683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120136733842238043748137821 45051275190839266405551683)
            ·
              refine ⟨67576912786258899608327525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45051275190839266405551683 67576912786258899608327525)
              ·
                refine ⟨12670671147423543676561411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67576912786258899608327525 12670671147423543676561411)
                ·
                  refine ⟨19006006721135315514842117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12670671147423543676561411 19006006721135315514842117)
                  ·
                    refine ⟨3563626260212871659032897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19006006721135315514842117 3563626260212871659032897)
                    ·
                      refine ⟨2672719695159653744274673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563626260212871659032897 2672719695159653744274673)
                      ·
                        rfl

theorem cell23_5205103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4, 2].length) (baseStart_5205103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205103 prefixEnd_5205103 := by exact prefixLift 5205103
  have htrace : WordTrace (prefixWord ++ tailWord_5205103) baseStart_5205103 baseEnd_5205103 := by
    simpa [prefixWord, tailWord_5205103, baseEnd_5205103] using wordTrace_append hprefix tailTrace_5205103
  have hstable : (prefixWord ++ tailWord_5205103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205103).length < 2 ^ (prefixWord ++ tailWord_5205103).sum := by decide
  have hdescent : baseEnd_5205103 < baseStart_5205103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205106 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5205106 : Nat := 118140960795 + 5205106 * 2 ^ 59
def prefixEnd_5205106 : Nat := 4983230072969 + 3 ^ 40 * 5205106 * 2
def baseEnd_5205106 : Nat := 2672721235601617232537159

theorem tailTrace_5205106 : CollatzResearch.WordTrace tailWord_5205106 prefixEnd_5205106 2672721235601617232537159 := by
  unfold tailWord_5205106
  simp only [CollatzResearch.WordTrace]
  refine ⟨47461453070199349544020793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126563874853864932117388781 47461453070199349544020793)
  ·
    refine ⟨35596089802649512158015595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47461453070199349544020793 35596089802649512158015595)
    ·
      refine ⟨53394134703974268237023393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35596089802649512158015595 53394134703974268237023393)
      ·
        refine ⟨40045601027980701177767545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53394134703974268237023393 40045601027980701177767545)
        ·
          refine ⟨30034200770985525883325659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40045601027980701177767545 30034200770985525883325659)
          ·
            refine ⟨45051301156478288824988489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30034200770985525883325659 45051301156478288824988489)
            ·
              refine ⟨33788475867358716618741367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45051301156478288824988489 33788475867358716618741367)
              ·
                refine ⟨50682713801038074928112051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33788475867358716618741367 50682713801038074928112051)
                ·
                  refine ⟨76024070701557112392168077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50682713801038074928112051 76024070701557112392168077)
                  ·
                    refine ⟨28509026513083917147063029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76024070701557112392168077 28509026513083917147063029)
                    ·
                      refine ⟨2672721235601617232537159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28509026513083917147063029 2672721235601617232537159)
                      ·
                        rfl

theorem cell23_5205106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5205106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205106 prefixEnd_5205106 := by exact prefixLift 5205106
  have htrace : WordTrace (prefixWord ++ tailWord_5205106) baseStart_5205106 baseEnd_5205106 := by
    simpa [prefixWord, tailWord_5205106, baseEnd_5205106] using wordTrace_append hprefix tailTrace_5205106
  have hstable : (prefixWord ++ tailWord_5205106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205106).length < 2 ^ (prefixWord ++ tailWord_5205106).sum := by decide
  have hdescent : baseEnd_5205106 < baseStart_5205106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205116 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_5205116 : Nat := 118140960795 + 5205116 * 2 ^ 59
def prefixEnd_5205116 : Nat := 4983230072969 + 3 ^ 40 * 5205116 * 2
def baseEnd_5205116 : Nat := 2672726370408162193412113

theorem tailTrace_5205116 : CollatzResearch.WordTrace tailWord_5205116 prefixEnd_5205116 2672726370408162193412113 := by
  unfold tailWord_5205116
  simp only [CollatzResearch.WordTrace]
  refine ⟨94923088505380584941973601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126564118007174113255964801 94923088505380584941973601)
  ·
    refine ⟨71192316379035438706480201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94923088505380584941973601 71192316379035438706480201)
    ·
      refine ⟨53394237284276579029860151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71192316379035438706480201 53394237284276579029860151)
      ·
        refine ⟨80091355926414868544790227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53394237284276579029860151 80091355926414868544790227)
        ·
          refine ⟨120137033889622302817185341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80091355926414868544790227 120137033889622302817185341)
          ·
            refine ⟨45051387708608363556444503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120137033889622302817185341 45051387708608363556444503)
            ·
              refine ⟨67577081562912545334666755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45051387708608363556444503 67577081562912545334666755)
              ·
                refine ⟨101365622344368818002000133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67577081562912545334666755 101365622344368818002000133)
                ·
                  refine ⟨19006054189569153375375025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101365622344368818002000133 19006054189569153375375025)
                  ·
                    refine ⟨14254540642176865031531269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19006054189569153375375025 14254540642176865031531269)
                    ·
                      refine ⟨2672726370408162193412113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14254540642176865031531269 2672726370408162193412113)
                      ·
                        rfl

theorem cell23_5205116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_5205116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205116 prefixEnd_5205116 := by exact prefixLift 5205116
  have htrace : WordTrace (prefixWord ++ tailWord_5205116) baseStart_5205116 baseEnd_5205116 := by
    simpa [prefixWord, tailWord_5205116, baseEnd_5205116] using wordTrace_append hprefix tailTrace_5205116
  have hstable : (prefixWord ++ tailWord_5205116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205116).length < 2 ^ (prefixWord ++ tailWord_5205116).sum := by decide
  have hdescent : baseEnd_5205116 < baseStart_5205116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205136 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3]
def baseStart_5205136 : Nat := 118140960795 + 5205136 * 2 ^ 59
def prefixEnd_5205136 : Nat := 4983230072969 + 3 ^ 40 * 5205136 * 2
def baseEnd_5205136 : Nat := 2672736640021252115162021

theorem tailTrace_5205136 : CollatzResearch.WordTrace tailWord_5205136 prefixEnd_5205136 2672736640021252115162021 := by
  unfold tailWord_5205136
  simp only [CollatzResearch.WordTrace]
  refine ⟨94923453235344356649837631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126564604313792475533116841 94923453235344356649837631)
  ·
    refine ⟨142385179853016534974756447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94923453235344356649837631 142385179853016534974756447)
    ·
      refine ⟨213577769779524802462134671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142385179853016534974756447 213577769779524802462134671)
      ·
        refine ⟨320366654669287203693202007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213577769779524802462134671 320366654669287203693202007)
        ·
          refine ⟨480549982003930805539803011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320366654669287203693202007 480549982003930805539803011)
          ·
            refine ⟨720824973005896208309704517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480549982003930805539803011 720824973005896208309704517)
            ·
              refine ⟨135154682438605539058069597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 720824973005896208309704517 135154682438605539058069597)
              ·
                refine ⟨50683005914477077146776099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135154682438605539058069597 50683005914477077146776099)
                ·
                  refine ⟨76024508871715615720164149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50683005914477077146776099 76024508871715615720164149)
                  ·
                    refine ⟨7127297706723338973765389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76024508871715615720164149 7127297706723338973765389)
                    ·
                      refine ⟨2672736640021252115162021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7127297706723338973765389 2672736640021252115162021)
                      ·
                        rfl

theorem cell23_5205136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_5205136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205136 prefixEnd_5205136 := by exact prefixLift 5205136
  have htrace : WordTrace (prefixWord ++ tailWord_5205136) baseStart_5205136 baseEnd_5205136 := by
    simpa [prefixWord, tailWord_5205136, baseEnd_5205136] using wordTrace_append hprefix tailTrace_5205136
  have hstable : (prefixWord ++ tailWord_5205136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205136).length < 2 ^ (prefixWord ++ tailWord_5205136).sum := by decide
  have hdescent : baseEnd_5205136 < baseStart_5205136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205176 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_5205176 : Nat := 118140960795 + 5205176 * 2 ^ 59
def prefixEnd_5205176 : Nat := 4983230072969 + 3 ^ 40 * 5205176 * 2
def baseEnd_5205176 : Nat := 2672757179247431958661837

theorem tailTrace_5205176 : CollatzResearch.WordTrace tailWord_5205176 prefixEnd_5205176 2672757179247431958661837 := by
  unfold tailWord_5205176
  simp only [CollatzResearch.WordTrace]
  refine ⟨94924182695271900065565691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126565576927029200087420921 94924182695271900065565691)
  ·
    refine ⟨142386274042907850098348537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94924182695271900065565691 142386274042907850098348537)
    ·
      refine ⟨106789705532180887573761403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142386274042907850098348537 106789705532180887573761403)
      ·
        refine ⟨160184558298271331360642105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106789705532180887573761403 160184558298271331360642105)
        ·
          refine ⟨120138418723703498520481579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160184558298271331360642105 120138418723703498520481579)
          ·
            refine ⟨180207628085555247780722369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120138418723703498520481579 180207628085555247780722369)
            ·
              refine ⟨135155721064166435835541777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180207628085555247780722369 135155721064166435835541777)
              ·
                refine ⟨101366790798124826876656333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135155721064166435835541777 101366790798124826876656333)
                ·
                  refine ⟨38012546549296810078746125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101366790798124826876656333 38012546549296810078746125)
                  ·
                    refine ⟨14254704955986303779529797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38012546549296810078746125 14254704955986303779529797)
                    ·
                      refine ⟨2672757179247431958661837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14254704955986303779529797 2672757179247431958661837)
                      ·
                        rfl

theorem cell23_5205176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_5205176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205176 prefixEnd_5205176 := by exact prefixLift 5205176
  have htrace : WordTrace (prefixWord ++ tailWord_5205176) baseStart_5205176 baseEnd_5205176 := by
    simpa [prefixWord, tailWord_5205176, baseEnd_5205176] using wordTrace_append hprefix tailTrace_5205176
  have hstable : (prefixWord ++ tailWord_5205176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205176).length < 2 ^ (prefixWord ++ tailWord_5205176).sum := by decide
  have hdescent : baseEnd_5205176 < baseStart_5205176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205188 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_5205188 : Nat := 118140960795 + 5205188 * 2 ^ 59
def prefixEnd_5205188 : Nat := 4983230072969 + 3 ^ 40 * 5205188 * 2
def baseEnd_5205188 : Nat := 2672763341015285911711783

theorem tailTrace_5205188 : CollatzResearch.WordTrace tailWord_5205188 prefixEnd_5205188 2672763341015285911711783 := by
  unfold tailWord_5205188
  simp only [CollatzResearch.WordTrace]
  refine ⟨94924401533250163090284109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126565868711000217453712145 94924401533250163090284109)
  ·
    refine ⟨35596650574968811158856541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94924401533250163090284109 35596650574968811158856541)
    ·
      refine ⟨13348743965613304184571203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35596650574968811158856541 13348743965613304184571203)
      ·
        refine ⟨20023115948419956276856805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13348743965613304184571203 20023115948419956276856805)
        ·
          refine ⟨3754334240328741801910651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20023115948419956276856805 3754334240328741801910651)
          ·
            refine ⟨5631501360493112702865977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754334240328741801910651 5631501360493112702865977)
            ·
              refine ⟨4223626020369834527149483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5631501360493112702865977 4223626020369834527149483)
              ·
                refine ⟨6335439030554751790724225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223626020369834527149483 6335439030554751790724225)
                ·
                  refine ⟨4751579272916063843043169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335439030554751790724225 4751579272916063843043169)
                  ·
                    refine ⟨3563684454687047882282377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4751579272916063843043169 3563684454687047882282377)
                    ·
                      refine ⟨2672763341015285911711783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563684454687047882282377 2672763341015285911711783)
                      ·
                        rfl

theorem cell23_5205188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_5205188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205188 prefixEnd_5205188 := by exact prefixLift 5205188
  have htrace : WordTrace (prefixWord ++ tailWord_5205188) baseStart_5205188 baseEnd_5205188 := by
    simpa [prefixWord, tailWord_5205188, baseEnd_5205188] using wordTrace_append hprefix tailTrace_5205188
  have hstable : (prefixWord ++ tailWord_5205188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205188).length < 2 ^ (prefixWord ++ tailWord_5205188).sum := by decide
  have hdescent : baseEnd_5205188 < baseStart_5205188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205193 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 6, 4, 2]
def baseStart_5205193 : Nat := 118140960795 + 5205193 * 2 ^ 59
def prefixEnd_5205193 : Nat := 4983230072969 + 3 ^ 40 * 5205193 * 2
def baseEnd_5205193 : Nat := 2672765908418558392149259

theorem tailTrace_5205193 : CollatzResearch.WordTrace tailWord_5205193 prefixEnd_5205193 2672765908418558392149259 := by
  unfold tailWord_5205193
  simp only [CollatzResearch.WordTrace]
  refine ⟨189848985431482212034500233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126565990287654808023000155 189848985431482212034500233)
  ·
    refine ⟨142386739073611659025875175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189848985431482212034500233 142386739073611659025875175)
    ·
      refine ⟨213580108610417488538812763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142386739073611659025875175 213580108610417488538812763)
      ·
        refine ⟨320370162915626232808219145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213580108610417488538812763 320370162915626232808219145)
        ·
          refine ⟨240277622186719674606164359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320370162915626232808219145 240277622186719674606164359)
          ·
            refine ⟨360416433280079511909246539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240277622186719674606164359 360416433280079511909246539)
            ·
              refine ⟨540624649920119267863869809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360416433280079511909246539 540624649920119267863869809)
              ·
                refine ⟨405468487440089450897902357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540624649920119267863869809 405468487440089450897902357)
                ·
                  refine ⟨19006335348754193010839173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 405468487440089450897902357 19006335348754193010839173)
                  ·
                    refine ⟨3563687877891411189532345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19006335348754193010839173 3563687877891411189532345)
                    ·
                      refine ⟨2672765908418558392149259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563687877891411189532345 2672765908418558392149259)
                      ·
                        rfl

theorem cell23_5205193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 4, 2].length) (baseStart_5205193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205193 prefixEnd_5205193 := by exact prefixLift 5205193
  have htrace : WordTrace (prefixWord ++ tailWord_5205193) baseStart_5205193 baseEnd_5205193 := by
    simpa [prefixWord, tailWord_5205193, baseEnd_5205193] using wordTrace_append hprefix tailTrace_5205193
  have hstable : (prefixWord ++ tailWord_5205193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205193).length < 2 ^ (prefixWord ++ tailWord_5205193).sum := by decide
  have hdescent : baseEnd_5205193 < baseStart_5205193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205230 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_5205230 : Nat := 118140960795 + 5205230 * 2 ^ 59
def prefixEnd_5205230 : Nat := 4983230072969 + 3 ^ 40 * 5205230 * 2
def baseEnd_5205230 : Nat := 2672784907202774747386589

theorem tailTrace_5205230 : CollatzResearch.WordTrace tailWord_5205230 prefixEnd_5205230 2672784907202774747386589 := by
  unfold tailWord_5205230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23731291866543520919199643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126566889954898778235731429 23731291866543520919199643)
  ·
    refine ⟨35596937799815281378799465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23731291866543520919199643 35596937799815281378799465)
    ·
      refine ⟨26697703349861461034099599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35596937799815281378799465 26697703349861461034099599)
      ·
        refine ⟨40046555024792191551149399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26697703349861461034099599 40046555024792191551149399)
        ·
          refine ⟨60069832537188287326724099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40046555024792191551149399 60069832537188287326724099)
          ·
            refine ⟨90104748805782430990086149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60069832537188287326724099 90104748805782430990086149)
            ·
              refine ⟨16894640401084205810641153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90104748805782430990086149 16894640401084205810641153)
              ·
                refine ⟨12670980300813154357980865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16894640401084205810641153 12670980300813154357980865)
                ·
                  refine ⟨9503235225609865768485649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12670980300813154357980865 9503235225609865768485649)
                  ·
                    refine ⟨7127426419207399326364237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9503235225609865768485649 7127426419207399326364237)
                    ·
                      refine ⟨2672784907202774747386589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7127426419207399326364237 2672784907202774747386589)
                      ·
                        rfl

theorem cell23_5205230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_5205230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205230 prefixEnd_5205230 := by exact prefixLift 5205230
  have htrace : WordTrace (prefixWord ++ tailWord_5205230) baseStart_5205230 baseEnd_5205230 := by
    simpa [prefixWord, tailWord_5205230, baseEnd_5205230] using wordTrace_append hprefix tailTrace_5205230
  have hstable : (prefixWord ++ tailWord_5205230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205230).length < 2 ^ (prefixWord ++ tailWord_5205230).sum := by decide
  have hdescent : baseEnd_5205230 < baseStart_5205230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205260 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_5205260 : Nat := 118140960795 + 5205260 * 2 ^ 59
def prefixEnd_5205260 : Nat := 4983230072969 + 3 ^ 40 * 5205260 * 2
def baseEnd_5205260 : Nat := 2672800311622409630011451

theorem tailTrace_5205260 : CollatzResearch.WordTrace tailWord_5205260 prefixEnd_5205260 2672800311622409630011451 := by
  unfold tailWord_5205260
  simp only [CollatzResearch.WordTrace]
  refine ⟨94925714561119741238594617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126567619414826321651459489 94925714561119741238594617)
  ·
    refine ⟨71194285920839805928945963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94925714561119741238594617 71194285920839805928945963)
    ·
      refine ⟨106791428881259708893418945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71194285920839805928945963 106791428881259708893418945)
      ·
        refine ⟨80093571660944781670064209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106791428881259708893418945 80093571660944781670064209)
        ·
          refine ⟨60070178745708586252548157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80093571660944781670064209 60070178745708586252548157)
          ·
            refine ⟨22526317029640719844705559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60070178745708586252548157 22526317029640719844705559)
            ·
              refine ⟨33789475544461079767058339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22526317029640719844705559 33789475544461079767058339)
              ·
                refine ⟨50684213316691619650587509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33789475544461079767058339 50684213316691619650587509)
                ·
                  refine ⟨4751644998439839342242579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50684213316691619650587509 4751644998439839342242579)
                  ·
                    refine ⟨7127467497659759013363869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751644998439839342242579 7127467497659759013363869)
                    ·
                      refine ⟨2672800311622409630011451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7127467497659759013363869 2672800311622409630011451)
                      ·
                        rfl

theorem cell23_5205260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_5205260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205260 prefixEnd_5205260 := by exact prefixLift 5205260
  have htrace : WordTrace (prefixWord ++ tailWord_5205260) baseStart_5205260 baseEnd_5205260 := by
    simpa [prefixWord, tailWord_5205260, baseEnd_5205260] using wordTrace_append hprefix tailTrace_5205260
  have hstable : (prefixWord ++ tailWord_5205260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205260).length < 2 ^ (prefixWord ++ tailWord_5205260).sum := by decide
  have hdescent : baseEnd_5205260 < baseStart_5205260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205351 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_5205351 : Nat := 118140960795 + 5205351 * 2 ^ 59
def prefixEnd_5205351 : Nat := 4983230072969 + 3 ^ 40 * 5205351 * 2
def baseEnd_5205351 : Nat := 2672847038361968773973533

theorem tailTrace_5205351 : CollatzResearch.WordTrace tailWord_5205351 prefixEnd_5205351 2672847038361968773973533 := by
  unfold tailWord_5205351
  simp only [CollatzResearch.WordTrace]
  refine ⟨189854748164909805018751907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126569832109939870012501271 189854748164909805018751907)
  ·
    refine ⟨284782122247364707528127861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189854748164909805018751907 284782122247364707528127861)
    ·
      refine ⟨26698323960690441330761987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 284782122247364707528127861 26698323960690441330761987)
      ·
        refine ⟨40047485941035661996142981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26698323960690441330761987 40047485941035661996142981)
        ·
          refine ⟨7508903613944186624276809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40047485941035661996142981 7508903613944186624276809)
          ·
            refine ⟨5631677710458139968207607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7508903613944186624276809 5631677710458139968207607)
            ·
              refine ⟨8447516565687209952311411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631677710458139968207607 8447516565687209952311411)
              ·
                refine ⟨12671274848530814928467117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8447516565687209952311411 12671274848530814928467117)
                ·
                  refine ⟨4751728068199055598175169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12671274848530814928467117 4751728068199055598175169)
                  ·
                    refine ⟨3563796051149291698631377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4751728068199055598175169 3563796051149291698631377)
                    ·
                      refine ⟨2672847038361968773973533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563796051149291698631377 2672847038361968773973533)
                      ·
                        rfl

theorem cell23_5205351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_5205351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205351 prefixEnd_5205351 := by exact prefixLift 5205351
  have htrace : WordTrace (prefixWord ++ tailWord_5205351) baseStart_5205351 baseEnd_5205351 := by
    simpa [prefixWord, tailWord_5205351, baseEnd_5205351] using wordTrace_append hprefix tailTrace_5205351
  have hstable : (prefixWord ++ tailWord_5205351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205351).length < 2 ^ (prefixWord ++ tailWord_5205351).sum := by decide
  have hdescent : baseEnd_5205351 < baseStart_5205351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205367 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_5205367 : Nat := 118140960795 + 5205367 * 2 ^ 59
def prefixEnd_5205367 : Nat := 4983230072969 + 3 ^ 40 * 5205367 * 2
def baseEnd_5205367 : Nat := 2672855254052440711373459

theorem tailTrace_5205367 : CollatzResearch.WordTrace tailWord_5205367 prefixEnd_5205367 2672855254052440711373459 := by
  unfold tailWord_5205367
  simp only [CollatzResearch.WordTrace]
  refine ⟨189855331732851839751334355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126570221155234559834222903 189855331732851839751334355)
  ·
    refine ⟨284782997599277759627001533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189855331732851839751334355 284782997599277759627001533)
    ·
      refine ⟨106793624099729159860125575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284782997599277759627001533 106793624099729159860125575)
      ·
        refine ⟨160190436149593739790188363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106793624099729159860125575 160190436149593739790188363)
        ·
          refine ⟨240285654224390609685282545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160190436149593739790188363 240285654224390609685282545)
          ·
            refine ⟨180214240668292957263961909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240285654224390609685282545 180214240668292957263961909)
            ·
              refine ⟨16895085062652464743496429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180214240668292957263961909 16895085062652464743496429)
              ·
                refine ⟨6335656898494674278811161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16895085062652464743496429 6335656898494674278811161)
                ·
                  refine ⟨4751742673871005709108371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335656898494674278811161 4751742673871005709108371)
                  ·
                    refine ⟨7127614010806508563662557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751742673871005709108371 7127614010806508563662557)
                    ·
                      refine ⟨2672855254052440711373459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7127614010806508563662557 2672855254052440711373459)
                      ·
                        rfl

theorem cell23_5205367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_5205367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205367 prefixEnd_5205367 := by exact prefixLift 5205367
  have htrace : WordTrace (prefixWord ++ tailWord_5205367) baseStart_5205367 baseEnd_5205367 := by
    simpa [prefixWord, tailWord_5205367, baseEnd_5205367] using wordTrace_append hprefix tailTrace_5205367
  have hstable : (prefixWord ++ tailWord_5205367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205367).length < 2 ^ (prefixWord ++ tailWord_5205367).sum := by decide
  have hdescent : baseEnd_5205367 < baseStart_5205367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205447 : List Nat := [1, 1, 4, 1, 1, 3, 4, 3, 5]
def baseStart_5205447 : Nat := 118140960795 + 5205447 * 2 ^ 59
def prefixEnd_5205447 : Nat := 4983230072969 + 3 ^ 40 * 5205447 * 2
def baseEnd_5205447 : Nat := 296988481389422266485899

theorem tailTrace_5205447 : CollatzResearch.WordTrace tailWord_5205447 prefixEnd_5205447 296988481389422266485899 := by
  unfold tailWord_5205447
  simp only [CollatzResearch.WordTrace]
  refine ⟨189858249572562013414246595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126572166381708008942831063 189858249572562013414246595)
  ·
    refine ⟨284787374358843020121369893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189858249572562013414246595 284787374358843020121369893)
    ·
      refine ⟨53397632692283066272756855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284787374358843020121369893 53397632692283066272756855)
      ·
        refine ⟨80096449038424599409135283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53397632692283066272756855 80096449038424599409135283)
        ·
          refine ⟨120144673557636899113702925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80096449038424599409135283 120144673557636899113702925)
          ·
            refine ⟨45054252584113837167638597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120144673557636899113702925 45054252584113837167638597)
            ·
              refine ⟨8447672359521344468932237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45054252584113837167638597 8447672359521344468932237)
              ·
                refine ⟨3167877134820504175849589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8447672359521344468932237 3167877134820504175849589)
                ·
                  refine ⟨296988481389422266485899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3167877134820504175849589 296988481389422266485899)
                  ·
                    rfl

theorem cell23_5205447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 5].length) (baseStart_5205447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205447 prefixEnd_5205447 := by exact prefixLift 5205447
  have htrace : WordTrace (prefixWord ++ tailWord_5205447) baseStart_5205447 baseEnd_5205447 := by
    simpa [prefixWord, tailWord_5205447, baseEnd_5205447] using wordTrace_append hprefix tailTrace_5205447
  have hstable : (prefixWord ++ tailWord_5205447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205447).length < 2 ^ (prefixWord ++ tailWord_5205447).sum := by decide
  have hdescent : baseEnd_5205447 < baseStart_5205447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205480 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5205480 : Nat := 118140960795 + 5205480 * 2 ^ 59
def prefixEnd_5205480 : Nat := 4983230072969 + 3 ^ 40 * 5205480 * 2
def baseEnd_5205480 : Nat := 2672913277366398769260439

theorem tailTrace_5205480 : CollatzResearch.WordTrace tailWord_5205480 prefixEnd_5205480 2672913277366398769260439 := by
  unfold tailWord_5205480
  simp only [CollatzResearch.WordTrace]
  refine ⟨94929726590721230025098947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126572968787628306700131929 94929726590721230025098947)
  ·
    refine ⟨142394589886081845037648421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94929726590721230025098947 142394589886081845037648421)
    ·
      refine ⟨26698985603640345944559079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142394589886081845037648421 26698985603640345944559079)
      ·
        refine ⟨40048478405460518916838619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26698985603640345944559079 40048478405460518916838619)
        ·
          refine ⟨60072717608190778375257929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40048478405460518916838619 60072717608190778375257929)
          ·
            refine ⟨45054538206143083781443447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60072717608190778375257929 45054538206143083781443447)
            ·
              refine ⟨67581807309214625672165171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45054538206143083781443447 67581807309214625672165171)
              ·
                refine ⟨101372710963821938508247757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67581807309214625672165171 101372710963821938508247757)
                ·
                  refine ⟨38014766611433226940592909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101372710963821938508247757 38014766611433226940592909)
                  ·
                    refine ⟨14255537479287460102722341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38014766611433226940592909 14255537479287460102722341)
                    ·
                      refine ⟨2672913277366398769260439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14255537479287460102722341 2672913277366398769260439)
                      ·
                        rfl

theorem cell23_5205480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5205480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205480 prefixEnd_5205480 := by exact prefixLift 5205480
  have htrace : WordTrace (prefixWord ++ tailWord_5205480) baseStart_5205480 baseEnd_5205480 := by
    simpa [prefixWord, tailWord_5205480, baseEnd_5205480] using wordTrace_append hprefix tailTrace_5205480
  have hstable : (prefixWord ++ tailWord_5205480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205480).length < 2 ^ (prefixWord ++ tailWord_5205480).sum := by decide
  have hdescent : baseEnd_5205480 < baseStart_5205480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205537 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 6]
def baseStart_5205537 : Nat := 118140960795 + 5205537 * 2 ^ 59
def prefixEnd_5205537 : Nat := 4983230072969 + 3 ^ 40 * 5205537 * 2
def baseEnd_5205537 : Nat := 296993616195967227360853

theorem tailTrace_5205537 : CollatzResearch.WordTrace tailWord_5205537 prefixEnd_5205537 296993616195967227360853 := by
  unfold tailWord_5205537
  simp only [CollatzResearch.WordTrace]
  refine ⟨189861532142235958785022865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126574354761490639190015243 189861532142235958785022865)
  ·
    refine ⟨142396149106676969088767149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189861532142235958785022865 142396149106676969088767149)
    ·
      refine ⟨53398555915003863408287681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142396149106676969088767149 53398555915003863408287681)
      ·
        refine ⟨40048916936252897556215761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53398555915003863408287681 40048916936252897556215761)
        ·
          refine ⟨30036687702189673167161821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40048916936252897556215761 30036687702189673167161821)
          ·
            refine ⟨11263757888321127437685683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30036687702189673167161821 11263757888321127437685683)
            ·
              refine ⟨16895636832481691156528525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11263757888321127437685683 16895636832481691156528525)
              ·
                refine ⟨6335863812180634183698197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16895636832481691156528525 6335863812180634183698197)
                ·
                  refine ⟨296993616195967227360853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6335863812180634183698197 296993616195967227360853)
                  ·
                    rfl

theorem cell23_5205537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 6].length) (baseStart_5205537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205537 prefixEnd_5205537 := by exact prefixLift 5205537
  have htrace : WordTrace (prefixWord ++ tailWord_5205537) baseStart_5205537 baseEnd_5205537 := by
    simpa [prefixWord, tailWord_5205537, baseEnd_5205537] using wordTrace_append hprefix tailTrace_5205537
  have hstable : (prefixWord ++ tailWord_5205537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205537).length < 2 ^ (prefixWord ++ tailWord_5205537).sum := by decide
  have hdescent : baseEnd_5205537 < baseStart_5205537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205575 : List Nat := [1, 1, 4, 1, 6, 1, 2, 2, 1, 4]
def baseStart_5205575 : Nat := 118140960795 + 5205575 * 2 ^ 59
def prefixEnd_5205575 : Nat := 4983230072969 + 3 ^ 40 * 5205575 * 2
def baseEnd_5205575 : Nat := 890987352676191965857501

theorem tailTrace_5205575 : CollatzResearch.WordTrace tailWord_5205575 prefixEnd_5205575 890987352676191965857501 := by
  unfold tailWord_5205575
  simp only [CollatzResearch.WordTrace]
  refine ⟨189862918116098291274906179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126575278744065527516604119 189862918116098291274906179)
  ·
    refine ⟨284794377174147436912359269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189862918116098291274906179 284794377174147436912359269)
    ·
      refine ⟨53398945720152644421067363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284794377174147436912359269 53398945720152644421067363)
      ·
        refine ⟨80098418580228966631601045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53398945720152644421067363 80098418580228966631601045)
        ·
          refine ⟨3754613370948232810856299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80098418580228966631601045 3754613370948232810856299)
          ·
            refine ⟨5631920056422349216284449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754613370948232810856299 5631920056422349216284449)
            ·
              refine ⟨4223940042316761912213337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5631920056422349216284449 4223940042316761912213337)
              ·
                refine ⟨3167955031737571434160003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4223940042316761912213337 3167955031737571434160003)
                ·
                  refine ⟨4751932547606357151240005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3167955031737571434160003 4751932547606357151240005)
                  ·
                    refine ⟨890987352676191965857501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751932547606357151240005 890987352676191965857501)
                    ·
                      rfl

theorem cell23_5205575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_5205575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205575 prefixEnd_5205575 := by exact prefixLift 5205575
  have htrace : WordTrace (prefixWord ++ tailWord_5205575) baseStart_5205575 baseEnd_5205575 := by
    simpa [prefixWord, tailWord_5205575, baseEnd_5205575] using wordTrace_append hprefix tailTrace_5205575
  have hstable : (prefixWord ++ tailWord_5205575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205575).length < 2 ^ (prefixWord ++ tailWord_5205575).sum := by decide
  have hdescent : baseEnd_5205575 < baseStart_5205575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205608 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5205608 : Nat := 118140960795 + 5205608 * 2 ^ 59
def prefixEnd_5205608 : Nat := 4983230072969 + 3 ^ 40 * 5205608 * 2
def baseEnd_5205608 : Nat := 2672979002890174268459851

theorem tailTrace_5205608 : CollatzResearch.WordTrace tailWord_5205608 prefixEnd_5205608 2672979002890174268459851 := by
  unfold tailWord_5205608
  simp only [CollatzResearch.WordTrace]
  refine ⟨94932060862489368955428739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126576081149985825273904985 94932060862489368955428739)
  ·
    refine ⟨142398091293734053433143109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94932060862489368955428739 142398091293734053433143109)
    ·
      refine ⟨26699642117575135018714333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142398091293734053433143109 26699642117575135018714333)
      ·
        refine ⟨10012365794090675632017875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26699642117575135018714333 10012365794090675632017875)
        ·
          refine ⟨15018548691136013448026813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10012365794090675632017875 15018548691136013448026813)
          ·
            refine ⟨5631955759176005043010055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15018548691136013448026813 5631955759176005043010055)
            ·
              refine ⟨8447933638764007564515083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631955759176005043010055 8447933638764007564515083)
              ·
                refine ⟨12671900458146011346772625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8447933638764007564515083 12671900458146011346772625)
                ·
                  refine ⟨9503925343609508510079469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12671900458146011346772625 9503925343609508510079469)
                  ·
                    refine ⟨3563972003853565691279801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9503925343609508510079469 3563972003853565691279801)
                    ·
                      refine ⟨2672979002890174268459851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3563972003853565691279801 2672979002890174268459851)
                      ·
                        rfl

theorem cell23_5205608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5205608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205608 prefixEnd_5205608 := by exact prefixLift 5205608
  have htrace : WordTrace (prefixWord ++ tailWord_5205608) baseStart_5205608 baseEnd_5205608 := by
    simpa [prefixWord, tailWord_5205608, baseEnd_5205608] using wordTrace_append hprefix tailTrace_5205608
  have hstable : (prefixWord ++ tailWord_5205608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205608).length < 2 ^ (prefixWord ++ tailWord_5205608).sum := by decide
  have hdescent : baseEnd_5205608 < baseStart_5205608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205621 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5205621 : Nat := 118140960795 + 5205621 * 2 ^ 59
def prefixEnd_5205621 : Nat := 4983230072969 + 3 ^ 40 * 5205621 * 2
def baseEnd_5205621 : Nat := 2672985678138682717597291

theorem tailTrace_5205621 : CollatzResearch.WordTrace tailWord_5205621 prefixEnd_5205621 2672985678138682717597291 := by
  unfold tailWord_5205621
  simp only [CollatzResearch.WordTrace]
  refine ⟨189864595873931641131080717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126576397249287760754053811 189864595873931641131080717)
  ·
    refine ⟨71199223452724365424155269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189864595873931641131080717 71199223452724365424155269)
    ·
      refine ⟨13349854397385818517029113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71199223452724365424155269 13349854397385818517029113)
      ·
        refine ⟨10012390798039363887771835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13349854397385818517029113 10012390798039363887771835)
        ·
          refine ⟨15018586197059045831657753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10012390798039363887771835 15018586197059045831657753)
          ·
            refine ⟨11263939647794284373743315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15018586197059045831657753 11263939647794284373743315)
            ·
              refine ⟨16895909471691426560614973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11263939647794284373743315 16895909471691426560614973)
              ·
                refine ⟨6335966051884284960230615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16895909471691426560614973 6335966051884284960230615)
                ·
                  refine ⟨9503949077826427440345923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6335966051884284960230615 9503949077826427440345923)
                  ·
                    refine ⟨14255923616739641160518885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9503949077826427440345923 14255923616739641160518885)
                    ·
                      refine ⟨2672985678138682717597291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14255923616739641160518885 2672985678138682717597291)
                      ·
                        rfl

theorem cell23_5205621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5205621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205621 prefixEnd_5205621 := by exact prefixLift 5205621
  have htrace : WordTrace (prefixWord ++ tailWord_5205621) baseStart_5205621 baseEnd_5205621 := by
    simpa [prefixWord, tailWord_5205621, baseEnd_5205621] using wordTrace_append hprefix tailTrace_5205621
  have hstable : (prefixWord ++ tailWord_5205621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205621).length < 2 ^ (prefixWord ++ tailWord_5205621).sum := by decide
  have hdescent : baseEnd_5205621 < baseStart_5205621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205707 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4]
def baseStart_5205707 : Nat := 118140960795 + 5205707 * 2 ^ 59
def prefixEnd_5205707 : Nat := 4983230072969 + 3 ^ 40 * 5205707 * 2
def baseEnd_5205707 : Nat := 2673029837474969381121895

theorem tailTrace_5205707 : CollatzResearch.WordTrace tailWord_5205707 prefixEnd_5205707 2673029837474969381121895 := by
  unfold tailWord_5205707
  simp only [CollatzResearch.WordTrace]
  refine ⟨189867732551620077818711375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126578488367746718545807583 189867732551620077818711375)
  ·
    refine ⟨284801598827430116728067063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189867732551620077818711375 284801598827430116728067063)
    ·
      refine ⟨427202398241145175092100595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284801598827430116728067063 427202398241145175092100595)
      ·
        refine ⟨640803597361717762638150893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427202398241145175092100595 640803597361717762638150893)
        ·
          refine ⟨240301349010644160989306585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640803597361717762638150893 240301349010644160989306585)
          ·
            refine ⟨180226011757983120741979939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240301349010644160989306585 180226011757983120741979939)
            ·
              refine ⟨270339017636974681112969909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180226011757983120741979939 270339017636974681112969909)
              ·
                refine ⟨25344282903466376354340929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270339017636974681112969909 25344282903466376354340929)
                ·
                  refine ⟨19008212177599782265755697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25344282903466376354340929 19008212177599782265755697)
                  ·
                    refine ⟨14256159133199836699316773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19008212177599782265755697 14256159133199836699316773)
                    ·
                      refine ⟨2673029837474969381121895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14256159133199836699316773 2673029837474969381121895)
                      ·
                        rfl

theorem cell23_5205707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_5205707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205707 prefixEnd_5205707 := by exact prefixLift 5205707
  have htrace : WordTrace (prefixWord ++ tailWord_5205707) baseStart_5205707 baseEnd_5205707 := by
    simpa [prefixWord, tailWord_5205707, baseEnd_5205707] using wordTrace_append hprefix tailTrace_5205707
  have hstable : (prefixWord ++ tailWord_5205707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205707).length < 2 ^ (prefixWord ++ tailWord_5205707).sum := by decide
  have hdescent : baseEnd_5205707 < baseStart_5205707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205714 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_5205714 : Nat := 118140960795 + 5205714 * 2 ^ 59
def prefixEnd_5205714 : Nat := 4983230072969 + 3 ^ 40 * 5205714 * 2
def baseEnd_5205714 : Nat := 2673033431839550853734363

theorem tailTrace_5205714 : CollatzResearch.WordTrace tailWord_5205714 prefixEnd_5205714 2673033431839550853734363 := by
  unfold tailWord_5205714
  simp only [CollatzResearch.WordTrace]
  refine ⟨47466996965648679503554049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126578658575063145342810797 47466996965648679503554049)
  ·
    refine ⟨35600247724236509627665537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47466996965648679503554049 35600247724236509627665537)
    ·
      refine ⟨26700185793177382220749153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35600247724236509627665537 26700185793177382220749153)
      ·
        refine ⟨20025139344883036665561865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26700185793177382220749153 20025139344883036665561865)
        ·
          refine ⟨15018854508662277499171399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20025139344883036665561865 15018854508662277499171399)
          ·
            refine ⟨22528281762993416248757099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15018854508662277499171399 22528281762993416248757099)
            ·
              refine ⟨33792422644490124373135649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22528281762993416248757099 33792422644490124373135649)
              ·
                refine ⟨25344316983367593279851737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33792422644490124373135649 25344316983367593279851737)
                ·
                  refine ⟨19008237737525694959888803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25344316983367593279851737 19008237737525694959888803)
                  ·
                    refine ⟨28512356606288542439833205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19008237737525694959888803 28512356606288542439833205)
                    ·
                      refine ⟨2673033431839550853734363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28512356606288542439833205 2673033431839550853734363)
                      ·
                        rfl

theorem cell23_5205714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_5205714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205714 prefixEnd_5205714 := by exact prefixLift 5205714
  have htrace : WordTrace (prefixWord ++ tailWord_5205714) baseStart_5205714 baseEnd_5205714 := by
    simpa [prefixWord, tailWord_5205714, baseEnd_5205714] using wordTrace_append hprefix tailTrace_5205714
  have hstable : (prefixWord ++ tailWord_5205714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205714).length < 2 ^ (prefixWord ++ tailWord_5205714).sum := by decide
  have hdescent : baseEnd_5205714 < baseStart_5205714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205748 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5205748 : Nat := 118140960795 + 5205748 * 2 ^ 59
def prefixEnd_5205748 : Nat := 4983230072969 + 3 ^ 40 * 5205748 * 2
def baseEnd_5205748 : Nat := 2673050890181803720709207

theorem tailTrace_5205748 : CollatzResearch.WordTrace tailWord_5205748 prefixEnd_5205748 2673050890181803720709207 := by
  unfold tailWord_5205748
  simp only [CollatzResearch.WordTrace]
  refine ⟨94934613972235770910476949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126579485296314361213969265 94934613972235770910476949)
  ·
    refine ⟨4450060029948551761428607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94934613972235770910476949 4450060029948551761428607)
    ·
      refine ⟨6675090044922827642142911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4450060029948551761428607 6675090044922827642142911)
      ·
        refine ⟨10012635067384241463214367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6675090044922827642142911 10012635067384241463214367)
        ·
          refine ⟨15018952601076362194821551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10012635067384241463214367 15018952601076362194821551)
          ·
            refine ⟨22528428901614543292232327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15018952601076362194821551 22528428901614543292232327)
            ·
              refine ⟨33792643352421814938348491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22528428901614543292232327 33792643352421814938348491)
              ·
                refine ⟨50688965028632722407522737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33792643352421814938348491 50688965028632722407522737)
                ·
                  refine ⟨38016723771474541805642053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50688965028632722407522737 38016723771474541805642053)
                  ·
                    refine ⟨7128135707151476588557885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38016723771474541805642053 7128135707151476588557885)
                    ·
                      refine ⟨2673050890181803720709207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128135707151476588557885 2673050890181803720709207)
                      ·
                        rfl

theorem cell23_5205748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5205748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205748 prefixEnd_5205748 := by exact prefixLift 5205748
  have htrace : WordTrace (prefixWord ++ tailWord_5205748) baseStart_5205748 baseEnd_5205748 := by
    simpa [prefixWord, tailWord_5205748, baseEnd_5205748] using wordTrace_append hprefix tailTrace_5205748
  have hstable : (prefixWord ++ tailWord_5205748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205748).length < 2 ^ (prefixWord ++ tailWord_5205748).sum := by decide
  have hdescent : baseEnd_5205748 < baseStart_5205748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205751 : List Nat := [1, 1, 3, 1, 1, 1, 8, 2, 5]
def baseStart_5205751 : Nat := 118140960795 + 5205751 * 2 ^ 59
def prefixEnd_5205751 : Nat := 4983230072969 + 3 ^ 40 * 5205751 * 2
def baseEnd_5205751 : Nat := 297005825624863023219077

theorem tailTrace_5205751 : CollatzResearch.WordTrace tailWord_5205751 prefixEnd_5205751 297005825624863023219077 := by
  unfold tailWord_5205751
  simp only [CollatzResearch.WordTrace]
  refine ⟨189869337363460673333313107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126579558242307115555542071 189869337363460673333313107)
  ·
    refine ⟨284804006045191009999969661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189869337363460673333313107 284804006045191009999969661)
    ·
      refine ⟨106801502266946628749988623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284804006045191009999969661 106801502266946628749988623)
      ·
        refine ⟨160202253400419943124982935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106801502266946628749988623 160202253400419943124982935)
        ·
          refine ⟨240303380100629914687474403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160202253400419943124982935 240303380100629914687474403)
          ·
            refine ⟨360455070150944872031211605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240303380100629914687474403 360455070150944872031211605)
            ·
              refine ⟨4224082853331385219115761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 360455070150944872031211605 4224082853331385219115761)
              ·
                refine ⟨3168062139998538914336821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4224082853331385219115761 3168062139998538914336821)
                ·
                  refine ⟨297005825624863023219077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3168062139998538914336821 297005825624863023219077)
                  ·
                    rfl

theorem cell23_5205751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 5].length) (baseStart_5205751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205751 prefixEnd_5205751 := by exact prefixLift 5205751
  have htrace : WordTrace (prefixWord ++ tailWord_5205751) baseStart_5205751 baseEnd_5205751 := by
    simpa [prefixWord, tailWord_5205751, baseEnd_5205751] using wordTrace_append hprefix tailTrace_5205751
  have hstable : (prefixWord ++ tailWord_5205751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205751).length < 2 ^ (prefixWord ++ tailWord_5205751).sum := by decide
  have hdescent : baseEnd_5205751 < baseStart_5205751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205757 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_5205757 : Nat := 118140960795 + 5205757 * 2 ^ 59
def prefixEnd_5205757 : Nat := 4983230072969 + 3 ^ 40 * 5205757 * 2
def baseEnd_5205757 : Nat := 2673055511507694185496665

theorem tailTrace_5205757 : CollatzResearch.WordTrace tailWord_5205757 prefixEnd_5205757 2673055511507694185496665 := by
  unfold tailWord_5205757
  simp only [CollatzResearch.WordTrace]
  refine ⟨189869556201438936358031525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126579704134292624238687683 189869556201438936358031525)
  ·
    refine ⟨35600541787769800567130911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189869556201438936358031525 35600541787769800567130911)
    ·
      refine ⟨53400812681654700850696367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35600541787769800567130911 53400812681654700850696367)
      ·
        refine ⟨80101219022482051276044551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53400812681654700850696367 80101219022482051276044551)
        ·
          refine ⟨120151828533723076914066827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80101219022482051276044551 120151828533723076914066827)
          ·
            refine ⟨180227742800584615371100241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120151828533723076914066827 180227742800584615371100241)
            ·
              refine ⟨135170807100438461528325181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180227742800584615371100241 135170807100438461528325181)
              ·
                refine ⟨50689052662664423073121943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135170807100438461528325181 50689052662664423073121943)
                ·
                  refine ⟨76033578993996634609682915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50689052662664423073121943 76033578993996634609682915)
                  ·
                    refine ⟨114050368490994951914524373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76033578993996634609682915 114050368490994951914524373)
                    ·
                      refine ⟨2673055511507694185496665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114050368490994951914524373 2673055511507694185496665)
                      ·
                        rfl

theorem cell23_5205757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_5205757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205757 prefixEnd_5205757 := by exact prefixLift 5205757
  have htrace : WordTrace (prefixWord ++ tailWord_5205757) baseStart_5205757 baseEnd_5205757 := by
    simpa [prefixWord, tailWord_5205757, baseEnd_5205757] using wordTrace_append hprefix tailTrace_5205757
  have hstable : (prefixWord ++ tailWord_5205757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205757).length < 2 ^ (prefixWord ++ tailWord_5205757).sum := by decide
  have hdescent : baseEnd_5205757 < baseStart_5205757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205781 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_5205781 : Nat := 118140960795 + 5205781 * 2 ^ 59
def prefixEnd_5205781 : Nat := 4983230072969 + 3 ^ 40 * 5205781 * 2
def baseEnd_5205781 : Nat := 891022611681134030532185

theorem tailTrace_5205781 : CollatzResearch.WordTrace tailWord_5205781 prefixEnd_5205781 891022611681134030532185 := by
  unfold tailWord_5205781
  simp only [CollatzResearch.WordTrace]
  refine ⟨189870431553351988456905197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126580287702234658971270131 189870431553351988456905197)
  ·
    refine ⟨71201411832506995671339449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189870431553351988456905197 71201411832506995671339449)
    ·
      refine ⟨53401058874380246753504587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71201411832506995671339449 53401058874380246753504587)
      ·
        refine ⟨80101588311570370130256881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53401058874380246753504587 80101588311570370130256881)
        ·
          refine ⟨60076191233677777597692661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80101588311570370130256881 60076191233677777597692661)
          ·
            refine ⟨5632142928157291649783687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60076191233677777597692661 5632142928157291649783687)
            ·
              refine ⟨8448214392235937474675531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632142928157291649783687 8448214392235937474675531)
              ·
                refine ⟨12672321588353906212013297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448214392235937474675531 12672321588353906212013297)
                ·
                  refine ⟨9504241191265429659009973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12672321588353906212013297 9504241191265429659009973)
                  ·
                    refine ⟨891022611681134030532185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9504241191265429659009973 891022611681134030532185)
                    ·
                      rfl

theorem cell23_5205781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_5205781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205781 prefixEnd_5205781 := by exact prefixLift 5205781
  have htrace : WordTrace (prefixWord ++ tailWord_5205781) baseStart_5205781 baseEnd_5205781 := by
    simpa [prefixWord, tailWord_5205781, baseEnd_5205781] using wordTrace_append hprefix tailTrace_5205781
  have hstable : (prefixWord ++ tailWord_5205781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205781).length < 2 ^ (prefixWord ++ tailWord_5205781).sum := by decide
  have hdescent : baseEnd_5205781 < baseStart_5205781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205807 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 8]
def baseStart_5205807 : Nat := 118140960795 + 5205807 * 2 ^ 59
def prefixEnd_5205807 : Nat := 4983230072969 + 3 ^ 40 * 5205807 * 2
def baseEnd_5205807 : Nat := 297009020615602109985715

theorem tailTrace_5205807 : CollatzResearch.WordTrace tailWord_5205807 prefixEnd_5205807 297009020615602109985715 := by
  unfold tailWord_5205807
  simp only [CollatzResearch.WordTrace]
  refine ⟨189871379851257794897351675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126580919900838529931567783 189871379851257794897351675)
  ·
    refine ⟨284807069776886692346027513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189871379851257794897351675 284807069776886692346027513)
    ·
      refine ⟨213605302332665019259520635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284807069776886692346027513 213605302332665019259520635)
      ·
        refine ⟨320407953498997528889280953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213605302332665019259520635 320407953498997528889280953)
        ·
          refine ⟨240305965124248146666960715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320407953498997528889280953 240305965124248146666960715)
          ·
            refine ⟨360458947686372220000441073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240305965124248146666960715 360458947686372220000441073)
            ·
              refine ⟨270344210764779165000330805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360458947686372220000441073 270344210764779165000330805)
              ·
                refine ⟨25344769759198046718781013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270344210764779165000330805 25344769759198046718781013)
                ·
                  refine ⟨297009020615602109985715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25344769759198046718781013 297009020615602109985715)
                  ·
                    rfl

theorem cell23_5205807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 8].length) (baseStart_5205807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205807 prefixEnd_5205807 := by exact prefixLift 5205807
  have htrace : WordTrace (prefixWord ++ tailWord_5205807) baseStart_5205807 baseEnd_5205807 := by
    simpa [prefixWord, tailWord_5205807, baseEnd_5205807] using wordTrace_append hprefix tailTrace_5205807
  have hstable : (prefixWord ++ tailWord_5205807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205807).length < 2 ^ (prefixWord ++ tailWord_5205807).sum := by decide
  have hdescent : baseEnd_5205807 < baseStart_5205807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205821 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5205821 : Nat := 118140960795 + 5205821 * 2 ^ 59
def prefixEnd_5205821 : Nat := 4983230072969 + 3 ^ 40 * 5205821 * 2
def baseEnd_5205821 : Nat := 2673088374269581935096371

theorem tailTrace_5205821 : CollatzResearch.WordTrace tailWord_5205821 prefixEnd_5205821 2673088374269581935096371 := by
  unfold tailWord_5205821
  simp only [CollatzResearch.WordTrace]
  refine ⟨189871890473207075288361317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126581260315471383525574211 189871890473207075288361317)
  ·
    refine ⟨35600979463726326616567747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189871890473207075288361317 35600979463726326616567747)
    ·
      refine ⟨53401469195589489924851621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35600979463726326616567747 53401469195589489924851621)
      ·
        refine ⟨10012775474173029360909679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53401469195589489924851621 10012775474173029360909679)
        ·
          refine ⟨15019163211259544041364519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10012775474173029360909679 15019163211259544041364519)
          ·
            refine ⟨22528744816889316062046779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15019163211259544041364519 22528744816889316062046779)
            ·
              refine ⟨33793117225333974093070169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22528744816889316062046779 33793117225333974093070169)
              ·
                refine ⟨25344837919000480569802627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33793117225333974093070169 25344837919000480569802627)
                ·
                  refine ⟨38017256878500720854703941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25344837919000480569802627 38017256878500720854703941)
                  ·
                    refine ⟨7128235664718885160256989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38017256878500720854703941 7128235664718885160256989)
                    ·
                      refine ⟨2673088374269581935096371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128235664718885160256989 2673088374269581935096371)
                      ·
                        rfl

theorem cell23_5205821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5205821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205821 prefixEnd_5205821 := by exact prefixLift 5205821
  have htrace : WordTrace (prefixWord ++ tailWord_5205821) baseStart_5205821 baseEnd_5205821 := by
    simpa [prefixWord, tailWord_5205821, baseEnd_5205821] using wordTrace_append hprefix tailTrace_5205821
  have hstable : (prefixWord ++ tailWord_5205821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205821).length < 2 ^ (prefixWord ++ tailWord_5205821).sum := by decide
  have hdescent : baseEnd_5205821 < baseStart_5205821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205834 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_5205834 : Nat := 118140960795 + 5205834 * 2 ^ 59
def prefixEnd_5205834 : Nat := 4983230072969 + 3 ^ 40 * 5205834 * 2
def baseEnd_5205834 : Nat := 2673095049518090384233811

theorem tailTrace_5205834 : CollatzResearch.WordTrace tailWord_5205834 prefixEnd_5205834 2673095049518090384233811 := by
  unfold tailWord_5205834
  simp only [CollatzResearch.WordTrace]
  refine ⟨47468091155539994627146139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126581576414773319005723037 47468091155539994627146139)
  ·
    refine ⟨71202136733309991940719209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47468091155539994627146139 71202136733309991940719209)
    ·
      refine ⟨53401602549982493955539407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71202136733309991940719209 53401602549982493955539407)
      ·
        refine ⟨80102403824973740933309111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53401602549982493955539407 80102403824973740933309111)
        ·
          refine ⟨120153605737460611399963667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80102403824973740933309111 120153605737460611399963667)
          ·
            refine ⟨180230408606190917099945501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120153605737460611399963667 180230408606190917099945501)
            ·
              refine ⟨67586403227321593912479563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180230408606190917099945501 67586403227321593912479563)
              ·
                refine ⟨101379604840982390868719345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67586403227321593912479563 101379604840982390868719345)
                ·
                  refine ⟨76034703630736793151539509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101379604840982390868719345 76034703630736793151539509)
                  ·
                    refine ⟨7128253465381574357956829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76034703630736793151539509 7128253465381574357956829)
                    ·
                      refine ⟨2673095049518090384233811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128253465381574357956829 2673095049518090384233811)
                      ·
                        rfl

theorem cell23_5205834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_5205834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205834 prefixEnd_5205834 := by exact prefixLift 5205834
  have htrace : WordTrace (prefixWord ++ tailWord_5205834) baseStart_5205834 baseEnd_5205834 := by
    simpa [prefixWord, tailWord_5205834, baseEnd_5205834] using wordTrace_append hprefix tailTrace_5205834
  have hstable : (prefixWord ++ tailWord_5205834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205834).length < 2 ^ (prefixWord ++ tailWord_5205834).sum := by decide
  have hdescent : baseEnd_5205834 < baseStart_5205834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205845 : List Nat := [1, 3, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_5205845 : Nat := 118140960795 + 5205845 * 2 ^ 59
def prefixEnd_5205845 : Nat := 4983230072969 + 3 ^ 40 * 5205845 * 2
def baseEnd_5205845 : Nat := 891033565935096613732087

theorem tailTrace_5205845 : CollatzResearch.WordTrace tailWord_5205845 prefixEnd_5205845 891033565935096613732087 := by
  unfold tailWord_5205845
  simp only [CollatzResearch.WordTrace]
  refine ⟨189872765825120127387234989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126581843883413418258156659 189872765825120127387234989)
  ·
    refine ⟨71202287184420047770213121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189872765825120127387234989 71202287184420047770213121)
    ·
      refine ⟨53401715388315035827659841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71202287184420047770213121 53401715388315035827659841)
      ·
        refine ⟨40051286541236276870744881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53401715388315035827659841 40051286541236276870744881)
        ·
          refine ⟨30038464905927207653058661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40051286541236276870744881 30038464905927207653058661)
          ·
            refine ⟨5632212169861351434948499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30038464905927207653058661 5632212169861351434948499)
            ·
              refine ⟨8448318254792027152422749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632212169861351434948499 8448318254792027152422749)
              ·
                refine ⟨3168119345547010182158531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8448318254792027152422749 3168119345547010182158531)
                ·
                  refine ⟨4752179018320515273237797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168119345547010182158531 4752179018320515273237797)
                  ·
                    refine ⟨891033565935096613732087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752179018320515273237797 891033565935096613732087)
                    ·
                      rfl

theorem cell23_5205845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_5205845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205845 prefixEnd_5205845 := by exact prefixLift 5205845
  have htrace : WordTrace (prefixWord ++ tailWord_5205845) baseStart_5205845 baseEnd_5205845 := by
    simpa [prefixWord, tailWord_5205845, baseEnd_5205845] using wordTrace_append hprefix tailTrace_5205845
  have hstable : (prefixWord ++ tailWord_5205845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205845).length < 2 ^ (prefixWord ++ tailWord_5205845).sum := by decide
  have hdescent : baseEnd_5205845 < baseStart_5205845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205868 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_5205868 : Nat := 118140960795 + 5205868 * 2 ^ 59
def prefixEnd_5205868 : Nat := 4983230072969 + 3 ^ 40 * 5205868 * 2
def baseEnd_5205868 : Nat := 2673112507860343251208655

theorem tailTrace_5205868 : CollatzResearch.WordTrace tailWord_5205868 prefixEnd_5205868 2673112507860343251208655 := by
  unfold tailWord_5205868
  simp only [CollatzResearch.WordTrace]
  refine ⟨94936802352018401157661129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126582403136024534876881505 94936802352018401157661129)
  ·
    refine ⟨71202601764013800868245847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94936802352018401157661129 71202601764013800868245847)
    ·
      refine ⟨106803902646020701302368771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71202601764013800868245847 106803902646020701302368771)
      ·
        refine ⟨160205853969031051953553157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106803902646020701302368771 160205853969031051953553157)
        ·
          refine ⟨30038597619193322241291217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160205853969031051953553157 30038597619193322241291217)
          ·
            refine ⟨22528948214394991680968413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30038597619193322241291217 22528948214394991680968413)
            ·
              refine ⟨8448355580398121880363155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22528948214394991680968413 8448355580398121880363155)
              ·
                refine ⟨12672533370597182820544733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448355580398121880363155 12672533370597182820544733)
                ·
                  refine ⟨4752200013973943557704275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12672533370597182820544733 4752200013973943557704275)
                  ·
                    refine ⟨7128300020960915336556413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4752200013973943557704275 7128300020960915336556413)
                    ·
                      refine ⟨2673112507860343251208655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128300020960915336556413 2673112507860343251208655)
                      ·
                        rfl

theorem cell23_5205868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_5205868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205868 prefixEnd_5205868 := by exact prefixLift 5205868
  have htrace : WordTrace (prefixWord ++ tailWord_5205868) baseStart_5205868 baseEnd_5205868 := by
    simpa [prefixWord, tailWord_5205868, baseEnd_5205868] using wordTrace_append hprefix tailTrace_5205868
  have hstable : (prefixWord ++ tailWord_5205868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205868).length < 2 ^ (prefixWord ++ tailWord_5205868).sum := by decide
  have hdescent : baseEnd_5205868 < baseStart_5205868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205874 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5205874 : Nat := 118140960795 + 5205874 * 2 ^ 59
def prefixEnd_5205874 : Nat := 4983230072969 + 3 ^ 40 * 5205874 * 2
def baseEnd_5205874 : Nat := 2673115588744270227733627

theorem tailTrace_5205874 : CollatzResearch.WordTrace tailWord_5205874 prefixEnd_5205874 2673115588744270227733627 := by
  unfold tailWord_5205874
  simp only [CollatzResearch.WordTrace]
  refine ⟨47468455885503766335010169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126582549028010043560027117 47468455885503766335010169)
  ·
    refine ⟨35601341914127824751257627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47468455885503766335010169 35601341914127824751257627)
    ·
      refine ⟨53402012871191737126886441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35601341914127824751257627 53402012871191737126886441)
      ·
        refine ⟨40051509653393802845164831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53402012871191737126886441 40051509653393802845164831)
        ·
          refine ⟨60077264480090704267747247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40051509653393802845164831 60077264480090704267747247)
          ·
            refine ⟨90115896720136056401620871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60077264480090704267747247 90115896720136056401620871)
            ·
              refine ⟨135173845080204084602431307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90115896720136056401620871 135173845080204084602431307)
              ·
                refine ⟨202760767620306126903646961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135173845080204084602431307 202760767620306126903646961)
                ·
                  refine ⟨152070575715229595177735221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202760767620306126903646961 152070575715229595177735221)
                  ·
                    refine ⟨14256616473302774547912677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 152070575715229595177735221 14256616473302774547912677)
                    ·
                      refine ⟨2673115588744270227733627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14256616473302774547912677 2673115588744270227733627)
                      ·
                        rfl

theorem cell23_5205874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5205874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205874 prefixEnd_5205874 := by exact prefixLift 5205874
  have htrace : WordTrace (prefixWord ++ tailWord_5205874) baseStart_5205874 baseEnd_5205874 := by
    simpa [prefixWord, tailWord_5205874, baseEnd_5205874] using wordTrace_append hprefix tailTrace_5205874
  have hstable : (prefixWord ++ tailWord_5205874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205874).length < 2 ^ (prefixWord ++ tailWord_5205874).sum := by decide
  have hdescent : baseEnd_5205874 < baseStart_5205874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205891 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 4]
def baseStart_5205891 : Nat := 118140960795 + 5205891 * 2 ^ 59
def prefixEnd_5205891 : Nat := 4983230072969 + 3 ^ 40 * 5205891 * 2
def baseEnd_5205891 : Nat := 2673124317915396661221049

theorem tailTrace_5205891 : CollatzResearch.WordTrace tailWord_5205891 prefixEnd_5205891 2673124317915396661221049 := by
  unfold tailWord_5205891
  simp only [CollatzResearch.WordTrace]
  refine ⟨189874443582953477243409527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126582962388635651495606351 189874443582953477243409527)
  ·
    refine ⟨284811665374430215865114291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189874443582953477243409527 284811665374430215865114291)
    ·
      refine ⟨427217498061645323797671437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284811665374430215865114291 427217498061645323797671437)
      ·
        refine ⟨160206561773116996424126789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 427217498061645323797671437 160206561773116996424126789)
        ·
          refine ⟨30038730332459436829523773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160206561773116996424126789 30038730332459436829523773)
          ·
            refine ⟨11264523874672288811071415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30038730332459436829523773 11264523874672288811071415)
            ·
              refine ⟨16896785812008433216607123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11264523874672288811071415 16896785812008433216607123)
              ·
                refine ⟨25345178718012649824910685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16896785812008433216607123 25345178718012649824910685)
                ·
                  refine ⟨9504442019254743684341507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25345178718012649824910685 9504442019254743684341507)
                  ·
                    refine ⟨14256663028882115526512261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9504442019254743684341507 14256663028882115526512261)
                    ·
                      refine ⟨2673124317915396661221049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14256663028882115526512261 2673124317915396661221049)
                      ·
                        rfl

theorem cell23_5205891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_5205891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205891 prefixEnd_5205891 := by exact prefixLift 5205891
  have htrace : WordTrace (prefixWord ++ tailWord_5205891) baseStart_5205891 baseEnd_5205891 := by
    simpa [prefixWord, tailWord_5205891, baseEnd_5205891] using wordTrace_append hprefix tailTrace_5205891
  have hstable : (prefixWord ++ tailWord_5205891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205891).length < 2 ^ (prefixWord ++ tailWord_5205891).sum := by decide
  have hdescent : baseEnd_5205891 < baseStart_5205891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205895 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_5205895 : Nat := 118140960795 + 5205895 * 2 ^ 59
def prefixEnd_5205895 : Nat := 4983230072969 + 3 ^ 40 * 5205895 * 2
def baseEnd_5205895 : Nat := 2673126371838014645571031

theorem tailTrace_5205895 : CollatzResearch.WordTrace tailWord_5205895 prefixEnd_5205895 2673126371838014645571031 := by
  unfold tailWord_5205895
  simp only [CollatzResearch.WordTrace]
  refine ⟨189874589474938985926555139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126583059649959323951036759 189874589474938985926555139)
  ·
    refine ⟨284811884212408478889832709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189874589474938985926555139 284811884212408478889832709)
    ·
      refine ⟨53402228289826589791843633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284811884212408478889832709 53402228289826589791843633)
      ·
        refine ⟨40051671217369942343882725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53402228289826589791843633 40051671217369942343882725)
        ·
          refine ⟨7509688353256864189478011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40051671217369942343882725 7509688353256864189478011)
          ·
            refine ⟨11264532529885296284217017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7509688353256864189478011 11264532529885296284217017)
            ·
              refine ⟨8448399397413972213162763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11264532529885296284217017 8448399397413972213162763)
              ·
                refine ⟨12672599096120958319744145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448399397413972213162763 12672599096120958319744145)
                ·
                  refine ⟨9504449322090718739808109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12672599096120958319744145 9504449322090718739808109)
                  ·
                    refine ⟨3564168495784019527428041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9504449322090718739808109 3564168495784019527428041)
                    ·
                      refine ⟨2673126371838014645571031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564168495784019527428041 2673126371838014645571031)
                      ·
                        rfl

theorem cell23_5205895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_5205895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205895 prefixEnd_5205895 := by exact prefixLift 5205895
  have htrace : WordTrace (prefixWord ++ tailWord_5205895) baseStart_5205895 baseEnd_5205895 := by
    simpa [prefixWord, tailWord_5205895, baseEnd_5205895] using wordTrace_append hprefix tailTrace_5205895
  have hstable : (prefixWord ++ tailWord_5205895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205895).length < 2 ^ (prefixWord ++ tailWord_5205895).sum := by decide
  have hdescent : baseEnd_5205895 < baseStart_5205895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205904 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_5205904 : Nat := 118140960795 + 5205904 * 2 ^ 59
def prefixEnd_5205904 : Nat := 4983230072969 + 3 ^ 40 * 5205904 * 2
def baseEnd_5205904 : Nat := 2673130993163905110358489

theorem tailTrace_5205904 : CollatzResearch.WordTrace tailWord_5205904 prefixEnd_5205904 2673130993163905110358489 := by
  unfold tailWord_5205904
  simp only [CollatzResearch.WordTrace]
  refine ⟨94937458865953190231816383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126583278487937586975755177 94937458865953190231816383)
  ·
    refine ⟨142406188298929785347724575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94937458865953190231816383 142406188298929785347724575)
    ·
      refine ⟨213609282448394678021586863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142406188298929785347724575 213609282448394678021586863)
      ·
        refine ⟨320413923672592017032380295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213609282448394678021586863 320413923672592017032380295)
        ·
          refine ⟨480620885508888025548570443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320413923672592017032380295 480620885508888025548570443)
          ·
            refine ⟨720931328263332038322855665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480620885508888025548570443 720931328263332038322855665)
            ·
              refine ⟨540698496197499028742141749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720931328263332038322855665 540698496197499028742141749)
              ·
                refine ⟨50690484018515533944575789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540698496197499028742141749 50690484018515533944575789)
                ·
                  refine ⟨19008931506943325229215921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50690484018515533944575789 19008931506943325229215921)
                  ·
                    refine ⟨14256698630207493921911941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19008931506943325229215921 14256698630207493921911941)
                    ·
                      refine ⟨2673130993163905110358489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14256698630207493921911941 2673130993163905110358489)
                      ·
                        rfl

theorem cell23_5205904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_5205904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205904 prefixEnd_5205904 := by exact prefixLift 5205904
  have htrace : WordTrace (prefixWord ++ tailWord_5205904) baseStart_5205904 baseEnd_5205904 := by
    simpa [prefixWord, tailWord_5205904, baseEnd_5205904] using wordTrace_append hprefix tailTrace_5205904
  have hstable : (prefixWord ++ tailWord_5205904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205904).length < 2 ^ (prefixWord ++ tailWord_5205904).sum := by decide
  have hdescent : baseEnd_5205904 < baseStart_5205904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205911 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_5205911 : Nat := 118140960795 + 5205911 * 2 ^ 59
def prefixEnd_5205911 : Nat := 4983230072969 + 3 ^ 40 * 5205911 * 2
def baseEnd_5205911 : Nat := 2673134587528486582970957

theorem tailTrace_5205911 : CollatzResearch.WordTrace tailWord_5205911 prefixEnd_5205911 2673134587528486582970957 := by
  unfold tailWord_5205911
  simp only [CollatzResearch.WordTrace]
  refine ⟨189875173042881020659137587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126583448695254013772758391 189875173042881020659137587)
  ·
    refine ⟨284812759564321530988706381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189875173042881020659137587 284812759564321530988706381)
    ·
      refine ⟨106804784836620574120764893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284812759564321530988706381 106804784836620574120764893)
      ·
        refine ⟨40051794313732715295286835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106804784836620574120764893 40051794313732715295286835)
        ·
          refine ⟨60077691470599072942930253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40051794313732715295286835 60077691470599072942930253)
          ·
            refine ⟨22529134301474652353598845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60077691470599072942930253 22529134301474652353598845)
            ·
              refine ⟨8448425363052994632599567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22529134301474652353598845 8448425363052994632599567)
              ·
                refine ⟨12672638044579491948899351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448425363052994632599567 12672638044579491948899351)
                ·
                  refine ⟨19008957066869237923349027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12672638044579491948899351 19008957066869237923349027)
                  ·
                    refine ⟨28513435600303856885023541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19008957066869237923349027 28513435600303856885023541)
                    ·
                      refine ⟨2673134587528486582970957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28513435600303856885023541 2673134587528486582970957)
                      ·
                        rfl

theorem cell23_5205911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_5205911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205911 prefixEnd_5205911 := by exact prefixLift 5205911
  have htrace : WordTrace (prefixWord ++ tailWord_5205911) baseStart_5205911 baseEnd_5205911 := by
    simpa [prefixWord, tailWord_5205911, baseEnd_5205911] using wordTrace_append hprefix tailTrace_5205911
  have hstable : (prefixWord ++ tailWord_5205911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205911).length < 2 ^ (prefixWord ++ tailWord_5205911).sum := by decide
  have hdescent : baseEnd_5205911 < baseStart_5205911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205914 : List Nat := [3, 1, 1, 4, 2, 12]
def baseStart_5205914 : Nat := 118140960795 + 5205914 * 2 ^ 59
def prefixEnd_5205914 : Nat := 4983230072969 + 3 ^ 40 * 5205914 * 2
def baseEnd_5205914 : Nat := 11000560197409259552401

theorem tailTrace_5205914 : CollatzResearch.WordTrace tailWord_5205914 prefixEnd_5205914 11000560197409259552401 := by
  unfold tailWord_5205914
  simp only [CollatzResearch.WordTrace]
  refine ⟨47468820615467538042874199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126583521641246768114331197 47468820615467538042874199)
  ·
    refine ⟨71203230923201307064311299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47468820615467538042874199 71203230923201307064311299)
    ·
      refine ⟨106804846384801960596466949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71203230923201307064311299 106804846384801960596466949)
      ·
        refine ⟨20025908697150367611837553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106804846384801960596466949 20025908697150367611837553)
        ·
          refine ⟨15019431522862775708878165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20025908697150367611837553 15019431522862775708878165)
          ·
            refine ⟨11000560197409259552401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15019431522862775708878165 11000560197409259552401)
            ·
              rfl

theorem cell23_5205914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 12].length) (baseStart_5205914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205914 prefixEnd_5205914 := by exact prefixLift 5205914
  have htrace : WordTrace (prefixWord ++ tailWord_5205914) baseStart_5205914 baseEnd_5205914 := by
    simpa [prefixWord, tailWord_5205914, baseEnd_5205914] using wordTrace_append hprefix tailTrace_5205914
  have hstable : (prefixWord ++ tailWord_5205914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205914).length < 2 ^ (prefixWord ++ tailWord_5205914).sum := by decide
  have hdescent : baseEnd_5205914 < baseStart_5205914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205919 : List Nat := [1, 1, 2, 5, 3, 2, 2, 2, 1, 1, 3]
def baseStart_5205919 : Nat := 118140960795 + 5205919 * 2 ^ 59
def prefixEnd_5205919 : Nat := 4983230072969 + 3 ^ 40 * 5205919 * 2
def baseEnd_5205919 : Nat := 2673138695373722551670921

theorem tailTrace_5205919 : CollatzResearch.WordTrace tailWord_5205919 prefixEnd_5205919 2673138695373722551670921 := by
  unfold tailWord_5205919
  simp only [CollatzResearch.WordTrace]
  refine ⟨189875464826852038025428811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126583643217901358683619207 189875464826852038025428811)
  ·
    refine ⟨284813197240278057038143217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189875464826852038025428811 284813197240278057038143217)
    ·
      refine ⟨213609897930208542778607413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284813197240278057038143217 213609897930208542778607413)
      ·
        refine ⟨20025927930957050885494445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213609897930208542778607413 20025927930957050885494445)
        ·
          refine ⟨7509722974108894082060417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20025927930957050885494445 7509722974108894082060417)
          ·
            refine ⟨5632292230581670561545313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7509722974108894082060417 5632292230581670561545313)
            ·
              refine ⟨4224219172936252921158985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5632292230581670561545313 4224219172936252921158985)
              ·
                refine ⟨3168164379702189690869239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4224219172936252921158985 3168164379702189690869239)
                ·
                  refine ⟨4752246569553284536303859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168164379702189690869239 4752246569553284536303859)
                  ·
                    refine ⟨7128369854329926804455789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4752246569553284536303859 7128369854329926804455789)
                    ·
                      refine ⟨2673138695373722551670921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128369854329926804455789 2673138695373722551670921)
                      ·
                        rfl

theorem cell23_5205919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_5205919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205919 prefixEnd_5205919 := by exact prefixLift 5205919
  have htrace : WordTrace (prefixWord ++ tailWord_5205919) baseStart_5205919 baseEnd_5205919 := by
    simpa [prefixWord, tailWord_5205919, baseEnd_5205919] using wordTrace_append hprefix tailTrace_5205919
  have hstable : (prefixWord ++ tailWord_5205919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205919).length < 2 ^ (prefixWord ++ tailWord_5205919).sum := by decide
  have hdescent : baseEnd_5205919 < baseStart_5205919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5205944 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 2, 7]
def baseStart_5205944 : Nat := 118140960795 + 5205944 * 2 ^ 59
def prefixEnd_5205944 : Nat := 4983230072969 + 3 ^ 40 * 5205944 * 2
def baseEnd_5205944 : Nat := 891050510796694984619435

theorem tailTrace_5205944 : CollatzResearch.WordTrace tailWord_5205944 prefixEnd_5205944 891050510796694984619435 := by
  unfold tailWord_5205944
  simp only [CollatzResearch.WordTrace]
  refine ⟨94938188325880733647544443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126584251101174311530059257 94938188325880733647544443)
  ·
    refine ⟨142407282488821100471316665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94938188325880733647544443 142407282488821100471316665)
    ·
      refine ⟨106805461866615825353487499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142407282488821100471316665 106805461866615825353487499)
      ·
        refine ⟨160208192799923738030231249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106805461866615825353487499 160208192799923738030231249)
        ·
          refine ⟨120156144599942803522673437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160208192799923738030231249 120156144599942803522673437)
          ·
            refine ⟨45058554224978551321002539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120156144599942803522673437 45058554224978551321002539)
            ·
              refine ⟨67587831337467826981503809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45058554224978551321002539 67587831337467826981503809)
              ·
                refine ⟨50690873503100870236127857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67587831337467826981503809 50690873503100870236127857)
                ·
                  refine ⟨38018155127325652677095893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50690873503100870236127857 38018155127325652677095893)
                  ·
                    refine ⟨891050510796694984619435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38018155127325652677095893 891050510796694984619435)
                    ·
                      rfl

theorem cell23_5205944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_5205944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5205944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5205944 prefixEnd_5205944 := by exact prefixLift 5205944
  have htrace : WordTrace (prefixWord ++ tailWord_5205944) baseStart_5205944 baseEnd_5205944 := by
    simpa [prefixWord, tailWord_5205944, baseEnd_5205944] using wordTrace_append hprefix tailTrace_5205944
  have hstable : (prefixWord ++ tailWord_5205944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5205944).length < 2 ^ (prefixWord ++ tailWord_5205944).sum := by decide
  have hdescent : baseEnd_5205944 < baseStart_5205944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5205944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206051 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 4, 5]
def baseStart_5206051 : Nat := 118140960795 + 5206051 * 2 ^ 59
def prefixEnd_5206051 : Nat := 4983230072969 + 3 ^ 40 * 5206051 * 2
def baseEnd_5206051 : Nat := 891068824940038678406771

theorem tailTrace_5206051 : CollatzResearch.WordTrace tailWord_5206051 prefixEnd_5206051 891068824940038678406771 := by
  unfold tailWord_5206051
  simp only [CollatzResearch.WordTrace]
  refine ⟨189880279262373824569234007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126586852841582549712822671 189880279262373824569234007)
  ·
    refine ⟨284820418893560736853851011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189880279262373824569234007 284820418893560736853851011)
    ·
      refine ⟨427230628340341105280776517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284820418893560736853851011 427230628340341105280776517)
      ·
        refine ⟨80105742813813957240145597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 427230628340341105280776517 80105742813813957240145597)
        ·
          refine ⟨30039653555180233965054599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80105742813813957240145597 30039653555180233965054599)
          ·
            refine ⟨45059480332770350947581899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30039653555180233965054599 45059480332770350947581899)
            ·
              refine ⟨67589220499155526421372849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45059480332770350947581899 67589220499155526421372849)
              ·
                refine ⟨50691915374366644816029637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67589220499155526421372849 50691915374366644816029637)
                ·
                  refine ⟨9504734132693745903005557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50691915374366644816029637 9504734132693745903005557)
                  ·
                    refine ⟨891068824940038678406771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9504734132693745903005557 891068824940038678406771)
                    ·
                      rfl

theorem cell23_5206051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 5].length) (baseStart_5206051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206051 prefixEnd_5206051 := by exact prefixLift 5206051
  have htrace : WordTrace (prefixWord ++ tailWord_5206051) baseStart_5206051 baseEnd_5206051 := by
    simpa [prefixWord, tailWord_5206051, baseEnd_5206051] using wordTrace_append hprefix tailTrace_5206051
  have hstable : (prefixWord ++ tailWord_5206051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206051).length < 2 ^ (prefixWord ++ tailWord_5206051).sum := by decide
  have hdescent : baseEnd_5206051 < baseStart_5206051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206071 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_5206071 : Nat := 118140960795 + 5206071 * 2 ^ 59
def prefixEnd_5206071 : Nat := 4983230072969 + 3 ^ 40 * 5206071 * 2
def baseEnd_5206071 : Nat := 2673216744433205956970221

theorem tailTrace_5206071 : CollatzResearch.WordTrace tailWord_5206071 prefixEnd_5206071 2673216744433205956970221 := by
  unfold tailWord_5206071
  simp only [CollatzResearch.WordTrace]
  refine ⟨189881008722301367984962067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126587339148200911989974711 189881008722301367984962067)
  ·
    refine ⟨284821513083452051977443101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189881008722301367984962067 284821513083452051977443101)
    ·
      refine ⟨106808067406294519491541163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284821513083452051977443101 106808067406294519491541163)
      ·
        refine ⟨160212101109441779237311745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106808067406294519491541163 160212101109441779237311745)
        ·
          refine ⟨120159075832081334427983809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160212101109441779237311745 120159075832081334427983809)
          ·
            refine ⟨90119306874061000820987857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120159075832081334427983809 90119306874061000820987857)
            ·
              refine ⟨67589480155545750615740893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90119306874061000820987857 67589480155545750615740893)
              ·
                refine ⟨25346055058329656480902835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67589480155545750615740893 25346055058329656480902835)
                ·
                  refine ⟨38019082587494484721354253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25346055058329656480902835 38019082587494484721354253)
                  ·
                    refine ⟨14257155970310431770507845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38019082587494484721354253 14257155970310431770507845)
                    ·
                      refine ⟨2673216744433205956970221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14257155970310431770507845 2673216744433205956970221)
                      ·
                        rfl

theorem cell23_5206071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_5206071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206071 prefixEnd_5206071 := by exact prefixLift 5206071
  have htrace : WordTrace (prefixWord ++ tailWord_5206071) baseStart_5206071 baseEnd_5206071 := by
    simpa [prefixWord, tailWord_5206071, baseEnd_5206071] using wordTrace_append hprefix tailTrace_5206071
  have hstable : (prefixWord ++ tailWord_5206071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206071).length < 2 ^ (prefixWord ++ tailWord_5206071).sum := by decide
  have hdescent : baseEnd_5206071 < baseStart_5206071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206122 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_5206122 : Nat := 118140960795 + 5206122 * 2 ^ 59
def prefixEnd_5206122 : Nat := 4983230072969 + 3 ^ 40 * 5206122 * 2
def baseEnd_5206122 : Nat := 2673242931946585257432487

theorem tailTrace_5206122 : CollatzResearch.WordTrace tailWord_5206122 prefixEnd_5206122 2673242931946585257432487 := by
  unfold tailWord_5206122
  simp only [CollatzResearch.WordTrace]
  refine ⟨47470717211279150923767155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126588579230077735796712413 47470717211279150923767155)
  ·
    refine ⟨71206075816918726385650733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47470717211279150923767155 71206075816918726385650733)
    ·
      refine ⟨26702278431344522394619025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71206075816918726385650733 26702278431344522394619025)
      ·
        refine ⟨20026708823508391795964269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26702278431344522394619025 20026708823508391795964269)
        ·
          refine ⟨7510015808815646923486601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20026708823508391795964269 7510015808815646923486601)
          ·
            refine ⟨5632511856611735192614951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7510015808815646923486601 5632511856611735192614951)
            ·
              refine ⟨8448767784917602788922427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632511856611735192614951 8448767784917602788922427)
              ·
                refine ⟨12673151677376404183383641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448767784917602788922427 12673151677376404183383641)
                ·
                  refine ⟨9504863758032303137537731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12673151677376404183383641 9504863758032303137537731)
                  ·
                    refine ⟨14257295637048454706306597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9504863758032303137537731 14257295637048454706306597)
                    ·
                      refine ⟨2673242931946585257432487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14257295637048454706306597 2673242931946585257432487)
                      ·
                        rfl

theorem cell23_5206122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_5206122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206122 prefixEnd_5206122 := by exact prefixLift 5206122
  have htrace : WordTrace (prefixWord ++ tailWord_5206122) baseStart_5206122 baseEnd_5206122 := by
    simpa [prefixWord, tailWord_5206122, baseEnd_5206122] using wordTrace_append hprefix tailTrace_5206122
  have hstable : (prefixWord ++ tailWord_5206122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206122).length < 2 ^ (prefixWord ++ tailWord_5206122).sum := by decide
  have hdescent : baseEnd_5206122 < baseStart_5206122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206171 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 5, 6]
def baseStart_5206171 : Nat := 118140960795 + 5206171 * 2 ^ 59
def prefixEnd_5206171 : Nat := 4983230072969 + 3 ^ 40 * 5206171 * 2
def baseEnd_5206171 : Nat := 891089364166218521906587

theorem tailTrace_5206171 : CollatzResearch.WordTrace tailWord_5206171 prefixEnd_5206171 891089364166218521906587 := by
  unfold tailWord_5206171
  simp only [CollatzResearch.WordTrace]
  refine ⟨189884656021939085063602367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126589770681292723375734911 189884656021939085063602367)
  ·
    refine ⟨284826984032908627595403551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189884656021939085063602367 284826984032908627595403551)
    ·
      refine ⟨427240476049362941393105327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284826984032908627595403551 427240476049362941393105327)
      ·
        refine ⟨640860714074044412089657991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427240476049362941393105327 640860714074044412089657991)
        ·
          refine ⟨961291071111066618134486987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640860714074044412089657991 961291071111066618134486987)
          ·
            refine ⟨1441936606666599927201730481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961291071111066618134486987 1441936606666599927201730481)
            ·
              refine ⟨1081452454999949945401297861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441936606666599927201730481 1081452454999949945401297861)
              ·
                refine ⟨202772335312490614762743349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1081452454999949945401297861 202772335312490614762743349)
                ·
                  refine ⟨19009906435545995134007189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202772335312490614762743349 19009906435545995134007189)
                  ·
                    refine ⟨891089364166218521906587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19009906435545995134007189 891089364166218521906587)
                    ·
                      rfl

theorem cell23_5206171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 6].length) (baseStart_5206171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206171 prefixEnd_5206171 := by exact prefixLift 5206171
  have htrace : WordTrace (prefixWord ++ tailWord_5206171) baseStart_5206171 baseEnd_5206171 := by
    simpa [prefixWord, tailWord_5206171, baseEnd_5206171] using wordTrace_append hprefix tailTrace_5206171
  have hstable : (prefixWord ++ tailWord_5206171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206171).length < 2 ^ (prefixWord ++ tailWord_5206171).sum := by decide
  have hdescent : baseEnd_5206171 < baseStart_5206171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206175 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 1, 5]
def baseStart_5206175 : Nat := 118140960795 + 5206175 * 2 ^ 59
def prefixEnd_5206175 : Nat := 4983230072969 + 3 ^ 40 * 5206175 * 2
def baseEnd_5206175 : Nat := 891090048807091183356581

theorem tailTrace_5206175 : CollatzResearch.WordTrace tailWord_5206175 prefixEnd_5206175 891090048807091183356581 := by
  unfold tailWord_5206175
  simp only [CollatzResearch.WordTrace]
  refine ⟨189884801913924593746747979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126589867942616395831165319 189884801913924593746747979)
  ·
    refine ⟨284827202870886890620121969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189884801913924593746747979 284827202870886890620121969)
    ·
      refine ⟨213620402153165167965091477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284827202870886890620121969 213620402153165167965091477)
      ·
        refine ⟨10013456350929617248363663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 213620402153165167965091477 10013456350929617248363663)
        ·
          refine ⟨15020184526394425872545495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10013456350929617248363663 15020184526394425872545495)
          ·
            refine ⟨22530276789591638808818243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15020184526394425872545495 22530276789591638808818243)
            ·
              refine ⟨33795415184387458213227365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22530276789591638808818243 33795415184387458213227365)
              ·
                refine ⟨6336640347072648414980131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33795415184387458213227365 6336640347072648414980131)
                ·
                  refine ⟨9504960520608972622470197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6336640347072648414980131 9504960520608972622470197)
                  ·
                    refine ⟨891090048807091183356581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9504960520608972622470197 891090048807091183356581)
                    ·
                      rfl

theorem cell23_5206175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_5206175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206175 prefixEnd_5206175 := by exact prefixLift 5206175
  have htrace : WordTrace (prefixWord ++ tailWord_5206175) baseStart_5206175 baseEnd_5206175 := by
    simpa [prefixWord, tailWord_5206175, baseEnd_5206175] using wordTrace_append hprefix tailTrace_5206175
  have hstable : (prefixWord ++ tailWord_5206175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206175).length < 2 ^ (prefixWord ++ tailWord_5206175).sum := by decide
  have hdescent : baseEnd_5206175 < baseStart_5206175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206205 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_5206205 : Nat := 118140960795 + 5206205 * 2 ^ 59
def prefixEnd_5206205 : Nat := 4983230072969 + 3 ^ 40 * 5206205 * 2
def baseEnd_5206205 : Nat := 891095183613636144231535

theorem tailTrace_5206205 : CollatzResearch.WordTrace tailWord_5206205 prefixEnd_5206205 891095183613636144231535 := by
  unfold tailWord_5206205
  simp only [CollatzResearch.WordTrace]
  refine ⟨189885896103815908870340069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126590597402543939246893379 189885896103815908870340069)
  ·
    refine ⟨35603605519465482913188763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189885896103815908870340069 35603605519465482913188763)
    ·
      refine ⟨53405408279198224369783145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35603605519465482913188763 53405408279198224369783145)
      ·
        refine ⟨40054056209398668277337359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53405408279198224369783145 40054056209398668277337359)
        ·
          refine ⟨60081084314098002416006039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40054056209398668277337359 60081084314098002416006039)
          ·
            refine ⟨90121626471147003624009059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60081084314098002416006039 90121626471147003624009059)
            ·
              refine ⟨135182439706720505436013589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90121626471147003624009059 135182439706720505436013589)
              ·
                refine ⟨6336676861252523692313137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135182439706720505436013589 6336676861252523692313137)
                ·
                  refine ⟨4752507645939392769234853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6336676861252523692313137 4752507645939392769234853)
                  ·
                    refine ⟨891095183613636144231535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752507645939392769234853 891095183613636144231535)
                    ·
                      rfl

theorem cell23_5206205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_5206205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206205 prefixEnd_5206205 := by exact prefixLift 5206205
  have htrace : WordTrace (prefixWord ++ tailWord_5206205) baseStart_5206205 baseEnd_5206205 := by
    simpa [prefixWord, tailWord_5206205, baseEnd_5206205] using wordTrace_append hprefix tailTrace_5206205
  have hstable : (prefixWord ++ tailWord_5206205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206205).length < 2 ^ (prefixWord ++ tailWord_5206205).sum := by decide
  have hdescent : baseEnd_5206205 < baseStart_5206205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206206 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_5206206 : Nat := 118140960795 + 5206206 * 2 ^ 59
def prefixEnd_5206206 : Nat := 4983230072969 + 3 ^ 40 * 5206206 * 2
def baseEnd_5206206 : Nat := 2673286064321562928782101

theorem tailTrace_5206206 : CollatzResearch.WordTrace tailWord_5206206 prefixEnd_5206206 2673286064321562928782101 := by
  unfold tailWord_5206206
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735741572101535755140809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126590621717874857360750981 23735741572101535755140809)
  ·
    refine ⟨17801806179076151816355607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23735741572101535755140809 17801806179076151816355607)
    ·
      refine ⟨26702709268614227724533411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17801806179076151816355607 26702709268614227724533411)
      ·
        refine ⟨40054063902921341586800117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26702709268614227724533411 40054063902921341586800117)
        ·
          refine ⟨3755068490898875773762511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40054063902921341586800117 3755068490898875773762511)
          ·
            refine ⟨5632602736348313660643767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755068490898875773762511 5632602736348313660643767)
            ·
              refine ⟨8448904104522470490965651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632602736348313660643767 8448904104522470490965651)
              ·
                refine ⟨12673356156783705736448477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448904104522470490965651 12673356156783705736448477)
                ·
                  refine ⟨4752508558793889651168179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12673356156783705736448477 4752508558793889651168179)
                  ·
                    refine ⟨7128762838190834476752269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4752508558793889651168179 7128762838190834476752269)
                    ·
                      refine ⟨2673286064321562928782101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128762838190834476752269 2673286064321562928782101)
                      ·
                        rfl

theorem cell23_5206206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_5206206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206206 prefixEnd_5206206 := by exact prefixLift 5206206
  have htrace : WordTrace (prefixWord ++ tailWord_5206206) baseStart_5206206 baseEnd_5206206 := by
    simpa [prefixWord, tailWord_5206206, baseEnd_5206206] using wordTrace_append hprefix tailTrace_5206206
  have hstable : (prefixWord ++ tailWord_5206206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206206).length < 2 ^ (prefixWord ++ tailWord_5206206).sum := by decide
  have hdescent : baseEnd_5206206 < baseStart_5206206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206208 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_5206208 : Nat := 118140960795 + 5206208 * 2 ^ 59
def prefixEnd_5206208 : Nat := 4983230072969 + 3 ^ 40 * 5206208 * 2
def baseEnd_5206208 : Nat := 2673287091282871920957091

theorem tailTrace_5206208 : CollatzResearch.WordTrace tailWord_5206208 prefixEnd_5206208 2673287091282871920957091 := by
  unfold tailWord_5206208
  simp only [CollatzResearch.WordTrace]
  refine ⟨94943002761402520191349639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126590670348536693588466185 94943002761402520191349639)
  ·
    refine ⟨142414504142103780287024459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94943002761402520191349639 142414504142103780287024459)
    ·
      refine ⟨213621756213155670430536689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142414504142103780287024459 213621756213155670430536689)
      ·
        refine ⟨160216317159866752822902517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213621756213155670430536689 160216317159866752822902517)
        ·
          refine ⟨15020279733737508077147111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160216317159866752822902517 15020279733737508077147111)
          ·
            refine ⟨22530419600606262115720667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15020279733737508077147111 22530419600606262115720667)
            ·
              refine ⟨33795629400909393173581001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22530419600606262115720667 33795629400909393173581001)
              ·
                refine ⟨25346722050682044880185751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33795629400909393173581001 25346722050682044880185751)
                ·
                  refine ⟨38020083076023067320278627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25346722050682044880185751 38020083076023067320278627)
                  ·
                    refine ⟨57030124614034600980417941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38020083076023067320278627 57030124614034600980417941)
                    ·
                      refine ⟨2673287091282871920957091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57030124614034600980417941 2673287091282871920957091)
                      ·
                        rfl

theorem cell23_5206208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_5206208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206208 prefixEnd_5206208 := by exact prefixLift 5206208
  have htrace : WordTrace (prefixWord ++ tailWord_5206208) baseStart_5206208 baseEnd_5206208 := by
    simpa [prefixWord, tailWord_5206208, baseEnd_5206208] using wordTrace_append hprefix tailTrace_5206208
  have hstable : (prefixWord ++ tailWord_5206208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206208).length < 2 ^ (prefixWord ++ tailWord_5206208).sum := by decide
  have hdescent : baseEnd_5206208 < baseStart_5206208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206218 : List Nat := [3, 1, 2, 1, 3, 1, 4, 8]
def baseStart_5206218 : Nat := 118140960795 + 5206218 * 2 ^ 59
def prefixEnd_5206218 : Nat := 4983230072969 + 3 ^ 40 * 5206218 * 2
def baseEnd_5206218 : Nat := 99010823188496921549335

theorem tailTrace_5206218 : CollatzResearch.WordTrace tailWord_5206218 prefixEnd_5206218 99010823188496921549335 := by
  unfold tailWord_5206218
  simp only [CollatzResearch.WordTrace]
  refine ⟨47471592563192203022640827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126590913501845874727042205 47471592563192203022640827)
  ·
    refine ⟨71207388844788304533961241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47471592563192203022640827 71207388844788304533961241)
    ·
      refine ⟨53405541633591228400470931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71207388844788304533961241 53405541633591228400470931)
      ·
        refine ⟨80108312450386842600706397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53405541633591228400470931 80108312450386842600706397)
        ·
          refine ⟨30040617168895065975264899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80108312450386842600706397 30040617168895065975264899)
          ·
            refine ⟨45060925753342598962897349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30040617168895065975264899 45060925753342598962897349)
            ·
              refine ⟨8448923578751737305543253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45060925753342598962897349 8448923578751737305543253)
              ·
                refine ⟨99010823188496921549335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8448923578751737305543253 99010823188496921549335)
                ·
                  rfl

theorem cell23_5206218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_5206218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206218 prefixEnd_5206218 := by exact prefixLift 5206218
  have htrace : WordTrace (prefixWord ++ tailWord_5206218) baseStart_5206218 baseEnd_5206218 := by
    simpa [prefixWord, tailWord_5206218, baseEnd_5206218] using wordTrace_append hprefix tailTrace_5206218
  have hstable : (prefixWord ++ tailWord_5206218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206218).length < 2 ^ (prefixWord ++ tailWord_5206218).sum := by decide
  have hdescent : baseEnd_5206218 < baseStart_5206218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206222 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_5206222 : Nat := 118140960795 + 5206222 * 2 ^ 59
def prefixEnd_5206222 : Nat := 4983230072969 + 3 ^ 40 * 5206222 * 2
def baseEnd_5206222 : Nat := 891098093337344955394009

theorem tailTrace_5206222 : CollatzResearch.WordTrace tailWord_5206222 prefixEnd_5206222 891098093337344955394009 := by
  unfold tailWord_5206222
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735814518094290096713615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126591010763169547182472613 23735814518094290096713615)
  ·
    refine ⟨35603721777141435145070423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23735814518094290096713615 35603721777141435145070423)
    ·
      refine ⟨53405582665712152717605635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35603721777141435145070423 53405582665712152717605635)
      ·
        refine ⟨80108373998568229076408453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53405582665712152717605635 80108373998568229076408453)
        ·
          refine ⟨15020320124731542951826585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80108373998568229076408453 15020320124731542951826585)
          ·
            refine ⟨11265240093548657213869939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15020320124731542951826585 11265240093548657213869939)
            ·
              refine ⟨16897860140322985820804909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11265240093548657213869939 16897860140322985820804909)
              ·
                refine ⟨6336697552621119682801841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16897860140322985820804909 6336697552621119682801841)
                ·
                  refine ⟨4752523164465839762101381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6336697552621119682801841 4752523164465839762101381)
                  ·
                    refine ⟨891098093337344955394009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752523164465839762101381 891098093337344955394009)
                    ·
                      rfl

theorem cell23_5206222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_5206222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206222 prefixEnd_5206222 := by exact prefixLift 5206222
  have htrace : WordTrace (prefixWord ++ tailWord_5206222) baseStart_5206222 baseEnd_5206222 := by
    simpa [prefixWord, tailWord_5206222, baseEnd_5206222] using wordTrace_append hprefix tailTrace_5206222
  have hstable : (prefixWord ++ tailWord_5206222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206222).length < 2 ^ (prefixWord ++ tailWord_5206222).sum := by decide
  have hdescent : baseEnd_5206222 < baseStart_5206222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206229 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5206229 : Nat := 118140960795 + 5206229 * 2 ^ 59
def prefixEnd_5206229 : Nat := 4983230072969 + 3 ^ 40 * 5206229 * 2
def baseEnd_5206229 : Nat := 2673297874376616338794495

theorem tailTrace_5206229 : CollatzResearch.WordTrace tailWord_5206229 prefixEnd_5206229 2673297874376616338794495 := by
  unfold tailWord_5206229
  simp only [CollatzResearch.WordTrace]
  refine ⟨189886771455728960969213741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126591180970485973979475827 189886771455728960969213741)
  ·
    refine ⟨71207539295898360363455153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189886771455728960969213741 71207539295898360363455153)
    ·
      refine ⟨53405654471923770272591365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71207539295898360363455153 53405654471923770272591365)
      ·
        refine ⟨10013560213485706926110881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53405654471923770272591365 10013560213485706926110881)
        ·
          refine ⟨7510170160114280194583161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10013560213485706926110881 7510170160114280194583161)
          ·
            refine ⟨5632627620085710145937371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7510170160114280194583161 5632627620085710145937371)
            ·
              refine ⟨8448941430128565218906057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632627620085710145937371 8448941430128565218906057)
              ·
                refine ⟨6336706072596423914179543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8448941430128565218906057 6336706072596423914179543)
                ·
                  refine ⟨9505059108894635871269315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6336706072596423914179543 9505059108894635871269315)
                  ·
                    refine ⟨14257588663341953806903973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9505059108894635871269315 14257588663341953806903973)
                    ·
                      refine ⟨2673297874376616338794495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14257588663341953806903973 2673297874376616338794495)
                      ·
                        rfl

theorem cell23_5206229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5206229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206229 prefixEnd_5206229 := by exact prefixLift 5206229
  have htrace : WordTrace (prefixWord ++ tailWord_5206229) baseStart_5206229 baseEnd_5206229 := by
    simpa [prefixWord, tailWord_5206229, baseEnd_5206229] using wordTrace_append hprefix tailTrace_5206229
  have hstable : (prefixWord ++ tailWord_5206229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206229).length < 2 ^ (prefixWord ++ tailWord_5206229).sum := by decide
  have hdescent : baseEnd_5206229 < baseStart_5206229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206232 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_5206232 : Nat := 118140960795 + 5206232 * 2 ^ 59
def prefixEnd_5206232 : Nat := 4983230072969 + 3 ^ 40 * 5206232 * 2
def baseEnd_5206232 : Nat := 2673299414818579827056981

theorem tailTrace_5206232 : CollatzResearch.WordTrace tailWord_5206232 prefixEnd_5206232 2673299414818579827056981 := by
  unfold tailWord_5206232
  simp only [CollatzResearch.WordTrace]
  refine ⟨94943440437359046240786475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126591253916478728321048633 94943440437359046240786475)
  ·
    refine ⟨142415160656038569361179713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94943440437359046240786475 142415160656038569361179713)
    ·
      refine ⟨106811370492028927020884785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142415160656038569361179713 106811370492028927020884785)
      ·
        refine ⟨80108527869021695265663589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106811370492028927020884785 80108527869021695265663589)
        ·
          refine ⟨15020348975441567862311923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80108527869021695265663589 15020348975441567862311923)
          ·
            refine ⟨22530523463162351793467885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15020348975441567862311923 22530523463162351793467885)
            ·
              refine ⟨8448946298685881922550457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22530523463162351793467885 8448946298685881922550457)
              ·
                refine ⟨6336709724014411441912843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8448946298685881922550457 6336709724014411441912843)
                ·
                  refine ⟨9505064586021617162869265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6336709724014411441912843 9505064586021617162869265)
                  ·
                    refine ⟨7128798439516212872151949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9505064586021617162869265 7128798439516212872151949)
                    ·
                      refine ⟨2673299414818579827056981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128798439516212872151949 2673299414818579827056981)
                      ·
                        rfl

theorem cell23_5206232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_5206232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206232 prefixEnd_5206232 := by exact prefixLift 5206232
  have htrace : WordTrace (prefixWord ++ tailWord_5206232) baseStart_5206232 baseEnd_5206232 := by
    simpa [prefixWord, tailWord_5206232, baseEnd_5206232] using wordTrace_append hprefix tailTrace_5206232
  have hstable : (prefixWord ++ tailWord_5206232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206232).length < 2 ^ (prefixWord ++ tailWord_5206232).sum := by decide
  have hdescent : baseEnd_5206232 < baseStart_5206232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206245 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_5206245 : Nat := 118140960795 + 5206245 * 2 ^ 59
def prefixEnd_5206245 : Nat := 4983230072969 + 3 ^ 40 * 5206245 * 2
def baseEnd_5206245 : Nat := 2673306090067088276194421

theorem tailTrace_5206245 : CollatzResearch.WordTrace tailWord_5206245 prefixEnd_5206245 2673306090067088276194421 := by
  unfold tailWord_5206245
  simp only [CollatzResearch.WordTrace]
  refine ⟨189887355023670995701796189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126591570015780663801197459 189887355023670995701796189)
  ·
    refine ⟨71207758133876623388173571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189887355023670995701796189 71207758133876623388173571)
    ·
      refine ⟨106811637200814935082260357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71207758133876623388173571 106811637200814935082260357)
      ·
        refine ⟨20027181975152800327923817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106811637200814935082260357 20027181975152800327923817)
        ·
          refine ⟨15020386481364600245942863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20027181975152800327923817 15020386481364600245942863)
          ·
            refine ⟨22530579722046900368914295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15020386481364600245942863 22530579722046900368914295)
            ·
              refine ⟨33795869583070350553371443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22530579722046900368914295 33795869583070350553371443)
              ·
                refine ⟨50693804374605525830057165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33795869583070350553371443 50693804374605525830057165)
                ·
                  refine ⟨19010176640477072186271437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50693804374605525830057165 19010176640477072186271437)
                  ·
                    refine ⟨7128816240178902069851789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19010176640477072186271437 7128816240178902069851789)
                    ·
                      refine ⟨2673306090067088276194421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128816240178902069851789 2673306090067088276194421)
                      ·
                        rfl

theorem cell23_5206245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_5206245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206245 prefixEnd_5206245 := by exact prefixLift 5206245
  have htrace : WordTrace (prefixWord ++ tailWord_5206245) baseStart_5206245 baseEnd_5206245 := by
    simpa [prefixWord, tailWord_5206245, baseEnd_5206245] using wordTrace_append hprefix tailTrace_5206245
  have hstable : (prefixWord ++ tailWord_5206245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206245).length < 2 ^ (prefixWord ++ tailWord_5206245).sum := by decide
  have hdescent : baseEnd_5206245 < baseStart_5206245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206262 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_5206262 : Nat := 118140960795 + 5206262 * 2 ^ 59
def prefixEnd_5206262 : Nat := 4983230072969 + 3 ^ 40 * 5206262 * 2
def baseEnd_5206262 : Nat := 2673314819238214709681843

theorem tailTrace_5206262 : CollatzResearch.WordTrace tailWord_5206262 prefixEnd_5206262 2673314819238214709681843 := by
  unfold tailWord_5206262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867998441538087975322815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126591983376406271736776693 11867998441538087975322815)
  ·
    refine ⟨17801997662307131962984223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11867998441538087975322815 17801997662307131962984223)
    ·
      refine ⟨26702996493460697944476335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17801997662307131962984223 26702996493460697944476335)
      ·
        refine ⟨40054494740191046916714503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26702996493460697944476335 40054494740191046916714503)
        ·
          refine ⟨60081742110286570375071755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40054494740191046916714503 60081742110286570375071755)
          ·
            refine ⟨90122613165429855562607633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60081742110286570375071755 90122613165429855562607633)
            ·
              refine ⟨67591959874072391671955725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90122613165429855562607633 67591959874072391671955725)
              ·
                refine ⟨25346984952777146876983397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67591959874072391671955725 25346984952777146876983397)
                ·
                  refine ⟨4752559678645715039434387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25346984952777146876983397 4752559678645715039434387)
                  ·
                    refine ⟨7128839517968572559151581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4752559678645715039434387 7128839517968572559151581)
                    ·
                      refine ⟨2673314819238214709681843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128839517968572559151581 2673314819238214709681843)
                      ·
                        rfl

theorem cell23_5206262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_5206262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206262 prefixEnd_5206262 := by exact prefixLift 5206262
  have htrace : WordTrace (prefixWord ++ tailWord_5206262) baseStart_5206262 baseEnd_5206262 := by
    simpa [prefixWord, tailWord_5206262, baseEnd_5206262] using wordTrace_append hprefix tailTrace_5206262
  have hstable : (prefixWord ++ tailWord_5206262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206262).length < 2 ^ (prefixWord ++ tailWord_5206262).sum := by decide
  have hdescent : baseEnd_5206262 < baseStart_5206262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206279 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5206279 : Nat := 118140960795 + 5206279 * 2 ^ 59
def prefixEnd_5206279 : Nat := 4983230072969 + 3 ^ 40 * 5206279 * 2
def baseEnd_5206279 : Nat := 2673323548409341143169265

theorem tailTrace_5206279 : CollatzResearch.WordTrace tailWord_5206279 prefixEnd_5206279 2673323548409341143169265 := by
  unfold tailWord_5206279
  simp only [CollatzResearch.WordTrace]
  refine ⟨189888595105547819508533891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126592396737031879672355927 189888595105547819508533891)
  ·
    refine ⟨284832892658321729262800837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189888595105547819508533891 284832892658321729262800837)
    ·
      refine ⟨53406167373435324236775157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284832892658321729262800837 53406167373435324236775157)
      ·
        refine ⟨5006828191259561647197671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53406167373435324236775157 5006828191259561647197671)
        ·
          refine ⟨7510242286889342470796507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5006828191259561647197671 7510242286889342470796507)
          ·
            refine ⟨11265363430334013706194761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510242286889342470796507 11265363430334013706194761)
            ·
              refine ⟨8449022572750510279646071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11265363430334013706194761 8449022572750510279646071)
              ·
                refine ⟨12673533859125765419469107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449022572750510279646071 12673533859125765419469107)
                ·
                  refine ⟨19010300788688648129203661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12673533859125765419469107 19010300788688648129203661)
                  ·
                    refine ⟨7128862795758243048451373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19010300788688648129203661 7128862795758243048451373)
                    ·
                      refine ⟨2673323548409341143169265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128862795758243048451373 2673323548409341143169265)
                      ·
                        rfl

theorem cell23_5206279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5206279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206279 prefixEnd_5206279 := by exact prefixLift 5206279
  have htrace : WordTrace (prefixWord ++ tailWord_5206279) baseStart_5206279 baseEnd_5206279 := by
    simpa [prefixWord, tailWord_5206279, baseEnd_5206279] using wordTrace_append hprefix tailTrace_5206279
  have hstable : (prefixWord ++ tailWord_5206279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206279).length < 2 ^ (prefixWord ++ tailWord_5206279).sum := by decide
  have hdescent : baseEnd_5206279 < baseStart_5206279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206306 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_5206306 : Nat := 118140960795 + 5206306 * 2 ^ 59
def prefixEnd_5206306 : Nat := 4983230072969 + 3 ^ 40 * 5206306 * 2
def baseEnd_5206306 : Nat := 2673337412387012537531641

theorem tailTrace_5206306 : CollatzResearch.WordTrace tailWord_5206306 prefixEnd_5206306 2673337412387012537531641 := by
  unfold tailWord_5206306
  simp only [CollatzResearch.WordTrace]
  refine ⟨47472394969112500779941693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126593053250966668746511181 47472394969112500779941693)
  ·
    refine ⟨17802148113417187792478135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47472394969112500779941693 17802148113417187792478135)
    ·
      refine ⟨26703222170125781688717203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17802148113417187792478135 26703222170125781688717203)
      ·
        refine ⟨40054833255188672533075805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26703222170125781688717203 40054833255188672533075805)
        ·
          refine ⟨15020562470695752199903427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40054833255188672533075805 15020562470695752199903427)
          ·
            refine ⟨22530843706043628299855141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15020562470695752199903427 22530843706043628299855141)
            ·
              refine ⟨4224533194883180306222839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22530843706043628299855141 4224533194883180306222839)
              ·
                refine ⟨6336799792324770459334259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224533194883180306222839 6336799792324770459334259)
                ·
                  refine ⟨9505199688487155689001389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6336799792324770459334259 9505199688487155689001389)
                  ·
                    refine ⟨3564449883182683383375521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9505199688487155689001389 3564449883182683383375521)
                    ·
                      refine ⟨2673337412387012537531641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564449883182683383375521 2673337412387012537531641)
                      ·
                        rfl

theorem cell23_5206306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_5206306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206306 prefixEnd_5206306 := by exact prefixLift 5206306
  have htrace : WordTrace (prefixWord ++ tailWord_5206306) baseStart_5206306 baseEnd_5206306 := by
    simpa [prefixWord, tailWord_5206306, baseEnd_5206306] using wordTrace_append hprefix tailTrace_5206306
  have hstable : (prefixWord ++ tailWord_5206306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206306).length < 2 ^ (prefixWord ++ tailWord_5206306).sum := by decide
  have hdescent : baseEnd_5206306 < baseStart_5206306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206319 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 2, 2, 2]
def baseStart_5206319 : Nat := 118140960795 + 5206319 * 2 ^ 59
def prefixEnd_5206319 : Nat := 4983230072969 + 3 ^ 40 * 5206319 * 2
def baseEnd_5206319 : Nat := 2673344087635520986669081

theorem tailTrace_5206319 : CollatzResearch.WordTrace tailWord_5206319 prefixEnd_5206319 2673344087635520986669081 := by
  unfold tailWord_5206319
  simp only [CollatzResearch.WordTrace]
  refine ⟨189890054025402906339990011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126593369350268604226660007 189890054025402906339990011)
  ·
    refine ⟨284835081038104359509985017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189890054025402906339990011 284835081038104359509985017)
    ·
      refine ⟨213626310778578269632488763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284835081038104359509985017 213626310778578269632488763)
      ·
        refine ⟨320439466167867404448733145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213626310778578269632488763 320439466167867404448733145)
        ·
          refine ⟨240329599625900553336549859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320439466167867404448733145 240329599625900553336549859)
          ·
            refine ⟨360494399438850830004824789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240329599625900553336549859 360494399438850830004824789)
            ·
              refine ⟨8449087486848066328238081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 360494399438850830004824789 8449087486848066328238081)
              ·
                refine ⟨6336815615136049746178561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8449087486848066328238081 6336815615136049746178561)
                ·
                  refine ⟨4752611711352037309633921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6336815615136049746178561 4752611711352037309633921)
                  ·
                    refine ⟨3564458783514027982225441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4752611711352037309633921 3564458783514027982225441)
                    ·
                      refine ⟨2673344087635520986669081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564458783514027982225441 2673344087635520986669081)
                      ·
                        rfl

theorem cell23_5206319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 2, 2].length) (baseStart_5206319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206319 prefixEnd_5206319 := by exact prefixLift 5206319
  have htrace : WordTrace (prefixWord ++ tailWord_5206319) baseStart_5206319 baseEnd_5206319 := by
    simpa [prefixWord, tailWord_5206319, baseEnd_5206319] using wordTrace_append hprefix tailTrace_5206319
  have hstable : (prefixWord ++ tailWord_5206319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206319).length < 2 ^ (prefixWord ++ tailWord_5206319).sum := by decide
  have hdescent : baseEnd_5206319 < baseStart_5206319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206325 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 7]
def baseStart_5206325 : Nat := 118140960795 + 5206325 * 2 ^ 59
def prefixEnd_5206325 : Nat := 4983230072969 + 3 ^ 40 * 5206325 * 2
def baseEnd_5206325 : Nat := 297038574279938662577117

theorem tailTrace_5206325 : CollatzResearch.WordTrace tailWord_5206325 prefixEnd_5206325 297038574279938662577117 := by
  unfold tailWord_5206325
  simp only [CollatzResearch.WordTrace]
  refine ⟨189890272863381169364708429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126593515242254112909805619 189890272863381169364708429)
  ·
    refine ⟨71208852323767938511765661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189890272863381169364708429 71208852323767938511765661)
    ·
      refine ⟨26703319621412976941912123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71208852323767938511765661 26703319621412976941912123)
      ·
        refine ⟨40054979432119465412868185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26703319621412976941912123 40054979432119465412868185)
        ·
          refine ⟨30041234574089599059651139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40054979432119465412868185 30041234574089599059651139)
          ·
            refine ⟨45061851861134398589476709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30041234574089599059651139 45061851861134398589476709)
            ·
              refine ⟨8449097223962699735526883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45061851861134398589476709 8449097223962699735526883)
              ·
                refine ⟨12673645835944049603290325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449097223962699735526883 12673645835944049603290325)
                ·
                  refine ⟨297038574279938662577117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12673645835944049603290325 297038574279938662577117)
                  ·
                    rfl

theorem cell23_5206325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_5206325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206325 prefixEnd_5206325 := by exact prefixLift 5206325
  have htrace : WordTrace (prefixWord ++ tailWord_5206325) baseStart_5206325 baseEnd_5206325 := by
    simpa [prefixWord, tailWord_5206325, baseEnd_5206325] using wordTrace_append hprefix tailTrace_5206325
  have hstable : (prefixWord ++ tailWord_5206325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206325).length < 2 ^ (prefixWord ++ tailWord_5206325).sum := by decide
  have hdescent : baseEnd_5206325 < baseStart_5206325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206335 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 3]
def baseStart_5206335 : Nat := 118140960795 + 5206335 * 2 ^ 59
def prefixEnd_5206335 : Nat := 4983230072969 + 3 ^ 40 * 5206335 * 2
def baseEnd_5206335 : Nat := 2673352303325992924069007

theorem tailTrace_5206335 : CollatzResearch.WordTrace tailWord_5206335 prefixEnd_5206335 2673352303325992924069007 := by
  unfold tailWord_5206335
  simp only [CollatzResearch.WordTrace]
  refine ⟨189890637593344941072572459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126593758395563294048381639 189890637593344941072572459)
  ·
    refine ⟨284835956390017411608858689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189890637593344941072572459 284835956390017411608858689)
    ·
      refine ⟨213626967292513058706644017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284835956390017411608858689 213626967292513058706644017)
      ·
        refine ⟨160220225469384794029983013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213626967292513058706644017 160220225469384794029983013)
        ·
          refine ⟨30041292275509648880621815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160220225469384794029983013 30041292275509648880621815)
          ·
            refine ⟨45061938413264473320932723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30041292275509648880621815 45061938413264473320932723)
            ·
              refine ⟨67592907619896709981399085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45061938413264473320932723 67592907619896709981399085)
              ·
                refine ⟨25347340357461266243024657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67592907619896709981399085 25347340357461266243024657)
                ·
                  refine ⟨19010505268095949682268493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25347340357461266243024657 19010505268095949682268493)
                  ·
                    refine ⟨7128939475535981130850685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19010505268095949682268493 7128939475535981130850685)
                    ·
                      refine ⟨2673352303325992924069007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7128939475535981130850685 2673352303325992924069007)
                      ·
                        rfl

theorem cell23_5206335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_5206335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206335 prefixEnd_5206335 := by exact prefixLift 5206335
  have htrace : WordTrace (prefixWord ++ tailWord_5206335) baseStart_5206335 baseEnd_5206335 := by
    simpa [prefixWord, tailWord_5206335, baseEnd_5206335] using wordTrace_append hprefix tailTrace_5206335
  have hstable : (prefixWord ++ tailWord_5206335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206335).length < 2 ^ (prefixWord ++ tailWord_5206335).sum := by decide
  have hdescent : baseEnd_5206335 < baseStart_5206335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206412 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_5206412 : Nat := 118140960795 + 5206412 * 2 ^ 59
def prefixEnd_5206412 : Nat := 4983230072969 + 3 ^ 40 * 5206412 * 2
def baseEnd_5206412 : Nat := 2673391841336389122806153

theorem tailTrace_5206412 : CollatzResearch.WordTrace tailWord_5206412 prefixEnd_5206412 2673391841336389122806153 := by
  unfold tailWord_5206412
  simp only [CollatzResearch.WordTrace]
  refine ⟨94946723007032991611562745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126595630676043988815416993 94946723007032991611562745)
  ·
    refine ⟨71210042255274743708672059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94946723007032991611562745 71210042255274743708672059)
    ·
      refine ⟨106815063382912115563008089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71210042255274743708672059 106815063382912115563008089)
      ·
        refine ⟨80111297537184086672256067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106815063382912115563008089 80111297537184086672256067)
        ·
          refine ⟨120166946305776130008384101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80111297537184086672256067 120166946305776130008384101)
          ·
            refine ⟨22531302432333024376572019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120166946305776130008384101 22531302432333024376572019)
            ·
              refine ⟨33796953648499536564858029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22531302432333024376572019 33796953648499536564858029)
              ·
                refine ⟨12673857618187326211821761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33796953648499536564858029 12673857618187326211821761)
                ·
                  refine ⟨9505393213640494658866321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12673857618187326211821761 9505393213640494658866321)
                  ·
                    refine ⟨7129044910230370994149741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9505393213640494658866321 7129044910230370994149741)
                    ·
                      refine ⟨2673391841336389122806153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7129044910230370994149741 2673391841336389122806153)
                      ·
                        rfl

theorem cell23_5206412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_5206412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206412 prefixEnd_5206412 := by exact prefixLift 5206412
  have htrace : WordTrace (prefixWord ++ tailWord_5206412) baseStart_5206412 baseEnd_5206412 := by
    simpa [prefixWord, tailWord_5206412, baseEnd_5206412] using wordTrace_append hprefix tailTrace_5206412
  have hstable : (prefixWord ++ tailWord_5206412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206412).length < 2 ^ (prefixWord ++ tailWord_5206412).sum := by decide
  have hdescent : baseEnd_5206412 < baseStart_5206412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206432 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 6]
def baseStart_5206432 : Nat := 118140960795 + 5206432 * 2 ^ 59
def prefixEnd_5206432 : Nat := 4983230072969 + 3 ^ 40 * 5206432 * 2
def baseEnd_5206432 : Nat := 297044678994386560506229

theorem tailTrace_5206432 : CollatzResearch.WordTrace tailWord_5206432 prefixEnd_5206432 297044678994386560506229 := by
  unfold tailWord_5206432
  simp only [CollatzResearch.WordTrace]
  refine ⟨94947087736996763319426775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126596116982662351092569033 94947087736996763319426775)
  ·
    refine ⟨142420631605495144979140163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94947087736996763319426775 142420631605495144979140163)
    ·
      refine ⟨213630947408242717468710245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142420631605495144979140163 213630947408242717468710245)
      ·
        refine ⟨40055802639045509525383171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213630947408242717468710245 40055802639045509525383171)
        ·
          refine ⟨60083703958568264288074757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40055802639045509525383171 60083703958568264288074757)
          ·
            refine ⟨11265694492231549554014017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60083703958568264288074757 11265694492231549554014017)
            ·
              refine ⟨8449270869173662165510513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11265694492231549554014017 8449270869173662165510513)
              ·
                refine ⟨6336953151880246624132885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8449270869173662165510513 6336953151880246624132885)
                ·
                  refine ⟨297044678994386560506229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6336953151880246624132885 297044678994386560506229)
                  ·
                    rfl

theorem cell23_5206432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 6].length) (baseStart_5206432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206432 prefixEnd_5206432 := by exact prefixLift 5206432
  have htrace : WordTrace (prefixWord ++ tailWord_5206432) baseStart_5206432 baseEnd_5206432 := by
    simpa [prefixWord, tailWord_5206432, baseEnd_5206432] using wordTrace_append hprefix tailTrace_5206432
  have hstable : (prefixWord ++ tailWord_5206432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206432).length < 2 ^ (prefixWord ++ tailWord_5206432).sum := by decide
  have hdescent : baseEnd_5206432 < baseStart_5206432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206436 : List Nat := [2, 3, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_5206436 : Nat := 118140960795 + 5206436 * 2 ^ 59
def prefixEnd_5206436 : Nat := 4983230072969 + 3 ^ 40 * 5206436 * 2
def baseEnd_5206436 : Nat := 891134721624032342968681

theorem tailTrace_5206436 : CollatzResearch.WordTrace tailWord_5206436 prefixEnd_5206436 891134721624032342968681 := by
  unfold tailWord_5206436
  simp only [CollatzResearch.WordTrace]
  refine ⟨94947160682989517660999581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126596214243986023547999441 94947160682989517660999581)
  ·
    refine ⟨35605185256121069122874843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94947160682989517660999581 35605185256121069122874843)
    ·
      refine ⟨53407777884181603684312265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35605185256121069122874843 53407777884181603684312265)
      ·
        refine ⟨40055833413136202763234199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53407777884181603684312265 40055833413136202763234199)
        ·
          refine ⟨60083750119704304144851299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40055833413136202763234199 60083750119704304144851299)
          ·
            refine ⟨90125625179556456217276949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60083750119704304144851299 90125625179556456217276949)
            ·
              refine ⟨4224638680291708885184857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90125625179556456217276949 4224638680291708885184857)
              ·
                refine ⟨3168479010218781663888643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4224638680291708885184857 3168479010218781663888643)
                ·
                  refine ⟨4752718515328172495832965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168479010218781663888643 4752718515328172495832965)
                  ·
                    refine ⟨891134721624032342968681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752718515328172495832965 891134721624032342968681)
                    ·
                      rfl

theorem cell23_5206436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_5206436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206436 prefixEnd_5206436 := by exact prefixLift 5206436
  have htrace : WordTrace (prefixWord ++ tailWord_5206436) baseStart_5206436 baseEnd_5206436 := by
    simpa [prefixWord, tailWord_5206436, baseEnd_5206436] using wordTrace_append hprefix tailTrace_5206436
  have hstable : (prefixWord ++ tailWord_5206436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206436).length < 2 ^ (prefixWord ++ tailWord_5206436).sum := by decide
  have hdescent : baseEnd_5206436 < baseStart_5206436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206462 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_5206462 : Nat := 118140960795 + 5206462 * 2 ^ 59
def prefixEnd_5206462 : Nat := 4983230072969 + 3 ^ 40 * 5206462 * 2
def baseEnd_5206462 : Nat := 891139171789704642393641

theorem tailTrace_5206462 : CollatzResearch.WordTrace tailWord_5206462 prefixEnd_5206462 891139171789704642393641 := by
  unfold tailWord_5206462
  simp only [CollatzResearch.WordTrace]
  refine ⟨23736908707985605220305705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126596846442589894508297093 23736908707985605220305705)
  ·
    refine ⟨17802681530989203915229279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23736908707985605220305705 17802681530989203915229279)
    ·
      refine ⟨26704022296483805872843919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17802681530989203915229279 26704022296483805872843919)
      ·
        refine ⟨40056033444725708809265879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26704022296483805872843919 40056033444725708809265879)
        ·
          refine ⟨60084050167088563213898819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40056033444725708809265879 60084050167088563213898819)
          ·
            refine ⟨90126075250632844820848229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60084050167088563213898819 90126075250632844820848229)
            ·
              refine ⟨16898639109493658403909043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90126075250632844820848229 16898639109493658403909043)
              ·
                refine ⟨25347958664240487605863565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16898639109493658403909043 25347958664240487605863565)
                ·
                  refine ⟨9505484499090182852198837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25347958664240487605863565 9505484499090182852198837)
                  ·
                    refine ⟨891139171789704642393641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9505484499090182852198837 891139171789704642393641)
                    ·
                      rfl

theorem cell23_5206462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_5206462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206462 prefixEnd_5206462 := by exact prefixLift 5206462
  have htrace : WordTrace (prefixWord ++ tailWord_5206462) baseStart_5206462 baseEnd_5206462 := by
    simpa [prefixWord, tailWord_5206462, baseEnd_5206462] using wordTrace_append hprefix tailTrace_5206462
  have hstable : (prefixWord ++ tailWord_5206462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206462).length < 2 ^ (prefixWord ++ tailWord_5206462).sum := by decide
  have hdescent : baseEnd_5206462 < baseStart_5206462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206486 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_5206486 : Nat := 118140960795 + 5206486 * 2 ^ 59
def prefixEnd_5206486 : Nat := 4983230072969 + 3 ^ 40 * 5206486 * 2
def baseEnd_5206486 : Nat := 2673429838904821833280813

theorem tailTrace_5206486 : CollatzResearch.WordTrace tailWord_5206486 prefixEnd_5206486 2673429838904821833280813 := by
  unfold tailWord_5206486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11868509063487368366332457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126597430010531929240879541 11868509063487368366332457)
  ·
    refine ⟨8901381797615526274749343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11868509063487368366332457 8901381797615526274749343)
    ·
      refine ⟨13352072696423289412124015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8901381797615526274749343 13352072696423289412124015)
      ·
        refine ⟨20028109044634934118186023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13352072696423289412124015 20028109044634934118186023)
        ·
          refine ⟨30042163566952401177279035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20028109044634934118186023 30042163566952401177279035)
          ·
            refine ⟨45063245350428601765918553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30042163566952401177279035 45063245350428601765918553)
            ·
              refine ⟨33797434012821451324438915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45063245350428601765918553 33797434012821451324438915)
              ·
                refine ⟨50696151019232176986658373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33797434012821451324438915 50696151019232176986658373)
                ·
                  refine ⟨9505528316106033184998445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50696151019232176986658373 9505528316106033184998445)
                  ·
                    refine ⟨3564573118539762444374417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9505528316106033184998445 3564573118539762444374417)
                    ·
                      refine ⟨2673429838904821833280813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564573118539762444374417 2673429838904821833280813)
                      ·
                        rfl

theorem cell23_5206486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_5206486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206486 prefixEnd_5206486 := by exact prefixLift 5206486
  have htrace : WordTrace (prefixWord ++ tailWord_5206486) baseStart_5206486 baseEnd_5206486 := by
    simpa [prefixWord, tailWord_5206486, baseEnd_5206486] using wordTrace_append hprefix tailTrace_5206486
  have hstable : (prefixWord ++ tailWord_5206486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206486).length < 2 ^ (prefixWord ++ tailWord_5206486).sum := by decide
  have hdescent : baseEnd_5206486 < baseStart_5206486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206509 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_5206509 : Nat := 118140960795 + 5206509 * 2 ^ 59
def prefixEnd_5206509 : Nat := 4983230072969 + 3 ^ 40 * 5206509 * 2
def baseEnd_5206509 : Nat := 891147216319958414431069

theorem tailTrace_5206509 : CollatzResearch.WordTrace tailWord_5206509 prefixEnd_5206509 891147216319958414431069 := by
  unfold tailWord_5206509
  simp only [CollatzResearch.WordTrace]
  refine ⟨189896983894714568789406581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126597989263143045859604387 189896983894714568789406581)
  ·
    refine ⟨17802842240129490824006867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189896983894714568789406581 17802842240129490824006867)
    ·
      refine ⟨26704263360194236236010301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17802842240129490824006867 26704263360194236236010301)
      ·
        refine ⟨10014098760072838588503863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26704263360194236236010301 10014098760072838588503863)
        ·
          refine ⟨15021148140109257882755795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10014098760072838588503863 15021148140109257882755795)
          ·
            refine ⟨22531722210163886824133693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15021148140109257882755795 22531722210163886824133693)
            ·
              refine ⟨8449395828811457559050135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22531722210163886824133693 8449395828811457559050135)
              ·
                refine ⟨12674093743217186338575203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449395828811457559050135 12674093743217186338575203)
                ·
                  refine ⟨19011140614825779507862805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12674093743217186338575203 19011140614825779507862805)
                  ·
                    refine ⟨891147216319958414431069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19011140614825779507862805 891147216319958414431069)
                    ·
                      rfl

theorem cell23_5206509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_5206509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206509 prefixEnd_5206509 := by exact prefixLift 5206509
  have htrace : WordTrace (prefixWord ++ tailWord_5206509) baseStart_5206509 baseEnd_5206509 := by
    simpa [prefixWord, tailWord_5206509, baseEnd_5206509] using wordTrace_append hprefix tailTrace_5206509
  have hstable : (prefixWord ++ tailWord_5206509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206509).length < 2 ^ (prefixWord ++ tailWord_5206509).sum := by decide
  have hdescent : baseEnd_5206509 < baseStart_5206509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206533 : List Nat := [1, 3, 1, 1, 2, 2, 5, 3, 1, 2, 2]
def baseStart_5206533 : Nat := 118140960795 + 5206533 * 2 ^ 59
def prefixEnd_5206533 : Nat := 4983230072969 + 3 ^ 40 * 5206533 * 2
def baseEnd_5206533 : Nat := 2673453972495583149393097

theorem tailTrace_5206533 : CollatzResearch.WordTrace tailWord_5206533 prefixEnd_5206533 2673453972495583149393097 := by
  unfold tailWord_5206533
  simp only [CollatzResearch.WordTrace]
  refine ⟨189897859246627620888280253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126598572831085080592186835 189897859246627620888280253)
  ·
    refine ⟨71211697217485357833105095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189897859246627620888280253 71211697217485357833105095)
    ·
      refine ⟨106817545826228036749657643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71211697217485357833105095 106817545826228036749657643)
      ·
        refine ⟨160226318739342055124486465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106817545826228036749657643 160226318739342055124486465)
        ·
          refine ⟨120169739054506541343364849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160226318739342055124486465 120169739054506541343364849)
          ·
            refine ⟨90127304290879906007523637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120169739054506541343364849 90127304290879906007523637)
            ·
              refine ⟨8449434777269991188205341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90127304290879906007523637 8449434777269991188205341)
              ·
                refine ⟨3168538041476246695577003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8449434777269991188205341 3168538041476246695577003)
                ·
                  refine ⟨4752807062214370043365505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168538041476246695577003 4752807062214370043365505)
                  ·
                    refine ⟨3564605296660777532524129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4752807062214370043365505 3564605296660777532524129)
                    ·
                      refine ⟨2673453972495583149393097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564605296660777532524129 2673453972495583149393097)
                      ·
                        rfl

theorem cell23_5206533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_5206533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206533 prefixEnd_5206533 := by exact prefixLift 5206533
  have htrace : WordTrace (prefixWord ++ tailWord_5206533) baseStart_5206533 baseEnd_5206533 := by
    simpa [prefixWord, tailWord_5206533, baseEnd_5206533] using wordTrace_append hprefix tailTrace_5206533
  have hstable : (prefixWord ++ tailWord_5206533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206533).length < 2 ^ (prefixWord ++ tailWord_5206533).sum := by decide
  have hdescent : baseEnd_5206533 < baseStart_5206533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206549 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_5206549 : Nat := 118140960795 + 5206549 * 2 ^ 59
def prefixEnd_5206549 : Nat := 4983230072969 + 3 ^ 40 * 5206549 * 2
def baseEnd_5206549 : Nat := 2673462188186055086793023

theorem tailTrace_5206549 : CollatzResearch.WordTrace tailWord_5206549 prefixEnd_5206549 2673462188186055086793023 := by
  unfold tailWord_5206549
  simp only [CollatzResearch.WordTrace]
  refine ⟨189898442814569655620862701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126598961876379770413908467 189898442814569655620862701)
  ·
    refine ⟨71211916055463620857823513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189898442814569655620862701 71211916055463620857823513)
    ·
      refine ⟨53408937041597715643367635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71211916055463620857823513 53408937041597715643367635)
      ·
        refine ⟨80113405562396573465051453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53408937041597715643367635 80113405562396573465051453)
        ·
          refine ⟨30042527085898715049394295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80113405562396573465051453 30042527085898715049394295)
          ·
            refine ⟨45063790628848072574091443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30042527085898715049394295 45063790628848072574091443)
            ·
              refine ⟨67595685943272108861137165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45063790628848072574091443 67595685943272108861137165)
              ·
                refine ⟨25348382228727040822926437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67595685943272108861137165 25348382228727040822926437)
                ·
                  refine ⟨4752821667886320154298707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25348382228727040822926437 4752821667886320154298707)
                  ·
                    refine ⟨7129232501829480231448061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4752821667886320154298707 7129232501829480231448061)
                    ·
                      refine ⟨2673462188186055086793023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7129232501829480231448061 2673462188186055086793023)
                      ·
                        rfl

theorem cell23_5206549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_5206549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206549 prefixEnd_5206549 := by exact prefixLift 5206549
  have htrace : WordTrace (prefixWord ++ tailWord_5206549) baseStart_5206549 baseEnd_5206549 := by
    simpa [prefixWord, tailWord_5206549, baseEnd_5206549] using wordTrace_append hprefix tailTrace_5206549
  have hstable : (prefixWord ++ tailWord_5206549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206549).length < 2 ^ (prefixWord ++ tailWord_5206549).sum := by decide
  have hdescent : baseEnd_5206549 < baseStart_5206549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206559 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 3, 3, 2]
def baseStart_5206559 : Nat := 118140960795 + 5206559 * 2 ^ 59
def prefixEnd_5206559 : Nat := 4983230072969 + 3 ^ 40 * 5206559 * 2
def baseEnd_5206559 : Nat := 2673467322992600047667977

theorem tailTrace_5206559 : CollatzResearch.WordTrace tailWord_5206559 prefixEnd_5206559 2673467322992600047667977 := by
  unfold tailWord_5206559
  simp only [CollatzResearch.WordTrace]
  refine ⟨189898807544533427328726731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126599205029688951552484487 189898807544533427328726731)
  ·
    refine ⟨284848211316800140993090097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189898807544533427328726731 284848211316800140993090097)
    ·
      refine ⟨213636158487600105744817573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284848211316800140993090097 213636158487600105744817573)
      ·
        refine ⟨40056779716425019827153295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213636158487600105744817573 40056779716425019827153295)
        ·
          refine ⟨60085169574637529740729943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40056779716425019827153295 60085169574637529740729943)
          ·
            refine ⟨90127754361956294611094915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60085169574637529740729943 90127754361956294611094915)
            ·
              refine ⟨135191631542934441916642373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90127754361956294611094915 135191631542934441916642373)
              ·
                refine ⟨25348430914300207859370445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135191631542934441916642373 25348430914300207859370445)
                ·
                  refine ⟨9505661592862577947263917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25348430914300207859370445 9505661592862577947263917)
                  ·
                    refine ⟨3564623097323466730223969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9505661592862577947263917 3564623097323466730223969)
                    ·
                      refine ⟨2673467322992600047667977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564623097323466730223969 2673467322992600047667977)
                      ·
                        rfl

theorem cell23_5206559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_5206559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206559 prefixEnd_5206559 := by exact prefixLift 5206559
  have htrace : WordTrace (prefixWord ++ tailWord_5206559) baseStart_5206559 baseEnd_5206559 := by
    simpa [prefixWord, tailWord_5206559, baseEnd_5206559] using wordTrace_append hprefix tailTrace_5206559
  have hstable : (prefixWord ++ tailWord_5206559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206559).length < 2 ^ (prefixWord ++ tailWord_5206559).sum := by decide
  have hdescent : baseEnd_5206559 < baseStart_5206559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206560 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 2, 4]
def baseStart_5206560 : Nat := 118140960795 + 5206560 * 2 ^ 59
def prefixEnd_5206560 : Nat := 4983230072969 + 3 ^ 40 * 5206560 * 2
def baseEnd_5206560 : Nat := 891155945491084847918491

theorem tailTrace_5206560 : CollatzResearch.WordTrace tailWord_5206560 prefixEnd_5206560 891155945491084847918491 := by
  unfold tailWord_5206560
  simp only [CollatzResearch.WordTrace]
  refine ⟨94949422008764902249756567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126599229345019869666342089 94949422008764902249756567)
  ·
    refine ⟨142424133013147353374634851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94949422008764902249756567 142424133013147353374634851)
    ·
      refine ⟨213636199519721030061952277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142424133013147353374634851 213636199519721030061952277)
      ·
        refine ⟨10014196852486923284154013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 213636199519721030061952277 10014196852486923284154013)
        ·
          refine ⟨3755323819682596231557755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10014196852486923284154013 3755323819682596231557755)
          ·
            refine ⟨5632985729523894347336633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755323819682596231557755 5632985729523894347336633)
            ·
              refine ⟨4224739297142920760502475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5632985729523894347336633 4224739297142920760502475)
              ·
                refine ⟨6337108945714381140753713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224739297142920760502475 6337108945714381140753713)
                ·
                  refine ⟨4752831709285785855565285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6337108945714381140753713 4752831709285785855565285)
                  ·
                    refine ⟨891155945491084847918491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752831709285785855565285 891155945491084847918491)
                    ·
                      rfl

theorem cell23_5206560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 4].length) (baseStart_5206560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206560 prefixEnd_5206560 := by exact prefixLift 5206560
  have htrace : WordTrace (prefixWord ++ tailWord_5206560) baseStart_5206560 baseEnd_5206560 := by
    simpa [prefixWord, tailWord_5206560, baseEnd_5206560] using wordTrace_append hprefix tailTrace_5206560
  have hstable : (prefixWord ++ tailWord_5206560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206560).length < 2 ^ (prefixWord ++ tailWord_5206560).sum := by decide
  have hdescent : baseEnd_5206560 < baseStart_5206560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206575 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_5206575 : Nat := 118140960795 + 5206575 * 2 ^ 59
def prefixEnd_5206575 : Nat := 4983230072969 + 3 ^ 40 * 5206575 * 2
def baseEnd_5206575 : Nat := 2673475538683071985067903

theorem tailTrace_5206575 : CollatzResearch.WordTrace tailWord_5206575 prefixEnd_5206575 2673475538683071985067903 := by
  unfold tailWord_5206575
  simp only [CollatzResearch.WordTrace]
  refine ⟨189899391112475462061309179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126599594074983641374206119 189899391112475462061309179)
  ·
    refine ⟨284849086668713193091963769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189899391112475462061309179 284849086668713193091963769)
    ·
      refine ⟨213636815001534894818972827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284849086668713193091963769 213636815001534894818972827)
      ·
        refine ⟨320455222502302342228459241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213636815001534894818972827 320455222502302342228459241)
        ·
          refine ⟨240341416876726756671344431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320455222502302342228459241 240341416876726756671344431)
          ·
            refine ⟨360512125315090135007016647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240341416876726756671344431 360512125315090135007016647)
            ·
              refine ⟨540768187972635202510524971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360512125315090135007016647 540768187972635202510524971)
              ·
                refine ⟨811152281958952803765787457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540768187972635202510524971 811152281958952803765787457)
                ·
                  refine ⟨608364211469214602824340593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 811152281958952803765787457 608364211469214602824340593)
                  ·
                    refine ⟨456273158601910952118255445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608364211469214602824340593 456273158601910952118255445)
                    ·
                      refine ⟨2673475538683071985067903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 456273158601910952118255445 2673475538683071985067903)
                      ·
                        rfl

theorem cell23_5206575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_5206575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206575 prefixEnd_5206575 := by exact prefixLift 5206575
  have htrace : WordTrace (prefixWord ++ tailWord_5206575) baseStart_5206575 baseEnd_5206575 := by
    simpa [prefixWord, tailWord_5206575, baseEnd_5206575] using wordTrace_append hprefix tailTrace_5206575
  have hstable : (prefixWord ++ tailWord_5206575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206575).length < 2 ^ (prefixWord ++ tailWord_5206575).sum := by decide
  have hdescent : baseEnd_5206575 < baseStart_5206575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206576 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 1, 3, 2]
def baseStart_5206576 : Nat := 118140960795 + 5206576 * 2 ^ 59
def prefixEnd_5206576 : Nat := 4983230072969 + 3 ^ 40 * 5206576 * 2
def baseEnd_5206576 : Nat := 2673476052163726481155399

theorem tailTrace_5206576 : CollatzResearch.WordTrace tailWord_5206576 prefixEnd_5206576 2673476052163726481155399 := by
  unfold tailWord_5206576
  simp only [CollatzResearch.WordTrace]
  refine ⟨94949713792735919616047791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126599618390314559488063721 94949713792735919616047791)
  ·
    refine ⟨142424570689103879424071687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94949713792735919616047791 142424570689103879424071687)
    ·
      refine ⟨213636856033655819136107531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142424570689103879424071687 213636856033655819136107531)
      ·
        refine ⟨320455284050483728704161297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213636856033655819136107531 320455284050483728704161297)
        ·
          refine ⟨240341463037862796528120973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320455284050483728704161297 240341463037862796528120973)
          ·
            refine ⟨90128048639198548698045365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240341463037862796528120973 90128048639198548698045365)
            ·
              refine ⟨8449504559924863940441753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90128048639198548698045365 8449504559924863940441753)
              ·
                refine ⟨6337128419943647955331315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8449504559924863940441753 6337128419943647955331315)
                ·
                  refine ⟨9505692629915471932996973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6337128419943647955331315 9505692629915471932996973)
                  ·
                    refine ⟨3564634736218301974873865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9505692629915471932996973 3564634736218301974873865)
                    ·
                      refine ⟨2673476052163726481155399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564634736218301974873865 2673476052163726481155399)
                      ·
                        rfl

theorem cell23_5206576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 3, 2].length) (baseStart_5206576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206576 prefixEnd_5206576 := by exact prefixLift 5206576
  have htrace : WordTrace (prefixWord ++ tailWord_5206576) baseStart_5206576 baseEnd_5206576 := by
    simpa [prefixWord, tailWord_5206576, baseEnd_5206576] using wordTrace_append hprefix tailTrace_5206576
  have hstable : (prefixWord ++ tailWord_5206576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206576).length < 2 ^ (prefixWord ++ tailWord_5206576).sum := by decide
  have hdescent : baseEnd_5206576 < baseStart_5206576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206592 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_5206592 : Nat := 118140960795 + 5206592 * 2 ^ 59
def prefixEnd_5206592 : Nat := 4983230072969 + 3 ^ 40 * 5206592 * 2
def baseEnd_5206592 : Nat := 2673484267854198418555325

theorem tailTrace_5206592 : CollatzResearch.WordTrace tailWord_5206592 prefixEnd_5206592 2673484267854198418555325 := by
  unfold tailWord_5206592
  simp only [CollatzResearch.WordTrace]
  refine ⟨94950005576706936982339015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126600007435609249309785353 94950005576706936982339015)
  ·
    refine ⟨142425008365060405473508523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94950005576706936982339015 142425008365060405473508523)
    ·
      refine ⟨213637512547590608210262785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142425008365060405473508523 213637512547590608210262785)
      ·
        refine ⟨160228134410692956157697089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213637512547590608210262785 160228134410692956157697089)
        ·
          refine ⟨120171100808019717118272817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160228134410692956157697089 120171100808019717118272817)
          ·
            refine ⟨90128325606014787838704613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120171100808019717118272817 90128325606014787838704613)
            ·
              refine ⟨16899061051127772719757115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90128325606014787838704613 16899061051127772719757115)
              ·
                refine ⟨25348591576691659079635673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16899061051127772719757115 25348591576691659079635673)
                ·
                  refine ⟨19011443682518744309726755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25348591576691659079635673 19011443682518744309726755)
                  ·
                    refine ⟨28517165523778116464590133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19011443682518744309726755 28517165523778116464590133)
                    ·
                      refine ⟨2673484267854198418555325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28517165523778116464590133 2673484267854198418555325)
                      ·
                        rfl

theorem cell23_5206592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_5206592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206592 prefixEnd_5206592 := by exact prefixLift 5206592
  have htrace : WordTrace (prefixWord ++ tailWord_5206592) baseStart_5206592 baseEnd_5206592 := by
    simpa [prefixWord, tailWord_5206592, baseEnd_5206592] using wordTrace_append hprefix tailTrace_5206592
  have hstable : (prefixWord ++ tailWord_5206592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206592).length < 2 ^ (prefixWord ++ tailWord_5206592).sum := by decide
  have hdescent : baseEnd_5206592 < baseStart_5206592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206606 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_5206606 : Nat := 118140960795 + 5206606 * 2 ^ 59
def prefixEnd_5206606 : Nat := 4983230072969 + 3 ^ 40 * 5206606 * 2
def baseEnd_5206606 : Nat := 2673491456583361363780261

theorem tailTrace_5206606 : CollatzResearch.WordTrace tailWord_5206606 prefixEnd_5206606 2673491456583361363780261 := by
  unfold tailWord_5206606
  simp only [CollatzResearch.WordTrace]
  refine ⟨23737565221920394294460959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126600347850242102903791781 23737565221920394294460959)
  ·
    refine ⟨35606347832880591441691439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23737565221920394294460959 35606347832880591441691439)
    ·
      refine ⟨53409521749320887162537159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35606347832880591441691439 53409521749320887162537159)
      ·
        refine ⟨80114282623981330743805739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53409521749320887162537159 80114282623981330743805739)
        ·
          refine ⟨120171423935971996115708609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80114282623981330743805739 120171423935971996115708609)
          ·
            refine ⟨90128567951978997086781457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120171423935971996115708609 90128567951978997086781457)
            ·
              refine ⟨67596425963984247815086093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90128567951978997086781457 67596425963984247815086093)
              ·
                refine ⟨25348659736494092930657285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67596425963984247815086093 25348659736494092930657285)
                ·
                  refine ⟨4752873700592642424498241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25348659736494092930657285 4752873700592642424498241)
                  ·
                    refine ⟨3564655275444481818373681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4752873700592642424498241 3564655275444481818373681)
                    ·
                      refine ⟨2673491456583361363780261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564655275444481818373681 2673491456583361363780261)
                      ·
                        rfl

theorem cell23_5206606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_5206606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206606 prefixEnd_5206606 := by exact prefixLift 5206606
  have htrace : WordTrace (prefixWord ++ tailWord_5206606) baseStart_5206606 baseEnd_5206606 := by
    simpa [prefixWord, tailWord_5206606, baseEnd_5206606] using wordTrace_append hprefix tailTrace_5206606
  have hstable : (prefixWord ++ tailWord_5206606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206606).length < 2 ^ (prefixWord ++ tailWord_5206606).sum := by decide
  have hdescent : baseEnd_5206606 < baseStart_5206606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206629 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 7]
def baseStart_5206629 : Nat := 118140960795 + 5206629 * 2 ^ 59
def prefixEnd_5206629 : Nat := 4983230072969 + 3 ^ 40 * 5206629 * 2
def baseEnd_5206629 : Nat := 297055918515379419310295

theorem tailTrace_5206629 : CollatzResearch.WordTrace tailWord_5206629 prefixEnd_5206629 297055918515379419310295 := by
  unfold tailWord_5206629
  simp only [CollatzResearch.WordTrace]
  refine ⟨189901360654279829283774941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126600907102853219522516627 189901360654279829283774941)
  ·
    refine ⟨71213010245354935981415603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189901360654279829283774941 71213010245354935981415603)
    ·
      refine ⟨106819515368032403972123405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71213010245354935981415603 106819515368032403972123405)
      ·
        refine ⟨40057318263012151489546277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106819515368032403972123405 40057318263012151489546277)
        ·
          refine ⟨7510747174314778404289927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40057318263012151489546277 7510747174314778404289927)
          ·
            refine ⟨11266120761472167606434891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510747174314778404289927 11266120761472167606434891)
            ·
              refine ⟨16899181142208251409652337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11266120761472167606434891 16899181142208251409652337)
              ·
                refine ⟨12674385856656188557239253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16899181142208251409652337 12674385856656188557239253)
                ·
                  refine ⟨297055918515379419310295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12674385856656188557239253 297055918515379419310295)
                  ·
                    rfl

theorem cell23_5206629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_5206629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206629 prefixEnd_5206629 := by exact prefixLift 5206629
  have htrace : WordTrace (prefixWord ++ tailWord_5206629) baseStart_5206629 baseEnd_5206629 := by
    simpa [prefixWord, tailWord_5206629, baseEnd_5206629] using wordTrace_append hprefix tailTrace_5206629
  have hstable : (prefixWord ++ tailWord_5206629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206629).length < 2 ^ (prefixWord ++ tailWord_5206629).sum := by decide
  have hdescent : baseEnd_5206629 < baseStart_5206629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206652 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_5206652 : Nat := 118140960795 + 5206652 * 2 ^ 59
def prefixEnd_5206652 : Nat := 4983230072969 + 3 ^ 40 * 5206652 * 2
def baseEnd_5206652 : Nat := 2673515076693468183805049

theorem tailTrace_5206652 : CollatzResearch.WordTrace tailWord_5206652 prefixEnd_5206652 2673515076693468183805049 := by
  unfold tailWord_5206652
  simp only [CollatzResearch.WordTrace]
  refine ⟨94951099766598252105931105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126601466355464336141241473 94951099766598252105931105)
  ·
    refine ⟨71213324824948689079448329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94951099766598252105931105 71213324824948689079448329)
    ·
      refine ⟨53409993618711516809586247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71213324824948689079448329 53409993618711516809586247)
      ·
        refine ⟨80114990428067275214379371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53409993618711516809586247 80114990428067275214379371)
        ·
          refine ⟨120172485642100912821569057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80114990428067275214379371 120172485642100912821569057)
          ·
            refine ⟨90129364231575684616176793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120172485642100912821569057 90129364231575684616176793)
            ·
              refine ⟨67597023173681763462132595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90129364231575684616176793 67597023173681763462132595)
              ·
                refine ⟨101395534760522645193198893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67597023173681763462132595 101395534760522645193198893)
                ·
                  refine ⟨38023325535195991947449585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101395534760522645193198893 38023325535195991947449585)
                  ·
                    refine ⟨28517494151396993960587189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38023325535195991947449585 28517494151396993960587189)
                    ·
                      refine ⟨2673515076693468183805049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28517494151396993960587189 2673515076693468183805049)
                      ·
                        rfl

theorem cell23_5206652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_5206652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206652 prefixEnd_5206652 := by exact prefixLift 5206652
  have htrace : WordTrace (prefixWord ++ tailWord_5206652) baseStart_5206652 baseEnd_5206652 := by
    simpa [prefixWord, tailWord_5206652, baseEnd_5206652] using wordTrace_append hprefix tailTrace_5206652
  have hstable : (prefixWord ++ tailWord_5206652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206652).length < 2 ^ (prefixWord ++ tailWord_5206652).sum := by decide
  have hdescent : baseEnd_5206652 < baseStart_5206652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206716 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_5206716 : Nat := 118140960795 + 5206716 * 2 ^ 59
def prefixEnd_5206716 : Nat := 4983230072969 + 3 ^ 40 * 5206716 * 2
def baseEnd_5206716 : Nat := 2673547939455355933404755

theorem tailTrace_5206716 : CollatzResearch.WordTrace tailWord_5206716 prefixEnd_5206716 2673547939455355933404755 := by
  unfold tailWord_5206716
  simp only [CollatzResearch.WordTrace]
  refine ⟨94952266902482321571096001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126603022536643095428128001 94952266902482321571096001)
  ·
    refine ⟨71214200176861741178322001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94952266902482321571096001 71214200176861741178322001)
    ·
      refine ⟨53410650132646305883741501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71214200176861741178322001 53410650132646305883741501)
      ·
        refine ⟨20028993799742364706403063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53410650132646305883741501 20028993799742364706403063)
        ·
          refine ⟨30043490699613547059604595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20028993799742364706403063 30043490699613547059604595)
          ·
            refine ⟨45065236049420320589406893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30043490699613547059604595 45065236049420320589406893)
            ·
              refine ⟨16899463518532620221027585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45065236049420320589406893 16899463518532620221027585)
              ·
                refine ⟨12674597638899465165770689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16899463518532620221027585 12674597638899465165770689)
                ·
                  refine ⟨9505948229174598874328017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12674597638899465165770689 9505948229174598874328017)
                  ·
                    refine ⟨7129461171880949155746013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9505948229174598874328017 7129461171880949155746013)
                    ·
                      refine ⟨2673547939455355933404755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7129461171880949155746013 2673547939455355933404755)
                      ·
                        rfl

theorem cell23_5206716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_5206716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206716 prefixEnd_5206716 := by exact prefixLift 5206716
  have htrace : WordTrace (prefixWord ++ tailWord_5206716) baseStart_5206716 baseEnd_5206716 := by
    simpa [prefixWord, tailWord_5206716, baseEnd_5206716] using wordTrace_append hprefix tailTrace_5206716
  have hstable : (prefixWord ++ tailWord_5206716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206716).length < 2 ^ (prefixWord ++ tailWord_5206716).sum := by decide
  have hdescent : baseEnd_5206716 < baseStart_5206716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206746 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_5206746 : Nat := 118140960795 + 5206746 * 2 ^ 59
def prefixEnd_5206746 : Nat := 4983230072969 + 3 ^ 40 * 5206746 * 2
def baseEnd_5206746 : Nat := 2673563343874990816029617

theorem tailTrace_5206746 : CollatzResearch.WordTrace tailWord_5206746 prefixEnd_5206746 2673563343874990816029617 := by
  unfold tailWord_5206746
  simp only [CollatzResearch.WordTrace]
  refine ⟨47476406998713989566446023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126603751996570638843856061 47476406998713989566446023)
  ·
    refine ⟨71214610498070984349669035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47476406998713989566446023 71214610498070984349669035)
    ·
      refine ⟨106821915747106476524503553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71214610498070984349669035 106821915747106476524503553)
      ·
        refine ⟨80116436810329857393377665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106821915747106476524503553 80116436810329857393377665)
        ·
          refine ⟨60087327607747393045033249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80116436810329857393377665 60087327607747393045033249)
          ·
            refine ⟨45065495705810544783774937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60087327607747393045033249 45065495705810544783774937)
            ·
              refine ⟨33799121779357908587831203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45065495705810544783774937 33799121779357908587831203)
              ·
                refine ⟨50698682669036862881746805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33799121779357908587831203 50698682669036862881746805)
                ·
                  refine ⟨4753001500222205895163763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50698682669036862881746805 4753001500222205895163763)
                  ·
                    refine ⟨7129502250333308842745645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753001500222205895163763 7129502250333308842745645)
                    ·
                      refine ⟨2673563343874990816029617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7129502250333308842745645 2673563343874990816029617)
                      ·
                        rfl

theorem cell23_5206746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_5206746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206746 prefixEnd_5206746 := by exact prefixLift 5206746
  have htrace : WordTrace (prefixWord ++ tailWord_5206746) baseStart_5206746 baseEnd_5206746 := by
    simpa [prefixWord, tailWord_5206746, baseEnd_5206746] using wordTrace_append hprefix tailTrace_5206746
  have hstable : (prefixWord ++ tailWord_5206746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206746).length < 2 ^ (prefixWord ++ tailWord_5206746).sum := by decide
  have hdescent : baseEnd_5206746 < baseStart_5206746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206763 : List Nat := [1, 1, 1, 1, 2, 4, 1, 7, 1, 1, 3]
def baseStart_5206763 : Nat := 118140960795 + 5206763 * 2 ^ 59
def prefixEnd_5206763 : Nat := 4983230072969 + 3 ^ 40 * 5206763 * 2
def baseEnd_5206763 : Nat := 2673572073046117249517039

theorem tailTrace_5206763 : CollatzResearch.WordTrace tailWord_5206763 prefixEnd_5206763 2673572073046117249517039 := by
  unfold tailWord_5206763
  simp only [CollatzResearch.WordTrace]
  refine ⟨189906248035794370169152943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126604165357196246779435295 189906248035794370169152943)
  ·
    refine ⟨284859372053691555253729415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189906248035794370169152943 284859372053691555253729415)
    ·
      refine ⟨427289058080537332880594123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284859372053691555253729415 427289058080537332880594123)
      ·
        refine ⟨640933587120805999320891185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427289058080537332880594123 640933587120805999320891185)
        ·
          refine ⟨480700190340604499490668389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640933587120805999320891185 480700190340604499490668389)
          ·
            refine ⟨90131285688863343654500323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 480700190340604499490668389 90131285688863343654500323)
            ·
              refine ⟨135196928533295015481750485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90131285688863343654500323 135196928533295015481750485)
              ·
                refine ⟨3168678012499101925353527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135196928533295015481750485 3168678012499101925353527)
                ·
                  refine ⟨4753017018748652888030291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168678012499101925353527 4753017018748652888030291)
                  ·
                    refine ⟨7129525528122979332045437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753017018748652888030291 7129525528122979332045437)
                    ·
                      refine ⟨2673572073046117249517039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7129525528122979332045437 2673572073046117249517039)
                      ·
                        rfl

theorem cell23_5206763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 1, 3].length) (baseStart_5206763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206763 prefixEnd_5206763 := by exact prefixLift 5206763
  have htrace : WordTrace (prefixWord ++ tailWord_5206763) baseStart_5206763 baseEnd_5206763 := by
    simpa [prefixWord, tailWord_5206763, baseEnd_5206763] using wordTrace_append hprefix tailTrace_5206763
  have hstable : (prefixWord ++ tailWord_5206763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206763).length < 2 ^ (prefixWord ++ tailWord_5206763).sum := by decide
  have hdescent : baseEnd_5206763 < baseStart_5206763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206779 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 8, 4]
def baseStart_5206779 : Nat := 118140960795 + 5206779 * 2 ^ 59
def prefixEnd_5206779 : Nat := 4983230072969 + 3 ^ 40 * 5206779 * 2
def baseEnd_5206779 : Nat := 891193429578863062305655

theorem tailTrace_5206779 : CollatzResearch.WordTrace tailWord_5206779 prefixEnd_5206779 891193429578863062305655 := by
  unfold tailWord_5206779
  simp only [CollatzResearch.WordTrace]
  refine ⟨189906831603736404901735391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126604554402490936601156927 189906831603736404901735391)
  ·
    refine ⟨284860247405604607352603087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189906831603736404901735391 284860247405604607352603087)
    ·
      refine ⟨427290371108406911028904631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284860247405604607352603087 427290371108406911028904631)
      ·
        refine ⟨640935556662610366543356947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427290371108406911028904631 640935556662610366543356947)
        ·
          refine ⟨961403334993915549815035421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640935556662610366543356947 961403334993915549815035421)
          ·
            refine ⟨360526250622718331180638283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 961403334993915549815035421 360526250622718331180638283)
            ·
              refine ⟨540789375934077496770957425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360526250622718331180638283 540789375934077496770957425)
              ·
                refine ⟨405592031950558122578218069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540789375934077496770957425 405592031950558122578218069)
                ·
                  refine ⟨4753031624420602998963493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 405592031950558122578218069 4753031624420602998963493)
                  ·
                    refine ⟨891193429578863062305655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4753031624420602998963493 891193429578863062305655)
                    ·
                      rfl

theorem cell23_5206779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 4].length) (baseStart_5206779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206779 prefixEnd_5206779 := by exact prefixLift 5206779
  have htrace : WordTrace (prefixWord ++ tailWord_5206779) baseStart_5206779 baseEnd_5206779 := by
    simpa [prefixWord, tailWord_5206779, baseEnd_5206779] using wordTrace_append hprefix tailTrace_5206779
  have hstable : (prefixWord ++ tailWord_5206779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206779).length < 2 ^ (prefixWord ++ tailWord_5206779).sum := by decide
  have hdescent : baseEnd_5206779 < baseStart_5206779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206780 : List Nat := [2, 2, 2, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_5206780 : Nat := 118140960795 + 5206780 * 2 ^ 59
def prefixEnd_5206780 : Nat := 4983230072969 + 3 ^ 40 * 5206780 * 2
def baseEnd_5206780 : Nat := 2673580802217243683004461

theorem tailTrace_5206780 : CollatzResearch.WordTrace tailWord_5206780 prefixEnd_5206780 2673580802217243683004461 := by
  unfold tailWord_5206780
  simp only [CollatzResearch.WordTrace]
  refine ⟨94953434038366391036260897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126604578717821854715014529 94953434038366391036260897)
  ·
    refine ⟨71215075528774793277195673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94953434038366391036260897 71215075528774793277195673)
    ·
      refine ⟨53411306646581094957896755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71215075528774793277195673 53411306646581094957896755)
      ·
        refine ⟨80116959969871642436845133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53411306646581094957896755 80116959969871642436845133)
        ·
          refine ⟨30043859988701865913816925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80116959969871642436845133 30043859988701865913816925)
          ·
            refine ⟨11266447495763199717681347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30043859988701865913816925 11266447495763199717681347)
            ·
              refine ⟨16899671243644799576522021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11266447495763199717681347 16899671243644799576522021)
              ·
                refine ⟨3168688358183399920597879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16899671243644799576522021 3168688358183399920597879)
                ·
                  refine ⟨4753032537275099880896819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168688358183399920597879 4753032537275099880896819)
                  ·
                    refine ⟨7129548805912649821345229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753032537275099880896819 7129548805912649821345229)
                    ·
                      refine ⟨2673580802217243683004461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7129548805912649821345229 2673580802217243683004461)
                      ·
                        rfl

theorem cell23_5206780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_5206780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206780 prefixEnd_5206780 := by exact prefixLift 5206780
  have htrace : WordTrace (prefixWord ++ tailWord_5206780) baseStart_5206780 baseEnd_5206780 := by
    simpa [prefixWord, tailWord_5206780, baseEnd_5206780] using wordTrace_append hprefix tailTrace_5206780
  have hstable : (prefixWord ++ tailWord_5206780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206780).length < 2 ^ (prefixWord ++ tailWord_5206780).sum := by decide
  have hdescent : baseEnd_5206780 < baseStart_5206780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206789 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_5206789 : Nat := 118140960795 + 5206789 * 2 ^ 59
def prefixEnd_5206789 : Nat := 4983230072969 + 3 ^ 40 * 5206789 * 2
def baseEnd_5206789 : Nat := 2673585423543134147791919

theorem tailTrace_5206789 : CollatzResearch.WordTrace tailWord_5206789 prefixEnd_5206789 2673585423543134147791919 := by
  unfold tailWord_5206789
  simp only [CollatzResearch.WordTrace]
  refine ⟨189907196333700176609599421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126604797555800117739732947 189907196333700176609599421)
  ·
    refine ⟨71215198625137566228599783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189907196333700176609599421 71215198625137566228599783)
    ·
      refine ⟨106822797937706349342899675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71215198625137566228599783 106822797937706349342899675)
      ·
        refine ⟨160234196906559524014349513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106822797937706349342899675 160234196906559524014349513)
        ·
          refine ⟨120175647679919643010762135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160234196906559524014349513 120175647679919643010762135)
          ·
            refine ⟨180263471519879464516143203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120175647679919643010762135 180263471519879464516143203)
            ·
              refine ⟨270395207279819196774214805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180263471519879464516143203 270395207279819196774214805)
              ·
                refine ⟨12674775341241524848791319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270395207279819196774214805 12674775341241524848791319)
                ·
                  refine ⟨19012163011862287273186979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12674775341241524848791319 19012163011862287273186979)
                  ·
                    refine ⟨28518244517793430909780469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19012163011862287273186979 28518244517793430909780469)
                    ·
                      refine ⟨2673585423543134147791919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28518244517793430909780469 2673585423543134147791919)
                      ·
                        rfl

theorem cell23_5206789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_5206789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206789 prefixEnd_5206789 := by exact prefixLift 5206789
  have htrace : WordTrace (prefixWord ++ tailWord_5206789) baseStart_5206789 baseEnd_5206789 := by
    simpa [prefixWord, tailWord_5206789, baseEnd_5206789] using wordTrace_append hprefix tailTrace_5206789
  have hstable : (prefixWord ++ tailWord_5206789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206789).length < 2 ^ (prefixWord ++ tailWord_5206789).sum := by decide
  have hdescent : baseEnd_5206789 < baseStart_5206789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206803 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 3, 2, 2]
def baseStart_5206803 : Nat := 118140960795 + 5206803 * 2 ^ 59
def prefixEnd_5206803 : Nat := 4983230072969 + 3 ^ 40 * 5206803 * 2
def baseEnd_5206803 : Nat := 2673592612272297093016855

theorem tailTrace_5206803 : CollatzResearch.WordTrace tailWord_5206803 prefixEnd_5206803 2673592612272297093016855 := by
  unfold tailWord_5206803
  simp only [CollatzResearch.WordTrace]
  refine ⟨189907706955649457000609063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126605137970432971333739375 189907706955649457000609063)
  ·
    refine ⟨284861560433474185500913595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189907706955649457000609063 284861560433474185500913595)
    ·
      refine ⟨427292340650211278251370393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284861560433474185500913595 427292340650211278251370393)
      ·
        refine ⟨320469255487658458688527795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427292340650211278251370393 320469255487658458688527795)
        ·
          refine ⟨480703883231487688032791693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320469255487658458688527795 480703883231487688032791693)
          ·
            refine ⟨180263956211807883012296885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 480703883231487688032791693 180263956211807883012296885)
            ·
              refine ⟨16899745894856989032402833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180263956211807883012296885 16899745894856989032402833)
              ·
                refine ⟨12674809421142741774302125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16899745894856989032402833 12674809421142741774302125)
                ·
                  refine ⟨4753053532928528165363297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12674809421142741774302125 4753053532928528165363297)
                  ·
                    refine ⟨3564790149696396124022473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4753053532928528165363297 3564790149696396124022473)
                    ·
                      refine ⟨2673592612272297093016855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564790149696396124022473 2673592612272297093016855)
                      ·
                        rfl

theorem cell23_5206803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 2, 2].length) (baseStart_5206803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206803 prefixEnd_5206803 := by exact prefixLift 5206803
  have htrace : WordTrace (prefixWord ++ tailWord_5206803) baseStart_5206803 baseEnd_5206803 := by
    simpa [prefixWord, tailWord_5206803, baseEnd_5206803] using wordTrace_append hprefix tailTrace_5206803
  have hstable : (prefixWord ++ tailWord_5206803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206803).length < 2 ^ (prefixWord ++ tailWord_5206803).sum := by decide
  have hdescent : baseEnd_5206803 < baseStart_5206803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206807 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 2, 3, 2]
def baseStart_5206807 : Nat := 118140960795 + 5206807 * 2 ^ 59
def prefixEnd_5206807 : Nat := 4983230072969 + 3 ^ 40 * 5206807 * 2
def baseEnd_5206807 : Nat := 2673594666194915077366837

theorem tailTrace_5206807 : CollatzResearch.WordTrace tailWord_5206807 prefixEnd_5206807 2673594666194915077366837 := by
  unfold tailWord_5206807
  simp only [CollatzResearch.WordTrace]
  refine ⟨189907852847634965683754675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126605235231756643789169783 189907852847634965683754675)
  ·
    refine ⟨284861779271452448525632013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189907852847634965683754675 284861779271452448525632013)
    ·
      refine ⟨106823167226794668197112005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284861779271452448525632013 106823167226794668197112005)
      ·
        refine ⟨20029343855024000286958501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106823167226794668197112005 20029343855024000286958501)
        ·
          refine ⟨3755501972817000053804719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20029343855024000286958501 3755501972817000053804719)
          ·
            refine ⟨5633252959225500080707079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755501972817000053804719 5633252959225500080707079)
            ·
              refine ⟨8449879438838250121060619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5633252959225500080707079 8449879438838250121060619)
              ·
                refine ⟨12674819158257375181590929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449879438838250121060619 12674819158257375181590929)
                ·
                  refine ⟨9506114368693031386193197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12674819158257375181590929 9506114368693031386193197)
                  ·
                    refine ⟨3564792888259886769822449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9506114368693031386193197 3564792888259886769822449)
                    ·
                      refine ⟨2673594666194915077366837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564792888259886769822449 2673594666194915077366837)
                      ·
                        rfl

theorem cell23_5206807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_5206807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206807 prefixEnd_5206807 := by exact prefixLift 5206807
  have htrace : WordTrace (prefixWord ++ tailWord_5206807) baseStart_5206807 baseEnd_5206807 := by
    simpa [prefixWord, tailWord_5206807, baseEnd_5206807] using wordTrace_append hprefix tailTrace_5206807
  have hstable : (prefixWord ++ tailWord_5206807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206807).length < 2 ^ (prefixWord ++ tailWord_5206807).sum := by decide
  have hdescent : baseEnd_5206807 < baseStart_5206807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206816 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5206816 : Nat := 118140960795 + 5206816 * 2 ^ 59
def prefixEnd_5206816 : Nat := 4983230072969 + 3 ^ 40 * 5206816 * 2
def baseEnd_5206816 : Nat := 2673599287520805542154295

theorem tailTrace_5206816 : CollatzResearch.WordTrace tailWord_5206816 prefixEnd_5206816 2673599287520805542154295 := by
  unfold tailWord_5206816
  simp only [CollatzResearch.WordTrace]
  refine ⟨94954090552301180110416151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126605454069734906813888201 94954090552301180110416151)
  ·
    refine ⟨142431135828451770165624227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94954090552301180110416151 142431135828451770165624227)
    ·
      refine ⟨213646703742677655248436341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142431135828451770165624227 213646703742677655248436341)
      ·
        refine ⟨20029378475876030179540907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213646703742677655248436341 20029378475876030179540907)
        ·
          refine ⟨30044067713814045269311361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20029378475876030179540907 30044067713814045269311361)
          ·
            refine ⟨22533050785360533951983521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30044067713814045269311361 22533050785360533951983521)
            ·
              refine ⟨16899788089020400463987641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22533050785360533951983521 16899788089020400463987641)
              ·
                refine ⟨12674841066765300347990731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16899788089020400463987641 12674841066765300347990731)
                ·
                  refine ⟨19012261600147950521986097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12674841066765300347990731 19012261600147950521986097)
                  ·
                    refine ⟨14259196200110962891489573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19012261600147950521986097 14259196200110962891489573)
                    ·
                      refine ⟨2673599287520805542154295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14259196200110962891489573 2673599287520805542154295)
                      ·
                        rfl

theorem cell23_5206816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5206816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206816 prefixEnd_5206816 := by exact prefixLift 5206816
  have htrace : WordTrace (prefixWord ++ tailWord_5206816) baseStart_5206816 baseEnd_5206816 := by
    simpa [prefixWord, tailWord_5206816, baseEnd_5206816] using wordTrace_append hprefix tailTrace_5206816
  have hstable : (prefixWord ++ tailWord_5206816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206816).length < 2 ^ (prefixWord ++ tailWord_5206816).sum := by decide
  have hdescent : baseEnd_5206816 < baseStart_5206816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206830 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_5206830 : Nat := 118140960795 + 5206830 * 2 ^ 59
def prefixEnd_5206830 : Nat := 4983230072969 + 3 ^ 40 * 5206830 * 2
def baseEnd_5206830 : Nat := 891202158749989495793077

theorem tailTrace_5206830 : CollatzResearch.WordTrace tailWord_5206830 prefixEnd_5206830 891202158749989495793077 := by
  unfold tailWord_5206830
  simp only [CollatzResearch.WordTrace]
  refine ⟨23738586465818955076480243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126605794484367760407894629 23738586465818955076480243)
  ·
    refine ⟨35607879698728432614720365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23738586465818955076480243 35607879698728432614720365)
    ·
      refine ⟨13352954887023162230520137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35607879698728432614720365 13352954887023162230520137)
      ·
        refine ⟨10014716165267371672890103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13352954887023162230520137 10014716165267371672890103)
        ·
          refine ⟨15022074247901057509335155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10014716165267371672890103 15022074247901057509335155)
          ·
            refine ⟨22533111371851586264002733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15022074247901057509335155 22533111371851586264002733)
            ·
              refine ⟨8449916764444344849001025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22533111371851586264002733 8449916764444344849001025)
              ·
                refine ⟨6337437573333258636750769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8449916764444344849001025 6337437573333258636750769)
                ·
                  refine ⟨4753078179999943977563077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6337437573333258636750769 4753078179999943977563077)
                  ·
                    refine ⟨891202158749989495793077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4753078179999943977563077 891202158749989495793077)
                    ·
                      rfl

theorem cell23_5206830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_5206830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206830 prefixEnd_5206830 := by exact prefixLift 5206830
  have htrace : WordTrace (prefixWord ++ tailWord_5206830) baseStart_5206830 baseEnd_5206830 := by
    simpa [prefixWord, tailWord_5206830, baseEnd_5206830] using wordTrace_append hprefix tailTrace_5206830
  have hstable : (prefixWord ++ tailWord_5206830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206830).length < 2 ^ (prefixWord ++ tailWord_5206830).sum := by decide
  have hdescent : baseEnd_5206830 < baseStart_5206830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206837 : List Nat := [1, 3, 3, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_5206837 : Nat := 118140960795 + 5206837 * 2 ^ 59
def prefixEnd_5206837 : Nat := 4983230072969 + 3 ^ 40 * 5206837 * 2
def baseEnd_5206837 : Nat := 2673610070614549959991699

theorem tailTrace_5206837 : CollatzResearch.WordTrace tailWord_5206837 prefixEnd_5206837 2673610070614549959991699 := by
  unfold tailWord_5206837
  simp only [CollatzResearch.WordTrace]
  refine ⟨189908947037526280807346765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126605964691684187204897843 189908947037526280807346765)
  ·
    refine ⟨71215855139072355302755037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189908947037526280807346765 71215855139072355302755037)
    ·
      refine ⟨26705945677152133238533139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71215855139072355302755037 26705945677152133238533139)
      ·
        refine ⟨40058918515728199857799709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26705945677152133238533139 40058918515728199857799709)
        ·
          refine ⟨15022094443398074946674891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40058918515728199857799709 15022094443398074946674891)
          ·
            refine ⟨22533141665097112420012337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15022094443398074946674891 22533141665097112420012337)
            ·
              refine ⟨16899856248822834315009253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22533141665097112420012337 16899856248822834315009253)
              ·
                refine ⟨3168723046654281434064235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16899856248822834315009253 3168723046654281434064235)
                ·
                  refine ⟨4753084569981422151096353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168723046654281434064235 4753084569981422151096353)
                  ·
                    refine ⟨3564813427486066613322265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4753084569981422151096353 3564813427486066613322265)
                    ·
                      refine ⟨2673610070614549959991699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564813427486066613322265 2673610070614549959991699)
                      ·
                        rfl

theorem cell23_5206837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_5206837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206837 prefixEnd_5206837 := by exact prefixLift 5206837
  have htrace : WordTrace (prefixWord ++ tailWord_5206837) baseStart_5206837 baseEnd_5206837 := by
    simpa [prefixWord, tailWord_5206837, baseEnd_5206837] using wordTrace_append hprefix tailTrace_5206837
  have hstable : (prefixWord ++ tailWord_5206837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206837).length < 2 ^ (prefixWord ++ tailWord_5206837).sum := by decide
  have hdescent : baseEnd_5206837 < baseStart_5206837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206914 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5206914 : Nat := 118140960795 + 5206914 * 2 ^ 59
def prefixEnd_5206914 : Nat := 4983230072969 + 3 ^ 40 * 5206914 * 2
def baseEnd_5206914 : Nat := 2673649608624946158728845

theorem tailTrace_5206914 : CollatzResearch.WordTrace tailWord_5206914 prefixEnd_5206914 2673649608624946158728845 := by
  unfold tailWord_5206914
  simp only [CollatzResearch.WordTrace]
  refine ⟨47477938864561830739474949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126607836972164881971933197 47477938864561830739474949)
  ·
    refine ⟨8902113537105343263651553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47477938864561830739474949 8902113537105343263651553)
    ·
      refine ⟨6676585152829007447738665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8902113537105343263651553 6676585152829007447738665)
      ·
        refine ⟨5007438864621755585803999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6676585152829007447738665 5007438864621755585803999)
        ·
          refine ⟨7511158296932633378705999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007438864621755585803999 7511158296932633378705999)
          ·
            refine ⟨11266737445398950068058999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511158296932633378705999 11266737445398950068058999)
            ·
              refine ⟨16900106168098425102088499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11266737445398950068058999 16900106168098425102088499)
              ·
                refine ⟨25350159252147637653132749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16900106168098425102088499 25350159252147637653132749)
                ·
                  refine ⟨9506309719555364119924781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25350159252147637653132749 9506309719555364119924781)
                  ·
                    refine ⟨3564866144833261544971793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9506309719555364119924781 3564866144833261544971793)
                    ·
                      refine ⟨2673649608624946158728845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564866144833261544971793 2673649608624946158728845)
                      ·
                        rfl

theorem cell23_5206914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5206914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206914 prefixEnd_5206914 := by exact prefixLift 5206914
  have htrace : WordTrace (prefixWord ++ tailWord_5206914) baseStart_5206914 baseEnd_5206914 := by
    simpa [prefixWord, tailWord_5206914, baseEnd_5206914] using wordTrace_append hprefix tailTrace_5206914
  have hstable : (prefixWord ++ tailWord_5206914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206914).length < 2 ^ (prefixWord ++ tailWord_5206914).sum := by decide
  have hdescent : baseEnd_5206914 < baseStart_5206914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206980 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_5206980 : Nat := 118140960795 + 5206980 * 2 ^ 59
def prefixEnd_5206980 : Nat := 4983230072969 + 3 ^ 40 * 5206980 * 2
def baseEnd_5206980 : Nat := 891227832782714300167847

theorem tailTrace_5206980 : CollatzResearch.WordTrace tailWord_5206980 prefixEnd_5206980 891227832782714300167847 := by
  unfold tailWord_5206980
  simp only [CollatzResearch.WordTrace]
  refine ⟨94957081338004108114901197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126609441784005477486534929 94957081338004108114901197)
  ·
    refine ⟨35608905501751540543087949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94957081338004108114901197 35608905501751540543087949)
    ·
      refine ⟨13353339563156827703657981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35608905501751540543087949 13353339563156827703657981)
      ·
        refine ⟨5007502336183810388871743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13353339563156827703657981 5007502336183810388871743)
        ·
          refine ⟨7511253504275715583307615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007502336183810388871743 7511253504275715583307615)
          ·
            refine ⟨11266880256413573374961423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511253504275715583307615 11266880256413573374961423)
            ·
              refine ⟨16900320384620360062442135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11266880256413573374961423 16900320384620360062442135)
              ·
                refine ⟨25350480576930540093663203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16900320384620360062442135 25350480576930540093663203)
                ·
                  refine ⟨38025720865395810140494805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25350480576930540093663203 38025720865395810140494805)
                  ·
                    refine ⟨891227832782714300167847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38025720865395810140494805 891227832782714300167847)
                    ·
                      rfl

theorem cell23_5206980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_5206980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206980 prefixEnd_5206980 := by exact prefixLift 5206980
  have htrace : WordTrace (prefixWord ++ tailWord_5206980) baseStart_5206980 baseEnd_5206980 := by
    simpa [prefixWord, tailWord_5206980, baseEnd_5206980] using wordTrace_append hprefix tailTrace_5206980
  have hstable : (prefixWord ++ tailWord_5206980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206980).length < 2 ^ (prefixWord ++ tailWord_5206980).sum := by decide
  have hdescent : baseEnd_5206980 < baseStart_5206980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206982 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5206982 : Nat := 118140960795 + 5206982 * 2 ^ 59
def prefixEnd_5206982 : Nat := 4983230072969 + 3 ^ 40 * 5206982 * 2
def baseEnd_5206982 : Nat := 2673684525309451892678533

theorem tailTrace_5206982 : CollatzResearch.WordTrace tailWord_5206982 prefixEnd_5206982 2673684525309451892678533 := by
  unfold tailWord_5206982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5934819863187530330355475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126609490414667313714250133 5934819863187530330355475)
  ·
    refine ⟨8902229794781295495533213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5934819863187530330355475 8902229794781295495533213)
    ·
      refine ⟨3338336173042985810824955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8902229794781295495533213 3338336173042985810824955)
      ·
        refine ⟨5007504259564478716237433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338336173042985810824955 5007504259564478716237433)
        ·
          refine ⟨3755628194673359037178075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5007504259564478716237433 3755628194673359037178075)
          ·
            refine ⟨5633442292010038555767113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755628194673359037178075 5633442292010038555767113)
            ·
              refine ⟨4225081719007528916825335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5633442292010038555767113 4225081719007528916825335)
              ·
                refine ⟨6337622578511293375238003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225081719007528916825335 6337622578511293375238003)
                ·
                  refine ⟨9506433867766940062857005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6337622578511293375238003 9506433867766940062857005)
                  ·
                    refine ⟨3564912700412602523571377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9506433867766940062857005 3564912700412602523571377)
                    ·
                      refine ⟨2673684525309451892678533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564912700412602523571377 2673684525309451892678533)
                      ·
                        rfl

theorem cell23_5206982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5206982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206982 prefixEnd_5206982 := by exact prefixLift 5206982
  have htrace : WordTrace (prefixWord ++ tailWord_5206982) baseStart_5206982 baseEnd_5206982 := by
    simpa [prefixWord, tailWord_5206982, baseEnd_5206982] using wordTrace_append hprefix tailTrace_5206982
  have hstable : (prefixWord ++ tailWord_5206982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206982).length < 2 ^ (prefixWord ++ tailWord_5206982).sum := by decide
  have hdescent : baseEnd_5206982 < baseStart_5206982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206983 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_5206983 : Nat := 118140960795 + 5206983 * 2 ^ 59
def prefixEnd_5206983 : Nat := 4983230072969 + 3 ^ 40 * 5206983 * 2
def baseEnd_5206983 : Nat := 2673685038790106388766027

theorem tailTrace_5206983 : CollatzResearch.WordTrace tailWord_5206983 prefixEnd_5206983 2673685038790106388766027 := by
  unfold tailWord_5206983
  simp only [CollatzResearch.WordTrace]
  refine ⟨189914272094997347742161603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126609514729998231828107735 189914272094997347742161603)
  ·
    refine ⟨284871408142496021613242405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189914272094997347742161603 284871408142496021613242405)
    ·
      refine ⟨53413389026718004052482951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284871408142496021613242405 53413389026718004052482951)
      ·
        refine ⟨80120083540077006078724427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53413389026718004052482951 80120083540077006078724427)
        ·
          refine ⟨120180125310115509118086641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80120083540077006078724427 120180125310115509118086641)
          ·
            refine ⟨90135093982586631838564981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120180125310115509118086641 90135093982586631838564981)
            ·
              refine ⟨8450165060867496734865467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90135093982586631838564981 8450165060867496734865467)
              ·
                refine ⟨12675247591301245102298201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8450165060867496734865467 12675247591301245102298201)
                ·
                  refine ⟨9506435693475933826723651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12675247591301245102298201 9506435693475933826723651)
                  ·
                    refine ⟨14259653540213900740085477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9506435693475933826723651 14259653540213900740085477)
                    ·
                      refine ⟨2673685038790106388766027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14259653540213900740085477 2673685038790106388766027)
                      ·
                        rfl

theorem cell23_5206983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_5206983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5206983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5206983 prefixEnd_5206983 := by exact prefixLift 5206983
  have htrace : WordTrace (prefixWord ++ tailWord_5206983) baseStart_5206983 baseEnd_5206983 := by
    simpa [prefixWord, tailWord_5206983, baseEnd_5206983] using wordTrace_append hprefix tailTrace_5206983
  have hstable : (prefixWord ++ tailWord_5206983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206983).length < 2 ^ (prefixWord ++ tailWord_5206983).sum := by decide
  have hdescent : baseEnd_5206983 < baseStart_5206983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207094 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_5207094 : Nat := 118140960795 + 5207094 * 2 ^ 59
def prefixEnd_5207094 : Nat := 4983230072969 + 3 ^ 40 * 5207094 * 2
def baseEnd_5207094 : Nat := 2673742035142755454478017

theorem tailTrace_5207094 : CollatzResearch.WordTrace tailWord_5207094 prefixEnd_5207094 2673742035142755454478017 := by
  unfold tailWord_5207094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869895037349700856215771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126612213731730142466301557 11869895037349700856215771)
  ·
    refine ⟨17804842556024551284323657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11869895037349700856215771 17804842556024551284323657)
    ·
      refine ⟨13353631917018413463242743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17804842556024551284323657 13353631917018413463242743)
      ·
        refine ⟨20030447875527620194864115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13353631917018413463242743 20030447875527620194864115)
        ·
          refine ⟨30045671813291430292296173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20030447875527620194864115 30045671813291430292296173)
          ·
            refine ⟨11267126929984286359611065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30045671813291430292296173 11267126929984286359611065)
            ·
              refine ⟨8450345197488214769708299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11267126929984286359611065 8450345197488214769708299)
              ·
                refine ⟨12675517796232322154562449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8450345197488214769708299 12675517796232322154562449)
                ·
                  refine ⟨9506638347174241615921837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12675517796232322154562449 9506638347174241615921837)
                  ·
                    refine ⟨3564989380190340605970689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9506638347174241615921837 3564989380190340605970689)
                    ·
                      refine ⟨2673742035142755454478017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3564989380190340605970689 2673742035142755454478017)
                      ·
                        rfl

theorem cell23_5207094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_5207094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207094 prefixEnd_5207094 := by exact prefixLift 5207094
  have htrace : WordTrace (prefixWord ++ tailWord_5207094) baseStart_5207094 baseEnd_5207094 := by
    simpa [prefixWord, tailWord_5207094, baseEnd_5207094] using wordTrace_append hprefix tailTrace_5207094
  have hstable : (prefixWord ++ tailWord_5207094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207094).length < 2 ^ (prefixWord ++ tailWord_5207094).sum := by decide
  have hdescent : baseEnd_5207094 < baseStart_5207094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207117 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_5207117 : Nat := 118140960795 + 5207117 * 2 ^ 59
def prefixEnd_5207117 : Nat := 4983230072969 + 3 ^ 40 * 5207117 * 2
def baseEnd_5207117 : Nat := 891251281732602954830137

theorem tailTrace_5207117 : CollatzResearch.WordTrace tailWord_5207117 prefixEnd_5207117 891251281732602954830137 := by
  unfold tailWord_5207117
  simp only [CollatzResearch.WordTrace]
  refine ⟨189919159476511888627539605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126612772984341259085026403 189919159476511888627539605)
  ·
    refine ⟨8902460600461494779415919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 189919159476511888627539605 8902460600461494779415919)
    ·
      refine ⟨13353690900692242169123879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8902460600461494779415919 13353690900692242169123879)
      ·
        refine ⟨20030536351038363253685819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13353690900692242169123879 20030536351038363253685819)
        ·
          refine ⟨30045804526557544880528729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20030536351038363253685819 30045804526557544880528729)
          ·
            refine ⟨22534353394918158660396547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30045804526557544880528729 22534353394918158660396547)
            ·
              refine ⟨33801530092377237990594821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22534353394918158660396547 33801530092377237990594821)
              ·
                refine ⟨6337786892320732123236529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33801530092377237990594821 6337786892320732123236529)
                ·
                  refine ⟨4753340169240549092427397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6337786892320732123236529 4753340169240549092427397)
                  ·
                    refine ⟨891251281732602954830137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4753340169240549092427397 891251281732602954830137)
                    ·
                      rfl

theorem cell23_5207117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_5207117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207117 prefixEnd_5207117 := by exact prefixLift 5207117
  have htrace : WordTrace (prefixWord ++ tailWord_5207117) baseStart_5207117 baseEnd_5207117 := by
    simpa [prefixWord, tailWord_5207117, baseEnd_5207117] using wordTrace_append hprefix tailTrace_5207117
  have hstable : (prefixWord ++ tailWord_5207117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207117).length < 2 ^ (prefixWord ++ tailWord_5207117).sum := by decide
  have hdescent : baseEnd_5207117 < baseStart_5207117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207134 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_5207134 : Nat := 118140960795 + 5207134 * 2 ^ 59
def prefixEnd_5207134 : Nat := 4983230072969 + 3 ^ 40 * 5207134 * 2
def baseEnd_5207134 : Nat := 891254191456311765992611

theorem tailTrace_5207134 : CollatzResearch.WordTrace tailWord_5207134 prefixEnd_5207134 891254191456311765992611 := by
  unfold tailWord_5207134
  simp only [CollatzResearch.WordTrace]
  refine ⟨23739972439681287566363557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126613186344966867020605637 23739972439681287566363557)
  ·
    refine ⟨4451244832440241418693167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23739972439681287566363557 4451244832440241418693167)
    ·
      refine ⟨6676867248660362128039751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4451244832440241418693167 6676867248660362128039751)
      ·
        refine ⟨10015300872990543192059627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6676867248660362128039751 10015300872990543192059627)
        ·
          refine ⟨15022951309485814788089441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10015300872990543192059627 15022951309485814788089441)
          ·
            refine ⟨11267213482114361091067081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15022951309485814788089441 11267213482114361091067081)
            ·
              refine ⟨8450410111585770818300311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11267213482114361091067081 8450410111585770818300311)
              ·
                refine ⟨12675615167378656227450467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8450410111585770818300311 12675615167378656227450467)
                ·
                  refine ⟨19013422751067984341175701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12675615167378656227450467 19013422751067984341175701)
                  ·
                    refine ⟨891254191456311765992611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19013422751067984341175701 891254191456311765992611)
                    ·
                      rfl

theorem cell23_5207134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_5207134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207134 prefixEnd_5207134 := by exact prefixLift 5207134
  have htrace : WordTrace (prefixWord ++ tailWord_5207134) baseStart_5207134 baseEnd_5207134 := by
    simpa [prefixWord, tailWord_5207134, baseEnd_5207134] using wordTrace_append hprefix tailTrace_5207134
  have hstable : (prefixWord ++ tailWord_5207134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207134).length < 2 ^ (prefixWord ++ tailWord_5207134).sum := by decide
  have hdescent : baseEnd_5207134 < baseStart_5207134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207140 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_5207140 : Nat := 118140960795 + 5207140 * 2 ^ 59
def prefixEnd_5207140 : Nat := 4983230072969 + 3 ^ 40 * 5207140 * 2
def baseEnd_5207140 : Nat := 2673765655252862274502805

theorem tailTrace_5207140 : CollatzResearch.WordTrace tailWord_5207140 prefixEnd_5207140 2673765655252862274502805 := by
  unfold tailWord_5207140
  simp only [CollatzResearch.WordTrace]
  refine ⟨94959999177714281777813437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126613332236952375703751249 94959999177714281777813437)
  ·
    refine ⟨35609999691642855666680039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94959999177714281777813437 35609999691642855666680039)
    ·
      refine ⟨53414999537464283500020059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35609999691642855666680039 53414999537464283500020059)
      ·
        refine ⟨80122499306196425250030089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53414999537464283500020059 80122499306196425250030089)
        ·
          refine ⟨60091874479647318937522567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80122499306196425250030089 60091874479647318937522567)
          ·
            refine ⟨90137811719470978406283851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60091874479647318937522567 90137811719470978406283851)
            ·
              refine ⟨135206717579206467609425777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90137811719470978406283851 135206717579206467609425777)
              ·
                refine ⟨101405038184404850707069333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135206717579206467609425777 101405038184404850707069333)
                ·
                  refine ⟨4753361164893977376893875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101405038184404850707069333 4753361164893977376893875)
                  ·
                    refine ⟨7130041747340966065340813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753361164893977376893875 7130041747340966065340813)
                    ·
                      refine ⟨2673765655252862274502805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130041747340966065340813 2673765655252862274502805)
                      ·
                        rfl

theorem cell23_5207140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_5207140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207140 prefixEnd_5207140 := by exact prefixLift 5207140
  have htrace : WordTrace (prefixWord ++ tailWord_5207140) baseStart_5207140 baseEnd_5207140 := by
    simpa [prefixWord, tailWord_5207140, baseEnd_5207140] using wordTrace_append hprefix tailTrace_5207140
  have hstable : (prefixWord ++ tailWord_5207140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207140).length < 2 ^ (prefixWord ++ tailWord_5207140).sum := by decide
  have hdescent : baseEnd_5207140 < baseStart_5207140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207161 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 1, 2, 3]
def baseStart_5207161 : Nat := 118140960795 + 5207161 * 2 ^ 59
def prefixEnd_5207161 : Nat := 4983230072969 + 3 ^ 40 * 5207161 * 2
def baseEnd_5207161 : Nat := 2673776438346606692340209

theorem tailTrace_5207161 : CollatzResearch.WordTrace tailWord_5207161 prefixEnd_5207161 2673776438346606692340209 := by
  unfold tailWord_5207161
  simp only [CollatzResearch.WordTrace]
  refine ⟨189920764288352484142141337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126613842858901656094760891 189920764288352484142141337)
  ·
    refine ⟨142440573216264363106606003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189920764288352484142141337 142440573216264363106606003)
    ·
      refine ⟨213660859824396544659909005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142440573216264363106606003 213660859824396544659909005)
      ·
        refine ⟨80122822434148704247465877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213660859824396544659909005 80122822434148704247465877)
        ·
          refine ⟨3755757301600720511599963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80122822434148704247465877 3755757301600720511599963)
          ·
            refine ⟨5633635952401080767399945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755757301600720511599963 5633635952401080767399945)
            ·
              refine ⟨4225226964300810575549959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5633635952401080767399945 4225226964300810575549959)
              ·
                refine ⟨6337840446451215863324939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225226964300810575549959 6337840446451215863324939)
                ·
                  refine ⟨9506760669676823794987409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6337840446451215863324939 9506760669676823794987409)
                  ·
                    refine ⟨7130070502257617846240557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9506760669676823794987409 7130070502257617846240557)
                    ·
                      refine ⟨2673776438346606692340209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130070502257617846240557 2673776438346606692340209)
                      ·
                        rfl

theorem cell23_5207161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_5207161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207161 prefixEnd_5207161 := by exact prefixLift 5207161
  have htrace : WordTrace (prefixWord ++ tailWord_5207161) baseStart_5207161 baseEnd_5207161 := by
    simpa [prefixWord, tailWord_5207161, baseEnd_5207161] using wordTrace_append hprefix tailTrace_5207161
  have hstable : (prefixWord ++ tailWord_5207161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207161).length < 2 ^ (prefixWord ++ tailWord_5207161).sum := by decide
  have hdescent : baseEnd_5207161 < baseStart_5207161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207180 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 3, 4, 2]
def baseStart_5207180 : Nat := 118140960795 + 5207180 * 2 ^ 59
def prefixEnd_5207180 : Nat := 4983230072969 + 3 ^ 40 * 5207180 * 2
def baseEnd_5207180 : Nat := 2673786194479042118002621

theorem tailTrace_5207180 : CollatzResearch.WordTrace tailWord_5207180 prefixEnd_5207180 2673786194479042118002621 := by
  unfold tailWord_5207180
  simp only [CollatzResearch.WordTrace]
  refine ⟨94960728637641825193541497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126614304850189100258055329 94960728637641825193541497)
  ·
    refine ⟨71220546478231368895156123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94960728637641825193541497 71220546478231368895156123)
    ·
      refine ⟨106830819717347053342734185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71220546478231368895156123 106830819717347053342734185)
      ·
        refine ⟨80123114788010290007050639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106830819717347053342734185 80123114788010290007050639)
        ·
          refine ⟨120184672182015435010575959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80123114788010290007050639 120184672182015435010575959)
          ·
            refine ⟨180277008273023152515863939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120184672182015435010575959 180277008273023152515863939)
            ·
              refine ⟨270415512409534728773795909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180277008273023152515863939 270415512409534728773795909)
              ·
                refine ⟨50702908576787761645086733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270415512409534728773795909 50702908576787761645086733)
                ·
                  refine ⟨19013590716295410616907525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50702908576787761645086733 19013590716295410616907525)
                  ·
                    refine ⟨3565048259305389490670161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19013590716295410616907525 3565048259305389490670161)
                    ·
                      refine ⟨2673786194479042118002621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565048259305389490670161 2673786194479042118002621)
                      ·
                        rfl

theorem cell23_5207180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_5207180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207180 prefixEnd_5207180 := by exact prefixLift 5207180
  have htrace : WordTrace (prefixWord ++ tailWord_5207180) baseStart_5207180 baseEnd_5207180 := by
    simpa [prefixWord, tailWord_5207180, baseEnd_5207180] using wordTrace_append hprefix tailTrace_5207180
  have hstable : (prefixWord ++ tailWord_5207180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207180).length < 2 ^ (prefixWord ++ tailWord_5207180).sum := by decide
  have hdescent : baseEnd_5207180 < baseStart_5207180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207183 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 3]
def baseStart_5207183 : Nat := 118140960795 + 5207183 * 2 ^ 59
def prefixEnd_5207183 : Nat := 4983230072969 + 3 ^ 40 * 5207183 * 2
def baseEnd_5207183 : Nat := 2673787734921005606265107

theorem tailTrace_5207183 : CollatzResearch.WordTrace tailWord_5207183 prefixEnd_5207183 2673787734921005606265107 := by
  unfold tailWord_5207183
  simp only [CollatzResearch.WordTrace]
  refine ⟨189921566694272781899442203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126614377796181854599628135 189921566694272781899442203)
  ·
    refine ⟨284882350041409172849163305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189921566694272781899442203 284882350041409172849163305)
    ·
      refine ⟨213661762531056879636872479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284882350041409172849163305 213661762531056879636872479)
      ·
        refine ⟨320492643796585319455308719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213661762531056879636872479 320492643796585319455308719)
        ·
          refine ⟨480738965694877979182963079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320492643796585319455308719 480738965694877979182963079)
          ·
            refine ⟨721108448542316968774444619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480738965694877979182963079 721108448542316968774444619)
            ·
              refine ⟨1081662672813475453161666929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721108448542316968774444619 1081662672813475453161666929)
              ·
                refine ⟨811247004610106589871250197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081662672813475453161666929 811247004610106589871250197)
                ·
                  refine ⟨38027203341098746400214853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 811247004610106589871250197 38027203341098746400214853)
                  ·
                    refine ⟨7130100626456014950040285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38027203341098746400214853 7130100626456014950040285)
                    ·
                      refine ⟨2673787734921005606265107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130100626456014950040285 2673787734921005606265107)
                      ·
                        rfl

theorem cell23_5207183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_5207183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207183 prefixEnd_5207183 := by exact prefixLift 5207183
  have htrace : WordTrace (prefixWord ++ tailWord_5207183) baseStart_5207183 baseEnd_5207183 := by
    simpa [prefixWord, tailWord_5207183, baseEnd_5207183] using wordTrace_append hprefix tailTrace_5207183
  have hstable : (prefixWord ++ tailWord_5207183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207183).length < 2 ^ (prefixWord ++ tailWord_5207183).sum := by decide
  have hdescent : baseEnd_5207183 < baseStart_5207183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207250 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_5207250 : Nat := 118140960795 + 5207250 * 2 ^ 59
def prefixEnd_5207250 : Nat := 4983230072969 + 3 ^ 40 * 5207250 * 2
def baseEnd_5207250 : Nat := 891274046041618948042433

theorem tailTrace_5207250 : CollatzResearch.WordTrace tailWord_5207250 prefixEnd_5207250 891274046041618948042433 := by
  unfold tailWord_5207250
  simp only [CollatzResearch.WordTrace]
  refine ⟨47481002596257513085532801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126616006923353368228087469 47481002596257513085532801)
  ·
    refine ⟨35610751947193134814149601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47481002596257513085532801 35610751947193134814149601)
    ·
      refine ⟨26708063960394851110612201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35610751947193134814149601 26708063960394851110612201)
      ·
        refine ⟨20031047970296138332959151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26708063960394851110612201 20031047970296138332959151)
        ·
          refine ⟨30046571955444207499438727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20031047970296138332959151 30046571955444207499438727)
          ·
            refine ⟨45069857933166311249158091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30046571955444207499438727 45069857933166311249158091)
            ·
              refine ⟨67604786899749466873737137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45069857933166311249158091 67604786899749466873737137)
              ·
                refine ⟨50703590174812100155302853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67604786899749466873737137 50703590174812100155302853)
                ·
                  refine ⟨9506923157777268779119285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50703590174812100155302853 9506923157777268779119285)
                  ·
                    refine ⟨891274046041618948042433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9506923157777268779119285 891274046041618948042433)
                    ·
                      rfl

theorem cell23_5207250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_5207250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207250 prefixEnd_5207250 := by exact prefixLift 5207250
  have htrace : WordTrace (prefixWord ++ tailWord_5207250) baseStart_5207250 baseEnd_5207250 := by
    simpa [prefixWord, tailWord_5207250, baseEnd_5207250] using wordTrace_append hprefix tailTrace_5207250
  have hstable : (prefixWord ++ tailWord_5207250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207250).length < 2 ^ (prefixWord ++ tailWord_5207250).sum := by decide
  have hdescent : baseEnd_5207250 < baseStart_5207250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207263 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 2, 8]
def baseStart_5207263 : Nat := 118140960795 + 5207263 * 2 ^ 59
def prefixEnd_5207263 : Nat := 4983230072969 + 3 ^ 40 * 5207263 * 2
def baseEnd_5207263 : Nat := 891276271124455097754913

theorem tailTrace_5207263 : CollatzResearch.WordTrace tailWord_5207263 prefixEnd_5207263 891276271124455097754913 := by
  unfold tailWord_5207263
  simp only [CollatzResearch.WordTrace]
  refine ⟨189924484533982955562354443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126616323022655303708236295 189924484533982955562354443)
  ·
    refine ⟨284886726800974433343531665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189924484533982955562354443 284886726800974433343531665)
    ·
      refine ⟨213665045100730825007648749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284886726800974433343531665 213665045100730825007648749)
      ·
        refine ⟨80124391912774059377868281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213665045100730825007648749 80124391912774059377868281)
        ·
          refine ⟨60093293934580544533401211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80124391912774059377868281 60093293934580544533401211)
          ·
            refine ⟨90139940901870816800101817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60093293934580544533401211 90139940901870816800101817)
            ·
              refine ⟨67604955676403112600076363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90139940901870816800101817 67604955676403112600076363)
              ·
                refine ⟨101407433514604668900114545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67604955676403112600076363 101407433514604668900114545)
                ·
                  refine ⟨76055575135953501675085909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101407433514604668900114545 76055575135953501675085909)
                  ·
                    refine ⟨891276271124455097754913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76055575135953501675085909 891276271124455097754913)
                    ·
                      rfl

theorem cell23_5207263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_5207263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207263 prefixEnd_5207263 := by exact prefixLift 5207263
  have htrace : WordTrace (prefixWord ++ tailWord_5207263) baseStart_5207263 baseEnd_5207263 := by
    simpa [prefixWord, tailWord_5207263, baseEnd_5207263] using wordTrace_append hprefix tailTrace_5207263
  have hstable : (prefixWord ++ tailWord_5207263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207263).length < 2 ^ (prefixWord ++ tailWord_5207263).sum := by decide
  have hdescent : baseEnd_5207263 < baseStart_5207263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207273 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_5207273 : Nat := 118140960795 + 5207273 * 2 ^ 59
def prefixEnd_5207273 : Nat := 4983230072969 + 3 ^ 40 * 5207273 * 2
def baseEnd_5207273 : Nat := 2673833948179910254139693

theorem tailTrace_5207273 : CollatzResearch.WordTrace tailWord_5207273 prefixEnd_5207273 2673833948179910254139693 := by
  unfold tailWord_5207273
  simp only [CollatzResearch.WordTrace]
  refine ⟨189924849263946727270218473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126616566175964484846812315 189924849263946727270218473)
  ·
    refine ⟨142443636947960045452663855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189924849263946727270218473 142443636947960045452663855)
    ·
      refine ⟨213665455421940068178995783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142443636947960045452663855 213665455421940068178995783)
      ·
        refine ⟨320498183132910102268493675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213665455421940068178995783 320498183132910102268493675)
        ·
          refine ⟨480747274699365153402740513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320498183132910102268493675 480747274699365153402740513)
          ·
            refine ⟨360560456024523865052055385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480747274699365153402740513 360560456024523865052055385)
            ·
              refine ⟨270420342018392898789041539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360560456024523865052055385 270420342018392898789041539)
              ·
                refine ⟨405630513027589348183562309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270420342018392898789041539 405630513027589348183562309)
                ·
                  refine ⟨76055721192673002784417933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405630513027589348183562309 76055721192673002784417933)
                  ·
                    refine ⟨28520895447252376044156725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76055721192673002784417933 28520895447252376044156725)
                    ·
                      refine ⟨2673833948179910254139693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28520895447252376044156725 2673833948179910254139693)
                      ·
                        rfl

theorem cell23_5207273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_5207273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207273 prefixEnd_5207273 := by exact prefixLift 5207273
  have htrace : WordTrace (prefixWord ++ tailWord_5207273) baseStart_5207273 baseEnd_5207273 := by
    simpa [prefixWord, tailWord_5207273, baseEnd_5207273] using wordTrace_append hprefix tailTrace_5207273
  have hstable : (prefixWord ++ tailWord_5207273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207273).length < 2 ^ (prefixWord ++ tailWord_5207273).sum := by decide
  have hdescent : baseEnd_5207273 < baseStart_5207273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207304 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_5207304 : Nat := 118140960795 + 5207304 * 2 ^ 59
def prefixEnd_5207304 : Nat := 4983230072969 + 3 ^ 40 * 5207304 * 2
def baseEnd_5207304 : Nat := 2673849866080199632852051

theorem tailTrace_5207304 : CollatzResearch.WordTrace tailWord_5207304 prefixEnd_5207304 2673849866080199632852051 := by
  unfold tailWord_5207304
  simp only [CollatzResearch.WordTrace]
  refine ⟨94962989963417209782298483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126617319951222946376397977 94962989963417209782298483)
  ·
    refine ⟨142444484945125814673447725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94962989963417209782298483 142444484945125814673447725)
    ·
      refine ⟨53416681854422180502542897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142444484945125814673447725 53416681854422180502542897)
      ·
        refine ⟨40062511390816635376907173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53416681854422180502542897 40062511390816635376907173)
        ·
          refine ⟨7511720885778119133170095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40062511390816635376907173 7511720885778119133170095)
          ·
            refine ⟨11267581328667178699755143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511720885778119133170095 11267581328667178699755143)
            ·
              refine ⟨16901371993000768049632715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11267581328667178699755143 16901371993000768049632715)
              ·
                refine ⟨25352057989501152074449073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16901371993000768049632715 25352057989501152074449073)
                ·
                  refine ⟨19014043492125864055836805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25352057989501152074449073 19014043492125864055836805)
                  ·
                    refine ⟨3565133154773599510469401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19014043492125864055836805 3565133154773599510469401)
                    ·
                      refine ⟨2673849866080199632852051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565133154773599510469401 2673849866080199632852051)
                      ·
                        rfl

theorem cell23_5207304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_5207304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207304 prefixEnd_5207304 := by exact prefixLift 5207304
  have htrace : WordTrace (prefixWord ++ tailWord_5207304) baseStart_5207304 baseEnd_5207304 := by
    simpa [prefixWord, tailWord_5207304, baseEnd_5207304] using wordTrace_append hprefix tailTrace_5207304
  have hstable : (prefixWord ++ tailWord_5207304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207304).length < 2 ^ (prefixWord ++ tailWord_5207304).sum := by decide
  have hdescent : baseEnd_5207304 < baseStart_5207304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
